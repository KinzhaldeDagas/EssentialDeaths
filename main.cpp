#include "config.h"

#include "obse/EventManager.h"
#include "obse/GameActorValues.h"
#include "obse/GameAPI.h"
#include "obse/GameData.h"
#include "obse/GameForms.h"
#include "obse/GameObjects.h"
#include "obse/PluginAPI.h"
#include "obse_common/SafeWrite.h"

#include <algorithm>
#include <shlobj.h>
#include <utility>
#include <vector>
#include <windows.h>

PluginHandle g_pluginHandle = kPluginHandle_Invalid;

namespace
{
	enum
	{
		kPlayerBaseRefID = 0x00000007,
		kFormerEssentialRecord = 0x514E5545,
		kFormerEssentialRecordVersion = 1,
	};

	typedef void (__cdecl* OpenLoadGameMenuFn)(UInt32 loadMode);
	typedef UInt8 (*ConsumeMessageBoxButtonFn)(void);
	typedef void (__thiscall* ActorDamageAVFFn)(Actor* actor, UInt32 avCode, float amount, Actor* attacker);
	typedef void (__thiscall* ActorHandleDeathStateFn)(Actor* actor, UInt32 newDeadState);
	typedef void (__thiscall* ActorKillFn)(Actor* victim, Actor* killer, float unk);

	const OpenLoadGameMenuFn OpenLoadGameMenu = reinterpret_cast<OpenLoadGameMenuFn>(0x005AEA60);
	const ConsumeMessageBoxButtonFn ConsumeMessageBoxButton = reinterpret_cast<ConsumeMessageBoxButtonFn>(0x00578D70);
	const ActorHandleDeathStateFn CallActorHandleDeathState = reinterpret_cast<ActorHandleDeathStateFn>(0x005E6680);
	const ActorKillFn CallActorKill = reinterpret_cast<ActorKillFn>(0x006005F0);
	const UInt32 kVtblCharacterDamageAVF = 0x00A6FF40;
	const UInt32 kActorKillEssentialCheckPatch = 0x00600681;
	UInt32 g_actorKillEssentialCheckResume = 0x00600689;
	UInt32 g_actorKillNormalDeathPath = 0x00600865;
	const UInt32 kActorHandleDeathStateEssentialCheckPatch = 0x005E66B7;
	UInt32 g_actorHandleDeathStateEssentialCheckResume = 0x005E66BF;
	UInt32 g_actorHandleDeathStateSkipEssentialConversion = 0x005E66D2;

	OBSEMessagingInterface* g_messaging = NULL;
	OBSESerializationInterface* g_serialization = NULL;
	OBSEEventManagerInterface* g_eventManager = NULL;
	OBSETasksInterface* g_tasks = NULL;
	OBSETasks2Interface* g_tasks2 = NULL;
	Task<void>* g_scanTask = NULL;
	Task<bool>* g_loadMenuTask = NULL;

	std::vector<UInt32> g_formerEssentialNpcIds;
	std::vector<UInt32> g_warnedNpcIds;
	std::vector<UInt32> g_currentEssentialRefIds;
	std::vector<std::pair<TESNPC*, TESObjectREFR*> > g_pendingWarnings;
	std::vector<TESNPC*> g_pendingEssentialRestores;

	TESObjectCELL* g_trackedCell = NULL;

	bool g_scanEnabled = false;
	bool g_loadMenuRequested = false;
	bool g_warningMessageOpen = false;
	bool g_forcingEssentialDeath = false;
	bool g_inDamageAVFHook = false;
	UInt8 g_bypassEssentialKill = 0;
	UInt8 g_bypassDeathStateEssentialConversion = 0;
	UInt32 g_loadMenuDelayTicks = 0;
	UInt32 g_runtimeVersion = 0;
	UInt32 g_lastScanTick = 0;
	UInt32 g_scanCount = 0;
	ActorDamageAVFFn g_originalCharacterDamageAVF = NULL;

	const char* kProphecyWarning =
		"With this character's death, the thread of prophecy is severed. "
		"Restore a saved game to restore the weave of fate, or persist in the doomed world you have created.";

	const float kForcedDeathHealthDamage = 1000000.0f;

	void FlushPendingWarnings();
	void FlushPendingEssentialRestores();

	const char* SafeText(const char* text)
	{
		return text ? text : "";
	}

	UInt32 RefId(const TESForm* form)
	{
		return form ? form->refID : 0;
	}

	const char* NpcName(const TESNPC* npc)
	{
		return (npc && npc->fullName.name.m_data) ? npc->fullName.name.m_data : "";
	}

	bool ContainsId(const std::vector<UInt32>& values, UInt32 refID)
	{
		return std::find(values.begin(), values.end(), refID) != values.end();
	}

	void AddUniqueId(std::vector<UInt32>& values, UInt32 refID)
	{
		if (refID && !ContainsId(values, refID))
			values.push_back(refID);
	}

	bool IsFormerEssentialNPC(const TESNPC* npc)
	{
		return npc && ContainsId(g_formerEssentialNpcIds, RefId(npc));
	}

	TESObjectCELL* GetPlayerCell()
	{
		PlayerCharacter* player = (g_thePlayer && *g_thePlayer) ? *g_thePlayer : NULL;
		return player ? player->parentCell : NULL;
	}

	bool IsTrackedEssentialRef(TESObjectREFR* ref, TESNPC* npc)
	{
		return ref &&
			npc &&
			g_trackedCell &&
			ref->parentCell == g_trackedCell &&
			ContainsId(g_currentEssentialRefIds, RefId(ref)) &&
			IsFormerEssentialNPC(npc);
	}

	void TrackEssentialRef(TESObjectREFR* ref, TESNPC* npc)
	{
		if (!ref || !npc)
			return;

		AddUniqueId(g_formerEssentialNpcIds, RefId(npc));
		AddUniqueId(g_currentEssentialRefIds, RefId(ref));
	}

	bool EnsureTrackedEssentialRefAtKillGate(TESObjectREFR* ref, TESNPC* npc)
	{
		if (!ref || !npc)
			return false;

		if (!npc->actorBaseData.IsEssential() && !IsTrackedEssentialRef(ref, npc) && !IsFormerEssentialNPC(npc))
			return false;

		TESObjectCELL* currentCell = GetPlayerCell();
		if (!currentCell || ref->parentCell != currentCell)
			return false;

		if (g_trackedCell != currentCell)
		{
			g_trackedCell = currentCell;
			g_formerEssentialNpcIds.clear();
			g_currentEssentialRefIds.clear();
			_MESSAGE("EssentialUntilNoQuests: kill gate adopted current cell=%08X", RefId(g_trackedCell));
		}

		TrackEssentialRef(ref, npc);
		return IsTrackedEssentialRef(ref, npc);
	}

	void TemporarilyClearEssentialForKill(TESNPC* npc)
	{
		if (!npc || !npc->actorBaseData.IsEssential())
			return;

		if (std::find(g_pendingEssentialRestores.begin(), g_pendingEssentialRestores.end(), npc) == g_pendingEssentialRestores.end())
			g_pendingEssentialRestores.push_back(npc);

		npc->actorBaseData.flags &= ~TESActorBaseData::kFlag_IsEssential;
	}

	void ClearEssentialForDeath(TESNPC* npc)
	{
		if (!npc || !npc->actorBaseData.IsEssential())
			return;

		npc->actorBaseData.flags &= ~TESActorBaseData::kFlag_IsEssential;
	}

	void FlushPendingEssentialRestores()
	{
		for (std::vector<TESNPC*>::iterator it = g_pendingEssentialRestores.begin(); it != g_pendingEssentialRestores.end(); ++it)
		{
			if (*it)
				(*it)->actorBaseData.flags |= TESActorBaseData::kFlag_IsEssential;
		}

		g_pendingEssentialRestores.clear();
	}

	DataHandler* GetDataHandler()
	{
		return (g_dataHandler && *g_dataHandler) ? *g_dataHandler : NULL;
	}

	bool HasExactRuntime()
	{
		return g_runtimeVersion == OBLIVION_VERSION_1_2_416;
	}

	bool IsCompatible(const OBSEInterface* obse)
	{
		if (!obse)
			return false;

		if (obse->isEditor)
		{
			_ERROR("ERROR::EssentialUntilNoQuests: editor load is not supported");
			return false;
		}

		if (!IVersionCheck::IsCompatibleVersion(
			obse->oblivionVersion,
			MINIMUM_RUNTIME_VERSION,
			SUPPORTED_RUNTIME_VERSION,
			SUPPORTED_RUNTIME_VERSION_STRICT))
		{
			_ERROR("ERROR::EssentialUntilNoQuests: unsupported runtime version 0x%08X", obse->oblivionVersion);
			return false;
		}

		return true;
	}

	TESNPC* AsNPC(TESBoundObject* object)
	{
		if (!object || object->GetFormType() != kFormType_NPC)
			return NULL;

		TESNPC* npc = static_cast<TESNPC*>(object);
		return RefId(npc) == kPlayerBaseRefID ? NULL : npc;
	}

	void ScanEssentialNPCs(const char* reason)
	{
		TESObjectCELL* cell = g_trackedCell;
		if (!cell)
			return;

		UInt32 refCount = 0;
		UInt32 newlyTracked = 0;
		PlayerCharacter* player = (g_thePlayer && *g_thePlayer) ? *g_thePlayer : NULL;

		for (TESObjectCELL::ObjectListEntry* entry = &cell->objectList; entry; entry = entry->next)
		{
			TESObjectREFR* ref = entry->refr;
			if (!ref || (player && ref == static_cast<TESObjectREFR*>(player)))
				continue;

			TESForm* baseForm = ref->GetBaseForm();
			if (!baseForm || baseForm->GetFormType() != kFormType_NPC)
				continue;

			TESNPC* npc = static_cast<TESNPC*>(baseForm);
			if (RefId(npc) == kPlayerBaseRefID)
				continue;

			++refCount;

			if (npc->actorBaseData.IsEssential())
			{
				if (!IsFormerEssentialNPC(npc))
					++newlyTracked;

				TrackEssentialRef(ref, npc);
			}
		}

		++g_scanCount;

		if (newlyTracked || ESSENTIAL_LOG_UNCHANGED_SCANS)
		{
			_MESSAGE(
				"EssentialUntilNoQuests: cell scan reason=%s cell=%08X refs=%u trackedRefs=%u trackedBases=%u newlyTrackedBases=%u scanCount=%u",
				SafeText(reason),
				RefId(cell),
				refCount,
				static_cast<UInt32>(g_currentEssentialRefIds.size()),
				static_cast<UInt32>(g_formerEssentialNpcIds.size()),
				newlyTracked,
				g_scanCount);
		}
	}

	void ResetTrackedCell()
	{
		g_trackedCell = NULL;
		g_formerEssentialNpcIds.clear();
		g_currentEssentialRefIds.clear();
	}

	void UpdateTrackedCell(const char* reason)
	{
		TESObjectCELL* currentCell = GetPlayerCell();
		if (currentCell == g_trackedCell)
			return;

		FlushPendingEssentialRestores();

		if (g_trackedCell)
			_MESSAGE("EssentialUntilNoQuests: leaving cell=%08X; clearing %u essential refs", RefId(g_trackedCell), static_cast<UInt32>(g_currentEssentialRefIds.size()));

		g_trackedCell = currentCell;
		g_formerEssentialNpcIds.clear();
		g_currentEssentialRefIds.clear();

		if (g_trackedCell)
			ScanEssentialNPCs(reason);
	}

	void OpenRequestedLoadMenu()
	{
		if (!g_loadMenuRequested)
			return;

		if (g_loadMenuDelayTicks)
		{
			--g_loadMenuDelayTicks;
			return;
		}

		g_loadMenuRequested = false;
		_MESSAGE("EssentialUntilNoQuests: opening load-game menu after prophecy warning");
		OpenLoadGameMenu(0);
	}

	bool OpenLoadMenuTask()
	{
		if (!g_loadMenuRequested)
		{
			g_loadMenuTask = NULL;
			return true;
		}

		OpenRequestedLoadMenu();
		if (!g_loadMenuRequested)
		{
			g_loadMenuTask = NULL;
			return true;
		}

		return false;
	}

	void ScheduleLoadMenuFromWarning()
	{
		g_loadMenuRequested = true;
		g_loadMenuDelayTicks = 1;

		if (!g_tasks2)
		{
			g_loadMenuDelayTicks = 0;
			return;
		}

		if (!g_loadMenuTask || !g_tasks2->IsTaskPresentRemovable(g_loadMenuTask))
			g_loadMenuTask = g_tasks2->EnqueueTaskRemovable(OpenLoadMenuTask);
	}

	bool ShouldScan(UInt32 now)
	{
		return g_lastScanTick == 0 || (now - g_lastScanTick) >= ESSENTIAL_SCAN_INTERVAL_MS;
	}

	void ScanTask()
	{
		UpdateTrackedCell("cell-entry");
		FlushPendingEssentialRestores();
		OpenRequestedLoadMenu();
		FlushPendingWarnings();

		if (!g_scanEnabled)
			return;

		const UInt32 now = GetTickCount();
		if (!ShouldScan(now))
			return;

		g_lastScanTick = now;
		ScanEssentialNPCs("periodic");
	}

	void RequestImmediateScan(const char* reason)
	{
		g_scanEnabled = true;
		g_lastScanTick = GetTickCount();
		UpdateTrackedCell(reason);
		ScanEssentialNPCs(reason);
	}

	void ResetRuntimeState(bool clearFormerEssential)
	{
		g_warnedNpcIds.clear();
		g_warningMessageOpen = false;
		g_loadMenuRequested = false;
		g_loadMenuDelayTicks = 0;
		if (g_tasks2 && g_loadMenuTask && g_tasks2->IsTaskPresentRemovable(g_loadMenuTask))
			g_tasks2->RemoveTaskRemovable(g_loadMenuTask);
		g_loadMenuTask = NULL;
		g_lastScanTick = 0;
		FlushPendingEssentialRestores();
		ResetTrackedCell();
		g_pendingWarnings.clear();

		if (clearFormerEssential)
			g_formerEssentialNpcIds.clear();
	}

	void ProphecyWarningCallback()
	{
		const UInt8 button = ConsumeMessageBoxButton();
		g_warningMessageOpen = false;

		_MESSAGE("EssentialUntilNoQuests: prophecy warning button=%u", button);

		if (button == 2)
			ScheduleLoadMenuFromWarning();
	}

	void ShowProphecyWarning(TESNPC* npc, TESObjectREFR* deadRef)
	{
		const UInt32 npcId = RefId(npc);
		if (!npcId || ContainsId(g_warnedNpcIds, npcId))
			return;

		AddUniqueId(g_warnedNpcIds, npcId);

		_MESSAGE(
			"EssentialUntilNoQuests: former-essential NPC died npc=%08X ref=%08X name=\"%s\"",
			npcId,
			RefId(deadRef),
			SafeText(NpcName(npc)));

		if (g_warningMessageOpen)
			return;

		g_warningMessageOpen = true;
		*ShowMessageBox_button = 0xFF;
		*ShowMessageBox_pScriptRefID = 0;
		ShowMessageBox(kProphecyWarning, static_cast<_ShowMessageBox_Callback>(ProphecyWarningCallback), 1, "Continue", "Load", 0);
	}

	bool IsWarningPending(UInt32 npcId)
	{
		for (std::vector<std::pair<TESNPC*, TESObjectREFR*> >::const_iterator it = g_pendingWarnings.begin(); it != g_pendingWarnings.end(); ++it)
		{
			if (RefId(it->first) == npcId)
				return true;
		}

		return false;
	}

	void QueueProphecyWarning(TESNPC* npc, TESObjectREFR* deadRef)
	{
		const UInt32 npcId = RefId(npc);
		if (!npcId || ContainsId(g_warnedNpcIds, npcId) || IsWarningPending(npcId))
			return;

		g_pendingWarnings.push_back(std::make_pair(npc, deadRef));
	}

	void FlushPendingWarnings()
	{
		if (g_warningMessageOpen || g_pendingWarnings.empty())
			return;

		std::pair<TESNPC*, TESObjectREFR*> warning = g_pendingWarnings.front();
		g_pendingWarnings.erase(g_pendingWarnings.begin());
		ShowProphecyWarning(warning.first, warning.second);
	}

	TESObjectREFR* ResolveEventRef(void* arg0, TESObjectREFR* thisObj)
	{
		TESObjectREFR* ref = static_cast<TESObjectREFR*>(arg0);
		return ref ? ref : thisObj;
	}

	TESNPC* ResolveNPCFromRef(TESObjectREFR* ref)
	{
		if (!ref)
			return NULL;

		TESForm* baseForm = ref->GetBaseForm();
		if (!baseForm || baseForm->GetFormType() != kFormType_NPC)
			return NULL;

		return static_cast<TESNPC*>(baseForm);
	}

	bool __stdcall ShouldBypassEssentialKill(Actor* actor, TESForm* baseForm)
	{
		if (!actor || !baseForm || baseForm->GetFormType() != kFormType_NPC)
			return false;

		if (g_forcingEssentialDeath)
			return false;

		TESNPC* npc = static_cast<TESNPC*>(baseForm);
		TESObjectREFR* ref = static_cast<TESObjectREFR*>(actor);
		if (!EnsureTrackedEssentialRefAtKillGate(ref, npc))
			return false;

		ClearEssentialForDeath(npc);
		QueueProphecyWarning(npc, ref);
		_MESSAGE("EssentialUntilNoQuests: bypassing Actor_Kill essential branch ref=%08X base=%08X cell=%08X",
			RefId(ref), RefId(npc), RefId(g_trackedCell));
		return true;
	}

	bool __stdcall ShouldBypassEssentialDeathState(Actor* actor, TESForm* baseForm, UInt32 newDeadState)
	{
		if (!actor || !baseForm || baseForm->GetFormType() != kFormType_NPC)
			return false;

		if (g_forcingEssentialDeath)
			return false;

		if (newDeadState != 1 && newDeadState != 2)
			return false;

		TESNPC* npc = static_cast<TESNPC*>(baseForm);
		TESObjectREFR* ref = static_cast<TESObjectREFR*>(actor);
		if (!EnsureTrackedEssentialRefAtKillGate(ref, npc))
			return false;

		ClearEssentialForDeath(npc);
		QueueProphecyWarning(npc, ref);
		_MESSAGE("EssentialUntilNoQuests: bypassing Actor_HandleDeathState essential conversion ref=%08X base=%08X requestedState=%u cell=%08X",
			RefId(ref), RefId(npc), newDeadState, RefId(g_trackedCell));
		return true;
	}

	void __declspec(naked) HookActorKillEssentialCheck()
	{
		__asm
		{
			pushad
			push edi
			push esi
			call ShouldBypassEssentialKill
			mov [g_bypassEssentialKill], al
			popad

			cmp byte ptr [g_bypassEssentialKill], 0
			jnz BypassEssential

			mov ecx, [edi+28h]
			shr ecx, 1
			test cl, 1
			jmp [g_actorKillEssentialCheckResume]

		BypassEssential:
			jmp [g_actorKillNormalDeathPath]
		}
	}

	void __declspec(naked) HookActorHandleDeathStateEssentialCheck()
	{
		__asm
		{
			pushad
			push ebp
			push ebx
			push esi
			call ShouldBypassEssentialDeathState
			mov [g_bypassDeathStateEssentialConversion], al
			popad

			cmp byte ptr [g_bypassDeathStateEssentialConversion], 0
			jnz BypassDeathStateConversion

			mov eax, [ebx+28h]
			shr eax, 1
			test al, 1
			pop ebx
			jmp [g_actorHandleDeathStateEssentialCheckResume]

		BypassDeathStateConversion:
			pop ebx
			jmp [g_actorHandleDeathStateSkipEssentialConversion]
		}
	}

	void __fastcall HookCharacterDamageAVF(Actor* actor, void* edx, UInt32 avCode, float amount, Actor* attacker)
	{
		if (!g_originalCharacterDamageAVF)
			return;

		TESNPC* npc = NULL;
		const bool shouldWatch =
			!g_inDamageAVFHook &&
			actor &&
			avCode == kActorVal_Health &&
			amount < 0.0f &&
			(npc = ResolveNPCFromRef(static_cast<TESObjectREFR*>(actor))) &&
			IsTrackedEssentialRef(static_cast<TESObjectREFR*>(actor), npc) &&
			npc->actorBaseData.IsEssential();

		if (!shouldWatch)
		{
			g_originalCharacterDamageAVF(actor, avCode, amount, attacker);
			return;
		}

		g_inDamageAVFHook = true;
		g_originalCharacterDamageAVF(actor, avCode, amount, attacker);
		g_inDamageAVFHook = false;

		if (actor->DeadState == 1)
			QueueProphecyWarning(npc, static_cast<TESObjectREFR*>(actor));
	}

	void InstallDamageHook()
	{
		if (g_originalCharacterDamageAVF)
			return;

		g_originalCharacterDamageAVF = reinterpret_cast<ActorDamageAVFFn>(*reinterpret_cast<UInt32*>(kVtblCharacterDamageAVF));
		SafeWrite32(kVtblCharacterDamageAVF, reinterpret_cast<UInt32>(&HookCharacterDamageAVF));
		WriteRelJump(kActorKillEssentialCheckPatch, reinterpret_cast<UInt32>(&HookActorKillEssentialCheck));
		WriteRelJump(kActorHandleDeathStateEssentialCheckPatch, reinterpret_cast<UInt32>(&HookActorHandleDeathStateEssentialCheck));
		_MESSAGE("EssentialUntilNoQuests: installed Character::DamageAV_F watcher, Actor_Kill essential bypass hook, and Actor_HandleDeathState essential conversion bypass hook");
	}

	void ForceEssentialDeath(TESObjectREFR* ref, TESNPC* npc)
	{
		if (!ref || !npc || g_forcingEssentialDeath)
			return;

		Actor* actor = static_cast<Actor*>(ref);
		if (!actor || actor->DeadState == 1)
			return;

		if (actor->GetActorValue(kActorVal_Health) > 0.0f)
			return;

		_MESSAGE("EssentialUntilNoQuests: forcing unconscious essential death ref=%08X base=%08X deadState=%u health=%.2f cell=%08X",
			RefId(ref), RefId(npc), actor->DeadState, actor->GetActorValue(kActorVal_Health), RefId(g_trackedCell));

		ClearEssentialForDeath(npc);

		g_forcingEssentialDeath = true;

		if (actor->DeadState == 6)
		{
			_MESSAGE("EssentialUntilNoQuests: resetting essential unconscious state before native kill ref=%08X base=%08X",
				RefId(ref), RefId(npc));
			CallActorHandleDeathState(actor, 0);
		}

		CallActorKill(actor, NULL, 0.0f);

		_MESSAGE("EssentialUntilNoQuests: native Actor_Kill returned ref=%08X base=%08X deadState=%u",
			RefId(ref), RefId(npc), actor->DeadState);

		if (actor->DeadState != 1)
		{
			_MESSAGE("EssentialUntilNoQuests: forcing final death state ref=%08X base=%08X deadState=%u",
				RefId(ref), RefId(npc), actor->DeadState);
			CallActorHandleDeathState(actor, 1);
		}

		g_forcingEssentialDeath = false;

		ShowProphecyWarning(npc, ref);
	}

	void OnDeathEvent(void* arg0, void* arg1, TESObjectREFR* thisObj)
	{
		TESObjectREFR* deadRef = ResolveEventRef(arg0, thisObj);
		TESNPC* npc = ResolveNPCFromRef(deadRef);
		if (!npc || !IsFormerEssentialNPC(npc))
			return;

		ShowProphecyWarning(npc, deadRef);
	}

	void OnKnockoutEvent(void* arg0, void* arg1, TESObjectREFR* thisObj)
	{
		TESObjectREFR* knockedRef = ResolveEventRef(arg0, thisObj);
		TESNPC* npc = ResolveNPCFromRef(knockedRef);
		if (!npc || !IsFormerEssentialNPC(npc))
			return;

		ForceEssentialDeath(knockedRef, npc);
	}

	void SaveCallback(void* reserved)
	{
		if (!g_serialization)
			return;

		if (!g_serialization->OpenRecord(kFormerEssentialRecord, kFormerEssentialRecordVersion))
			return;

		const UInt32 count = 0;
		g_serialization->WriteRecordData(&count, sizeof(count));

		_MESSAGE("EssentialUntilNoQuests: skipped serialization of cell-scoped essential NPC list");
	}

	void LoadCallback(void* reserved)
	{
		if (!g_serialization)
			return;

		g_formerEssentialNpcIds.clear();

		UInt32 type = 0;
		UInt32 version = 0;
		UInt32 length = 0;
		while (g_serialization->GetNextRecordInfo(&type, &version, &length))
		{
			if (type != kFormerEssentialRecord || version != kFormerEssentialRecordVersion || length < sizeof(UInt32))
				continue;

			UInt32 count = 0;
			if (g_serialization->ReadRecordData(&count, sizeof(count)) != sizeof(count))
				continue;

			for (UInt32 i = 0; i < count; ++i)
			{
				UInt32 storedRefID = 0;
				if (g_serialization->ReadRecordData(&storedRefID, sizeof(storedRefID)) != sizeof(storedRefID))
					break;

				UInt32 resolvedRefID = 0;
				if (g_serialization->ResolveRefID(storedRefID, &resolvedRefID))
					AddUniqueId(g_formerEssentialNpcIds, resolvedRefID);
			}
		}

		g_formerEssentialNpcIds.clear();
		g_currentEssentialRefIds.clear();
		_MESSAGE("EssentialUntilNoQuests: ignored persisted former-essential NPC ids; tracking is cell-scoped");
	}

	void NewGameCallback(void* reserved)
	{
		ResetRuntimeState(true);
		RequestImmediateScan("new-game");
	}

	void MessageHandler(OBSEMessagingInterface::Message* msg)
	{
		if (!msg)
			return;

		switch (msg->type)
		{
			case OBSEMessagingInterface::kMessage_PostLoad:
				RequestImmediateScan("post-load");
				break;

			case OBSEMessagingInterface::kMessage_PostPostLoad:
				RequestImmediateScan("post-post-load");
				break;

			case OBSEMessagingInterface::kMessage_GameInitialized:
				RequestImmediateScan("game-initialized");
				break;

			case OBSEMessagingInterface::kMessage_PreLoadGame:
				ResetRuntimeState(true);
				break;

			case OBSEMessagingInterface::kMessage_LoadGame:
				RequestImmediateScan("load-game");
				break;

			case OBSEMessagingInterface::kMessage_PostLoadGame:
				if (msg->data)
					RequestImmediateScan("post-load-game");
				else
					_MESSAGE("EssentialUntilNoQuests: skipped post-load-game scan because load failed");
				break;

			case OBSEMessagingInterface::kMessage_ExitGame:
			case OBSEMessagingInterface::kMessage_ExitGame_Console:
				g_scanEnabled = false;
				break;

			case OBSEMessagingInterface::kMessage_ExitToMainMenu:
				ResetRuntimeState(false);
				break;
		}
	}

	void InstallMessaging(const OBSEInterface* obse)
	{
		g_messaging = static_cast<OBSEMessagingInterface*>(obse->QueryInterface(kInterface_Messaging));
		if (!g_messaging)
		{
			_ERROR("ERROR::EssentialUntilNoQuests: OBSE messaging interface unavailable");
			return;
		}

		if (g_messaging->RegisterListener(g_pluginHandle, "OBSE", MessageHandler))
			_MESSAGE("EssentialUntilNoQuests: registered OBSE message listener");
		else
			_ERROR("ERROR::EssentialUntilNoQuests: failed to register OBSE message listener");
	}

	void InstallSerialization(const OBSEInterface* obse)
	{
		g_serialization = static_cast<OBSESerializationInterface*>(obse->QueryInterface(kInterface_Serialization));
		if (!g_serialization)
		{
			_ERROR("ERROR::EssentialUntilNoQuests: OBSE serialization interface unavailable; former-essential NPC list will not persist");
			return;
		}

		g_serialization->SetSaveCallback(g_pluginHandle, SaveCallback);
		g_serialization->SetLoadCallback(g_pluginHandle, LoadCallback);
		g_serialization->SetNewGameCallback(g_pluginHandle, NewGameCallback);
		_MESSAGE("EssentialUntilNoQuests: registered serialization callbacks");
	}

	void InstallEventHandlers(const OBSEInterface* obse)
	{
		g_eventManager = static_cast<OBSEEventManagerInterface*>(obse->QueryInterface(kInterface_EventManager));
		if (!g_eventManager)
		{
			_ERROR("ERROR::EssentialUntilNoQuests: OBSE event manager interface unavailable; knockout/death handling disabled");
			return;
		}

		if (g_eventManager->RegisterEvent("ondeath", OnDeathEvent, NULL, NULL, NULL))
			_MESSAGE("EssentialUntilNoQuests: registered ondeath handler");
		else
			_ERROR("ERROR::EssentialUntilNoQuests: failed to register ondeath handler");

		if (g_eventManager->RegisterEvent("onknockout", OnKnockoutEvent, NULL, NULL, NULL))
			_MESSAGE("EssentialUntilNoQuests: registered onknockout handler");
		else
			_ERROR("ERROR::EssentialUntilNoQuests: failed to register onknockout handler");
	}

	void InstallScanTask(const OBSEInterface* obse)
	{
		g_tasks2 = static_cast<OBSETasks2Interface*>(obse->QueryInterface(kInterface_Tasks2));
		g_tasks = static_cast<OBSETasksInterface*>(obse->QueryInterface(kInterface_Tasks));

		if (g_tasks2)
			g_scanTask = g_tasks2->EnqueueTask(ScanTask);
		else if (g_tasks)
			g_scanTask = g_tasks->EnqueueTask(ScanTask);

		if (g_scanTask)
			_MESSAGE("EssentialUntilNoQuests: installed periodic scan task intervalMs=%u", ESSENTIAL_SCAN_INTERVAL_MS);
		else
			_ERROR("ERROR::EssentialUntilNoQuests: OBSE task interface unavailable; only message-triggered scans will run");
	}
}

extern "C"
{
	bool OBSEPlugin_Query(const OBSEInterface* obse, PluginInfo* info)
	{
		gLog.OpenRelative(CSIDL_MYDOCUMENTS, PLUGIN_LOG_FILE);
		_MESSAGE(PLUGIN_VERSION_INFO);
		_MESSAGE("Plugin_Query: Querying");

		info->infoVersion = PluginInfo::kInfoVersion;
		info->name = PLUGIN_NAME_LONG;
		info->version = PLUGIN_VERSION_DLL;

		if (!IsCompatible(obse))
			return false;

		_MESSAGE("Plugin_Query: Queried Successfully");
		return true;
	}

	bool OBSEPlugin_Load(const OBSEInterface* obse)
	{
		gLog.OpenRelative(CSIDL_MYDOCUMENTS, PLUGIN_LOG_FILE);
		_MESSAGE(PLUGIN_VERSION_INFO);
		_MESSAGE("Plugin_Load: Loading");

		if (!IsCompatible(obse))
			return false;

		g_pluginHandle = obse->GetPluginHandle();
		g_runtimeVersion = obse->oblivionVersion;

		if (!HasExactRuntime())
		{
			_ERROR("ERROR::EssentialUntilNoQuests: exact Oblivion 1.2.0416 runtime required; got 0x%08X", g_runtimeVersion);
			return false;
		}

		InstallMessaging(obse);
		InstallSerialization(obse);
		InstallDamageHook();
		InstallScanTask(obse);

		_MESSAGE("Plugin_Load: Loaded Successfully");
		return true;
	}
}
