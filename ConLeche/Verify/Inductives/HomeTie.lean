module

public import ConLeche.Kernel.Inductives.RecHome
public import ConLeche.Verify.EnvExt.Ok
import ConLeche.Verify.EnvExt.FieldNf
import ConLeche.Verify.EnvExt.ScOps
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The home table at a later environment (PRIMREC / HOMETABLE)

The recursor check computes the home table itself (`homeTableRec`,
`Kernel/Inductives/RecCheck.lean`) at ITS environment; the walk's
records it must reproduce were made at the home's install environment.
This module is the member tie for the table: at two environments that
`Agree` on a scope (`Verify/EnvExt/`), the walk's context read at the
later environment's lookup and store (`NestCtx.atEnv`) — agreeing with the
earlier one on the scope, container by container (`CtxTie`) — a
successful table at the later environment is the table at the earlier
one (`homeTable_ok`, in the one-directional currency `Ok`).

The table reads the environment through the field-normal-form helper
(`nestTeleNf`, ENVEXT's `nestTeleNf_ok`) and through the context's
lookups: a leaf's container (`nestContainer`, `nestFrameMates`), its
instantiated former (`nestInstType`) and the members' formers
(`nestHoles`).  Every name read is scoped: a leaf is a scoped term, a
container's constructors are stored info of a scoped name.  A leaf the
table follows has no group-mates (`homeLeafNew`), so no mate is read.
-/

namespace ConLeche.EnvExt

open ConLeche

/-! ## Scoping through the table's term operations -/

variable {N : Name → Prop}

theorem sc_replaceConsts {f : Name → List Level → Option Expr}
    (hf : ∀ c us r, f c us = some r → Sc N r) : ∀ {e : Expr}, Sc N e → Sc N (e.replaceConsts f)
  | .bvar _, _ => by simp [Expr.replaceConsts]
  | .fvar _ ty, h => by
    simp only [Expr.replaceConsts, sc_fvar] at h ⊢; exact sc_replaceConsts hf h
  | .sort _, _ => by simp [Expr.replaceConsts]
  | .const c us, h => by
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none => exact h
    | some r => exact hf c us r hc
  | .app a b, h => by
    simp only [Expr.replaceConsts, sc_app] at h ⊢
    exact ⟨sc_replaceConsts hf h.1, sc_replaceConsts hf h.2⟩
  | .lam ty b _, h => by
    simp only [Expr.replaceConsts, sc_lam] at h ⊢
    exact ⟨sc_replaceConsts hf h.1, sc_replaceConsts hf h.2⟩
  | .forallE ty b _, h => by
    simp only [Expr.replaceConsts, sc_forallE] at h ⊢
    exact ⟨sc_replaceConsts hf h.1, sc_replaceConsts hf h.2⟩
  | .letE t v b, h => by
    simp only [Expr.replaceConsts, sc_letE] at h ⊢
    exact ⟨sc_replaceConsts hf h.1, sc_replaceConsts hf h.2.1, sc_replaceConsts hf h.2.2⟩
  | .lit _, h => by simpa [Expr.replaceConsts] using h
  | .proj _ _ e, h => by
    simp only [Expr.replaceConsts, sc_proj] at h ⊢
    exact ⟨h.1, sc_replaceConsts hf h.2⟩

theorem sc_instPisWith : ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, Sc N a) → Sc N e →
    instPisWith as e = some r → Sc N r
  | [], e, r, _, he, h => by simp only [instPisWith, Option.some.injEq] at h; exact h ▸ he
  | a :: as, .forallE _ body _, r, ha, he, h => by
    simp only [instPisWith] at h
    exact sc_instPisWith (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (sc_instantiate1' (sc_forallE.mp he).2 (ha a List.mem_cons_self)) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, h | _ :: _, .sort _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, h | _ :: _, .app _ _, _, _, _, h
  | _ :: _, .lam _ _ _, _, _, _, h | _ :: _, .letE _ _ _, _, _, _, h
  | _ :: _, .lit _, _, _, _, h | _ :: _, .proj _ _ _, _, _, _, h => by
    simp [instPisWith] at h

theorem sc_piLeaf : ∀ {e : Expr}, Sc N e → Sc N e.piLeaf
  | .forallE _ b _, h => by simp only [Expr.piLeaf]; exact sc_piLeaf (sc_forallE.mp h).2
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => h

/-! ## The currency over lists -/

namespace Ok

variable {α β : Type} {P : β → Prop}

theorem mapM {g f : α → CheckM β} :
    ∀ {l : List α}, (∀ a ∈ l, Ok P (g a) (f a)) →
      Ok (fun r => ∀ x ∈ r, P x) (l.mapM g) (l.mapM f)
  | [], _ => by
    simp only [List.mapM_nil]
    exact Ok.pure (fun _ h => nomatch h)
  | a :: l, h => by
    simp only [List.mapM_cons]
    refine Ok.bind (h a List.mem_cons_self) (fun b hb => ?_)
    refine Ok.bind (mapM (fun x hx => h x (List.mem_cons_of_mem _ hx))) (fun bs hbs => ?_)
    exact Ok.pure (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hbs x hx)

/-- A run that is the same at both environments, its successes
satisfying `P`. -/
theorem same {α : Type} {P : α → Prop} {x : CheckM α} (h : ∀ v, x = .ok v → P v) : Ok P x x :=
  fun v hv => ⟨hv, h v hv⟩

theorem unwrapOr {α : Type} {P : α → Prop} (o : Option α) (e : CheckError)
    (h : ∀ a, o = some a → P a) :
    Ok P (ConLeche.unwrapOr (m := CheckM) o e) (ConLeche.unwrapOr (m := CheckM) o e) := by
  cases o with
  | none => exact Ok.throw _
  | some a => exact Ok.pure (h a rfl)

end Ok

theorem option_mapM_congr {α β : Type} {g h : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, g a = h a) → l.mapM g = l.mapM h
  | [], _ => rfl
  | a :: l, hh => by
    simp only [List.mapM_cons]
    rw [hh a List.mem_cons_self, option_mapM_congr (fun x hx => hh x (List.mem_cons_of_mem _ hx))]

theorem option_mapM_mem' {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ y ∈ r, ∃ x ∈ l, g x = some y
  | [], r, h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact nomatch hy
  | a :: l, r, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases ha : g a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, hgx⟩ := option_mapM_mem' hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hgx⟩

theorem flatMap_congr' {α β : Type} {g h : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, g a = h a) → l.flatMap g = l.flatMap h
  | [], _ => rfl
  | a :: l, hh => by
    simp only [List.flatMap_cons]
    rw [hh a List.mem_cons_self, flatMap_congr' (fun x hx => hh x (List.mem_cons_of_mem _ hx))]

theorem filterMap_congr' {α β : Type} {g h : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, g a = h a) → l.filterMap g = l.filterMap h
  | [], _ => rfl
  | a :: l, hh => by
    simp only [List.filterMap_cons]
    rw [hh a List.mem_cons_self, filterMap_congr' (fun x hx => hh x (List.mem_cons_of_mem _ hx))]

/-- A container's constructors are stored constants' types. -/
theorem nestContainer_sc {ctx : NestCtx} (hc : ∀ ci ∈ ctx.consts, Sc N ci.toConstantVal.type)
    {C : Name} {q : Nat × List (ConstantVal × Nat)} (h : nestContainer ctx C = some q) :
    ∀ x ∈ q.2, Sc N x.1.type := by
  unfold nestContainer at h
  split at h
  · dsimp only at h
    generalize hcs : List.filterMap _ ctx.consts = cs at h
    have hall : ∀ y ∈ cs, Sc N y.1.type := by
      intro y hy
      rw [← hcs] at hy
      obtain ⟨ci, hci, hmap⟩ := List.mem_filterMap.mp hy
      split at hmap
      · split at hmap
        · split at hmap
          · split at hmap
            · simp only [Option.some.injEq] at hmap
              subst hmap
              exact hc _ hci
            · exact nomatch hmap
          · exact nomatch hmap
        · exact nomatch hmap
      · exact nomatch hmap
    cases cs with
    | nil => simp only [Option.some.injEq] at h; subst h; intro x hx; exact nomatch hx
    | cons y0 rest =>
      simp only [Option.some.injEq] at h
      subst h
      intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hall y hy
  · exact nomatch h

theorem option_mapM_all {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ a ∈ l, ∃ b, g a = some b
  | [], _, _, a, ha => nomatch ha
  | a :: l, r, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases ha : g a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [ha, hl] at h
      | some bs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, ha⟩
        · exact option_mapM_all hl x hx

/-- The members' names are stored where their holes were read. -/
theorem nestHoles_names {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes) :
    ∀ n ∈ ctx.names, (ctx.find? n).isSome = true := by
  intro n hn
  obtain ⟨mm, hmm, rfl⟩ := List.getElem_of_mem hn
  unfold nestHoles at h
  obtain ⟨x, hx⟩ := option_mapM_all h mm (List.mem_range.mpr hmm)
  have e : ctx.names.getD mm .anonymous = ctx.names[mm] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm, Option.getD_some]
  simp only [e] at hx
  split at hx
  · rename_i cv caps hf; rw [hf]; rfl
  · exact nomatch hx

/-- A telescope opened at variables: its variables and its rest are
scoped where the telescope is. -/
theorem sc_openPisAtFvars :
    ∀ {n : Nat} {e : Expr} {i : Nat} {fvs : List Expr} {rest : Expr}, Sc N e →
      openPisAtFvars n e i = some (fvs, rest) → (∀ x ∈ fvs, Sc N x) ∧ Sc N rest
  | 0, e, _, fvs, rest, he, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, .forallE dom body _, i, fvs, rest, he, h => by
    simp only [openPisAtFvars] at h
    have hpi := sc_forallE.mp he
    split at h
    · rename_i fvs' e' hrec
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := sc_openPisAtFvars (sc_instantiate1' hpi.2 (sc_fvar.mpr hpi.1)) hrec
      refine ⟨fun x hx => ?_, h2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sc_fvar.mpr hpi.1
      · exact h1 x hx
    · exact nomatch h
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => by simp [openPisAtFvars] at h

/-! ## The context at another environment -/

/-- The walk's context with another environment's lookup and store. -/
@[expose] def _root_.ConLeche.NestCtx.atEnv (ctx : NestCtx) (f : Name → Option ConstantInfo)
    (cs : List ConstantInfo) : NestCtx :=
  { ctx with find? := f, consts := cs }

/-- **The table's view of the two environments** (see the module
docstring): the knot's agreement, the context's lookups agreeing on the
scope, its stored info scoped, its containers agreeing at scoped
non-members and their constructors scoped, its parameters and members
scoped. -/
structure CtxTie (N : Name → Prop) (E₁ E₂ : Env) (ctx : NestCtx)
    (f : Name → Option ConstantInfo) (cs : List ConstantInfo) : Prop where
  agree : Agree N E₁ E₂
  find : ∀ {n : Name}, N n → f n = ctx.find? n
  closed : ∀ {n : Name} {ci : ConstantInfo}, N n → ctx.find? n = some ci → CiSc N ci
  cont : ∀ {C : Name}, N C → ctx.names.contains C = false →
    nestContainer (ctx.atEnv f cs) C = nestContainer ctx C
  contSc : ∀ {C : Name} {nPc : Nat} {cts : List (ConstantVal × Nat)}, N C →
    nestContainer ctx C = some (nPc, cts) → ∀ c ∈ cts, Sc N c.1.type
  params : ∀ x ∈ ctx.params, Sc N x
  names : ∀ n ∈ ctx.names, N n

/-- A recomputed constructor's leaves, scoped. -/
@[expose] def NfSc (N : Name → Prop) (n : NestClassCtorNf) : Prop :=
  ∀ l, some l ∈ n.leaves → Sc N l

/-- Every entry's leaves, scoped. -/
@[expose] def TabSc (N : Name → Prop) (T : List HomeEntry) : Prop :=
  ∀ e ∈ T, ∀ n ∈ e.nfs, NfSc N n

section Tie

variable {E₁ E₂ : Env} {ctx : NestCtx} {f : Name → Option ConstantInfo}
  {cs : List ConstantInfo} (H : CtxTie N E₁ E₂ ctx f cs) (mode : CheckMode) (F : Nat)
include H

omit H in
theorem nfSc_of {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
    {cv : ConstantVal} {nds : List (Expr × BinderMeta)} {cur : Expr}
    (hn : ∀ x ∈ nds, Sc N x.1) : NfSc N (nestClassCtorNfOf ctx prog hi us ds cv nds cur) := by
  intro l hl
  simp only [nestClassCtorNfOf, List.mem_map] at hl
  obtain ⟨q, hq, hql⟩ := hl
  split at hql
  · cases hql; exact sc_piLeaf (hn q hq)
  · exact nomatch hql

omit H in
theorem getD_mem_names {mm : Nat} (hm : mm < ctx.names.length) :
    ctx.names.getD mm .anonymous ∈ ctx.names := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; exact List.getElem_mem hm

/-- The members' holes read the members' formers alike. -/
theorem nestHoles_at : nestHoles (ctx.atEnv f cs) = nestHoles ctx := by
  unfold nestHoles
  refine option_mapM_congr (fun mm hm => ?_)
  have hm' : mm < ctx.names.length := List.mem_range.mp hm
  show (match f (ctx.names.getD mm .anonymous) with
      | some (.indInfo cv _) => some (Expr.fvar (ctx.nP + mm) cv.type) | _ => none) = _
  rw [H.find (H.names _ (getD_mem_names hm'))]
  rfl

/-- The holes are scoped. -/
theorem nestHoles_sc {holes : List Expr} (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, Sc N x := by
  intro x hx
  unfold nestHoles at h
  obtain ⟨mm, hmm, hx'⟩ := option_mapM_mem' h x hx
  have hm' : mm < ctx.names.length := List.mem_range.mp hmm
  split at hx'
  · rename_i cv caps hf
    cases hx'
    have := H.closed (H.names _ (getD_mem_names hm'))
      hf
    simp only [CiSc] at this
    exact sc_fvar.mpr this
  · exact nomatch hx'

/-- A member constructor, recomputed at the later environment. -/
theorem nestMemberCtorNf_ok {holes : List Expr} (hholes : ∀ x ∈ holes, Sc N x)
    {cv : ConstantVal} (hcv : Sc N cv.type) (nF : Nat) :
    Ok (NfSc N) (nestMemberCtorNf (fueledOps mode F) E₂ (ctx.atEnv f cs) holes cv nF)
      (nestMemberCtorNf (fueledOps mode F) E₁ ctx holes cv nF) := by
  have e : nestMemberCtorNf (fueledOps mode F) E₂ (ctx.atEnv f cs) holes cv nF
      = nestMemberCtorNf (fueledOps mode F) E₂ ctx holes cv nF := rfl
  refine Ok.rw_left e ?_
  unfold nestMemberCtorNf
  have habs : Sc N (nestAbstract ctx holes cv.type) := by
    unfold nestAbstract
    refine sc_replaceConsts (fun c us r hr => ?_) hcv
    split at hr
    · split at hr
      · exact hholes r (List.mem_of_getElem? hr)
      · exact nomatch hr
    · exact nomatch hr
  refine Ok.bind (Ok.unwrapOr _ _ (fun crest h => sc_instPisWith H.params habs h))
    (fun crest hcrest => ?_)
  refine Ok.bind (nestTeleNf_ok mode F _ _ _ H.agree _ _ _ _ hcrest) (fun r hr => ?_)
  exact Ok.pure (nfSc_of (fun x hx => hr.1 x hx))

/-- A container's instantiated former reads its container alike. -/
theorem nestInstType_at {hi : Nat} {key : NestKey} (hk : N key.cname) :
    nestInstType (m := CheckM) (ctx.atEnv f cs) hi key = nestInstType ctx hi key := by
  have e : (ctx.atEnv f cs).find? key.cname = ctx.find? key.cname := H.find hk
  unfold nestInstType
  rw [e]; rfl

/-- A container's group-mates read its record alike. -/
theorem nestFrameMates_at {I : Name} (hI : N I) :
    nestFrameMates (ctx.atEnv f cs) I = nestFrameMates ctx I := by
  have e : (ctx.atEnv f cs).find? I = ctx.find? I := H.find hI
  unfold nestFrameMates nestBlockOf
  rw [e]

/-- A group-mate-free container's group at a key, alike, its hole types
scoped. -/
theorem nestClassGroup_at {I : Name} (hI : N I) (hm : (nestFrameMates ctx I).isEmpty = true)
    (us : List Level) (ds : List Expr) :
    nestClassGroup (m := CheckM) (ctx.atEnv f cs) I us ds = nestClassGroup ctx I us ds ∧
      ∀ grp, nestClassGroup (m := CheckM) ctx I us ds = .ok grp → ∀ q ∈ grp, Sc N q.2 := by
  have hm0 : nestFrameMates ctx I = [] := by simpa using hm
  refine ⟨?_, fun grp h q hq => ?_⟩
  · unfold nestClassGroup
    rw [nestInstType_at H (key := ⟨I, us, ds⟩) hI, nestFrameMates_at H hI, hm0]
    rfl
  · unfold nestClassGroup at h
    rw [hm0] at h
    obtain ⟨⟨nI, cty⟩, hi, h⟩ := exceptBind_ok h
    simp only [nestGrowGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [List.mem_singleton] at hq
    subst hq
    obtain ⟨cvC, caps, hf, -, hcty, -⟩ := nestInstType_inv hi
    have hc := H.closed hI hf
    simp only [CiSc] at hc
    rw [hcty]
    exact sc_instantiateLevelParams _ _ _ hc

/-- A container constructor, recomputed at the later environment. -/
theorem nestFrameCtorNf_ok {us : List Level} {ds : List Expr} (hds : ∀ x ∈ ds, Sc N x)
    {grp : List (Name × Expr)} (hgrp : ∀ q ∈ grp, Sc N q.2) {cv : ConstantVal}
    (hcv : Sc N cv.type) (nF : Nat) :
    Ok (NfSc N) (nestFrameCtorNf (fueledOps mode F) E₂ (ctx.atEnv f cs) us ds grp cv nF)
      (nestFrameCtorNf (fueledOps mode F) E₁ ctx us ds grp cv nF) := by
  have e : nestFrameCtorNf (fueledOps mode F) E₂ (ctx.atEnv f cs) us ds grp cv nF
      = nestFrameCtorNf (fueledOps mode F) E₂ ctx us ds grp cv nF := rfl
  refine Ok.rw_left e ?_
  unfold nestFrameCtorNf
  have hsub : Sc N ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt 0) grp)) := by
    refine sc_replaceConsts (fun c us' r hr => ?_) (sc_instantiateLevelParams _ _ _ hcv)
    unfold grpSub at hr
    split at hr
    · obtain ⟨x, hx⟩ : ∃ x, (List.mapIdx (fun i (p : Name × Expr) => (p.1, Expr.fvar
          (ctx.hiAt 0 + i) p.2)) grp).lookup c = some x := ⟨r, hr⟩
      have hmem : (c, x) ∈ List.mapIdx (fun i (p : Name × Expr) => (p.1, Expr.fvar
          (ctx.hiAt 0 + i) p.2)) grp := by
        obtain ⟨l1, l2, heq, -⟩ := List.lookup_eq_some_iff.mp hx
        rw [heq]; exact List.mem_append_right _ List.mem_cons_self
      rw [List.mem_mapIdx] at hmem
      obtain ⟨i, hi, hq⟩ := hmem
      simp only [Prod.mk.injEq] at hq
      rw [hr] at hx; cases hx
      rw [← hq.2]
      exact sc_fvar.mpr (hgrp _ (List.getElem_mem hi))
    · exact nomatch hr
  refine Ok.bind (Ok.unwrapOr _ _ (fun crest h => sc_instPisWith hds hsub h))
    (fun crest hcrest => ?_)
  refine Ok.bind (nestTeleNf_ok mode F _ _ _ H.agree _ _ _ _ hcrest) (fun r hr => ?_)
  exact Ok.pure (nfSc_of (fun x hx => hr.1 x hx))

/-- A class's constructors at a member key, alike. -/
theorem homeEntryNfs_none_ok {holes : List Expr} (hholes : ∀ x ∈ holes, Sc N x) {I : Name}
    {us : List Level} {ctors : List (ConstantVal × Nat)} (hct : ∀ c ∈ ctors, Sc N c.1.type) :
    Ok (fun r => ∀ n ∈ r, NfSc N n)
      (homeEntryNfs (fueledOps mode F) E₂ (ctx.atEnv f cs) holes I us ctors none)
      (homeEntryNfs (fueledOps mode F) E₁ ctx holes I us ctors none) := by
  unfold homeEntryNfs
  exact Ok.mapM (fun c hc => nestMemberCtorNf_ok H mode F hholes (hct c hc) c.2)

/-- A class's constructors at a container key, alike. -/
theorem homeEntryNfs_some_ok {holes : List Expr} {I : Name} (hI : N I)
    (hm : (nestFrameMates ctx I).isEmpty = true) {us : List Level} {ds : List Expr}
    (hds : ∀ x ∈ ds, Sc N x) {ctors : List (ConstantVal × Nat)}
    (hct : ∀ c ∈ ctors, Sc N c.1.type) :
    Ok (fun r => ∀ n ∈ r, NfSc N n)
      (homeEntryNfs (fueledOps mode F) E₂ (ctx.atEnv f cs) holes I us ctors (some ds))
      (homeEntryNfs (fueledOps mode F) E₁ ctx holes I us ctors (some ds)) := by
  simp only [homeEntryNfs]
  obtain ⟨hg, hgs⟩ := nestClassGroup_at H hI hm us ds
  rw [hg]
  refine Ok.bind (Ok.same (fun grp h => hgs grp h)) (fun grp hgrp => ?_)
  exact Ok.mapM (fun c hc => nestFrameCtorNf_ok H mode F hds hgrp (hct c hc) c.2)

/-- What a followed leaf names: a scoped group-mate-free container, at
scoped parameters, its constructors scoped. -/
@[expose] def NewsOk (N : Name → Prop) (ctx : NestCtx)
    (q : Name × List Level × List Expr × Nat × List (ConstantVal × Nat)) : Prop :=
  N q.1 ∧ (nestFrameMates ctx q.1).isEmpty = true ∧ (∀ x ∈ q.2.2.1, Sc N x) ∧
    ∀ c ∈ q.2.2.2.2, Sc N c.1.type

/-- A scoped leaf names the same container instance at both
environments, and a scoped one. -/
theorem homeLeafNew_at {l : Expr} (hl : Sc N l) :
    homeLeafNew (ctx.atEnv f cs) l = homeLeafNew ctx l ∧
      ∀ q, homeLeafNew ctx l = some q → NewsOk N ctx q := by
  have hfn := sc_getAppFn hl
  have hargs := sc_getAppArgs hl
  unfold homeLeafNew
  split
  · rename_i I us hfI
    rw [hfI] at hfn
    have hI : N I := sc_const.mp hfn
    have hmates := nestFrameMates_at H hI
    by_cases hc : (ctx.names.contains I || !(nestFrameMates ctx I).isEmpty) = true
    · have hc' : ((ctx.atEnv f cs).names.contains I ||
          !(nestFrameMates (ctx.atEnv f cs) I).isEmpty) = true := by
        rw [hmates]; exact hc
      rw [if_pos hc', if_pos hc]
      exact ⟨rfl, fun _ h => nomatch h⟩
    · have hc' : ¬ ((ctx.atEnv f cs).names.contains I ||
          !(nestFrameMates (ctx.atEnv f cs) I).isEmpty) = true := by
        rw [hmates]; exact hc
      rw [if_neg hc', if_neg hc]
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true] at hc
      rw [H.cont hI hc.1]
      refine ⟨rfl, fun q hq => ?_⟩
      split at hq
      · rename_i nPc ctors hcont
        dsimp only at hq
        split at hq
        · obtain rfl := Option.some.inj hq
          exact ⟨hI, by simpa using hc.2, fun x hx => hargs x (List.mem_of_mem_take hx),
            fun c hc' => H.contSc hI hcont c hc'⟩
        · exact nomatch hq
      · exact nomatch hq
  · exact ⟨rfl, fun _ h => nomatch h⟩

/-- The followed leaves of a scoped table, alike, and scoped. -/
theorem homeNews_at {T : List HomeEntry} (hT : TabSc N T) :
    homeNews (ctx.atEnv f cs) T = homeNews ctx T ∧ ∀ q ∈ homeNews ctx T, NewsOk N ctx q := by
  unfold homeNews
  constructor
  · refine flatMap_congr' (fun e he => ?_)
    split
    · refine flatMap_congr' (fun n hn => ?_)
      refine filterMap_congr' (fun l? hl => ?_)
      cases l? with
      | none => rfl
      | some l => exact (homeLeafNew_at H (hT e he n hn l hl)).1
    · rfl
  · intro q hq
    simp only [List.mem_flatMap] at hq
    obtain ⟨e, he, hq⟩ := hq
    split at hq
    · simp only [List.mem_flatMap, List.mem_filterMap] at hq
      obtain ⟨n, hn, l?, hl, hq⟩ := hq
      cases l? with
      | none => exact nomatch hq
      | some l => exact (homeLeafNew_at H (hT e he n hn l hl)).2 q hq
    · exact nomatch hq

/-- The new instances, recomputed alike. -/
theorem homeAdd_ok {holes : List Expr} :
    ∀ {T : List HomeEntry} {news : List (Name × List Level × List Expr × Nat ×
        List (ConstantVal × Nat))}, TabSc N T → (∀ q ∈ news, NewsOk N ctx q) →
      Ok (TabSc N) (homeAdd (fueledOps mode F) E₂ (ctx.atEnv f cs) holes T news)
        (homeAdd (fueledOps mode F) E₁ ctx holes T news)
  | T, [], hT, _ => by simp only [homeAdd]; exact Ok.pure hT
  | T, (I, us, a, nPc, ctors) :: rest, hT, hq => by
    have hq0 := hq _ List.mem_cons_self
    have hrest := fun q h => hq q (List.mem_cons_of_mem _ h)
    simp only [homeAdd]
    refine Ok.ite (fun _ => homeAdd_ok hT hrest) (fun _ => ?_)
    refine Ok.bind (homeEntryNfs_some_ok H mode F hq0.1 hq0.2.1 hq0.2.2.1 hq0.2.2.2)
      (fun nfs hnfs => ?_)
    refine homeAdd_ok (fun e he n hn => ?_) hrest
    rcases List.mem_append.mp he with he | he
    · exact hT e he n hn
    · simp only [List.mem_singleton] at he
      subst he
      exact hnfs n hn

/-- The rounds, alike. -/
theorem homeIter_ok {holes : List Expr} :
    ∀ (fuel : Nat) {T : List HomeEntry}, TabSc N T →
      Ok (TabSc N) (homeIter (fueledOps mode F) E₂ (ctx.atEnv f cs) holes fuel T)
        (homeIter (fueledOps mode F) E₁ ctx holes fuel T)
  | 0, T, hT => by simp only [homeIter]; exact Ok.pure hT
  | fuel + 1, T, hT => by
    simp only [homeIter]
    obtain ⟨hn, hns⟩ := homeNews_at H hT
    rw [hn]
    refine Ok.bind (homeAdd_ok H mode F hT hns) (fun T' hT' => ?_)
    exact Ok.ite (fun _ => Ok.pure hT') (fun _ => homeIter_ok fuel hT')

/-- The member classes, alike. -/
theorem homeMembers_ok {holes : List Expr} (hholes : ∀ x ∈ holes, Sc N x)
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hct : ∀ t, ∀ c ∈ ctorsAs.getD t [], Sc N c.1.type) :
    Ok (TabSc N) (homeMembers (fueledOps mode F) E₂ (ctx.atEnv f cs) holes ctorsAs)
      (homeMembers (fueledOps mode F) E₁ ctx holes ctorsAs) := by
  unfold homeMembers
  refine Ok.mono (Ok.mapM (P := fun e : HomeEntry => ∀ n ∈ e.nfs, NfSc N n)
    (fun t _ => ?_)) (fun T hT e he => hT e he)
  refine Ok.bind (homeEntryNfs_none_ok H mode F hholes (hct t)) (fun nfs hnfs => ?_)
  exact Ok.pure hnfs

/-- **The home table at a later environment**: a success there is the
table at the earlier environment. -/
theorem homeTable_ok {holes : List Expr} (hholes : ∀ x ∈ holes, Sc N x)
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hct : ∀ t, ∀ c ∈ ctorsAs.getD t [], Sc N c.1.type) (fuel : Nat) :
    Ok (TabSc N) (homeTable (fueledOps mode F) E₂ (ctx.atEnv f cs) holes ctorsAs fuel)
      (homeTable (fueledOps mode F) E₁ ctx holes ctorsAs fuel) := by
  unfold homeTable
  exact Ok.bind (homeMembers_ok H mode F hholes hct) (fun T hT => homeIter_ok H mode F fuel hT)

end Tie

end ConLeche.EnvExt
