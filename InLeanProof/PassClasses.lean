module

public import InLeanProof.PassNestKey
import ConLeche.Verify.Denote.IndFrame
import InLeanProof.DeclGuards
import ConLeche.Verify.Inductives.RecCheckScope

/-!
# O7-classes: the classes the recursors eliminate (task #451, lane O7-classes)

The pass's class stage (`checkBlockClasses`) against master's, piece by piece:

* `classReadMinorI_run`, `classReadSlotsI_run`, `classReadI_run`: InLean's
  pre-pass (the recursors' prefix opened at interned variables, two `for`
  loops) reads, at the final state, as master's pure `classRead` on the
  translated recursors (`trCR`: the keys' parameters through `TrS`).

The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## The translations -/

/-- A class key, read at a state. -/
@[expose] def trCK (s : InLean.CState) (k : InLean.ClassKey) : ConLeche.ClassKey :=
  ⟨toName k.ind, k.lvls.map trL, TrSL s k.ds⟩

/-- A prefix slot, read at a state. -/
@[expose] def trSlot (s : InLean.CState) : InLean.ClassSlot → ConLeche.ClassSlot
  | .motive k => .motive (trCK s k)
  | .minor c C ihs => .minor c (toName C) ihs

/-- The pre-pass's reading, at a state. -/
@[expose] def trCR (s : InLean.CState) (r : InLean.ClassRead) : ConLeche.ClassRead :=
  ⟨r.slots.map (trSlot s), r.recCls⟩

/-- A slot has a reading: its key's levels and parameters. -/
@[expose] def OkSlot (s : InLean.CState) : InLean.ClassSlot → Prop
  | .motive k => k.lvls.all okLv = true ∧ OkSL s k.ds = true
  | .minor .. => True

theorem OkSlot.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {x : InLean.ClassSlot}, OkSlot s₀ x → OkSlot s₁ x
  | .motive _, ⟨h1, h2⟩ => ⟨h1, okSL_of_tabLe h h2⟩
  | .minor .., _ => trivial

theorem trSlot_mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {x : InLean.ClassSlot}, OkSlot s₀ x → trSlot s₁ x = trSlot s₀ x
  | .motive k, ⟨_, h2⟩ => by simp only [trSlot, trCK, TrSL_of_tabLe h h2]
  | .minor .., _ => rfl

theorem classOfMotiveVar_tr : @ConLeche.classOfMotiveVar = @InLean.classOfMotiveVar := rfl

/-! ## Heads through the translation -/

theorem OkS_piResult {s : InLean.CState} : ∀ {e : Lean.Expr}, OkS s e = true →
    OkS s (InLean.piResult e) = true
  | .mdata _ e, h => by rw [InLean.piResult]; exact OkS_piResult h
  | .forallE _ t b _, h => by
    rw [InLean.piResult]
    simp only [OkS_forallE, Bool.and_eq_true] at h
    exact OkS_piResult h.2
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .app .., h | .lam .., h
  | .letE .., h | .lit _, h | .proj .., h => h

/-- A variable head, read: InLean's depth is the translation's head's index. -/
theorem headDepth_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    (∀ p, InLean.headDepth? e = some p → ∃ ty, (TrS s e).getAppFn = .fvar p ty) ∧
      (InLean.headDepth? e = none → ∀ p ty, (TrS s e).getAppFn ≠ .fvar p ty) := by
  unfold InLean.headDepth?
  rw [← TrS_getAppFnT]
  have hok := OkS_getAppFnT s h
  have hst := stripTop_getAppFnT e
  generalize Expr.getAppFnT e = x at hok hst ⊢
  cases x with
  | fvar id =>
    obtain ⟨d, ty, ht, hd⟩ := TrS_stripTop_fvar hok rfl
    rw [ht]
    simp only [hd]
    exact ⟨fun p hp => ⟨ty, by cases hp; rfl⟩, fun h => by cases h⟩
  | mdata m y => exact (stripTop_ne_mdata hst).elim
  | _ =>
    refine ⟨fun p hp => by simp at hp, fun _ p ty => ?_⟩
    exact TrS_not_fvar hok (fun id hid => by simp [hst] at hid) p ty

/-- A constant head, read. -/
theorem constHead_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    (∀ C us, e.getAppFnT = .const C us → (TrS s e).getAppFn = .const (toName C) (us.map trL)) ∧
      ((∀ C us, e.getAppFnT ≠ .const C us) → ∀ C us, (TrS s e).getAppFn ≠ .const C us) := by
  rw [← TrS_getAppFnT]
  have hok := OkS_getAppFnT s h
  have hst := stripTop_getAppFnT e
  generalize Expr.getAppFnT e = x at hok hst ⊢
  cases x with
  | const C us => exact ⟨fun C' us' h => by cases h; rfl, fun h => (h C us rfl).elim⟩
  | fvar id =>
    refine ⟨fun _ _ h => by simp at h, fun _ C us => ?_⟩
    rw [TrS_fvar hok]; exact fun h => by simp at h
  | mdata m y => exact (stripTop_ne_mdata hst).elim
  | mvar _ => simp [OkS, okE] at hok
  | _ => exact ⟨fun _ _ h => by simp at h, fun _ C us h => by simp [TrS, trE] at h⟩

theorem getLast?_TrSL {s : InLean.CState} (l : List Lean.Expr) :
    (TrSL s l).getLast? = (l.getLast?).map (TrS s) := by
  simp [TrSL, List.getLast?_map]

theorem okS_getLast? {s : InLean.CState} {l : List Lean.Expr} (h : OkSL s l = true) {a : Lean.Expr}
    (ha : l.getLast? = some a) : OkS s a = true := by
  simp only [OkSL, List.all_eq_true] at h
  exact h a (List.mem_of_getLast? ha)

/-! ## Loops -/

/-- **A `for` loop that reads no state and only accumulates**: the answer is
the fold of what each iteration yields. -/
theorem forIn_acc_run {α β : Type} (t₀ : InLean.CState) :
    ∀ (l : List α) (b₀ : β) (f : α → β → InLean.CheckCM (ForInStep β)) (G : α → β → β),
      (∀ a ∈ l, ∀ (b : β) (t' : InLean.CState) (st : ForInStep β),
        f a b t₀ = .ok (st, t') → t' = t₀ ∧ st = .yield (G a b)) →
      ∀ {r : β} {t₁ : InLean.CState}, forIn l b₀ f t₀ = .ok (r, t₁) →
        t₁ = t₀ ∧ r = l.foldl (fun b a => G a b) b₀
  | [], b₀, _, _, _, r, t₁, h => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨rfl, rfl⟩
  | a :: l, b₀, f, G, hf, r, t₁, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, t₂, h1, h⟩ := bind_run h
    obtain ⟨ht, rfl⟩ := hf a List.mem_cons_self b₀ t₂ st h1
    rw [ht] at h
    exact forIn_acc_run t₀ l (G a b₀) f G (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h

theorem foldl_filterMap {α γ : Type} (F : α → Option γ) :
    ∀ (l : List α) (acc : List γ),
      l.foldl (fun b a => b ++ (F a).toList) acc = acc ++ l.filterMap F
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, foldl_filterMap F l, List.filterMap_cons]
    cases F a <;> simp

/-- **A `for` loop with an early `return none`**: from `CSOKI`, the table
grows; a run that went through yields, per element, master's answer `F a`,
appended. -/
theorem forIn_early_run {α β γ : Type} :
    ∀ (l : List α) (acc : List γ) (f : α → Option (Option β) × List γ →
        InLean.CheckCM (ForInStep (Option (Option β) × List γ))) (F : α → Option γ),
      (∀ a ∈ l, ∀ (r : Option (Option β) × List γ) (t t' : InLean.CState) st,
        CSOKI mode eager env t → f a r t = .ok (st, t') →
        CSOKI mode eager env t' ∧ TabLe t t' ∧
          ((∃ c, F a = some c ∧ st = .yield (none, r.2 ++ [c])) ∨ st = .done (some none, r.2))) →
      ∀ {t₀ t₁ : InLean.CState} {r : Option (Option β) × List γ}, CSOKI mode eager env t₀ →
        forIn l (none, acc) f t₀ = .ok (r, t₁) →
        CSOKI mode eager env t₁ ∧ TabLe t₀ t₁ ∧ (∀ x, r.1 ≠ some (some x)) ∧
          (r.1 = none → ∃ rest, l.mapM F = some rest ∧ r.2 = acc ++ rest)
  | [], acc, _, _, _, t₀, t₁, r, ht, h => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨ht, TabLe.refl _, (fun _ h => by simp at h), fun _ => ⟨[], rfl, by simp⟩⟩
  | a :: l, acc, f, F, hf, t₀, t₁, r, ht, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, t₂, h1, h⟩ := bind_run h
    obtain ⟨ht₂, htt, hst⟩ := hf a List.mem_cons_self _ t₀ t₂ st ht h1
    rcases hst with ⟨c, hc, rfl⟩ | rfl
    · obtain ⟨ht', htt', hns, hR⟩ := forIn_early_run l (acc ++ [c]) f F
        (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) ht₂ h
      refine ⟨ht', htt.trans htt', hns, fun hn => ?_⟩
      obtain ⟨rest, hrest, hr⟩ := hR hn
      refine ⟨c :: rest, ?_, by simp [hr]⟩
      rw [List.mapM_cons, hc, hrest]; rfl
    · simp only at h
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨ht₂, htt, (fun _ h => by simp at h), fun h => by simp at h⟩

/-- **A `for` loop that reads no state and appends an option per element**:
the answer is master's `filterMap`. -/
theorem forIn_filterMap_run {α γ : Type} (t₀ : InLean.CState) (l : List α)
    (f : α → List γ → InLean.CheckCM (ForInStep (List γ))) (F : α → Option γ)
    (hf : ∀ a ∈ l, ∀ (b : List γ) (t' : InLean.CState) (st : ForInStep (List γ)),
      f a b t₀ = .ok (st, t') → t' = t₀ ∧ st = .yield (b ++ (F a).toList))
    {r : List γ} {t₁ : InLean.CState} (h : forIn l [] f t₀ = .ok (r, t₁)) :
    t₁ = t₀ ∧ l.filterMap F = r := by
  obtain ⟨h1, h2⟩ := forIn_acc_run t₀ l [] f (fun a b => b ++ (F a).toList) hf h
  refine ⟨h1, ?_⟩
  rw [h2, foldl_filterMap]; rfl

/-- Master's inductive-hypothesis reading of one binder of a minor premise
(`classReadMinor`'s `filterMap` body, named). -/
@[expose] def cIh (nP : Nat) (motPos : List Nat) (d : Nat) (fvs : List ConLeche.Expr) (q : Nat) :
    Option (Nat × Nat) :=
  match (fvs.getD q default).fvarTypeD.piResult.getAppFn with
  | ConLeche.Expr.fvar p' _ =>
    match ConLeche.classOfMotiveVar nP motPos p' with
    | some t =>
      match (fvs.getD q default).fvarTypeD.piResult.getAppArgs.getLast? with
      | some a =>
        match a.getAppFn with
        | ConLeche.Expr.fvar f _ => if d ≤ f then some (f - d, t) else none
        | _ => none
      | none => none
    | none => none
  | _ => none

/-! ## A minor premise -/

/-- **One minor premise, read** (`classReadMinor`): an answer of InLean's is
master's on the reading. -/
theorem classReadMinorI_run (nP : Nat) (motPos : List Nat) (d : Nat) {dom : Lean.Expr}
    {s₀ s' : InLean.CState} {r : Option InLean.ClassSlot} (hs : CSOKI mode eager env s₀)
    (hok : OkS s₀ dom = true) (hcl : (TrS s₀ dom).looseBVarsBounded 0 = true)
    (h : InLean.classReadMinor nP motPos d dom s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ x, r = some x → OkSlot s' x ∧
      ConLeche.classReadMinor nP motPos d (TrS s₀ dom) = some (trSlot s' x) := by
  unfold InLean.classReadMinor at h
  obtain ⟨o, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hR1⟩ := openPisAtFvarsI_run _ d hs hok hcl h1
  have hlen : (ConLeche.Expr.piBinders (TrS s₀ dom)).1.length = (InLean.piBinders dom).1.length := by
    rw [(piBinders_TrS dom hok).1]; simp
  unfold ConLeche.classReadMinor
  simp only [hlen]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, (fun _ h => by simp at h)⟩
  | some q =>
  obtain ⟨fvs, concl⟩ := q
  obtain ⟨hokf, hokc, hop⟩ := hR1 fvs concl rfl
  rw [hop]
  simp only [Option.bind_eq_bind, Option.bind_some]
  obtain ⟨hD1, -⟩ := headDepth_tr hokc
  cases hp : InLean.headDepth? concl with
  | none =>
    simp only [hp] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, (fun _ h => by simp at h)⟩
  | some p =>
  simp only [hp] at h
  obtain ⟨ty0, hty0⟩ := hD1 p hp
  rw [hty0]
  simp only
  rw [classOfMotiveVar_tr]
  cases hc : InLean.classOfMotiveVar nP motPos p with
  | none =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, (fun _ h => by simp at h)⟩
  | some c =>
  simp only [hc] at h
  simp only [Option.bind_some]
  rw [← TrSL_appArgs, getLast?_TrSL]
  cases hl : (InLean.appArgs concl).getLast? with
  | none =>
    simp only [hl] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, (fun _ h => by simp at h)⟩
  | some lastArg =>
  simp only [hl] at h
  simp only [Option.map_some, Option.bind_some]
  have hokl : OkS s₁ lastArg = true := okS_getLast? (OkSL_appArgs s₁ hokc) hl
  obtain ⟨hC1, -⟩ := constHead_tr hokl
  generalize hg : lastArg.getAppFnT = g at h
  cases g with
  | const C us =>
    rw [hC1 C us hg]
    simp only at h ⊢
    obtain ⟨ihs, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    have hlenf : (TrSL s₁ fvs).length = fvs.length := by simp [TrSL]
    refine (fun H => ?_) (forIn_filterMap_run s₁ (List.range fvs.length) _
      (cIh nP motPos d (TrSL s₁ fvs)) ?_ h2)
    · obtain ⟨rfl, hih⟩ := H
      refine ⟨hs₁, ht₁, fun x hx => ?_⟩
      cases hx
      refine ⟨trivial, ?_⟩
      simp only [trSlot]
      rw [hlenf, ← hih]
      rfl
    · intro q hq b t' st hrun
      have hq' : q < fvs.length := List.mem_range.1 hq
      have hx : fvs[q]? = some (fvs.getD q default) := by simp [hq']
      have hokx : OkS s₁ (fvs.getD q default) = true := okS_getElem? hokf hx
      obtain ⟨ty, hfx⟩ := ConLeche.openPisAtFvars_index _ _ _ hop q (TrS s₁ (fvs.getD q default))
        (TrSL_getElem? hx)
      obtain ⟨v, t₂, hv, hrun⟩ := bind_run hrun
      obtain ⟨ht2, hokv, htv, -⟩ := fvarTypeDI_run hs₁ hokx hfx hv
      rw [ht2] at hrun
      have hgd : (TrSL s₁ fvs).getD q default = TrS s₁ (fvs.getD q default) := by
        simp [TrSL, hq']
      have hpr : ((TrSL s₁ fvs).getD q default).fvarTypeD.piResult = TrS s₁ (InLean.piResult v) := by
        rw [hgd, hfx, TrS_piResult, htv]; rfl
      have hokp := OkS_piResult hokv
      unfold cIh
      rw [hpr]
      obtain ⟨hE1, hE2⟩ := headDepth_tr hokp
      cases hp' : InLean.headDepth? (InLean.piResult v) with
      | none =>
        simp only [hp'] at hrun
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        refine ⟨rfl, ?_⟩
        split
        · rename_i p ty heq; exact (hE2 hp' p ty heq).elim
        · simp
      | some p' =>
      simp only [hp'] at hrun
      obtain ⟨ty', hty'⟩ := hE1 p' hp'
      rw [hty']
      simp only
      rw [classOfMotiveVar_tr]
      cases ht : InLean.classOfMotiveVar nP motPos p' with
      | none =>
        simp only [ht] at hrun
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        exact ⟨rfl, by simp⟩
      | some tc =>
      simp only [ht] at hrun
      simp only
      rw [← TrSL_appArgs, getLast?_TrSL]
      cases hl : (InLean.appArgs (InLean.piResult v)).getLast? with
      | none =>
        simp only [hl] at hrun
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        exact ⟨rfl, by simp⟩
      | some a =>
      simp only [hl] at hrun
      simp only [Option.map_some]
      have hoka : OkS s₁ a = true := okS_getLast? (OkSL_appArgs s₁ hokp) hl
      obtain ⟨hA1, hA2⟩ := headDepth_tr hoka
      cases hf : InLean.headDepth? a with
      | none =>
        simp only [hf] at hrun
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        refine ⟨rfl, ?_⟩
        split
        · rename_i p ty heq; exact (hA2 hf p ty heq).elim
        · simp
      | some f =>
      simp only [hf] at hrun
      obtain ⟨tyf, htyf⟩ := hA1 f hf
      rw [htyf]
      simp only
      by_cases hdf : d ≤ f
      · simp only [hdf, ↓reduceIte] at hrun ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        exact ⟨rfl, rfl⟩
      · simp only [hdf, ↓reduceIte] at hrun ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        exact ⟨rfl, by simp⟩
  | _ =>
    simp only at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, (fun _ h => by simp at h)⟩

/-! ## The prefix -/

/-- **The prefix, read** (`classReadSlots`): an answer of InLean's is master's
on the reading, at related parameter counts. -/
theorem classReadSlotsI_run (nPcI : Lean.Name → Nat) (nPcC : ConLeche.Name → Nat)
    (hnPc : ∀ I, nPcC (toName I) = nPcI I) (np : Nat) :
    ∀ (n : Nat) (motPos : List Nat) (d : Nat) (e : Lean.Expr) {s₀ s' : InLean.CState}
      {r : Option (List InLean.ClassSlot)},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.classReadSlots nPcI np n motPos d e s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ xs, r = some xs → (∀ x ∈ xs, OkSlot s' x) ∧
        ConLeche.classReadSlots nPcC np n motPos d (TrS s₀ e) = some (xs.map (trSlot s'))
  | 0, motPos, d, e, s₀, s', r, hs, _, _, h => by
    rw [InLean.classReadSlots] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, fun xs hxs => ?_⟩
    cases hxs
    exact ⟨by simp, by simp [ConLeche.classReadSlots]⟩
  | n + 1, motPos, d, e, s₀, s', r, hs, hok, hcl, h => by
    induction e generalizing s₀ s' r with
    | mdata m e ih =>
      rw [InLean.classReadSlots] at h
      rw [OkS_mdata] at hok
      rw [TrS_mdata] at hcl ⊢
      exact ih s₀ s' r hs hok hcl h
    | forallE nm dom body bi _ _ =>
      rw [InLean.classReadSlots] at h
      simp only [OkS_forallE, Bool.and_eq_true] at hok
      rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hcl
      rw [TrS_forallE]
      simp only [ConLeche.classReadSlots]
      -- the continuation, common to both kinds of slot
      have hcont : ∀ (slot : InLean.ClassSlot) (s₁ : InLean.CState) {cslot : ConLeche.ClassSlot},
          CSOKI mode eager env s₁ → TabLe s₀ s₁ → OkSlot s₁ slot → cslot = trSlot s₁ slot →
          ∀ {r' : Option (List InLean.ClassSlot)},
          (do
            let x ← InLean.mkFVarM d dom
            let o ← InLean.classReadSlots nPcI np n
              (match slot with | .motive _ => motPos ++ [d - np] | _ => motPos) (d + 1) (body.inst1I x)
            match o with
            | some rest => pure (some (slot :: rest))
            | _ => pure none : InLean.CheckCM (Option (List InLean.ClassSlot))) s₁ = .ok (r', s') →
          CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ xs, r' = some xs → (∀ x ∈ xs, OkSlot s' x) ∧
            (do
              let rest ← ConLeche.classReadSlots nPcC np n
                (match cslot with | .motive _ => motPos ++ [d - np] | _ => motPos) (d + 1)
                ((TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)))
              pure (cslot :: rest) : Option (List ConLeche.ClassSlot)) = some (xs.map (trSlot s')) := by
        intro slot s₁ cslot hs₁ ht₁ hoks hcs r' h
        obtain ⟨x, s₂, hx, h⟩ := bind_run h
        have hokd₁ := okS_of_tabLe ht₁ hok.1
        have htd₁ := TrS_of_tabLe ht₁ hok.1
        obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1
          (mkFVarM_specI hs₁ d hokd₁ (by rw [htd₁]; exact hcl.1)) x s₂ hx
        obtain ⟨o, s₃, ho, h⟩ := bind_run h
        have ht02 := ht₁.trans ht₂
        have hb₂ : OkS s₂ body = true := okS_of_tabLe ht02 hok.2
        have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
        have hTI : TrS s₂ (body.inst1I x) = (TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0 := by
          rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht02 hok.2, htd₁]
        obtain ⟨hs₃, ht₃, hR⟩ := classReadSlotsI_run nPcI nPcC hnPc np n _ (d + 1) _ hs₂
          (OkS_inst1 hb₂ hokx hcx) (by rw [← inst1I_eq, hTI]; exact lbb_instantiate1 rfl hcl.2) ho
        cases o with
        | none =>
          obtain ⟨rfl, rfl⟩ := pure_run h
          exact ⟨hs₃, ht02.trans ht₃, fun _ h => by simp at h⟩
        | some rest =>
          obtain ⟨rfl, rfl⟩ := pure_run h
          obtain ⟨hokr, hm⟩ := hR rest rfl
          have ht13 := ht₂.trans ht₃
          refine ⟨hs₃, ht02.trans ht₃, fun xs hxs => ?_⟩
          cases hxs
          refine ⟨?_, ?_⟩
          · intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact OkSlot.mono ht13 hoks
            · exact hokr y hy
          · subst hcs
            rw [← hTI]
            have hsl := trSlot_mono ht13 hoks
            cases slot <;> simp only [inst1I_eq, trSlot] at hm hsl ⊢ <;> rw [hm] <;>
              simp only [Option.bind_eq_bind, Option.bind_some, List.map_cons] <;> (try rw [← hsl]) <;> rfl
      have hpr : (TrS s₀ dom).piResult = TrS s₀ (EO.stripTop (InLean.piResult dom)) := by
        rw [TrS_stripTop, TrS_piResult]
      have hokp : OkS s₀ (EO.stripTop (InLean.piResult dom)) = true := by
        rw [OkS_stripTop]; exact OkS_piResult hok.1
      have hnm : ∀ m b, EO.stripTop (InLean.piResult dom) ≠ .mdata m b := stripTop_ne_mdata' _
      rw [hpr]
      generalize EO.stripTop (InLean.piResult dom) = x at h hokp hnm
      have hminor :
          (do
            let slot? ← InLean.classReadMinor np motPos d dom
            match slot? with
            | some slot =>
              (do
                let x ← InLean.mkFVarM d dom
                let o ← InLean.classReadSlots nPcI np n
                  (match slot with | .motive _ => motPos ++ [d - np] | _ => motPos) (d + 1)
                  (body.inst1I x)
                match o with
                | some rest => pure (some (slot :: rest))
                | _ => pure none : InLean.CheckCM (Option (List InLean.ClassSlot)))
            | _ => pure none : InLean.CheckCM (Option (List InLean.ClassSlot))) s₀ = .ok (r, s') →
          CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ xs, r = some xs → (∀ x ∈ xs, OkSlot s' x) ∧
            (do
                let slot ← ConLeche.classReadMinor np motPos d (TrS s₀ dom)
                let rest ← ConLeche.classReadSlots nPcC np n
                  (match slot with | .motive _ => motPos ++ [d - np] | _ => motPos) (d + 1)
                  ((TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)))
                pure (slot :: rest) : Option (List ConLeche.ClassSlot)) = some (xs.map (trSlot s')) := by
        intro h
        obtain ⟨o, s₁, h1, h⟩ := bind_run h
        obtain ⟨hs₁, ht₁, hR1⟩ := classReadMinorI_run np motPos d hs hok.1 hcl.1 h1
        cases o with
        | none =>
          obtain ⟨rfl, rfl⟩ := pure_run h
          exact ⟨hs₁, ht₁, fun _ h => by simp at h⟩
        | some slot =>
          obtain ⟨hoks, hm⟩ := hR1 slot rfl
          obtain ⟨hs', ht', hR⟩ := hcont slot s₁ hs₁ ht₁ hoks rfl h
          refine ⟨hs', ht', fun xs hxs => ⟨(hR xs hxs).1, ?_⟩⟩
          rw [hm]
          exact (hR xs hxs).2
      cases x with
      | sort u =>
        simp only at h
        rw [TrS_sort]
        simp only
        obtain ⟨o, s₁, h1, h⟩ := bind_run h
        obtain ⟨ho, rfl⟩ := pure_run h1
        cases o with
        | none =>
          obtain ⟨rfl, rfl⟩ := pure_run h
          exact ⟨hs, TabLe.refl _, fun _ h => by simp at h⟩
        | some slot =>
        obtain ⟨hpb, hokbs, -, -⟩ := piBinders_TrS dom hok.1
        rw [hpb]
        simp only
        cases hb : InLean.piBinders dom with
        | mk bs b =>
        simp only [hb] at ho hokbs
        rw [List.getLast?_map]
        cases hl : bs.getLast? with
        | none => simp [hl] at ho
        | some mdom =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some] at ho
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        have hokm : OkS s₀ mdom = true := okS_getLast? hokbs hl
        obtain ⟨hC1, -⟩ := constHead_tr hokm
        cases hg : mdom.getAppFnT with
        | const I us =>
          simp only [hg] at ho
          cases ho
          rw [hC1 I us hg]
          simp only [Option.pure_def, Option.bind_some]
          have hokg := OkS_getAppFnT s₀ hokm
          rw [hg, OkS_const] at hokg
          have hoks : OkSlot s₀ (.motive ⟨I, us, (InLean.appArgs mdom).take (nPcI I)⟩) :=
            ⟨hokg, OkSL_take s₀ (OkSL_appArgs s₀ hokm) _⟩
          refine hcont _ s₀ (cslot := .motive ⟨toName I, us.map trL,
            (TrS s₀ mdom).getAppArgs.take (nPcC (toName I))⟩) hs (TabLe.refl _) hoks ?_ h
          simp only [trSlot, trCK, hnPc, TrSL_take, TrSL_appArgs]
        | _ => simp [hg] at ho
      | mdata m b => exact (hnm m b rfl).elim
      | mvar _ => simp [OkS, okE] at hokp
      | _ =>
        simp only at h
        obtain ⟨hs', ht', hR⟩ := hminor h
        refine ⟨hs', ht', fun xs hxs => ⟨(hR xs hxs).1, ?_⟩⟩
        split
        · rename_i v heq
          obtain ⟨u, hu⟩ := stripTop_of_TrS_sort s₀ heq
          simp [EO.stripTop] at hu
        · exact (hR xs hxs).2
    | _ =>
      rw [InLean.classReadSlots] at h
      · obtain ⟨rfl, rfl⟩ := pure_run h
        exact ⟨hs, TabLe.refl _, fun _ h => by simp at h⟩
      all_goals (intros; contradiction)

/-! ## The pre-pass -/

/-- InLean's motive positions (`classRead`'s `motPos`, named). -/
@[expose] def iMotPos (slots : List InLean.ClassSlot) : List Nat :=
  (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false

/-- Master's motive positions (`classRead`'s `motPos`, named). -/
@[expose] def cMotPos (slots : List ConLeche.ClassSlot) : List Nat :=
  (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false

theorem cMotPos_tr (s : InLean.CState) (slots : List InLean.ClassSlot) :
    cMotPos (slots.map (trSlot s)) = iMotPos slots := by
  unfold cMotPos iMotPos
  rw [List.length_map]
  congr 1
  funext i
  rw [List.getElem?_map]
  cases slots[i]? with
  | none => rfl
  | some x => cases x <;> rfl

/-- Master's class of one recursor (`classRead`'s `mapM` body, named). -/
@[expose] def cRecCl (nP : Nat) (motPos : List Nat) (rc : ConLeche.RecShape) : Option Nat := do
  let (_, concl) ← ConLeche.openPisAtFvars (rc.mI + 1) rc.cvR.type 0
  match concl.getAppFn with
  | .fvar p _ => ConLeche.classOfMotiveVar nP motPos p
  | _ => none

theorem mapM_map_option {α β γ : Type} (g : α → β) (f : β → Option γ) :
    ∀ l : List α, (l.map g).mapM f = l.mapM (f ∘ g)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, mapM_map_option g f l]; rfl

/-- **The pre-pass, read** (`classRead`): an answer of InLean's is master's on
the translated recursors, read at the final state. -/
theorem classReadI_run (nP : Nat) (nPcI : Lean.Name → Nat) (nPcC : ConLeche.Name → Nat)
    (hnPc : ∀ I, nPcC (toName I) = nPcI I) {recs : List InLean.RecShape}
    (hok : ∀ rc ∈ recs, okC rc.cvR.type = true ∧ (trC rc.cvR.type).looseBVarsBounded 0 = true)
    {s₀ s' : InLean.CState} {r : Option InLean.ClassRead} (hs : CSOKI mode eager env s₀)
    (h : InLean.classRead nP nPcI recs s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ rd, r = some rd → (∀ x ∈ rd.slots, OkSlot s' x) ∧
      ConLeche.classRead nP nPcC (recs.map trRec) = some (trCR s' rd) := by
  unfold InLean.classRead at h
  unfold ConLeche.classRead
  cases hh : recs.head? with
  | none =>
    simp only [hh] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, fun _ h => by simp at h⟩
  | some rc0 =>
  simp only [hh] at h
  have hrc0 : rc0 ∈ recs := List.mem_of_mem_head? hh
  obtain ⟨hok0, hcl0⟩ := hok rc0 hrc0
  rw [List.head?_map, hh]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨o, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hR1⟩ := openPisAtFvarsI_run nP 0 hs (OkS_of_okC _ hok0)
    (by rw [TrS_of_okC _ hok0]; exact hcl0) h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₁, ht₁, fun _ h => by simp at h⟩
  | some q =>
  obtain ⟨fvs0, body⟩ := q
  obtain ⟨-, hokb, hop⟩ := hR1 fvs0 body rfl
  rw [TrS_of_okC _ hok0] at hop
  simp only [trRec, trCV_type]
  rw [hop]
  simp only [Option.bind_some]
  have hclb : (TrS s₁ body).looseBVarsBounded 0 = true :=
    (ConLeche.Verify.openPisAtFvars_bounded nP hop hcl0).1
  obtain ⟨o2, s₂, h2, h⟩ := bind_run h
  obtain ⟨hs₂, ht₂, hR2⟩ := classReadSlotsI_run nPcI nPcC hnPc nP _ [] nP body hs₁ hokb hclb h2
  cases o2 with
  | none =>
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₂, ht₁.trans ht₂, fun _ h => by simp at h⟩
  | some slots =>
  obtain ⟨hoks, hsl⟩ := hR2 slots rfl
  rw [hsl]
  simp only [Option.bind_some]
  conv in List.filter _ _ => change cMotPos (slots.map (trSlot s₂))
  rw [cMotPos_tr]
  obtain ⟨st, s₃, h3, h⟩ := bind_run h
  refine (fun H => ?_) (forIn_early_run (mode := mode) (eager := eager) (env := env) recs []
    _ (fun rc => cRecCl nP (iMotPos slots) (trRec rc)) ?_ hs₂ h3)
  · obtain ⟨hs₃, ht₃, hns, hR3⟩ := H
    obtain ⟨r1, r2⟩ := st
    cases r1 with
    | some x =>
      cases x with
      | some y => exact (hns y rfl).elim
      | none =>
        obtain ⟨rfl, rfl⟩ := pure_run h
        exact ⟨hs₃, ht₁.trans (ht₂.trans ht₃), fun _ h => by simp at h⟩
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      obtain ⟨rest, hrest, hr2⟩ := hR3 rfl
      refine ⟨hs₃, ht₁.trans (ht₂.trans ht₃), fun rd hrd => ?_⟩
      cases hrd
      refine ⟨fun x hx => OkSlot.mono ht₃ (hoks x hx), ?_⟩
      have hm : (recs.map trRec).mapM (cRecCl nP (iMotPos slots)) = some rest := by
        rw [mapM_map_option]; exact hrest
      conv in List.mapM _ _ => change (recs.map trRec).mapM (cRecCl nP (iMotPos slots))
      rw [hm]
      simp only [List.nil_append] at hr2
      subst hr2
      simp only [Option.bind_some, trCR]
      congr 2
      exact (List.map_congr_left fun x hx => trSlot_mono ht₃ (hoks x hx)).symm
  · intro rc hrc rr t t' st ht hrun
    obtain ⟨hokr, hclr⟩ := hok rc hrc
    obtain ⟨o, t₁, h1, hrun⟩ := bind_run hrun
    obtain ⟨ht₁', htt₁, hR⟩ := openPisAtFvarsI_run (rc.mI + 1) 0 ht (OkS_of_okC _ hokr)
      (by rw [TrS_of_okC _ hokr]; exact hclr) h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run hrun
      exact ⟨ht₁', htt₁, .inr rfl⟩
    | some q =>
    obtain ⟨fvs, concl⟩ := q
    obtain ⟨-, hokc, hopr⟩ := hR fvs concl rfl
    rw [TrS_of_okC _ hokr] at hopr
    simp only at hrun
    obtain ⟨hD1, -⟩ := headDepth_tr hokc
    cases hp : InLean.headDepth? concl with
    | none =>
      simp only [hp] at hrun
      obtain ⟨rfl, rfl⟩ := pure_run hrun
      exact ⟨ht₁', htt₁, .inr rfl⟩
    | some p =>
    simp only [hp] at hrun
    conv at hrun in List.filter _ _ => change iMotPos slots
    cases hc : InLean.classOfMotiveVar nP (iMotPos slots) p with
    | none =>
      simp only [hc] at hrun
      obtain ⟨rfl, rfl⟩ := pure_run hrun
      exact ⟨ht₁', htt₁, .inr rfl⟩
    | some c =>
      simp only [hc] at hrun
      obtain ⟨rfl, rfl⟩ := pure_run hrun
      refine ⟨ht₁', htt₁, .inl ⟨c, ?_, rfl⟩⟩
      obtain ⟨ty, hty⟩ := hD1 p hp
      unfold cRecCl
      simp only [trRec, trCV_type, hopr, Option.bind_eq_bind, Option.bind_some, hty]
      rw [classOfMotiveVar_tr]
      exact hc

/-! ## Variable replacement and the range guards, read -/

theorem cReplaceFVars_noFvar (f : Nat → Option ConLeche.Expr) :
    ∀ {e : ConLeche.Expr}, e.hasFvar = false → ConLeche.Expr.replaceFVars f e = e := by
  intro e
  induction e <;> simp_all [ConLeche.Expr.hasFvar, ConLeche.Expr.replaceFVars]

/-- The callback of InLean's `replaceFVars`. -/
@[expose] def rfF (fI : Nat → Option Lean.Expr) (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .fvar id => match EO.fvDepth? id with
    | some i => fI i
    | none => none
  | x => if x.hasFVar then none else some x

theorem replaceFVars_eq (fI : Nat → Option Lean.Expr) (e : Lean.Expr) :
    InLean.replaceFVars fI e = if !e.hasFVar then e else mapSpec (fun x _ => rfF fI x) e 0 := by
  unfold InLean.replaceFVars EO.replace
  rw [mapOff_fresh]; rfl

/-- A substitution of variables, related: InLean's images have readings,
master's are their readings. -/
@[expose] def FvSubRel (s : InLean.CState) (fI : Nat → Option Lean.Expr)
    (fC : Nat → Option ConLeche.Expr) : Prop :=
  ∀ i, (fI i).map (TrS s) = fC i ∧ ∀ y, fI i = some y → OkS s y = true

theorem rfF_tr {s : InLean.CState} {fI fC} (hR : FvSubRel s fI fC) {x : Lean.Expr}
    (h : OkS s x = true) (y : Lean.Expr) (hy : rfF fI x = some y) :
    OkS s y = true ∧ TrS s y = ConLeche.Expr.replaceFVars fC (TrS s x) := by
  cases x with
  | fvar id =>
    obtain ⟨d, ty, ht, hd⟩ := TrS_stripTop_fvar h rfl
    simp only [rfF, hd] at hy
    obtain ⟨h1, h2⟩ := hR d
    rw [hy, Option.map_some] at h1
    refine ⟨h2 y hy, ?_⟩
    rw [ht]
    simp only [ConLeche.Expr.replaceFVars, ← h1, Option.getD_some]
  | _ =>
    simp only [rfF] at hy
    split at hy
    · cases hy
    · rename_i hf
      cases hy
      refine ⟨h, (cReplaceFVars_noFvar fC ?_).symm⟩
      rw [← hasFVar_TrS (s := s) h]
      simpa using hf

theorem rfF_none_tr {s : InLean.CState} {fI fC} (hR : FvSubRel s fI fC) {id : FVarId}
    (h : OkS s (.fvar id) = true) (hy : rfF fI (.fvar id) = none) :
    TrS s (.fvar id) = ConLeche.Expr.replaceFVars fC (TrS s (.fvar id)) := by
  obtain ⟨d, ty, ht, hd⟩ := TrS_stripTop_fvar h rfl
  simp only [rfF, hd] at hy
  obtain ⟨h1, -⟩ := hR d
  rw [hy, Option.map_none] at h1
  rw [ht]
  simp only [ConLeche.Expr.replaceFVars, ← h1, Option.getD_none]

theorem mapSpec_rfF_tr {s : InLean.CState} {fI fC} (hR : FvSubRel s fI fC) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      OkS s (mapSpec (fun x _ => rfF fI x) e k) = true ∧
        TrS s (mapSpec (fun x _ => rfF fI x) e k) = ConLeche.Expr.replaceFVars fC (TrS s e) := by
  intro e
  induction e with
  | fvar id =>
    intro k h
    cases hy : rfF fI (.fvar id) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [mapSpec, hy, Option.getD_none]
      exact ⟨h, rfF_none_tr hR h hy⟩
  | app f a ihf iha =>
    intro k h
    cases hy : rfF fI (.app f a) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [OkS_app, Bool.and_eq_true] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_app, TrS_app, ConLeche.Expr.replaceFVars,
        (ihf k h.1).1, (iha k h.2).1, (ihf k h.1).2, (iha k h.2).2, Bool.and_self, true_and]
  | lam nm t b bi iht ihb =>
    intro k h
    cases hy : rfF fI (.lam nm t b bi) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [OkS_lam, Bool.and_eq_true] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_lam, TrS_lam, ConLeche.Expr.replaceFVars,
        (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2, (ihb (k + 1) h.2).2, Bool.and_self,
        true_and]
  | forallE nm t b bi iht ihb =>
    intro k h
    cases hy : rfF fI (.forallE nm t b bi) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [OkS_forallE, Bool.and_eq_true] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_forallE, TrS_forallE,
        ConLeche.Expr.replaceFVars, (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2,
        (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | letE nm t v b nd iht ihv ihb =>
    intro k h
    cases hy : rfF fI (.letE nm t v b nd) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [OkS_letE, Bool.and_eq_true] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_letE, TrS_letE, ConLeche.Expr.replaceFVars,
        (iht k h.1.1).1, (ihv k h.1.2).1, (ihb (k + 1) h.2).1, (iht k h.1.1).2, (ihv k h.1.2).2,
        (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | proj sn i x ih =>
    intro k h
    cases hy : rfF fI (.proj sn i x) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      rw [OkS_proj] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_proj, TrS_proj, ConLeche.Expr.replaceFVars,
        (ih k h).1, (ih k h).2, true_and]
  | mdata m x ih =>
    intro k h
    cases hy : rfF fI (.mdata m x) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      rw [OkS_mdata] at h
      simp only [mapSpec, hy, Option.getD_none, OkS_mdata, TrS_mdata]
      exact ih k h
  | bvar i =>
    intro k h
    cases hy : rfF fI (.bvar i) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [mapSpec, hy, Option.getD_none]
      exact ⟨h, by simp [TrS, trE, ConLeche.Expr.replaceFVars]⟩
  | sort u =>
    intro k h
    cases hy : rfF fI (.sort u) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [mapSpec, hy, Option.getD_none]
      exact ⟨h, by simp [TrS, trE, ConLeche.Expr.replaceFVars]⟩
  | const c us =>
    intro k h
    cases hy : rfF fI (.const c us) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [mapSpec, hy, Option.getD_none]
      exact ⟨h, by simp [TrS, trE, ConLeche.Expr.replaceFVars]⟩
  | lit l =>
    intro k h
    cases hy : rfF fI (.lit l) with
    | some y => rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hy]; exact rfF_tr hR h y hy
    | none =>
      simp only [mapSpec, hy, Option.getD_none]
      exact ⟨h, by simp [TrS, trE, ConLeche.Expr.replaceFVars]⟩
  | mvar i => intro k h; simp [OkS, okE] at h

/-- **InLean's `replaceFVars`, read**: master's on the reading, at related
substitutions. -/
theorem replaceFVarsI_tr {s : InLean.CState} {fI fC} (hR : FvSubRel s fI fC) {e : Lean.Expr}
    (h : OkS s e = true) :
    OkS s (InLean.replaceFVars fI e) = true ∧
      TrS s (InLean.replaceFVars fI e) = ConLeche.Expr.replaceFVars fC (TrS s e) := by
  rw [replaceFVars_eq]
  cases hf : e.hasFVar with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    refine ⟨h, (cReplaceFVars_noFvar fC ?_).symm⟩
    rw [← hasFVar_TrS (s := s) h, hf]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact mapSpec_rfF_tr hR e 0 h

theorem fvSubRel_getElem? {s : InLean.CState} {pfvs : List Lean.Expr} (h : OkSL s pfvs = true) :
    FvSubRel s (fun i => pfvs[i]?) (fun i => (TrSL s pfvs)[i]?) := by
  intro i
  refine ⟨?_, fun y hy => okS_getElem? h hy⟩
  simp [TrSL]

/-- **A term moved to the openers, read** (`targetCanonParams`). -/
theorem targetCanonParamsI_tr {s : InLean.CState} {pfvs : List Lean.Expr} (hp : OkSL s pfvs = true)
    {e : Lean.Expr} (h : OkS s e = true) :
    OkS s (InLean.targetCanonParams pfvs e) = true ∧
      TrS s (InLean.targetCanonParams pfvs e) = ConLeche.targetCanonParams (TrSL s pfvs) (TrS s e) :=
  replaceFVarsI_tr (fvSubRel_getElem? hp) h

/-- The loose-bvar bound of a reading is the cached range's spec. -/
theorem bvarBound_TrS {s : InLean.CState} : ∀ {e : Lean.Expr}, OkS s e = true →
    (TrS s e).bvarBound = rangeS e := by
  intro e
  induction e with
  | fvar id => intro h; rw [TrS_fvar h]; rfl
  | mvar _ => intro h; simp [OkS, okE] at h
  | app f a ihf iha =>
    intro h; simp only [OkS_app, Bool.and_eq_true] at h
    simp only [TrS_app, ConLeche.Expr.bvarBound, rangeS, ihf h.1, iha h.2]
  | lam _ t b _ iht ihb =>
    intro h; simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [TrS_lam, ConLeche.Expr.bvarBound, rangeS, iht h.1, ihb h.2]
  | forallE _ t b _ iht ihb =>
    intro h; simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [TrS_forallE, ConLeche.Expr.bvarBound, rangeS, iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [TrS_letE, ConLeche.Expr.bvarBound, rangeS, iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ x ih => intro h; rw [OkS_mdata] at h; rw [TrS_mdata]; exact ih h
  | proj _ _ x ih => intro h; rw [OkS_proj] at h; simp only [TrS_proj, ConLeche.Expr.bvarBound, rangeS, ih h]
  | bvar i => intro _; rfl
  | sort _ => intro _; rfl
  | const _ _ => intro _; rfl
  | lit _ => intro _; rfl

/-- InLean's loose-bvar test is master's bound test on the reading. -/
theorem hasLooseBVars_TrS {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    (!e.hasLooseBVars) = ((TrS s e).bvarB == 0) := by
  rw [hasLooseBVars_eq (RangeOk_of_OkS h), ConLeche.Expr.bvarB_eq, bvarBound_TrS h]
  cases rangeS e <;> simp

/-- The fold of `fvarB`. -/
@[expose] def fvbStep (acc : Nat) (id : FVarId) : Nat :=
  match EO.fvDepth? id with
  | some d => max acc (d + 1)
  | none => acc

theorem fvbFold_le {M : Nat} : ∀ (l : List FVarId) (acc : Nat), acc ≤ M →
    (∀ id ∈ l, ∀ d, EO.fvDepth? id = some d → d + 1 ≤ M) → l.foldl fvbStep acc ≤ M
  | [], _, h, _ => h
  | id :: l, acc, h, hl => by
    rw [List.foldl_cons]
    refine fvbFold_le l _ ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    unfold fvbStep
    cases hd : EO.fvDepth? id with
    | none => exact h
    | some d => exact Nat.max_le.2 ⟨h, hl id List.mem_cons_self d hd⟩

theorem fvbFold_ge : ∀ (l : List FVarId) (acc : Nat), acc ≤ l.foldl fvbStep acc ∧
    ∀ id ∈ l, ∀ d, EO.fvDepth? id = some d → d + 1 ≤ l.foldl fvbStep acc
  | [], acc => ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | id :: l, acc => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := fvbFold_ge l (fvbStep acc id)
    have hst : acc ≤ fvbStep acc id ∧ ∀ d, EO.fvDepth? id = some d → d + 1 ≤ fvbStep acc id := by
      unfold fvbStep
      cases EO.fvDepth? id with
      | none => exact ⟨Nat.le_refl _, fun _ h => by simp at h⟩
      | some d' => exact ⟨Nat.le_max_left _ _, fun d h => by cases h; exact Nat.le_max_right _ _⟩
    refine ⟨Nat.le_trans hst.1 h1, fun x hx d hd => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_trans (hst.2 d hd) h1
    · exact h2 x hx d hd

/-- A reading's variable range is at most `M` when every variable's depth is below. -/
theorem fvarRange_TrS_le {s : InLean.CState} {M : Nat} : ∀ {e : Lean.Expr}, OkS s e = true →
    (∀ id, OccF id e → ∀ d, EO.fvDepth? id = some d → d + 1 ≤ M) → (TrS s e).fvarRange ≤ M := by
  intro e
  induction e with
  | fvar id =>
    intro h hM
    obtain ⟨d, ty, ht, hd⟩ := TrS_stripTop_fvar h rfl
    rw [ht]
    exact hM id rfl d hd
  | mvar _ => intro h; simp [OkS, okE] at h
  | app f a ihf iha =>
    intro h hM; simp only [OkS_app, Bool.and_eq_true] at h
    simp only [TrS_app, ConLeche.Expr.fvarRange, Nat.max_le]
    exact ⟨ihf h.1 fun id ho => hM id (.inl ho), iha h.2 fun id ho => hM id (.inr ho)⟩
  | lam _ t b _ iht ihb =>
    intro h hM; simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [TrS_lam, ConLeche.Expr.fvarRange, Nat.max_le]
    exact ⟨iht h.1 fun id ho => hM id (.inl ho), ihb h.2 fun id ho => hM id (.inr ho)⟩
  | forallE _ t b _ iht ihb =>
    intro h hM; simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [TrS_forallE, ConLeche.Expr.fvarRange, Nat.max_le]
    exact ⟨iht h.1 fun id ho => hM id (.inl ho), ihb h.2 fun id ho => hM id (.inr ho)⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h hM; simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [TrS_letE, ConLeche.Expr.fvarRange, Nat.max_le]
    exact ⟨⟨iht h.1.1 fun id ho => hM id (.inl ho), ihv h.1.2 fun id ho => hM id (.inr (.inl ho))⟩,
      ihb h.2 fun id ho => hM id (.inr (.inr ho))⟩
  | mdata _ x ih => intro h hM; rw [OkS_mdata] at h; rw [TrS_mdata]; exact ih h hM
  | proj _ _ x ih =>
    intro h hM; rw [OkS_proj] at h
    simp only [TrS_proj, ConLeche.Expr.fvarRange]; exact ih h hM
  | bvar _ | sort _ | const _ _ | lit _ => intro _ _; exact Nat.zero_le _

/-- InLean's variable bound at most `M` means the reading's range is. -/
theorem fvarB_le_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) {M : Nat}
    (hb : InLean.fvarB e ≤ M) : (TrS s e).fvarRange ≤ M := by
  unfold InLean.fvarB at hb
  cases hf : e.hasFVar with
  | false =>
    have : (TrS s e).hasFvar = false := by rw [← hasFVar_TrS (s := s) h, hf]
    rw [ConLeche.Expr.hasFvar_eq_false_iff.1 this]
    exact Nat.zero_le _
  | true =>
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb
    refine fvarRange_TrS_le h fun id ho d hd => ?_
    have hmem : id ∈ (EO.fvarIds e).toList :=
      Array.mem_toList_iff.2 ((mem_fvarIds (RangeOk_of_OkS h) id).2 ho)
    rw [← Array.foldl_toList] at hb
    exact Nat.le_trans ((fvbFold_ge _ 0).2 id hmem d hd) hb

/-- InLean's range guard on a term passing means master's passes on the reading. -/
theorem rangeGuard_tr {s : InLean.CState} {x : Lean.Expr} (h : OkS s x = true) {n : Nat}
    (hg : (!x.hasLooseBVars && decide (InLean.fvarB x ≤ n)) = true) :
    ((TrS s x).bvarB == 0 && decide ((TrS s x).fvarB ≤ n)) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
  refine ⟨by rw [← hasLooseBVars_TrS h]; exact hg.1, ?_⟩
  rw [ConLeche.Expr.fvarB_eq]
  exact fvarB_le_tr h hg.2

/-- Every element of a list runs to its answer under `f`. -/
@[expose] def RunsAll {α β : Type} (f : α → ConLeche.FueledM β) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: bs => Runs (f a) b ∧ RunsAll f l bs
  | _, _ => False

/-- Master's `mapM` runs where every element does (`FueledM` has no lawful-monad
instance, so through `mapM.loop`). -/
theorem runs_mapM_loop {α β : Type} {f : α → ConLeche.FueledM β} :
    ∀ {l : List α} {bs : List β}, RunsAll f l bs →
      ∀ acc : List β, Runs (List.mapM.loop f l acc) (acc.reverse ++ bs)
  | [], [], _, acc => by simp only [List.append_nil]; exact Runs.pure _
  | a :: l, b :: bs, h, acc => by
    have := runs_mapM_loop h.2 (b :: acc)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
    exact Runs.bind h.1 this
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

theorem runs_mapM {α β : Type} {f : α → ConLeche.FueledM β} {l : List α} {bs : List β}
    (h : RunsAll f l bs) : Runs (l.mapM f) bs := by
  have := runs_mapM_loop h []
  simp only [List.reverse_nil, List.nil_append] at this
  exact this

/-! ## The class keys -/

/-- A recorded constructor normal form, read at a state. -/
@[expose] def trNf (s : InLean.CState) (e : InLean.NestCtorNf) : ConLeche.NestCtorNf :=
  ⟨toName e.ctor, e.lvls.map trL, TrSL s e.ds, TrS s e.ty⟩

/-- A resolved major, read at a state. -/
@[expose] def trTM (s : InLean.CState) (M : InLean.TargetMajor) : ConLeche.TargetMajor :=
  ⟨toName M.ind, M.lvls.map trL, TrSL s M.ds, M.nPc, M.nIdx, M.ctors.map trCtor, M.member,
    M.nfs.map (trNf s), TrSL s M.pfvs⟩

theorem classes_trCR (s : InLean.CState) (r : InLean.ClassRead) :
    (trCR s r).classes = r.classes.map (trCK s) := by
  unfold ConLeche.ClassRead.classes InLean.ClassRead.classes trCR
  simp only
  induction r.slots with
  | nil => rfl
  | cons x l ih =>
    cases x <;> simp [trSlot, ih]

theorem okSlot_classes {s : InLean.CState} {r : InLean.ClassRead} (h : ∀ x ∈ r.slots, OkSlot s x) :
    ∀ k ∈ r.classes, k.lvls.all okLv = true ∧ OkSL s k.ds = true := by
  intro k hk
  unfold InLean.ClassRead.classes at hk
  obtain ⟨x, hx, hxk⟩ := List.mem_filterMap.1 hk
  cases x with
  | motive k' => cases hxk; exact h _ hx
  | minor => cases hxk

/-- The pre-pass's parameter counts, related (`classNPcOf`). -/
theorem classNPcOf_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (p : InLean.BlockShape) (I : Lean.Name) :
    ConLeche.classNPcOf (trShape p) (ConLeche.mkFEnv L) (toName I) = InLean.classNPcOf p fe I := by
  unfold ConLeche.classNPcOf InLean.classNPcOf
  rw [trShape_memberNames, contains_map_toName, ConLeche.mkFEnv_find?, trShape_nP]
  by_cases hm : p.memberNames.contains I = true
  · simp only [hm, ↓reduceIte]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    cases hv : fe.indView? I with
    | some q =>
      obtain ⟨cv, caps⟩ := q
      obtain ⟨hL, -, -⟩ := indView_trCV hJ hv
      rw [hL]; rfl
    | none =>
      have hn := indView_none_tr hJ hv
      split
      · rename_i ccv caps heq; exact (hn ccv caps heq).elim
      · rfl

/-- **A class key made checkable** (`classKeyOf`): InLean's key is master's on
the reading; its parameters pass master's range guard. -/
theorem classKeyOfI_run {nP : Nat} {params : List Lean.Expr} {k k' : InLean.ClassKey}
    {s₀ s' : InLean.CState} (hp : OkSL s₀ params = true) (hlv : k.lvls.all okLv = true)
    (hds : OkSL s₀ k.ds = true) (h : InLean.classKeyOf nP params k s₀ = .ok (k', s')) :
    s' = s₀ ∧ k'.lvls.all okLv = true ∧ OkSL s₀ k'.ds = true ∧
      (∀ x ∈ TrSL s₀ k'.ds, (x.bvarB = 0 ∧ x.fvarB ≤ nP) ∧
        ∃ y, x = ConLeche.targetCanonParams (TrSL s₀ params) y) ∧
      Runs (ConLeche.classKeyOf (m := ConLeche.FueledM) nP (TrSL s₀ params) (trCK s₀ k))
        (trCK s₀ k') := by
  unfold InLean.classKeyOf at h
  unfold ConLeche.classKeyOf
  have hc : ∀ x ∈ k.ds, OkS s₀ (InLean.targetCanonParams params x) = true ∧
      TrS s₀ (InLean.targetCanonParams params x) =
        ConLeche.targetCanonParams (TrSL s₀ params) (TrS s₀ x) := by
    intro x hx
    simp only [OkSL, List.all_eq_true] at hds
    exact targetCanonParamsI_tr hp (hds x hx)
  have hkc : ConLeche.classKeyCanon (TrSL s₀ params) (trCK s₀ k) =
      trCK s₀ (InLean.classKeyCanon params k) := by
    simp only [ConLeche.classKeyCanon, InLean.classKeyCanon, trCK, TrSL, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => (hc x hx).2.symm
  have hokc : OkSL s₀ (InLean.classKeyCanon params k).ds = true := by
    simp only [InLean.classKeyCanon, OkSL, List.all_map, List.all_eq_true, Function.comp_apply]
    exact fun x hx => (hc x hx).1
  rw [hkc]
  by_cases hg : ((InLean.classKeyCanon params k).ds.all
      fun x => !x.hasLooseBVars && decide (InLean.fvarB x ≤ nP)) = true
  · simp only [hg, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    have hgC : ((trCK s₀ (InLean.classKeyCanon params k)).ds.all
        fun x => x.bvarB == 0 && decide (x.fvarB ≤ nP)) = true := by
      simp only [trCK, TrSL, List.all_map, List.all_eq_true, Function.comp_apply] at hg ⊢
      intro x hx
      simp only [OkSL, List.all_eq_true] at hokc
      exact rangeGuard_tr (hokc x hx) (hg x hx)
    refine ⟨rfl, hlv, hokc, fun x hx => ?_, ?_⟩
    · simp only [trCK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgC
      refine ⟨hgC x hx, ?_⟩
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      simp only [InLean.classKeyCanon, List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨TrS s₀ y, (hc y hy).2⟩
    · simp only [hgC, ↓reduceIte]
      first | exact Runs.pure _ | exact Runs.bind (Runs.pure _) (Runs.pure _)
  · simp only [hg] at h
    obtain ⟨_, _, h1, -⟩ := bind_run h
    exact (throw_run h1).elim

/-- Every class key made checkable. -/
theorem mapM_classKeyOfI_run {nP : Nat} {params : List Lean.Expr} {s₀ : InLean.CState}
    (hp : OkSL s₀ params = true) :
    ∀ {ks ks' : List InLean.ClassKey} {s' : InLean.CState},
      (∀ k ∈ ks, k.lvls.all okLv = true ∧ OkSL s₀ k.ds = true) →
      ks.mapM (InLean.classKeyOf nP params) s₀ = .ok (ks', s') →
      s' = s₀ ∧ (∀ k ∈ ks', k.lvls.all okLv = true ∧ OkSL s₀ k.ds = true ∧
        ∀ x ∈ TrSL s₀ k.ds, (x.bvarB = 0 ∧ x.fvarB ≤ nP) ∧
          ∃ y, x = ConLeche.targetCanonParams (TrSL s₀ params) y) ∧
        RunsAll (ConLeche.classKeyOf (m := ConLeche.FueledM) nP (TrSL s₀ params))
          (ks.map (trCK s₀)) (ks'.map (trCK s₀))
  | [], ks', s', _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨rfl, by simp, trivial⟩
  | k :: ks, ks', s', hk, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨k', s₁, h1, h⟩ := bind_run h
    obtain ⟨hk1, hk2⟩ := hk k List.mem_cons_self
    obtain ⟨hs1, hlv', hds', hg', hR1⟩ := classKeyOfI_run hp hk1 hk2 h1
    rw [hs1] at h
    obtain ⟨ks'', s₂, h2, h⟩ := bind_run h
    obtain ⟨hs2, hall, hR2⟩ := mapM_classKeyOfI_run hp
      (fun x hx => hk x (List.mem_cons_of_mem _ hx)) h2
    rw [hs2] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨rfl, fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hlv', hds', hg'⟩
      · exact hall x hx
    · exact ⟨hR1, hR2⟩

/-! ## An outside major's container and type -/

/-- A constructor entry of a container, translated. -/
@[expose] def trCE (c : Lean.ConstantVal × Nat × Nat) : ConLeche.ConstantVal × Nat × Nat :=
  (trCV c.1, c.2.1, c.2.2)

theorem nestCtorEntry_tr (C : Lean.Name) (cv : Lean.ConstantVal) (nPc nF : Nat) :
    ConLeche.nestCtorEntry (toName C) (.ctorInfo (trCV cv) nPc nF) =
      (InLean.nestCtorEntry C cv nPc nF).map trCE := by
  unfold ConLeche.nestCtorEntry InLean.nestCtorEntry
  simp only
  rw [trCV_type, stripPis_tr]
  cases InLean.stripPis (nPc + nF) cv.type with
  | none => rfl
  | some q =>
    obtain ⟨ds, body⟩ := q
    simp only [Option.map_some]
    rw [getAppFn_tr]
    have hne : ∀ m b, Expr.getAppFnT body ≠ .mdata m b := fun m b h => getAppFnT_ne_mdata h
    generalize Expr.getAppFnT body = x at hne
    cases x with
    | const n us =>
      simp only [trC, trE, toName_beq]
      by_cases hn : (n == C) = true
      · simp only [hn, ↓reduceIte, Option.map_some]; rfl
      · simp only [hn, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    | mdata m b => exact (hne m b rfl).elim
    | fvar id => simp only [trC, trE, Option.getD_none, Option.map_none]
    | _ => simp [trC, trE]

theorem ctorEntry_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) (C n : Lean.Name) :
    (L.find? (toName n)).bind (ConLeche.nestCtorEntry (toName C)) =
      ((fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry C cv nPc nF).map trCE := by
  cases hv : fe.ctorView? n with
  | some q =>
    obtain ⟨cv, nPc, nF⟩ := q
    obtain ⟨ccv, hcv, hL⟩ := ctorView_rel hJ.pres hv
    rw [hL, hcv.eq_trCV]
    simp only [Option.bind_some]
    exact nestCtorEntry_tr C cv nPc nF
  | none =>
    have hn := ctorView_none hJ.pres hv
    simp only [Option.bind_none, Option.map_none]
    cases hL : L.find? (toName n) with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo ccv nP nF => exact (hn ccv nP nF hL).elim
      | _ => rfl

/-- **A stored container's constructors** (`targetCtorsOf`), at master's
lookup: InLean's answer translated. -/
theorem targetCtorsOf_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) (I : Lean.Name) :
    ConLeche.targetCtorsOf (ConLeche.mkFEnv L) (toName I) =
      (InLean.targetCtorsOf fe I).map fun q => (q.1, q.2.map trCtor) := by
  unfold ConLeche.targetCtorsOf InLean.targetCtorsOf ConLeche.nestContainer InLean.nestContainer
  simp only [ConLeche.mkFEnv_find?]
  cases hv : fe.indView? I with
  | none =>
    have hn := indView_none_tr hJ hv
    simp only [Option.map_none]
  | some q =>
    obtain ⟨cv, caps⟩ := q
    obtain ⟨hL, -, -⟩ := indView_trCV hJ hv
    rw [hL]
    simp only
    have hcs : (toCaps caps).ctors.filterMap
        (fun n => (L.find? n).bind (ConLeche.nestCtorEntry (toName I))) =
        (caps.ctors.filterMap fun n =>
          (fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry I cv nPc nF).map trCE := by
      simp only [toCaps, List.filterMap_map]
      rw [List.map_filterMap]
      congr 1
      funext n
      exact ctorEntry_tr hJ I n
    rw [hcs]
    generalize (caps.ctors.filterMap fun n =>
      (fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry I cv nPc nF) = cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      simp only [List.map_cons, Option.map_some, List.map_map]
      rfl

/-- A bind on the pure side, under three facts. -/
theorem runs3_bind {A B C : Prop} {α β : Type} {x : ConLeche.FueledM α} {f : α → ConLeche.FueledM β}
    {a : α} {b : β} (hx : Runs x a) (h : A ∧ B ∧ C ∧ Runs (f a) b) : A ∧ B ∧ C ∧ Runs (x >>= f) b :=
  ⟨h.1, h.2.1, h.2.2.1, Runs.bind hx h.2.2.2⟩

/-- **An outside major's instantiated type former** (`targetOutsideInst`):
InLean's index count and sort are master's at the readings. -/
theorem targetOutsideInstI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {I : Lean.Name} {us : List Lean.Level} {ds : List Lean.Expr}
    {s₀ s' : InLean.CState} {k : Nat} {sI : Lean.Level} (hs : CSOKI .verified false L s₀)
    (hlv : us.all okLv = true) (hokds : OkSL s₀ ds = true)
    (hcds : ∀ a ∈ ds, (TrS s₀ a).looseBVarsBounded 0 = true)
    (h : InLean.targetOutsideInst (sharedOpsC .verified fe) fe I us ds s₀ = .ok ((k, sI), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okL sI = true ∧
      Runs (ConLeche.targetOutsideInst (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (toName I) (us.map trL) (TrSL s₀ ds)) (k, trL sI) := by
  unfold InLean.targetOutsideInst at h
  unfold ConLeche.targetOutsideInst
  simp only [ConLeche.mkFEnv_find?]
  cases hv : fe.indView? I with
  | none => rw [hv] at h; exact (throw_run h).elim
  | some q =>
  rw [hv] at h
  obtain ⟨cv, caps⟩ := q
  obtain ⟨hL, hok, hcl⟩ := indView_trCV hJ hv
  rw [hL]
  simp only at h ⊢
  obtain ⟨tyC, s₂, h2, h⟩ := bind_run h
  obtain ⟨hs₂, ht₂, hokC, hclC, hRC⟩ := familyTelescopeI_run hJ hRF hok hcl hs h2
  refine runs3_bind hRC ?_
  obtain ⟨r, s₃, h3, h⟩ := bind_run h
  obtain ⟨hs₃, ht₃, hokr, htrr⟩ := tripleI_iff_run.1
    (instLevelParamsM_specI hs₂ (OkS_of_okC s₂ hokC) (fvarS_of_okC hokC) hlv) r s₃ h3
  rw [TrS_of_okC _ hokC] at htrr
  have ht13 := ht₂.trans ht₃
  have hokds₃ := okSL_of_tabLe ht13 hokds
  have hcds₃ : ∀ a ∈ ds, (TrS s₃ a).looseBVarsBounded 0 = true := by
    intro a ha
    rw [TrS_of_tabLe ht13 (by simp only [OkSL, List.all_eq_true] at hokds; exact hokds a ha)]
    exact hcds a ha
  have hmap := instPisWithI_map ds r hokr hokds₃ hcds₃
  rw [htrr, TrSL_of_tabLe ht13 hokds] at hmap
  simp only [trCV_levelParams]
  cases hi : InLean.instPisWith ds r with
  | none => simp only [hi] at h; exact (throw_run h).elim
  | some ty0 =>
  simp only [hi] at h
  rw [hi, Option.map_some] at hmap
  rw [← hmap]
  simp only
  obtain ⟨hokty, -⟩ := instPisWithI_tr ds r hokr hokds₃ hcds₃ hi
  obtain ⟨hpb, -, hokend, hnm⟩ := piBinders_TrS ty0 hokty
  rw [hpb]
  simp only
  generalize hx : (InLean.piBinders ty0).2 = x at h hokend hnm
  cases x with
  | sort u0 =>
    simp only [EO.stripTop] at h
    obtain ⟨hkt, rfl⟩ := pure_run h
    simp only [Prod.mk.injEq] at hkt
    obtain ⟨rfl, rfl⟩ := hkt
    rw [TrS_sort]
    simp only [List.length_map]
    have hu0 : okL u0 = true := by
      simp only [OkS_sort, okLv, Bool.and_eq_true] at hokend
      exact hokend.1
    exact ⟨hs₃, ht13, hu0, Runs.pure _⟩
  | mdata m b => exact (hnm m b rfl).elim
  | fvar id => simp only [EO.stripTop] at h; exact (throw_run h).elim
  | _ => simp only [EO.stripTop] at h; exact (throw_run h).elim

/-! ## A class as a major -/

/-- A resolved major has a reading at a state (and no recorded normal forms
yet: the classes' are filled in by the recursor stage). -/
@[expose] def OkTM (s : InLean.CState) (M : InLean.TargetMajor) : Prop :=
  M.lvls.all okLv = true ∧ OkSL s M.ds = true ∧ OkSL s M.pfvs = true ∧ M.nfs = []

theorem OkTM.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {M : InLean.TargetMajor}
    (hM : OkTM s₀ M) : OkTM s₁ M ∧ trTM s₁ M = trTM s₀ M := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨⟨h1, okSL_of_tabLe h h2, okSL_of_tabLe h h3, h4⟩, ?_⟩
  unfold trTM
  rw [TrSL_of_tabLe h h2, TrSL_of_tabLe h h3, h4]
  rfl

theorem toName_quotName : toName InLean.quotName = ConLeche.quotName := rfl

theorem trShape_members (p : InLean.BlockShape) : (trShape p).members = p.members.map trMember := rfl

/-- A bind on the pure side, under five facts. -/
theorem runs5_bind {A B C D E : Prop} {α β : Type} {x : ConLeche.FueledM α}
    {f : α → ConLeche.FueledM β} {a : α} {b : β} (hx : Runs x a)
    (h : A ∧ B ∧ C ∧ D ∧ E ∧ Runs (f a) b) : A ∧ B ∧ C ∧ D ∧ E ∧ Runs (x >>= f) b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, Runs.bind hx h.2.2.2.2.2⟩

theorem any_nestOcc_tr {s : InLean.CState} (names : List Lean.Name) (lo hi : Nat) :
    ∀ {l : List Lean.Expr}, OkSL s l = true →
      (TrSL s l).any (fun x => x.nestOcc (names.map toName) lo hi) =
        l.any (fun x => InLean.nestOcc names lo hi x)
  | [], _ => rfl
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    simp only [TrSL_cons, List.any_cons, any_nestOcc_tr names lo hi h.2,
      nestOccI_tr names lo hi h.1]

/-- **A class resolved as a major** (`targetMajorOf`): InLean's major is master's
on the readings, at master's lookup; an outside major's parameters pass
master's range guard. -/
theorem targetMajorOfI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {p : InLean.BlockShape} (hsr : okL p.resSort = true)
    {pfvs fvs : List Lean.Expr} {mty : Lean.Expr} {s₀ s' : InLean.CState} {M : InLean.TargetMajor}
    (hs : CSOKI .verified false L s₀) (hokp : OkSL s₀ pfvs = true) (hokf : OkSL s₀ fvs = true)
    (hokm : OkS s₀ mty = true)
    (hcl : ∀ a ∈ appArgs mty, (TrS s₀ a).looseBVarsBounded 0 = true)
    (h : InLean.targetMajorOf (sharedOpsC .verified fe) fe p pfvs fvs mty s₀ = .ok (M, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkTM s' M ∧
      (M.member = none → ∀ x ∈ TrSL s' M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      (M.member = none → ∀ x ∈ M.ds, x ∈ appArgs mty) ∧
      Runs (ConLeche.targetMajorOf (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) (trShape p)
        (TrSL s₀ pfvs) (TrSL s₀ fvs) (TrS s₀ mty)) (trTM s' M) := by
  unfold InLean.targetMajorOf at h
  unfold ConLeche.targetMajorOf
  have hokargs : OkSL s₀ (appArgs mty) = true := OkSL_appArgs s₀ hokm
  rw [← TrSL_appArgs]
  obtain ⟨hC1, -⟩ := constHead_tr hokm
  cases hg : mty.getAppFnT with
  | const I us =>
    simp only [hg] at h
    rw [hC1 I us hg]
    simp only
    have hokus : us.all okLv = true := by
      have := OkS_getAppFnT s₀ hokm
      rwa [hg, OkS_const] at this
    rw [trShape_memberNames, findIdx?_map_toName]
    cases hi : p.memberNames.findIdx? (· == I) with
    | some t =>
      simp only [hi] at h ⊢
      obtain ⟨ms, s₁, h1, h⟩ := bind_run h
      rw [trShape_members, List.getElem?_map]
      cases hm : p.members[t]? with
      | none => simp only [hm, InLean.unwrapOr] at h1; exact (throw_run h1).elim
      | some ms0 =>
      simp only [hm, InLean.unwrapOr] at h1
      obtain ⟨rfl, rfl⟩ := pure_run h1
      simp only [Option.map_some, ConLeche.unwrapOr]
      refine runs5_bind (Runs.pure _) ?_
      by_cases hgd : (us == p.lps.map Level.param && List.take p.nP (appArgs mty) ==
          List.take p.nP fvs) = true
      · simp only [hgd, ↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := pure_run h
        simp only [Bool.and_eq_true] at hgd
        have hlv : (us.map trL == (trShape p).lps.map ConLeche.Level.param) = true := by
          rw [trShape_lps, ← params_trL, map_trL_beq hokus (params_okLv _)]; exact hgd.1
        have hds : (List.take p.nP (TrSL s₀ (appArgs mty)) == List.take p.nP (TrSL s₀ fvs)) = true := by
          rw [← TrSL_take, ← TrSL_take, TrSL_of_beq (OkSL_take s₀ hokargs _)
            (fun b hb => TransS_of_ok (by
              simp only [OkSL, List.all_eq_true] at hokf
              exact hokf b (List.mem_of_mem_take hb))) hgd.2]
          exact beq_self_eq_true _
        simp only [hlv, hds, Bool.and_self, ↓reduceIte,
          trShape_nP]
        refine ⟨hs, TabLe.refl _, ⟨hokus, OkSL_take s₀ hokf _, hokp, rfl⟩, (fun h => by cases h),
          (fun h => by cases h), ?_⟩
        simp only [trTM, trMember, TrSL_take, List.map_nil]
        exact Runs.pure _
      · simp only [hgd] at h
        obtain ⟨_, _, h2, -⟩ := bind_run h
        exact (throw_run h2).elim
    | none =>
      simp only [hi] at h ⊢
      have hq : (toName I == ConLeche.quotName) = (I == InLean.quotName) := by
        rw [← toName_quotName, toName_beq]
      rw [hq]
      by_cases hqI : (I == InLean.quotName) = true
      · simp only [hqI, ↓reduceIte] at h
        obtain ⟨_, _, h1, -⟩ := bind_run h
        exact (throw_run h1).elim
      simp only [hqI, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [targetCtorsOf_tr hJ I]
      cases hc : InLean.targetCtorsOf fe I with
      | none => simp only [hc] at h; exact (throw_run h).elim
      | some q =>
      obtain ⟨nPc, ctors⟩ := q
      simp only [hc, Option.map_some] at h ⊢
      have hokds : OkSL s₀ ((appArgs mty).take nPc) = true := OkSL_take s₀ hokargs _
      have hcds : ∀ a ∈ (appArgs mty).take nPc, (TrS s₀ a).looseBVarsBounded 0 = true :=
        fun a ha => hcl a (List.mem_of_mem_take ha)
      by_cases hgd : (((appArgs mty).take nPc).length == nPc && ((appArgs mty).take nPc).all
          fun x => !x.hasLooseBVars && decide (InLean.fvarB x ≤ p.nP)) = true
      · simp only [hgd, ↓reduceIte] at h
        have hgC : (((TrSL s₀ (appArgs mty)).take nPc).length == nPc &&
            ((TrSL s₀ (appArgs mty)).take nPc).all
              fun x => x.bvarB == 0 && decide (x.fvarB ≤ (trShape p).nP)) = true := by
          rw [← TrSL_take]
          simp only [Bool.and_eq_true, TrSL_length] at hgd ⊢
          refine ⟨hgd.1, ?_⟩
          simp only [TrSL, List.all_map, List.all_eq_true, Function.comp_apply] at hgd ⊢
          intro x hx
          simp only [OkSL, List.all_eq_true] at hokds
          exact rangeGuard_tr (hokds x hx) (hgd.2 x hx)
        have hgdC : ∀ x ∈ TrSL s₀ ((appArgs mty).take nPc), x.bvarB = 0 ∧ x.fvarB ≤ p.nP := by
          rw [TrSL_take]
          simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hgC
          exact hgC.2
        simp only [hgC, ↓reduceIte]
        rw [← TrSL_take, any_nestOcc_tr p.memberNames 0 0 hokds]
        by_cases hn : ((appArgs mty).take nPc).any (fun x => InLean.nestOcc p.memberNames 0 0 x) = true
        · simp only [hn, ↓reduceIte] at h ⊢
          obtain ⟨ki, s₂, h2, h⟩ := bind_run h
          obtain ⟨nIdx, sI⟩ := ki
          obtain ⟨hs₂, ht₂, hsI, hR2⟩ := targetOutsideInstI_run hJ hRF hs hokus hokds hcds h2
          refine runs5_bind hR2 ?_
          obtain ⟨b, s₃, h3, h⟩ := bind_run h
          obtain ⟨hs₃, ht₃, hb⟩ := tripleI_iff_run.1 (liftFueled_specI hs₂ "level comparison" _) b s₃ h3
          rw [show (trShape p).resSort = trL p.resSort from rfl, ← isEquiv_trL hsI hsr, hb]
          refine runs5_bind (Runs.pure _) ?_
          cases b with
          | false =>
            simp only at h
            obtain ⟨_, _, h4, -⟩ := bind_run h
            exact (throw_run h4).elim
          | true =>
            simp only [↓reduceIte] at h ⊢
            obtain ⟨rfl, rfl⟩ := pure_run h
            have ht03 := ht₂.trans ht₃
            refine ⟨hs₃, ht03, ⟨hokus, okSL_of_tabLe ht03 hokds, okSL_of_tabLe ht03 hokp, rfl⟩,
              (fun _ => by rw [TrSL_of_tabLe ht03 hokds]; exact hgdC),
              (fun _ x hx => List.mem_of_mem_take hx), ?_⟩
            simp only [trTM, TrSL_of_tabLe ht03 hokds, TrSL_of_tabLe ht03 hokp, List.map_nil]
            exact Runs.pure _
        · simp only [hn] at h
          obtain ⟨_, _, h2, -⟩ := bind_run h
          exact (throw_run h2).elim
      · simp only [hgd] at h
        obtain ⟨_, _, h2, -⟩ := bind_run h
        exact (throw_run h2).elim
  | _ =>
    simp only [hg] at h
    exact (throw_run h).elim

/-! ## The majors' pins and every class -/

/-- **An outside major's parameters typed** (`targetPinTys`). -/
theorem targetPinTysI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L) {d : Nat} :
    ∀ (xs : List Lean.Expr) {s₀ s' : InLean.CState} {v : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ xs = true →
      (∀ a ∈ xs, ConLeche.Expr.WScoped d (TrS s₀ a) ∧ (TrS s₀ a).looseBVarsBounded 0 = true) →
      InLean.targetPinTys (sharedOpsC .verified fe) fe d xs s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.targetPinTys (ConLeche.fueledOpsM .verified) L d (TrSL s₀ xs)) ()
  | [], s₀, s', v, hs, _, _, h => by
    unfold InLean.targetPinTys at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.targetPinTys; exact Runs.pure _⟩
  | x :: xs, s₀, s', v, hs, hok, hw, h => by
    unfold InLean.targetPinTys at h
    simp only [OkSL_cons, Bool.and_eq_true] at hok
    obtain ⟨hwx, hcx⟩ := hw x List.mem_cons_self
    obtain ⟨t, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, -, hR1, -, -⟩ := tripleI_iff_run.1 (hO.infer hs hok.1 hwx hcx) t s₁ h1
    have hok₁ := okSL_of_tabLe ht₁ hok.2
    obtain ⟨hs', ht', hR⟩ := targetPinTysI_run hO xs hs₁ hok₁ (fun a ha => by
      rw [TrS_of_tabLe ht₁ (by simp only [OkSL, List.all_eq_true] at hok; exact hok.2 a ha)]
      exact hw a (List.mem_cons_of_mem _ ha)) h
    refine ⟨hs', ht₁.trans ht', ?_⟩
    rw [TrSL_cons]
    unfold ConLeche.targetPinTys
    rw [TrSL_of_tabLe ht₁ hok.2] at hR
    exact Runs.bind hR1 hR

theorem mkFEnv_find?_fun (L : ConLeche.Env) : (ConLeche.mkFEnv L).find? = L.find? :=
  funext (ConLeche.mkFEnv_find? L)

theorem lbb_of_bvarB {x : ConLeche.Expr} (h : x.bvarB = 0) : x.looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.looseBVarsBounded_iff, ← ConLeche.Expr.bvarB_eq, h]
  exact Nat.le_refl 0

/-- **A major's pins** (`targetMajorPins`): nothing at a member; an outside
major's parameters typed at the prefix and the instantiation checked. -/
theorem targetMajorPinsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {rP : Nat} {M : InLean.TargetMajor} {s₀ s' : InLean.CState} {v : Unit}
    (hs : CSOKI .verified false L s₀) (hM : OkTM s₀ M)
    (hw : M.member = none → ∀ a ∈ TrSL s₀ M.ds, ConLeche.Expr.WScoped rP a ∧ a.bvarB = 0)
    (h : InLean.targetMajorPins (sharedOpsC .verified fe) fe rP M s₀ = .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.targetMajorPins (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) rP
        (trTM s₀ M)) () := by
  unfold InLean.targetMajorPins at h
  unfold ConLeche.targetMajorPins
  simp only [trTM, mkFEnv_find?_fun]
  cases hm : M.member with
  | some t =>
    simp only [hm, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | none =>
    simp only [hm, Option.isNone_none, ↓reduceIte] at h ⊢
    obtain ⟨hlv, hds, -, -⟩ := hM
    have hw' : ∀ a ∈ M.ds, ConLeche.Expr.WScoped rP (TrS s₀ a) ∧
        (TrS s₀ a).looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨h1, h2⟩ := hw hm (TrS s₀ a) (List.mem_map_of_mem ha)
      exact ⟨h1, lbb_of_bvarB h2⟩
    obtain ⟨_, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hR1⟩ := targetPinTysI_run hJ.ops M.ds hs hds hw' h1
    have hds₁ := okSL_of_tabLe ht₁ hds
    obtain ⟨hs', ht', hR2⟩ := familyKeyCheckI_run (d := rP) hJ hRF hs₁ hlv hds₁ (fun a ha => by
      rw [TrS_of_tabLe ht₁ (by simp only [OkSL, List.all_eq_true] at hds; exact hds a ha)]
      exact hw' a ha) h
    refine ⟨hs', ht₁.trans ht', Runs.bind hR1 ?_⟩
    rw [TrSL_of_tabLe ht₁ hds] at hR2
    exact hR2

theorem TrS_mkAppL_const (s : InLean.CState) (I : Lean.Name) (us : List Lean.Level)
    (ds : List Lean.Expr) :
    TrS s (InLean.mkAppL (.const I us) ds) =
      ConLeche.Expr.mkAppN (.const (toName I) (us.map trL)) (TrSL s ds) :=
  TrS_mkAppN s ds _

theorem getAppArgs_mkAppN' : ∀ (ds : List ConLeche.Expr) (c : ConLeche.Expr),
    (ConLeche.Expr.mkAppN c ds).getAppArgs = c.getAppArgs ++ ds
  | [], c => by simp [ConLeche.Expr.mkAppN]
  | a :: ds, c => by
    rw [ConLeche.Expr.mkAppN, getAppArgs_mkAppN' ds (.app c a), ConLeche.Expr.getAppArgs]
    simp

theorem getAppArgs_mkAppN_const (c : ConLeche.Expr) (hc : c.getAppArgs = []) (ds : List ConLeche.Expr) :
    (ConLeche.Expr.mkAppN c ds).getAppArgs = ds := by
  rw [getAppArgs_mkAppN', hc, List.nil_append]

/-- **Every class checked as a major** (`classMajors`), over the openers
`pfvs`: InLean's majors are master's on the readings. -/
theorem classMajorsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {p : InLean.BlockShape} (hsr : okL p.resSort = true)
    {pfvs : List Lean.Expr} :
    ∀ {keys : List InLean.ClassKey} {s₀ s' : InLean.CState} {Ms : List InLean.TargetMajor},
      CSOKI .verified false L s₀ → OkSL s₀ pfvs = true →
      (∀ k ∈ keys, k.lvls.all okLv = true ∧ OkSL s₀ k.ds = true ∧
        ∀ x ∈ TrSL s₀ k.ds, ConLeche.Expr.WScoped p.nP x ∧ x.bvarB = 0) →
      InLean.classMajors (sharedOpsC .verified fe) fe p pfvs keys s₀ = .ok (Ms, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ M ∈ Ms, OkTM s' M) ∧
        Runs (ConLeche.classMajors (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) (trShape p)
          (TrSL s₀ pfvs) (keys.map (trCK s₀))) (Ms.map (trTM s'))
  | [], s₀, s', Ms, hs, _, _, h => by
    unfold InLean.classMajors at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by simp, by unfold ConLeche.classMajors; exact Runs.pure _⟩
  | key :: keys, s₀, s', Ms, hs, hokp, hk, h => by
    unfold InLean.classMajors at h
    obtain ⟨hlv, hds, hwd⟩ := hk key List.mem_cons_self
    obtain ⟨M, s₁, h1, h⟩ := bind_run h
    have hokm : OkS s₀ (InLean.mkAppL (.const key.ind key.lvls) key.ds) = true := by
      unfold InLean.mkAppL
      rw [OkS_mkAppN, OkS_const, hlv, hds]; rfl
    have hargs : TrSL s₀ (appArgs (InLean.mkAppL (.const key.ind key.lvls) key.ds)) =
        TrSL s₀ key.ds := by
      rw [TrSL_appArgs, TrS_mkAppL_const]
      exact getAppArgs_mkAppN_const _ rfl _
    have hmemA : ∀ a ∈ appArgs (InLean.mkAppL (.const key.ind key.lvls) key.ds),
        TrS s₀ a ∈ TrSL s₀ key.ds := by
      intro a ha
      rw [← hargs]
      exact List.mem_map_of_mem ha
    obtain ⟨hs₁, ht₁, hokM, hgM, hsub, hR1⟩ := targetMajorOfI_run hJ hRF hsr hs hokp hokp hokm
      (fun a ha => lbb_of_bvarB (hwd _ (hmemA a ha)).2) h1
    have hokA : OkSL s₀ (appArgs (InLean.mkAppL (.const key.ind key.lvls) key.ds)) = true :=
      OkSL_appArgs s₀ hokm
    obtain ⟨_, s₂, h2, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hR2⟩ := targetMajorPinsI_run (rP := p.nP) hJ hRF hs₁ hokM (fun hn a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      have hxA := hsub hn x hx
      have hokx : OkS s₀ x = true := by
        simp only [OkSL, List.all_eq_true] at hokA; exact hokA x hxA
      rw [TrS_of_tabLe ht₁ hokx]
      exact hwd _ (hmemA x hxA)) h2
    obtain ⟨Ms', s₃, h3, h⟩ := bind_run h
    have ht12 := ht₁.trans ht₂
    obtain ⟨hs₃, ht₃, hokMs, hR3⟩ := classMajorsI_run hJ hRF hsr hs₂ (okSL_of_tabLe ht12 hokp)
      (fun k hk' => by
        obtain ⟨a1, a2, a3⟩ := hk k (List.mem_cons_of_mem _ hk')
        refine ⟨a1, okSL_of_tabLe ht12 a2, ?_⟩
        rw [TrSL_of_tabLe ht12 a2]; exact a3) h3
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hokM', htrM⟩ := OkTM.mono (ht₂.trans ht₃) hokM
    refine ⟨hs₃, ht12.trans ht₃, fun M' hM' => ?_, ?_⟩
    · rcases List.mem_cons.1 hM' with rfl | hM'
      · exact hokM'
      · exact hokMs M' hM'
    · unfold ConLeche.classMajors
      simp only [List.map_cons, trCK]
      rw [← TrS_mkAppL_const]
      refine Runs.bind hR1 (Runs.bind hR2 (Runs.bind (a := Ms'.map (trTM s₃)) ?_ ?_))
      · rw [TrSL_of_tabLe ht12 hokp] at hR3
        have hks : keys.map (trCK s₂) = keys.map (trCK s₀) := List.map_congr_left fun k hk' => by
          simp only [trCK, TrSL_of_tabLe ht12 (hk k (List.mem_cons_of_mem _ hk')).2.1]
        rw [hks] at hR3
        exact hR3
      · rw [htrM]; exact Runs.pure _

/-! ## The class stage -/

/-- A term moved to the block's parameters, its variables below them, is
scoped there (master's `replaceFVars_WScoped_of_below`). -/
theorem canon_wscoped {params : List ConLeche.Expr} {d : Nat}
    (hp : ∀ (i : Nat) x, params[i]? = some x → ConLeche.Expr.WScoped d x) (hlen : d ≤ params.length)
    {y : ConLeche.Expr} (hb : (ConLeche.targetCanonParams params y).fvarB ≤ d) :
    ConLeche.Expr.WScoped d (ConLeche.targetCanonParams params y) := by
  rw [ConLeche.Expr.fvarB_eq] at hb
  exact ConLeche.replaceFVars_WScoped_of_below (g := fun i => params[i]?) (fun i r h => hp i r h)
    (fun i hi => by simp only [Option.isSome_iff_exists]; exact ⟨params[i]'(by omega), by simp⟩) y
    (ConLeche.Expr.fvarsBelow_iff.2 hb)

theorem trShape_k (p : InLean.BlockShape) : (trShape p).k = p.k := by
  simp [ConLeche.BlockShape.k, InLean.BlockShape.k, trShape]

theorem filter_member_trTM (s : InLean.CState) (Ms : List InLean.TargetMajor) (t : Nat) :
    ((Ms.map (trTM s)).filter (·.member == some t)).length = (Ms.filter (·.member == some t)).length := by
  rw [List.filter_map, List.length_map]
  rfl

/-- **The class stage** (`checkBlockClasses`): InLean's reading and classes are
master's on the readings, at master's lookup `mkFEnv L`, over the block's
parameters (variables scoped below the parameter count, one per parameter). -/
theorem checkBlockClassesI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {p : InLean.BlockShape} (hsr : okL p.resSort = true)
    (hrecs : ∀ rc ∈ p.recs, okC rc.cvR.type = true ∧ (trC rc.cvR.type).looseBVarsBounded 0 = true)
    {params : List Lean.Expr} {s₀ s' : InLean.CState} {rd : InLean.ClassRead}
    {Ms : List InLean.TargetMajor} (hs : CSOKI .verified false L s₀) (hokp : OkSL s₀ params = true)
    (hpar : ∀ (i : Nat) x, (TrSL s₀ params)[i]? = some x → ConLeche.Expr.WScoped p.nP x)
    (hlen : p.nP ≤ params.length)
    (h : InLean.checkBlockClasses (sharedOpsC .verified fe) fe p params s₀ = .ok ((rd, Ms), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ x ∈ rd.slots, OkSlot s' x) ∧
      (∀ M ∈ Ms, OkTM s' M) ∧
      Runs (ConLeche.checkBlockClasses (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) (trShape p)
        (TrSL s₀ params)) (trCR s' rd, Ms.map (trTM s')) := by
  unfold InLean.checkBlockClasses at h
  unfold ConLeche.checkBlockClasses
  obtain ⟨o, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hR1⟩ := classReadI_run p.nP (InLean.classNPcOf p fe)
    (ConLeche.classNPcOf (trShape p) (ConLeche.mkFEnv L)) (classNPcOf_tr hJ p) hrecs hs h1
  obtain ⟨rd', s₂, h2, h⟩ := bind_run h
  cases o with
  | none => simp only [InLean.unwrapOr] at h2; exact (throw_run h2).elim
  | some rd0 =>
  simp only [InLean.unwrapOr] at h2
  obtain ⟨rfl, rfl⟩ := pure_run h2
  obtain ⟨hoks, hcr⟩ := hR1 rd0 rfl
  rw [trShape_nP, show (trShape p).recs = p.recs.map trRec from rfl, hcr]
  simp only [ConLeche.unwrapOr]
  have hokp₁ := okSL_of_tabLe ht₁ hokp
  have htp₁ := TrSL_of_tabLe ht₁ hokp
  obtain ⟨keys, s₃, h3, h⟩ := bind_run h
  obtain ⟨hs3, hkeys, hRk⟩ := mapM_classKeyOfI_run (nP := p.nP) hokp₁ (okSlot_classes hoks) h3
  rw [hs3] at h
  obtain ⟨Ms0, s₄, h4, h⟩ := bind_run h
  obtain ⟨hs₄, ht₄, hokMs, hRM⟩ := classMajorsI_run hJ hRF hsr hs₁ hokp₁ (fun k hk => by
    obtain ⟨a1, a2, a3⟩ := hkeys k hk
    refine ⟨a1, a2, fun x hx => ?_⟩
    obtain ⟨⟨hb, hf⟩, y, rfl⟩ := a3 x hx
    rw [htp₁] at hf hb ⊢
    exact ⟨canon_wscoped hpar (by rw [TrSL_length]; exact hlen) hf, hb⟩) h4
  rw [htp₁] at hRM
  by_cases hg : ((List.range p.k).all fun t => (Ms0.filter (·.member == some t)).length == 1) = true
  · simp only [hg, ↓reduceIte] at h
    obtain ⟨hq, rfl⟩ := pure_run h
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hgC : ((List.range (trShape p).k).all fun t =>
        ((Ms0.map (trTM s₄)).filter (·.member == some t)).length == 1) = true := by
      simp only [trShape_k, filter_member_trTM]; exact hg
    have hsl : trCR s₄ rd0 = trCR s₁ rd0 := by
      simp only [trCR]
      congr 1
      exact List.map_congr_left fun x hx => trSlot_mono ht₄ (hoks x hx)
    refine ⟨hs₄, ht₁.trans ht₄, fun x hx => OkSlot.mono ht₄ (hoks x hx), hokMs, ?_⟩
    refine Runs.bind (Runs.pure _) ?_
    refine Runs.bind (a := keys.map (trCK s₁)) ?_ ?_
    · rw [classes_trCR, ← htp₁]
      exact runs_mapM hRk
    · refine Runs.bind hRM ?_
      simp only [hgC, ↓reduceIte, hsl]
      exact Runs.pure _
  · simp only [hg] at h
    obtain ⟨_, _, h5, -⟩ := bind_run h
    exact (throw_run h5).elim

/-! ## The seeds -/

theorem fvSubRel_nestKeyMap {s : InLean.CState} {ds holes : List Lean.Expr} (hd : OkSL s ds = true)
    (hh : OkSL s holes = true) :
    FvSubRel s (InLean.nestKeyMap ds holes) (ConLeche.nestKeyMap (TrSL s ds) (TrSL s holes)) := by
  intro i
  unfold InLean.nestKeyMap ConLeche.nestKeyMap
  rw [TrSL_length]
  by_cases hi : i < ds.length
  · simp only [hi, ↓reduceIte]
    exact ⟨by simp [TrSL], fun y hy => okS_getElem? hd hy⟩
  · simp only [hi, ↓reduceIte]
    exact ⟨by simp [TrSL], fun y hy => okS_getElem? hh hy⟩

/-- **A class as a seed** (`nestSeedOf`): InLean's key reads, at the final
state, as master's at the readings. -/
theorem nestSeedOfI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx)
    {s₀ s' : InLean.CState} (hs : CSOKI mode eager env s₀) {holes : List Lean.Expr}
    (hpar : cctx.params = TrSL s₀ ctx.params) (hokpar : OkSL s₀ ctx.params = true)
    (hokh : OkSL s₀ holes = true) {I : Lean.Name} {us : List Lean.Level} {ds : List Lean.Expr}
    {nPc : Nat} {r : InLean.NestKey × Nat} (hds : OkSL s₀ ds = true)
    (h : InLean.nestSeedOf ctx holes I us ds nPc s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' r.1.ds = true ∧ r.1.lvls = us ∧
      ConLeche.nestSeedOf cctx (TrSL s₀ holes) (toName I) (us.map trL) (TrSL s₀ ds) nPc =
        (trKey s' r.1, r.2) := by
  unfold InLean.nestSeedOf at h
  obtain ⟨vars, s₁, h1, h⟩ := bind_run h
  unfold InLean.nestCanonVars at h1
  obtain ⟨hs₁, ht₁, hokv, htrv⟩ := mapM_mkFVarM_run (mode := mode) (eager := eager) (env := env)
    (fun m => ctx.nP + m) (List.range ctx.names.length) hs h1
  obtain ⟨rfl, rfl⟩ := pure_run h
  have hsub := nestCanonSub_rel (s := s₁) (names := ctx.names) ctx.nP (params_okLv ctx.lps) hokv htrv
  have hkm := fvSubRel_nestKeyMap (okSL_of_tabLe ht₁ hokpar) (okSL_of_tabLe ht₁ hokh)
  have hx : ∀ x ∈ ds,
      OkS s₁ (InLean.replaceFVars (InLean.nestKeyMap ctx.params holes)
        (InLean.replaceApps (InLean.nestCanonSub ctx.names (ctx.lps.map .param) vars) 0 ctx.nP x)) = true ∧
      TrS s₁ (InLean.replaceFVars (InLean.nestKeyMap ctx.params holes)
        (InLean.replaceApps (InLean.nestCanonSub ctx.names (ctx.lps.map .param) vars) 0 ctx.nP x)) =
      ((TrS s₀ x).replaceApps (ConLeche.nestCanonSub cctx.names (cctx.lps.map .param) cctx.nP) 0
        cctx.nP).replaceFVars (ConLeche.nestKeyMap cctx.params (TrSL s₀ holes)) := by
    intro x hxd
    have hokx : OkS s₁ x = true := by
      simp only [OkSL, List.all_eq_true] at hds; exact okS_of_tabLe ht₁ (hds x hxd)
    have hA := replaceAppsI_tr hsub 0 ctx.nP x 0 hokx
    rw [← replaceApps_eq] at hA
    have hB := replaceFVarsI_tr hkm hA.1
    refine ⟨hB.1, ?_⟩
    rw [hB.2, hA.2, TrS_of_tabLe ht₁ (by simp only [OkSL, List.all_eq_true] at hds; exact hds x hxd),
      TrSL_of_tabLe ht₁ hokpar, TrSL_of_tabLe ht₁ hokh, hR.names, hR.lps, hR.nP, hpar, params_trL]
  refine ⟨hs₁, ht₁, ?_, rfl, ?_⟩
  · simp only [OkSL, List.all_map, List.all_eq_true, Function.comp_apply]
    exact fun x hxd => (hx x hxd).1
  · simp only [ConLeche.nestSeedOf, trKey]
    generalize TrSL s₀ holes = H at hx ⊢
    simp only [TrSL, List.map_map]
    congr 2
    exact List.map_congr_left fun x hxd => ((hx x hxd).2).symm

/-- **The seeds** (`classSeeds`): every outside class, as master's seed on the
readings. -/
theorem classSeedsI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx)
    {holes : List Lean.Expr} :
    ∀ {Ms : List InLean.TargetMajor} {s₀ s' : InLean.CState} {r : List (InLean.NestKey × Nat)},
      CSOKI mode eager env s₀ → cctx.params = TrSL s₀ ctx.params → OkSL s₀ ctx.params = true →
      OkSL s₀ holes = true → (∀ M ∈ Ms, OkTM s₀ M) →
      InLean.classSeeds ctx holes Ms s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ q ∈ r, OkSL s' q.1.ds = true) ∧
        ConLeche.classSeeds cctx (TrSL s₀ holes) (Ms.map (trTM s₀)) =
          r.map fun q => (trKey s' q.1, q.2)
  | [], s₀, s', r, hs, _, _, _, _, h => by
    unfold InLean.classSeeds at h
    rw [List.filterMapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by simp, rfl⟩
  | M :: Ms, s₀, s', r, hs, hpar, hokpar, hokh, hM, h => by
    unfold InLean.classSeeds at h
    rw [List.filterMapM_cons] at h
    obtain ⟨o, s₁, h1, h⟩ := bind_run h
    obtain ⟨hlv, hds, -, -⟩ := hM M List.mem_cons_self
    have hrest : ∀ {s₁ s'' : InLean.CState} {r' : List (InLean.NestKey × Nat)},
        CSOKI mode eager env s₁ →
        TabLe s₀ s₁ → InLean.classSeeds ctx holes Ms s₁ = .ok (r', s'') →
        CSOKI mode eager env s'' ∧ TabLe s₁ s'' ∧ (∀ q ∈ r', OkSL s'' q.1.ds = true) ∧
          ConLeche.classSeeds cctx (TrSL s₀ holes) (Ms.map (trTM s₀)) =
            r'.map fun q => (trKey s'' q.1, q.2) := by
      intro s₁ s'' r' hs₁ ht h'
      obtain ⟨a1, a2, a3, a4⟩ := classSeedsI_run hR hs₁ (by rw [TrSL_of_tabLe ht hokpar]; exact hpar)
        (okSL_of_tabLe ht hokpar) (okSL_of_tabLe ht hokh)
        (fun M' hM' => (OkTM.mono ht (hM M' (List.mem_cons_of_mem _ hM'))).1) h'
      refine ⟨a1, a2, a3, ?_⟩
      rw [← a4, TrSL_of_tabLe ht hokh]
      congr 1
      exact List.map_congr_left fun M' hM' =>
        ((OkTM.mono ht (hM M' (List.mem_cons_of_mem _ hM'))).2).symm
    unfold ConLeche.classSeeds
    rw [List.map_cons, List.filterMap_cons]
    cases hm : M.member with
    | some t =>
      simp only [hm, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h1
      obtain ⟨rfl, rfl⟩ := pure_run h1
      simp only at h
      obtain ⟨a1, a2, a3, a4⟩ := hrest hs (TabLe.refl _) h
      refine ⟨a1, a2, a3, ?_⟩
      simp only [trTM, hm, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      exact a4
    | none =>
      simp only [hm, Option.isNone_none, ↓reduceIte] at h1
      rw [map_eq_pure_bind] at h1
      obtain ⟨q, s₂, h2, h1⟩ := bind_run h1
      obtain ⟨rfl, rfl⟩ := pure_run h1
      obtain ⟨hs₂, ht₂, hokq, -, hseed⟩ := nestSeedOfI_run hR hs hpar hokpar hokh hds h2
      simp only at h
      obtain ⟨rest, s₃, h3, h⟩ := bind_run h
      obtain ⟨a1, a2, a3, a4⟩ := hrest hs₂ ht₂ (by unfold InLean.classSeeds; exact h3)
      obtain ⟨rfl, rfl⟩ := pure_run h
      refine ⟨a1, ht₂.trans a2, ?_, ?_⟩
      · intro q' hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact okSL_of_tabLe a2 hokq
        · exact a3 q' hq'
      · simp only [trTM, hm, Option.isNone_none, ↓reduceIte]
        rw [show ConLeche.nestSeedOf cctx (TrSL s₀ holes) (toName M.ind) (M.lvls.map trL)
          (TrSL s₀ M.ds) M.nPc = (trKey s₂ q.1, q.2) from hseed]
        unfold ConLeche.classSeeds at a4
        simp only [a4, List.map_cons, List.cons.injEq, Prod.mk.injEq, and_true]
        simp only [trKey, TrSL_of_tabLe a2 hokq]

end InLeanProof
