module

public import ConLeche.Model.Inductives.NestedRecTypes
public import ConLeche.Verify.Inductives.NestedRecWalk
import ConLeche.Model.Inductives.NestedTransfer
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Steps.CapsRows
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitErase
import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.EraseAnnots
import ConLeche.Verify.Level
public section

/-!
# The reading law of the restore WALK (task #315, M7-2, PLAN-M7 §1b)

`restoreWalk` replaces, top-down, every application headed by an
auxiliary type (`pins`) or an auxiliary constructor (`ctorPins`) by the
pin — the container at the block's parameters — lifted to the depth,
renames the auxiliary recursors (`recMap`), and leaves everything else
as it is.  **The readings agree**: at any model of the restored
environment and any model of the scratch one whose leaves agree off the
auxiliary names (`RestoreAgree`), the opened restored term and the
opened auxiliary term interpret alike at every frame at which the
restored reading is graded — not as the same `AnnotTerm` (the
auxiliary leaf is the copy's, the restored one the container's at the
components) but as the same set (`denoteMeta_restoreWalk`).  The
per-key agreements are the structure's fields: a pin's is
`nestedIdent_of` (`NestedCore.lean`), a constructor pin's its twin
(`nestedCtorIdent_of`), a recursor's a hypothesis (the rules' stage
supplies it).  The shape the walk relies on — every key-headed
application at the parameter variables — is `AuxAppsOk`
(`Verify/Inductives/NestedRecWalk.lean`, the model's face of the K.34
record); the induction is on it.

This is the SEMANTIC version of §U.21b's restore reading law, at every
term the walk visits — the recursor types (motives, minors, index
telescopes, majors) and the rules' λ-towers alike.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps fueledOps BinderMeta PropWhen
  RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Openers -/

/-- The standard openers of `n` binders from index `k₀`: the `i`-th is `fvar (k₀ + i)`. -/
@[expose] def OpenersFrom (fvs : List Expr) (k₀ n : Nat) : Prop :=
  fvs.length = n ∧ ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = Expr.fvar (k₀ + i) ty

omit [SetTheory V] in
theorem OpenersFrom.closed {fvs : List Expr} {k₀ n : Nat} (h : OpenersFrom fvs k₀ n) :
    ∀ a ∈ fvs, a.looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
  obtain ⟨ty, rfl⟩ := h.2 i a hi
  rfl

omit [SetTheory V] in
theorem OpenersFrom.snoc {fvs : List Expr} {k₀ n : Nat} (h : OpenersFrom fvs k₀ n) (ty : Expr) :
    OpenersFrom (fvs ++ [Expr.fvar (k₀ + n) ty]) k₀ (n + 1) := by
  refine ⟨by rw [List.length_append, List.length_singleton, h.1], ?_⟩
  intro i x hx
  rcases Nat.lt_or_ge i fvs.length with hi | hi
  · rw [List.getElem?_append_left hi] at hx
    exact h.2 i x hx
  · rw [List.getElem?_append_right hi] at hx
    have : i = fvs.length := by
      have hl := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_singleton] at hl
      omega
    subst this
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
    rw [← hx, h.1]
    exact ⟨ty, rfl⟩

omit [SetTheory V] in
theorem OpenersFrom.append {fvsP fvs : List Expr} {nP d : Nat} (hP : OpenersFrom fvsP 0 nP)
    (h : OpenersFrom fvs nP d) : OpenersFrom (fvsP ++ fvs) 0 (nP + d) := by
  refine ⟨by rw [List.length_append, hP.1, h.1], ?_⟩
  intro i x hx
  rcases Nat.lt_or_ge i fvsP.length with hi | hi
  · rw [List.getElem?_append_left hi] at hx
    exact hP.2 i x hx
  · rw [List.getElem?_append_right hi] at hx
    obtain ⟨ty, rfl⟩ := h.2 _ x hx
    have hl := hP.1
    exact ⟨ty, by congr 1; omega⟩

omit [SetTheory V] in
/-- A bound variable instantiated along closed openers is an opener or stays bound. -/
theorem instSeq_bvar_cases : ∀ (Vs : List Expr) (t i : Nat),
    (∀ a ∈ Vs, a.looseBVarsBounded 0 = true) →
    (∃ x ∈ Vs, Expr.instSeq Vs t (.bvar i) = x) ∨ ∃ j, Expr.instSeq Vs t (.bvar i) = .bvar j
  | [], _, i, _ => Or.inr ⟨i, rfl⟩
  | a :: Vs, t, i, hcl => by
    show (∃ x ∈ a :: Vs, Expr.instSeq Vs (t - 1) ((Expr.bvar i).instantiate1 a t) = x) ∨
      ∃ j, Expr.instSeq Vs (t - 1) ((Expr.bvar i).instantiate1 a t) = .bvar j
    by_cases hit : i = t
    · rw [show (Expr.bvar i).instantiate1 a t = a from by simp [Expr.instantiate1, hit],
        Expr.instSeq_eq_self _ _ (hcl a List.mem_cons_self)]
      exact Or.inl ⟨a, List.mem_cons_self, rfl⟩
    · have hb : (Expr.bvar i).instantiate1 a t = .bvar (if i > t then i - 1 else i) := by
        simp only [Expr.instantiate1, hit, if_false]
        split <;> rfl
      rw [hb]
      rcases instSeq_bvar_cases Vs (t - 1) (if i > t then i - 1 else i)
          (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) with ⟨x, hx, hxe⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨x, List.mem_cons_of_mem _ hx, hxe⟩
      · exact Or.inr ⟨j, hj⟩

omit [SetTheory V] in
/-- A free variable keeps its index along an instantiation sequence. -/
theorem instSeq_fvar_idx : ∀ (Vs : List Expr) (t i : Nat) (ty : Expr),
    Expr.instSeq Vs t (.fvar i ty) = .fvar i ty
  | [], _, _, _ => rfl
  | a :: Vs, t, i, ty => by
    show Expr.instSeq Vs (t - 1) ((Expr.fvar i ty).instantiate1 a t) = _
    rw [Expr.instantiate1_fvar]
    exact instSeq_fvar_idx Vs (t - 1) i ty

/-! ## The leaf agreements -/

/-- **The leaf agreements the walk's reading law consumes**, at two carriers
`acvalA`/`envA` (the scratch install's) and `acvalR`/`envR` (the restored
environment's), a level assignment `φ`, the block's parameter count and its
parameter telescope reading `params` (at `φ`):

* off the auxiliary names the two environments answer alike (a found name
  is found with the same level parameters, an absent one is absent) and the
  leaves agree; the auxiliary names are absent from `envR`;
* a `recMap` key's leaf is its restored name's, with the same level parameters;
* a `pins` key `n` (levels `lps`, the copy's index count `arityOf n`): its
  abstracted pin is bounded at `nP`, re-opened at the parameters it reads at
  any depth `nP + d` as the container `J` at the components lifted by `d`,
  and — THE PIN IDENTITY (`nestedIdent_of`) — that application at any index
  readings `Es` interprets, wherever it is graded at a frame whose parameter
  slots fit `params`, like the copy at the parameter variables and `Es`;
* a `ctorPins` key likewise, with the constructor's field count as arity, the
  restored head `newName` at the lifted components, and the constructor
  identity (`nestedCtorIdent_of`). -/
structure RestoreAgree (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (acvalA acvalR : Name → (Name → Nat) → AnnotTerm) (envA envR : Env) (φ : Name → Nat)
    (nP : Nat) (params : List AnnotTerm) : Prop where
  nPEq : R.nP = nP
  leafSome : ∀ n, n ∉ R.auxNames → ∀ ci : ConstantInfo, envA.find? n = some ci →
    ∃ ci' : ConstantInfo, envR.find? n = some ci' ∧
      ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams
  leafNone : ∀ n, n ∉ R.auxNames → envA.find? n = none → envR.find? n = none
  leaf : ∀ n, n ∉ R.auxNames → acvalA n = acvalR n
  auxFresh : ∀ n ∈ R.auxNames, envR.find? n = none
  recKey : ∀ n n', R.recMap.lookup n = some n' → ∀ ci : ConstantInfo, envA.find? n = some ci →
    ∃ ci' : ConstantInfo, envR.find? n' = some ci' ∧
      ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams ∧ acvalA n = acvalR n'
  recNone : ∀ n n', R.recMap.lookup n = some n' → envA.find? n = none → envR.find? n' = none
  pin : ∀ n pin, R.pins.lookup n = some pin →
    pin.looseBVarsBounded nP = true ∧
    ∃ (ci : ConstantInfo) (J : Name) (ψJ : Name → Nat) (Ds : List AnnotTerm) (nIdx : Nat),
      envA.find? n = some ci ∧ ci.toConstantVal.levelParams = lps ∧ arityOf n = some nIdx ∧
      (∀ (fvsP : List Expr) (d : Nat), OpenersFrom fvsP 0 nP →
        denoteMeta acvalR envR φ (nP + d) (Expr.instSeq fvsP (nP - 1) pin)
          = some (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0)))) ∧
      ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Es : List AnnotTerm),
        SpineFit ρ₀ params as → xs.length = d → Es.length = nIdx →
        WellDenoted V (consList xs (consList as ρ₀))
          (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0) ++ Es)) →
        interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalR J ψJ) (Ds.map (·.liftN d 0) ++ Es))
          = interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalA n φ) (paramBvarsAt nP (nP + d) ++ Es))
  ctor : ∀ n pin newName, R.ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName) →
    pin.looseBVarsBounded nP = true ∧ R.pins.lookup n = none ∧
    ∃ (ci : ConstantInfo) (J : Name) (ilvls : List Level) (ψJ : Name → Nat) (Ds : List AnnotTerm)
      (nF : Nat),
      envA.find? n = some ci ∧ ci.toConstantVal.levelParams = lps ∧ arityOf n = some nF ∧
      (∀ d, (pin.liftLooseBVars d 0).getAppFn = .const J ilvls) ∧
      (∀ (fvsP fvs : List Expr) (d : Nat), OpenersFrom fvsP 0 nP → OpenersFrom fvs nP d →
        denoteMeta acvalR envR φ (nP + d) (Expr.instSeq (fvsP ++ fvs) (nP + d - 1)
            (Expr.mkAppN (.const newName ilvls) (pin.liftLooseBVars d 0).getAppArgs))
          = some (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0)))) ∧
      ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Fs : List AnnotTerm),
        SpineFit ρ₀ params as → xs.length = d → Fs.length = nF →
        WellDenoted V (consList xs (consList as ρ₀))
          (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0) ++ Fs)) →
        interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalR newName ψJ) (Ds.map (·.liftN d 0) ++ Fs))
          = interp V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (acvalA n φ) (paramBvarsAt nP (nP + d) ++ Fs))

/-! ## The auxiliary-free congruence -/

section Congr

variable {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat}
  {acvalA acvalR : Name → (Name → Nat) → AnnotTerm} {envA envR : Env} {φ : Name → Nat}
  {nP : Nat} {params : List AnnotTerm}
  (hk : R.KeysInAux)
  (hag : RestoreAgree (V := V) R lps arityOf acvalA acvalR envA envR φ nP params)
include hk hag

/-- **An auxiliary-free term reads alike at the two carriers**, opened at any
closed variables `Vs` (as many as the depth `D`): the auxiliary names never
occur, so every constant is one the two environments answer alike with
agreeing leaves, and the shape `AuxAppsOk` rules out literals, projections
and lets. -/
theorem denoteMeta_congr_auxFree :
    ∀ {d : Nat} {e : Expr}, AuxAppsOk R lps arityOf d e →
      (∀ m ∈ R.auxNames, e.mentionsConst m = false) →
      ∀ (Vs : List Expr) (D : Nat), Vs.length = D → (∀ a ∈ Vs, ∃ i ty, a = Expr.fvar i ty) →
        denoteMeta acvalA envA φ D (Expr.instSeq Vs (D - 1) e)
          = denoteMeta acvalR envR φ D (Expr.instSeq Vs (D - 1) e) := by
  intro d e h
  induction h with
  | @key _ n args _ hkey _ _ _ _ _ =>
    intro hfree
    exfalso
    have hn : n ∈ R.auxNames := by
      rcases hkey with hp | hc
      · obtain ⟨pin, hpin⟩ := Option.isSome_iff_exists.mp hp
        exact hk.1 n pin hpin
      · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hc
        exact hk.2.1 n q hq
    have := hfree n hn
    rw [Expr.mentionsConst_mkAppN_head args _ (by simp [Expr.mentionsConst])] at this
    exact Bool.noConfusion this
  | @app _ _ _ _ _ _ ihf iha =>
    intro hfree Vs D hV hcl
    have hfa := fun m hm => Expr.mentionsConst_app_false (hfree m hm)
    rw [Expr.instSeq_app, denoteMeta_app, denoteMeta_app,
      ihf (fun m hm => (hfa m hm).1) Vs D hV hcl, iha (fun m hm => (hfa m hm).2) Vs D hV hcl]
  | @lam _ ty b bm _ _ ihty ihb =>
    intro hfree Vs D hV hcl
    have hfb := fun m hm => Expr.mentionsConst_lam_false (hfree m hm)
    rw [ConLeche.instSeq_lam Vs (D - 1) ty b bm (by omega), denoteMeta_lam, denoteMeta_lam,
      ihty (fun m hm => (hfb m hm).1) Vs D hV hcl]
    cases hty' : denoteMeta acvalR envR φ D (Expr.instSeq Vs (D - 1) ty) with
    | none => rfl
    | some ta =>
      simp only [bind, Option.bind]
      have hopen : (Expr.instSeq Vs (D - 1 + 1) b).instantiate1 (.fvar D (Expr.instSeq Vs (D - 1) ty)) 0
          = Expr.instSeq (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1 - 1) b := by
        rw [Nat.add_sub_cancel, ConLeche.instSeq_snoc_at hV]
        rcases Nat.eq_zero_or_pos D with h0 | hpos
        · subst h0
          obtain rfl : Vs = [] := List.eq_nil_of_length_eq_zero hV
          rfl
        · rw [show D - 1 + 1 = D from by omega]
      rw [hopen, ihb (fun m hm => (hfb m hm).2) _ (D + 1)
        (by rw [List.length_append, List.length_singleton, hV])
        (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact hcl a h
          · rw [List.mem_singleton] at h; exact ⟨_, _, h⟩)]
  | @forallE _ ty b bm _ _ ihty ihb =>
    intro hfree Vs D hV hcl
    have hfb := fun m hm => Expr.mentionsConst_forallE_false (hfree m hm)
    rw [Expr.instSeq_forallE Vs (D - 1) ty b bm (by omega), denoteMeta_forallE, denoteMeta_forallE,
      ihty (fun m hm => (hfb m hm).1) Vs D hV hcl]
    cases hty' : denoteMeta acvalR envR φ D (Expr.instSeq Vs (D - 1) ty) with
    | none => rfl
    | some ta =>
      simp only [bind, Option.bind]
      have hopen : (Expr.instSeq Vs (D - 1 + 1) b).instantiate1 (.fvar D (Expr.instSeq Vs (D - 1) ty)) 0
          = Expr.instSeq (Vs ++ [Expr.fvar D (Expr.instSeq Vs (D - 1) ty)]) (D + 1 - 1) b := by
        rw [Nat.add_sub_cancel, ConLeche.instSeq_snoc_at hV]
        rcases Nat.eq_zero_or_pos D with h0 | hpos
        · subst h0
          obtain rfl : Vs = [] := List.eq_nil_of_length_eq_zero hV
          rfl
        · rw [show D - 1 + 1 = D from by omega]
      rw [hopen, ihb (fun m hm => (hfb m hm).2) _ (D + 1)
        (by rw [List.length_append, List.length_singleton, hV])
        (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact hcl a h
          · rw [List.mem_singleton] at h; exact ⟨_, _, h⟩)]
  | @const _ n us _ _ =>
    intro hfree Vs D _ _
    have hnaux : n ∉ R.auxNames := by
      intro hn
      have := hfree n hn
      simp [Expr.mentionsConst] at this
    rw [Expr.instSeq_eq_self _ _ (e := Expr.const n us) rfl]
    cases hfA : envA.find? n with
    | none =>
      rw [denoteMeta, denoteMeta, hfA, hag.leafNone n hnaux hfA]
    | some ci =>
      obtain ⟨ci', hfR, hlps⟩ := hag.leafSome n hnaux ci hfA
      rw [denoteMeta, denoteMeta, hfA, hfR]
      show (if us.length = ci.toConstantVal.levelParams.length then
          some (acvalA n (Level.substFn φ ci.toConstantVal.levelParams us)) else none)
        = (if us.length = ci'.toConstantVal.levelParams.length then
          some (acvalR n (Level.substFn φ ci'.toConstantVal.levelParams us)) else none)
      rw [hlps, hag.leaf n hnaux]
  | @bvar _ i =>
    intro _ Vs D _ hfv
    have hcl : ∀ a ∈ Vs, a.looseBVarsBounded 0 = true := fun a ha => by
      obtain ⟨i, ty, rfl⟩ := hfv a ha
      rfl
    rcases instSeq_bvar_cases Vs (D - 1) i hcl with ⟨x, hx, hxe⟩ | ⟨j, hj⟩
    · obtain ⟨i', ty, rfl⟩ := hfv x hx
      rw [hxe, denoteMeta_fvar, denoteMeta_fvar]
    · rw [hj, denoteMeta_bvar, denoteMeta_bvar]
  | @sort _ u =>
    intro _ Vs D _ _
    rw [Expr.instSeq_eq_self _ _ (e := Expr.sort u) rfl, denoteMeta_sort, denoteMeta_sort]
  | @fvar _ i ty =>
    intro _ Vs D _ _
    rw [instSeq_fvar_idx, denoteMeta_fvar, denoteMeta_fvar]

end Congr

end ConLeche.Model
