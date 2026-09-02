import Setlec.SetR.Interp2.IndMembersP
import Setlec.SetR.Interp2.Step2.CapsRowsP

/-!
# The reading's ∀-telescope (task #161, IND TIER part 2)

The capability keys read a *stored theorem's* type — a syntactic
∀-telescope whose binders `checkEtaThm`/`checkUnitThm` pinned — and
fire it at a spine.  v1 does this with `stripPis_denoteTele`
(`Verify/Denote/IndFrame.lean`), whose output is a `PiTele` plus the
opened domain and body readings; this file is that lemma's transpose,
and the transposition is **near-verbatim** for one reason recorded in
part 1's `BitRename.lean`:

> `denoteP`'s binder clauses instantiate with the binder's *own* name
> and type, exactly as `denote`'s do, and `denoteP_erasedEq` is blind
> to both — so the re-opening at the anonymous opener (`openFvars`)
> that v1's induction performs transposes move for move.

The one shape delta: `denoteP` reads a `∀` to `.pi 0 (pwBit φ mb.pw)`,
so the reading's telescope carries *bits*, and `PiTeleP`'s `cons`
quantifies them existentially.  Nothing downstream reads them — the
consumers are `TeleFitP` (which quantifies its own) and
`annotOkP_mkAppN_of_fit` (which takes them from the grading).

Also here: the two consumers the keys need and the campaign did not
yet own —

* `memFoldl_of_teleFitP`, the *value-level* twin of
  `annotOkP_mkAppN_of_fit`.  The caps laws quantify their spines as
  bare `V`s (the divmod-leg lesson, frozen), so the applied-membership
  walk cannot go through the `AVExpr` form; it is the same induction
  with the grading conjuncts deleted, and it needs the type's grading
  only for `app_mem_piR`'s `v = 0` fibre premise.
* `teleFitP_of_piTeleP`, which rebuilds a fit at a *second* telescope
  from the memberships of a fit at the first.  The keys need it
  because the fit they are *given* is at the family former's type and
  the fit they must *fire* is at the checked statement's, and the two
  agree only through the pins' domain equalities.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The reading's telescope -/

/-- **`PiTele`'s transpose at the reading.**  The bits are existential
(see the module docstring): a `∀` reads to `.pi 0 (pwBit φ mb.pw)` and
no consumer of this file reads either component. -/
inductive PiTeleP : Nat → AVExpr → List AVExpr → AVExpr → Prop
  | nil {T : AVExpr} : PiTeleP 0 T [] T
  | cons {k u v : Nat} {A B R : AVExpr} {Γ : List AVExpr} :
      PiTeleP k B Γ R → PiTeleP (k + 1) (.pi u v A B) (Γ ++ [A]) R

theorem PiTeleP.length : ∀ {k : Nat} {T : AVExpr} {Γ : List AVExpr}
    {R : AVExpr}, PiTeleP k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A telescope of positive length exposes its head `.pi`. -/
theorem PiTeleP.succ_inv {k : Nat} {T : AVExpr} {Γ : List AVExpr}
    {R : AVExpr} (h : PiTeleP (k + 1) T Γ R) :
    ∃ (u v : Nat) (A B : AVExpr) (Γ' : List AVExpr),
      T = .pi u v A B ∧ Γ = Γ' ++ [A] ∧ PiTeleP k B Γ' R := by
  cases h with
  | cons h' => exact ⟨_, _, _, _, _, rfl, rfl, h'⟩

/-! ## The strip, read

`stripPis_denoteTele`'s transpose, move for move. -/

theorem stripPis_denotePTele :
    ∀ (k : Nat) {e : Expr} {j : Nat}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr}
      {E : AVExpr},
      e.stripPis k = some (bs, body) →
      denoteP acval env φ j e = some E →
      ∃ (Γ : List AVExpr) (C : AVExpr),
        PiTeleP k E Γ C ∧ Γ.length = k ∧
        denoteP acval env φ (j + k)
          (Expr.instSeq (openFvars j k) (k - 1) body) = some C ∧
        ∀ (i0 : Nat) (b : Name × Expr × BinderMeta), bs[i0]? = some b →
          denoteP acval env φ (j + i0)
            (Expr.instSeq (openFvars j i0) (i0 - 1) b.2.1) =
            some (Γ.getD (k - 1 - i0) default) := by
  intro k
  induction k with
  | zero =>
    intro e j bs body E h hE
    simp only [Setlec.Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], E, .nil, rfl, hE, fun i0 b hb => nomatch hb⟩
  | succ k ih =>
    intro e j bs body E h hE
    match e, h with
    | .forallE nm dom bodyE mb, h =>
      simp only [Setlec.Expr.stripPis] at h
      cases hs : bodyE.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p => ?_
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denoteP_forallE] at hE
      cases hA : denoteP acval env φ j dom with
      | none => rw [hA] at hE; exact nomatch hE
      | some A => ?_
      rw [hA] at hE
      cases hB : denoteP acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j nm dom)) with
      | none => rw [hB] at hE; exact nomatch hE
      | some Bv => ?_
      rw [hB] at hE
      obtain rfl : E = .pi 0 (pwBit φ mb.pw) A Bv := by
        simpa using hE.symm
      -- re-open at the anonymous opener (the reading is blind to it)
      have hB' : denoteP acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j Name.anonymous (.sort .zero)))
          = some Bv := by
        rw [denoteP_erasedEq (Setlec.Expr.ErasedEq.instantiate1
          (Setlec.Expr.ErasedEq.rfl bodyE)
          (show Setlec.Expr.ErasedEq
              (.fvar j Name.anonymous (.sort .zero)) (.fvar j nm dom)
            from by constructor)) (j + 1)]
        exact hB
      have hsI : ((bodyE.instantiate1 (.fvar j Name.anonymous
          (.sort .zero))).stripPis k).isSome :=
        Setlec.Expr.stripPis_instantiate1_isSome k 0 (by rw [hs]; rfl)
      obtain ⟨bs', body', hsI2⟩ : ∃ bs' body',
          (bodyE.instantiate1 (.fvar j Name.anonymous
            (.sort .zero))).stripPis k = some (bs', body') := by
        cases hq : (bodyE.instantiate1 (.fvar j Name.anonymous
            (.sort .zero))).stripPis k with
        | none => rw [hq] at hsI; exact nomatch hsI
        | some q => exact ⟨q.1, q.2, rfl⟩
      obtain ⟨hbody', hdoms'⟩ :=
        Setlec.Expr.stripPis_instantiate1_eq k 0 hs hsI2
      obtain ⟨Γ', C, htele, hΓlen, hbody, hdoms⟩ := ih hsI2 hB'
      have hbslen : p.1.length = k := Setlec.Expr.stripPis_length k hs
      have hbslen' : bs'.length = k :=
        Setlec.Expr.stripPis_length k hsI2
      refine ⟨Γ' ++ [A], C, .cons htele, by simp [hΓlen], ?_, ?_⟩
      · show denoteP acval env φ (j + (k + 1))
          (Expr.instSeq (openFvars j (k + 1)) (k + 1 - 1) p.2)
          = some C
        rw [show openFvars j (k + 1) = .fvar j Name.anonymous
            (.sort .zero) :: openFvars (j + 1) k from rfl,
          show Expr.instSeq (.fvar j Name.anonymous (.sort .zero)
              :: openFvars (j + 1) k) (k + 1 - 1) p.2 =
            Expr.instSeq (openFvars (j + 1) k) (k - 1)
              (p.2.instantiate1 (.fvar j Name.anonymous (.sort .zero))
                k) from by simp [Expr.instSeq],
          show j + (k + 1) = j + 1 + k from by omega,
          show p.2.instantiate1 (.fvar j Name.anonymous (.sort .zero))
              k = body' from by
            rw [hbody']; simp only [Nat.zero_add]]
        exact hbody
      · intro i0 b hb
        cases i0 with
        | zero =>
          obtain rfl : (nm, dom, mb) = b := by simpa using hb
          show denoteP acval env φ (j + 0)
            (Expr.instSeq (openFvars j 0) (0 - 1) dom) = _
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
            simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
            rw [List.getElem?_append_right (by omega), hΓlen,
              Nat.sub_self]
            rfl]
          exact hA
        | succ i0 =>
          rw [List.getElem?_cons_succ] at hb
          have hik : i0 < k := by
            rcases Nat.lt_or_ge i0 k with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none (by omega)] at hb
              exact nomatch hb
          have hb' : bs'[i0]? = some (bs'[i0]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          have hdomEq := hdoms' i0 b (bs'[i0]'(by omega)) hb hb'
          have h1 := hdoms i0 _ hb'
          rw [hdomEq] at h1
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i0 + 1)) default =
              Γ'.getD (k - 1 - i0) default from by
            simp only [List.getD]
            rw [show k + 1 - 1 - (i0 + 1) = k - 1 - i0 from by omega,
              List.getElem?_append_left (by omega)]]
          show denoteP acval env φ (j + (i0 + 1))
            (Expr.instSeq (openFvars j (i0 + 1)) (i0 + 1 - 1) b.2.1)
            = _
          rw [show openFvars j (i0 + 1) = .fvar j Name.anonymous
              (.sort .zero) :: openFvars (j + 1) i0 from rfl,
            show Expr.instSeq (.fvar j Name.anonymous (.sort .zero)
                :: openFvars (j + 1) i0) (i0 + 1 - 1) b.2.1 =
              Expr.instSeq (openFvars (j + 1) i0) (i0 - 1)
                (b.2.1.instantiate1 (.fvar j Name.anonymous
                  (.sort .zero)) i0) from by
              simp [Expr.instSeq],
            show j + (i0 + 1) = j + 1 + i0 from by omega]
          rw [show (0 : Nat) + i0 = i0 from by omega] at h1
          exact h1

/-! ## From a fit to an applied membership, at bare values

`annotOkP_mkAppN_of_fit`'s value-level twin: the caps laws' spines are
bare `V`s (frozen), so the applied-membership walk cannot be routed
through the `AVExpr` form.  Same induction, grading conjuncts deleted;
the type's grading survives only as `app_mem_piR`'s `v = 0` fibre
premise. -/

theorem memFoldl_of_teleFitP :
    ∀ (ts : List V) {ρ : Nat → V} {Ta : AVExpr} {f rest : V},
      AnnotOkP V ρ Ta →
      f ∈ˢ interp2 V ρ Ta →
      TeleFitP V ρ Ta ts rest →
      ts.foldl SetTheory.app f ∈ˢ rest := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta f rest _ hmem hfit
    obtain rfl : rest = interp2 V ρ Ta := teleFitP_nil_inv hfit
    exact hmem
  | cons t tsr ih =>
    intro ρ Ta f rest hokT hmem hfit
    cases hfit with
    | @cons _ u v A B _ _ _ ht hfit' =>
      have hokB : ∀ y, y ∈ˢ interp2 V ρ A → AnnotOkP V (cons y ρ) B :=
        fun y hy =>
          ⟨((AnnotOk2_pi V ρ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValidV_pi V ρ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp2 V ρ A →
          interp2 V (cons y ρ) B ∈ˢ (univZero : V) :=
        ((AnnotValidV_pi V ρ u v A B) ▸ hokT.2).2.2
      rw [interp2_pi] at hmem
      exact ih (hokB _ ht) (app_mem_piR hmem ht hfib) hfit'

/-! ## Fitting a *second* telescope from the first's memberships

The keys' central move.  The fit they are **given** is at the family
former's type; the fit they must **fire** is at the checked statement's
type, and the two coincide only through the pins' domain equalities
(`checkEtaThm`/`checkUnitThm`'s `hsdoms` conjunct, which is a
*syntactic* equality of the binder domains and therefore an equality of
their readings).  `teleFitP_congr` moves the fit across; `consN` names
the environment the fit ends in, so the residual of the second
telescope can be spoken about at all. -/

/-- The environment a fit ends in: the arguments consed in order. -/
def consN : List V → (Nat → V) → (Nat → V)
  | [], ρ => ρ
  | t :: ts, ρ => consN ts (cons t ρ)

omit [SetTheory V] in
@[simp] theorem consN_nil (ρ : Nat → V) : consN [] ρ = ρ := rfl

omit [SetTheory V] in
@[simp] theorem consN_cons (t : V) (ts : List V) (ρ : Nat → V) :
    consN (t :: ts) ρ = consN ts (cons t ρ) := rfl

/-- A fit's residual is its telescope's body, read at `consN`. -/
theorem teleFitP_residual :
    ∀ (ts : List V) {ρ : Nat → V} {Ta : AVExpr} {Γ : List AVExpr}
      {R : AVExpr} {rest : V},
      PiTeleP ts.length Ta Γ R → TeleFitP V ρ Ta ts rest →
      rest = interp2 V (consN ts ρ) R := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Γ R rest hT hfit
    cases hT
    exact teleFitP_nil_inv hfit
  | cons t tsr ih =>
    intro ρ Ta Γ R rest hT hfit
    obtain ⟨u, v, A, B, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ _ hfit' => exact ih hT' hfit'

/-- **The fit, moved across two telescopes with equal domains.** -/
theorem teleFitP_congr :
    ∀ (ts : List V) {ρ : Nat → V} {Ta Sa : AVExpr}
      {Γ Δ : List AVExpr} {R C : AVExpr} {rest : V},
      PiTeleP ts.length Ta Γ R →
      PiTeleP ts.length Sa Δ C →
      (∀ i, i < ts.length → Γ.getD i default = Δ.getD i default) →
      TeleFitP V ρ Ta ts rest →
      TeleFitP V ρ Sa ts (interp2 V (consN ts ρ) C) := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Sa Γ Δ R C rest _ hS _ _
    cases hS
    exact TeleFitP.nil
  | cons t tsr ih =>
    intro ρ Ta Sa Γ Δ R C rest hT hS hdoms hfit
    obtain ⟨u₁, v₁, A₁, B₁, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    obtain ⟨u₂, v₂, A₂, B₂, Δ', rfl, hΔ, hS'⟩ := hS.succ_inv
    have hΓl : Γ'.length = tsr.length := hT'.length
    have hΔl : Δ'.length = tsr.length := hS'.length
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ ht hfit' =>
      refine TeleFitP.cons ?_ (ih hT' hS' ?_ hfit')
      · -- the head domains sit last in both lists
        have h := hdoms tsr.length (by simp)
        rw [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega), hΓl, hΔl,
          Nat.sub_self] at h
        simp only [List.getElem?_cons_zero, Option.getD_some] at h
        rw [← h]
        exact ht
      · intro i hi
        have h := hdoms i (by simp only [List.length_cons]; omega)
        rwa [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_left (by omega),
          List.getElem?_append_left (by omega)] at h

end Setlec.SetR.Interp2
