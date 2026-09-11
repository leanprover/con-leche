module

public import ConLeche.Model.Inductives.FixData
public import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# A mutual block's constructor data (task #278, M2.4)

The mutual analogue of `FixData.lean`: a constructor of a mutual
block `T_1 … T_k`, read at the environment holding ALL `k` formers.

`MutualCtorDataI` is `FixCtorDataI` with a per-field TARGET MEMBER.
The block's members are `members : List (Name × Nat × Nat)` — name,
index, index count, as `MutualBlock.members3` spells them — and the
kinds are `List (RecFieldKind × Nat)`, each carrying the member the
field targets (`mutualCtorKinds`).  A recursive field's domain is the
TARGET member's former at the parameter variables and that member's
index expressions, so its entry is `mkAppN (m.acval T_{m''} ψ)
(params ++ Eis)`; a reflexive field's is the Π-tower of that over its
own telescope.  The constructor's own residual is its OWN member's
former at the parameters and its index expressions, which is exactly
`CtorDataI` at that member — so `MutualCtorDataI` extends it.

The readings are obtained from the constructor stage's run
(`checkMutualCtor`, `mutualCtorData_of`) the way `fixCtorData_of`
obtains `FixCtorDataI` from `checkSumCtor`'s: the run's shape
(`checkMutualCtor_shape`) is the same tuple `checkSumCtor_shape`
returns, so the sum route's reading argument is repeated here once,
shape-first (`ctorDataI_ofShape`), and everything target-agnostic is
reused from `FixData.lean`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The members, looked up by index -/

/-- Member `m'`'s name, as `mutualOpenedOk` reads it. -/
@[expose] def mutualNameOf (members : List (Name × Nat × Nat)) (m' : Nat) : Name :=
  ((members.find? (·.2.1 == m')).map (·.1)).getD .anonymous

/-- Member `m'`'s index count, as `mutualOpenedOk` reads it. -/
@[expose] def mutualNIdxOf (members : List (Name × Nat × Nat)) (m' : Nat) : Nat :=
  ((members.find? (·.2.1 == m')).map (·.2.2)).getD 0

/-- The kind of field `i`. -/
@[expose] def kindAt (ks : List (RecFieldKind × Nat)) (i : Nat) : RecFieldKind :=
  (ks.getD i (.ordinary, 0)).1

/-- The member field `i` targets. -/
@[expose] def tgtAt (ks : List (RecFieldKind × Nat)) (i : Nat) : Nat :=
  (ks.getD i (.ordinary, 0)).2

/-- The kinds without their targets. -/
@[expose] def kindsOf (ks : List (RecFieldKind × Nat)) : List RecFieldKind := ks.map (·.1)

omit [SetTheory V] in
/-- The kind entry at `i`, split into its kind and its target. -/
theorem getD_kind_eq {ks : List (RecFieldKind × Nat)} {i : Nat} {k : RecFieldKind}
    (hk : kindAt ks i = k) : ks.getD i (.ordinary, 0) = (k, tgtAt ks i) := by
  rw [← hk]; rfl

omit [SetTheory V] in
theorem kindsOf_length {ks : List (RecFieldKind × Nat)} : (kindsOf ks).length = ks.length := by
  simp [kindsOf]

omit [SetTheory V] in
theorem kindsOf_getD {ks : List (RecFieldKind × Nat)} {i : Nat} (hi : i < ks.length) :
    (kindsOf ks).getD i .ordinary = kindAt ks i := by
  simp only [kindsOf, kindAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-! ## The opened-form guard, positionally -/

/-- `mutualOpenedOk`, read positionally (`FixOpened` with a target
member at every recursive and reflexive field). -/
structure MutualOpened (env₀ : Env) (members : List (Name × Nat × Nat)) (lps : List Name)
    (nP nF : Nat) (ks : List (RecFieldKind × Nat)) (fvsP xFvs : List Expr) (xrest : Expr) :
    Prop where
  residRes : ∀ e ∈ xrest.getAppArgs.drop nP, e.constsResolve env₀ = true
  ord : ∀ i x, xFvs[i]? = some x → kindAt ks i = .ordinary →
    x.fvarTypeD.constsResolve env₀ = true
  recF : ∀ i x, xFvs[i]? = some x → kindAt ks i = .recursive →
    x.fvarTypeD.getAppFn
        = Expr.const (mutualNameOf members (tgtAt ks i)) (lps.map .param) ∧
    x.fvarTypeD.getAppArgs.take nP = fvsP ∧
    x.fvarTypeD.getAppArgs.length = nP + mutualNIdxOf members (tgtAt ks i) ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  reflF : ∀ i x, xFvs[i]? = some x → kindAt ks i = .reflexive →
    ∃ afvs body,
      openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      afvs.length ≠ 0 ∧
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true) ∧
      body.getAppFn = Expr.const (mutualNameOf members (tgtAt ks i)) (lps.map .param) ∧
      body.getAppArgs.take nP = fvsP ∧
      body.getAppArgs.length = nP + mutualNIdxOf members (tgtAt ks i) ∧
      (∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false
  kinds : ∀ i, i < nF → kindAt ks i = .ordinary ∨ kindAt ks i = .recursive ∨
    kindAt ks i = .reflexive

theorem mutualOpened_of {env₀ : Env} {members : List (Name × Nat × Nat)} {lps : List Name}
    {nP : Nat} {cty : Expr} {nF : Nat} {ks : List (RecFieldKind × Nat)}
    (h : ConLeche.mutualOpenedOk env₀ members lps nP cty nF ks = true) :
    ∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
      openPisAtFvars nP cty 0 = some (fvsP, crest) ∧
      openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
      MutualOpened env₀ members lps nP nF ks fvsP xFvs xrest := by
  unfold ConLeche.mutualOpenedOk at h
  split at h
  · next fvsP crest hop =>
    split at h
    · next xFvs xrest hox =>
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      obtain ⟨hres, hall⟩ := h
      have hlenX : xFvs.length = nF := openPisAtFvars_length _ hox
      refine ⟨fvsP, crest, xFvs, xrest, hop, hox, ⟨hres, ?_, ?_, ?_, ?_⟩⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have hthis := hall i hi
        rw [hx] at hthis
        rw [getD_kind_eq hk] at hthis
        exact hthis
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have hthis := hall i hi
        rw [hx] at hthis
        rw [getD_kind_eq hk] at hthis
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, List.any_eq_false] at hthis
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hthis
        exact ⟨h1, h2, h3, h4, fun y hy => by simpa using h5 y hy, h6⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have hthis := hall i hi
        rw [hx] at hthis
        rw [getD_kind_eq hk] at hthis
        dsimp only at hthis
        cases hopA : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
        | none => rw [hopA] at hthis; exact nomatch hthis
        | some q =>
          obtain ⟨afvs, body⟩ := q
          rw [hopA] at hthis
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, List.any_eq_false, bne_iff_ne, ne_eq] at hthis
          obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hthis
          exact ⟨afvs, body, rfl, h1, h2, h3, h4, h5, h6, fun y hy => by simpa using h7 y hy, h8⟩
      · intro i hi
        have hthis := hall i hi
        cases hx : xFvs[i]? with
        | none => rw [hx] at hthis; exact nomatch hthis
        | some x =>
          rw [hx] at hthis
          cases hk : kindAt ks i with
          | ordinary => exact Or.inl rfl
          | recursive => exact Or.inr (Or.inl rfl)
          | reflexive => exact Or.inr (Or.inr rfl)
          | negative =>
            rw [getD_kind_eq hk] at hthis
            exact nomatch hthis
          | unsupported =>
            rw [getD_kind_eq hk] at hthis
            exact nomatch hthis
    · exact nomatch h
  · exact nomatch h

/-! ## The constructor's data -/

/-- **A mutual constructor's data** at the environment holding all `k`
formers: the sum route's data at the constructor's OWN member
(`CtorDataI` at `T`, `nIdx`), together with the opened-form guard
(`MutualOpened`) and the readings it yields — a recursive field's
entry is its TARGET member's leaf at the parameter variables and that
member's index readings, a reflexive field's the Π-tower of that over
its own telescope (`FixCtorDataI` with the target). -/
structure MutualCtorDataI {env : Env} (m : EnvModel V env) (env₀ : Env)
    (members : List (Name × Nat × Nat)) (T : Name) (lps : List Name) (cvC : ConstantVal)
    (nP nF nIdx : Nat) (resSort : Level) (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (ks : List (RecFieldKind × Nat)) (fvsP xFvs : List Expr)
    (xrest : Expr) (Eiss : (Name → Nat) → List (List AnnotTerm))
    (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opened : MutualOpened env₀ members lps nP nF ks fvsP xFvs xrest
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  ksLen : ks.length = nF
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  eissLen : ∀ ψ, (Eiss ψ).length = nF
  eisRead : ∀ ψ i x, xFvs[i]? = some x → kindAt ks i = .recursive →
    DenoteMetaSpine m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLen : ∀ ψ i, kindAt ks i = .recursive → i < nF →
    ((Eiss ψ).getD i []).length = mutualNIdxOf members (tgtAt ks i)
  /-- a recursive field's entry: the TARGET member's leaf at the
  parameter variables and the field's index readings -/
  recEntry : ∀ ψ i, kindAt ks i = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AnnotTerm.mkAppN (m.acval (mutualNameOf members (tgtAt ks i)) ψ)
          (paramBvarsAt nP (nP + i) ++ (Eiss ψ).getD i [])
  eissParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → Eiss ψ₁ = Eiss ψ₂
  eissBelow : ∀ ψ i, ∀ E ∈ (Eiss ψ).getD i [],
    Term.bvarsBelow (nP + i + ((tss ψ).getD i []).length) E.erase
  ordNone : ∀ ψ i, kindAt ks i ≠ .recursive → kindAt ks i ≠ .reflexive →
    (Eiss ψ).getD i [] = []
  tssLen : ∀ ψ, (tss ψ).length = nF
  tssNone : ∀ ψ i, kindAt ks i ≠ .reflexive → (tss ψ).getD i [] = []
  tssBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], (d.2.1 = 0 ↔ resSort.eval ψ = 0)
  tssPiBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], d.1 = 0 ∧ d.2.1 ≤ 1
  tssBelow : ∀ ψ i, DomsBelow (nP + i) ((tss ψ).getD i [])
  tssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → tss ψ₁ = tss ψ₂
  reflOpen : ∀ ψ i x, xFvs[i]? = some x → kindAt ks i = .reflexive →
    ∃ afvs body,
      openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      ((tss ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
          = some (((tss ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
        (body.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLenRefl : ∀ ψ i, kindAt ks i = .reflexive → i < nF →
    ((Eiss ψ).getD i []).length = mutualNIdxOf members (tgtAt ks i)
  /-- a reflexive field's entry: the Π-tower over its telescope of the
  TARGET member's leaf at the parameter variables and the readings -/
  reflEntry : ∀ ψ i, kindAt ks i = .reflexive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (mutualNameOf members (tgtAt ks i)) ψ)
            (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))

end ConLeche.Model
