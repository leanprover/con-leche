module

import ConLeche.Model.Inductives.FixData
import ConLeche.Model.Inductives.MutualCtorShape
public import ConLeche.Model.Inductives.BlockRep
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

/-! ## The constructor's data, from its stage run -/

/-- **The mutual constructor's data**, from its stage run at the
environment holding all `k` formers and the opened-form guard
(`fixCtorData_of` with the per-field TARGET member).  `hfM` is what
the block's earlier stages supply about a target: its former is stored
with the block's level parameters, its telescope ends in a sort, and
that sort evaluates like the block's (official's
`check_inductive_types` compares the members' result sorts). -/
theorem mutualCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {members : List (Name × Nat × Nat)} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ks : List (RecFieldKind × Nat)}
    {sorts : List Level}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hks : ks.length = nF)
    (hfM : ∀ i, i < nF → (kindAt ks i = .recursive ∨ kindAt ks i = .reflexive) →
      ∃ (ci : ConstantInfo) (bs' : List (Expr × BinderMeta)) (s' : Level),
        env.find? (mutualNameOf members (tgtAt ks i)) = some ci ∧
        ci.toConstantVal.levelParams = lps ∧
        ci.toConstantVal.type.stripPis (nP + mutualNIdxOf members (tgtAt ks i))
          = some (bs', .sort s') ∧
        ∀ ψ : Name → Nat, s'.eval ψ = resSort.eval ψ)
    (hopened : ConLeche.mutualOpenedOk env₀ members lps nP cvCa.type nF ks = true) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat))
      (fvsP xFvs : List Expr) (xrest : Expr) (Eiss : (Name → Nat) → List (List AnnotTerm))
      (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      MutualCtorDataI mp.base2 env₀ members T lps cvCa nP nF nIdx resSort isProp large idxArgs
        ds Es srcs ks fvsP xFvs xrest Eiss tss := by
  obtain ⟨⟨ty', hccv⟩, hresid, fvsP, crest, tfvs, trest, xFvs, idxArgs, hopP, -, -, hopX0, hlenI,
    -, -, hsorts⟩ := ConLeche.checkMutualCtor_shape hCtor
  obtain ⟨ds, Es, srcs, hidxEq0, hCD⟩ :=
    ctorDataI_ofShape hμ mp hccv hresid hopP hopX0 hlenI hsorts hfT hlpsT hstripT
  obtain ⟨fvsP', crest', xFvs', xrest, hopP', hopX', hO⟩ := mutualOpened_of hopened
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopP'))
  obtain ⟨rfl, hxr⟩ := Prod.mk.inj (Option.some.inj (hopX0.symm.trans hopX'))
  have hopX : openPisAtFvars nF crest nP = some (xFvs, xrest) := by rw [← hxr]; exact hopX0
  have hidxEq : idxArgs = xrest.getAppArgs.drop nP := by rw [← hxr]; exact hidxEq0
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.mutual_ctor_typeWF hCtor
  obtain ⟨hlenP, hidxP, -⟩ := opening_vars_at hopP
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hidxX' : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty := hidxX
  have hidxP' : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty := fun k x hx => by
    obtain ⟨ty, h⟩ := hidxP k x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  -- every field's opened domain reads to its entry
  have hdomRead : ∀ ψ i x, xFvs[i]? = some x →
      denoteMeta mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some ((ds ψ).getD (nP + i) default).2.2 := by
    intro ψ i x hx
    have hO := opened_of_peel hopAll hcf hcb (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hx
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    have hd := hO.doms (nP + i) x hxA
    have hget : (ds ψ)[nP + i]? = some ((ds ψ).getD (nP + i) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hCD.len ψ]; omega)]
      rfl
    rw [getD_reverse_of_peel (hCD.len ψ) (by omega) hget] at hd
    exact hd
  -- the entries' closedness
  have hentryBelow : ∀ ψ i, i < nF → Term.bvarsBelow (nP + i) ((ds ψ).getD (nP + i) default).2.2.erase := by
    intro ψ i hi
    have hb := (hCD.below ψ).getD_below (nP + i) (by rw [hCD.len ψ]; omega)
    rwa [Nat.zero_add] at hb
  -- a member's former at the parameter variables followed by the index expressions
  have hfamRead : ∀ (T' : Name) (ci : ConstantInfo) (nI : Nat), env.find? T' = some ci →
      ci.toConstantVal.levelParams = lps →
      ∀ ψ (d : Nat) (body : Expr), body.getAppFn = Expr.const T' (lps.map .param) →
      body.getAppArgs.take nP = fvsP → body.getAppArgs.length = nP + nI →
      ∀ R, denoteMeta mp.base2.acval env ψ d body = some R →
      ∃ Eis : List AnnotTerm, Eis.length = nI ∧
        DenoteMetaSpine mp.base2.acval env ψ d (body.getAppArgs.drop nP) Eis ∧
        R = AnnotTerm.mkAppN (mp.base2.acval T' ψ) (paramBvarsAt nP d ++ Eis) := by
    intro T' ci nI hfT' hlpsT' ψ d body hfn htake hlenA R hread
    have hshape : body
        = Expr.mkAppN (.const T' (lps.map .param)) (fvsP ++ body.getAppArgs.drop nP) := by
      conv => lhs; rw [← Expr.mkAppN_getApp body]
      rw [hfn, ← htake, List.take_append_drop]
    rw [hshape] at hread
    obtain ⟨fa, vs, hfa, hsp, hea⟩ := denoteMeta_mkAppN_inv hread
    have hfa' : fa = mp.base2.acval T' ψ := by
      rw [denoteMeta_const hfT' (by rw [hlpsT']; simp), hlpsT', Level.substFn_param_self] at hfa
      exact (Option.some.inj hfa).symm
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hvs₁ : vs₁ = paramBvarsAt nP d :=
      DenoteMetaSpine.unique hsp₁ (denoteMetaSpine_params d hlenP hidxP')
    refine ⟨vs₂, ?_, hsp₂, ?_⟩
    · rw [← hsp₂.length, List.length_drop, hlenA]; omega
    · rw [hea, hfa', hvs₁]
  -- a recursive field's index readings
  have hex : ∀ (ψ : Name → Nat) (i : Nat), kindAt ks i = .recursive → i < nF →
      ∃ Eis : List AnnotTerm, Eis.length = mutualNIdxOf members (tgtAt ks i) ∧
        (∀ x, xFvs[i]? = some x →
          DenoteMetaSpine mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) Eis) ∧
        ((ds ψ).getD (nP + i) default).2.2
          = AnnotTerm.mkAppN (mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ)
              (paramBvarsAt nP (nP + i) ++ Eis) := by
    intro ψ i hk hi
    have hil : i < xFvs.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    obtain ⟨hfn, htake, hlenA, -, -, -⟩ := hO.recF i x hx hk
    obtain ⟨ci', -, -, hfT', hlpsT', -, -⟩ := hfM i hi (Or.inl hk)
    obtain ⟨Eis, hlen, hsp, heq⟩ := hfamRead _ ci' _ hfT' hlpsT' ψ (nP + i) x.fvarTypeD hfn htake
      hlenA _ (hdomRead ψ i x hx)
    refine ⟨Eis, hlen, fun x' hx' => ?_, heq⟩
    obtain rfl := Option.some.inj (hx.symm.trans hx')
    exact hsp
  -- a reflexive field's telescope and index readings (task #202)
  have hexR : ∀ (ψ : Name → Nat) (i : Nat), kindAt ks i = .reflexive → i < nF →
      ∃ (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm),
        Eis.length = mutualNIdxOf members (tgtAt ks i) ∧
        (∀ x, xFvs[i]? = some x → tl.length = (x.fvarTypeD.piBinders).1.length) ∧
        (∀ x, xFvs[i]? = some x → ∃ afvs body,
          openPisAtFvars tl.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
          (∀ k a, afvs[k]? = some a →
            denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD = some (tl.getD k default).2.2) ∧
          DenoteMetaSpine mp.base2.acval env ψ (nP + i + tl.length) (body.getAppArgs.drop nP) Eis) ∧
        ((ds ψ).getD (nP + i) default).2.2
          = mkPisAV tl (AnnotTerm.mkAppN (mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ)
              (paramBvarsAt nP (nP + i + tl.length) ++ Eis)) ∧
        (∀ d ∈ tl, (d.2.1 = 0 ↔ resSort.eval ψ = 0)) ∧
        (∀ d ∈ tl, d.1 = 0 ∧ d.2.1 ≤ 1) := by
    intro ψ i hk hi
    have hil : i < xFvs.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    obtain ⟨afvs, body, hopA, -, -, hfn, htake, hlenA, -, -, -⟩ := hO.reflF i x hx hk
    have hm : afvs.length = (x.fvarTypeD.piBinders).1.length := openPisAtFvars_length _ hopA
    obtain ⟨tl, R, hst, hbody, hlenT, hdoms⟩ := denoteMeta_openPis _ hopA (hdomRead ψ i x hx)
    obtain ⟨ci', bs', s', hfT', hlpsT', hstripT', hsEq⟩ := hfM i hi (Or.inr hk)
    obtain ⟨Eis, hlen, hsp, hR⟩ := hfamRead _ ci' _ hfT' hlpsT' ψ _ body hfn htake hlenA R hbody
    obtain ⟨hentry, -⟩ := stripPisAV_eq_mkPis hst
    -- the telescope's bits: the field's sort row, walked through the binders
    obtain ⟨fv, ty, u, hfv, -, hinf, hens, -, -⟩ := hrows i hi
    obtain rfl := Option.some.inj (hx.symm.trans hfv)
    obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ := piBits_of_infer hμ _ hopA hinf hens
    have hshape : body
        = Expr.mkAppN (.const (mutualNameOf members (tgtAt ks i)) (lps.map .param))
            (fvsP ++ body.getAppArgs.drop nP) := by
      conv => lhs; rw [← Expr.mkAppN_getApp body]
      rw [hfn, ← htake, List.take_append_drop]
    rw [hshape] at hib
    obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ body.getAppArgs.drop nP) hib
    obtain ⟨ci₂, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
    obtain rfl : ci₂ = ci' := Option.some.inj (hfci.symm.trans hfT')
    have htfT : ConLeche.inferTypeCore μ env F' (nP + i + (x.fvarTypeD.piBinders).1.length)
        (.const (mutualNameOf members (tgtAt ks i)) (lps.map .param))
          = .ok ci₂.toConstantVal.type := by
      have h2 := htf
      rw [hlpsT', Expr.instantiateLevelParams_self] at h2
      exact h2
    obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ body.getAppArgs.drop nP) htfT
      (by rw [List.length_append, hlenP, List.length_drop, hlenA, Nat.add_sub_cancel_left];
          exact hstripT') hib
    have hvb := ensureSortCore_sort_eq hensb
    rw [hvb] at hbits
    refine ⟨tl, Eis, hlen, fun x' hx' => ?_, fun x' hx' => ?_, by rw [hentry, hR, hlenT], ?_,
      stripPisAV_denoteMeta_bits _ hopA (hdomRead ψ i x hx) hst⟩
    · obtain rfl := Option.some.inj (hx.symm.trans hx')
      exact hlenT
    · obtain rfl := Option.some.inj (hx.symm.trans hx')
      refine ⟨afvs, body, by rw [hlenT]; exact hopA, fun k a hka => ?_, by rw [hlenT]; exact hsp⟩
      obtain ⟨p, hp, -, hread⟩ := hdoms k a hka
      rw [List.getD_eq_getElem?_getD, hp]
      exact hread
    · intro d hd
      have hb := stripPisAV_bits _ (hbits ψ) (hdomRead ψ i x hx) hst d hd
      rwa [hsEq ψ] at hb
  -- the readings, chosen
  let Eis : (Name → Nat) → Nat → List AnnotTerm := fun ψ i =>
    if h : kindAt ks i = .recursive ∧ i < nF then Classical.choose (hex ψ i h.1 h.2)
    else if h' : kindAt ks i = .reflexive ∧ i < nF then
      Classical.choose (Classical.choose_spec (hexR ψ i h'.1 h'.2))
    else []
  let Tl : (Name → Nat) → Nat → List (Nat × Nat × AnnotTerm) := fun ψ i =>
    if h' : kindAt ks i = .reflexive ∧ i < nF then Classical.choose (hexR ψ i h'.1 h'.2)
    else []
  have hnotboth : ∀ i, kindAt ks i = .recursive → ¬ kindAt ks i = .reflexive := by
    intro i h1 h2; rw [h1] at h2; exact nomatch h2
  have hEis : ∀ ψ i (h : kindAt ks i = .recursive ∧ i < nF),
      (Eis ψ i).length = mutualNIdxOf members (tgtAt ks i) ∧
      (∀ x, xFvs[i]? = some x →
        DenoteMetaSpine mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) (Eis ψ i)) ∧
      ((ds ψ).getD (nP + i) default).2.2
        = AnnotTerm.mkAppN (mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ)
            (paramBvarsAt nP (nP + i) ++ Eis ψ i) := by
    intro ψ i h
    simp only [Eis, dif_pos h]
    exact Classical.choose_spec (hex ψ i h.1 h.2)
  have hEisR : ∀ ψ i (h : kindAt ks i = .reflexive ∧ i < nF),
      (Eis ψ i).length = mutualNIdxOf members (tgtAt ks i) ∧
      (∀ x, xFvs[i]? = some x → (Tl ψ i).length = (x.fvarTypeD.piBinders).1.length) ∧
      (∀ x, xFvs[i]? = some x → ∃ afvs body,
        openPisAtFvars (Tl ψ i).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a →
          denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD = some ((Tl ψ i).getD k default).2.2) ∧
        DenoteMetaSpine mp.base2.acval env ψ (nP + i + (Tl ψ i).length) (body.getAppArgs.drop nP) (Eis ψ i)) ∧
      ((ds ψ).getD (nP + i) default).2.2
        = mkPisAV (Tl ψ i) (AnnotTerm.mkAppN (mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ)
            (paramBvarsAt nP (nP + i + (Tl ψ i).length) ++ Eis ψ i)) ∧
      (∀ d ∈ Tl ψ i, (d.2.1 = 0 ↔ resSort.eval ψ = 0)) ∧
      (∀ d ∈ Tl ψ i, d.1 = 0 ∧ d.2.1 ≤ 1) := by
    intro ψ i h
    have hnr : ¬ (kindAt ks i = .recursive ∧ i < nF) := fun hh => hnotboth i hh.1 h.1
    simp only [Eis, Tl, dif_neg hnr, dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hexR ψ i h.1 h.2))
  have hEisNone : ∀ ψ i, kindAt ks i ≠ .recursive → kindAt ks i ≠ .reflexive →
      Eis ψ i = [] := by
    intro ψ i h h'
    simp only [Eis]
    rw [dif_neg (fun hh => h hh.1), dif_neg (fun hh => h' hh.1)]
  have hTlNone : ∀ ψ i, kindAt ks i ≠ .reflexive → Tl ψ i = [] := by
    intro ψ i h
    simp only [Tl]
    rw [dif_neg (fun hh => h hh.1)]
  let Eiss : (Name → Nat) → List (List AnnotTerm) := fun ψ => (List.range nF).map (Eis ψ)
  let Tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun ψ => (List.range nF).map (Tl ψ)
  have hEissGet : ∀ ψ i, i < nF → (Eiss ψ).getD i [] = Eis ψ i := by
    intro ψ i hi
    simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  have hEissGet' : ∀ ψ i, (Eiss ψ).getD i [] = if i < nF then Eis ψ i else [] := by
    intro ψ i
    split
    · next hi => exact hEissGet ψ i hi
    · next hi =>
      simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  have hTssGet : ∀ ψ i, i < nF → (Tss ψ).getD i [] = Tl ψ i := by
    intro ψ i hi
    simp only [Tss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  have hTssGet' : ∀ ψ i, (Tss ψ).getD i [] = if i < nF then Tl ψ i else [] := by
    intro ψ i
    split
    · next hi => exact hTssGet ψ i hi
    · next hi =>
      simp only [Tss, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  -- the entries of a reflexive field, closed
  have hreflBelow : ∀ ψ i (h : kindAt ks i = .reflexive ∧ i < nF),
      DomsBelow (nP + i) (Tl ψ i) ∧
      ∀ E ∈ Eis ψ i, Term.bvarsBelow (nP + i + (Tl ψ i).length) E.erase := by
    intro ψ i h
    have hb := hentryBelow ψ i h.2
    rw [(hEisR ψ i h).2.2.2.1] at hb
    obtain ⟨h1, h2⟩ := bvarsBelow_mkPisAV_inv hb
    rw [AnnotTerm.erase_mkAppN] at h2
    obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv h2
    exact ⟨h1, fun E hE => hall E.erase (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)⟩
  refine ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, Tss, ⟨hCD, hO, ⟨crest, hopP, hopX⟩, hks,
    hlenX, hlenP, hidxX',
    hidxP', hidxEq, hdomRead, fun ψ => by simp [Eiss], ?_, ?_, ?_, ?_, ?_, ?_, fun ψ => by simp [Tss],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ψ i x hx hk
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.1 x hx
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).1
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.2
  · intro ψ₁ ψ₂ hφ
    have hds := (hCD.params ψ₁ ψ₂ hφ).1
    simp only [Eiss]
    apply List.map_congr_left
    intro i hi
    have hi' : i < nF := List.mem_range.mp hi
    by_cases hk : kindAt ks i = .recursive
    · have h1 := (hEis ψ₁ i ⟨hk, hi'⟩).2.2
      have h2 := (hEis ψ₂ i ⟨hk, hi'⟩).2.2
      rw [hds] at h1
      have heq := h1.symm.trans h2
      have hl : (paramBvarsAt nP (nP + i) ++ Eis ψ₁ i).length
          = (paramBvarsAt nP (nP + i) ++ Eis ψ₂ i).length := by
        simp [(hEis ψ₁ i ⟨hk, hi'⟩).1, (hEis ψ₂ i ⟨hk, hi'⟩).1]
      exact List.append_cancel_left (mkAppN_inj_args heq hl).2
    · by_cases hk' : kindAt ks i = .reflexive
      · have h1 := (hEisR ψ₁ i ⟨hk', hi'⟩).2.2.2.1
        have h2 := (hEisR ψ₂ i ⟨hk', hi'⟩).2.2.2.1
        rw [hds] at h1
        have heq := h1.symm.trans h2
        obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hlt : (Tl ψ₁ i).length = (Tl ψ₂ i).length := by
          rw [(hEisR ψ₁ i ⟨hk', hi'⟩).2.1 x hx, (hEisR ψ₂ i ⟨hk', hi'⟩).2.1 x hx]
        obtain ⟨hteq, hbeq⟩ := mkPisAV_inj hlt heq
        rw [hteq] at hbeq
        have hl : (paramBvarsAt nP (nP + i + (Tl ψ₂ i).length) ++ Eis ψ₁ i).length
            = (paramBvarsAt nP (nP + i + (Tl ψ₂ i).length) ++ Eis ψ₂ i).length := by
          simp [(hEisR ψ₁ i ⟨hk', hi'⟩).1, (hEisR ψ₂ i ⟨hk', hi'⟩).1]
        exact List.append_cancel_left (mkAppN_inj_args hbeq hl).2
      · rw [hEisNone ψ₁ i hk hk', hEisNone ψ₂ i hk hk']
  · intro ψ i E hE
    rw [hEissGet' ψ i] at hE
    rw [hTssGet' ψ i]
    split at hE
    · next hi =>
      rw [if_pos hi]
      by_cases hk : kindAt ks i = .recursive
      · have hentry := (hEis ψ i ⟨hk, hi⟩).2.2
        have hb := hentryBelow ψ i hi
        rw [hentry, AnnotTerm.erase_mkAppN] at hb
        obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv hb
        rw [hTlNone ψ i (hnotboth i hk), List.length_nil, Nat.add_zero]
        exact hall E.erase (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
      · by_cases hk' : kindAt ks i = .reflexive
        · exact (hreflBelow ψ i ⟨hk', hi⟩).2 E hE
        · rw [hEisNone ψ i hk hk'] at hE
          exact nomatch hE
    · exact nomatch hE
  · intro ψ i hk hk'
    rw [hEissGet' ψ i]
    split
    · exact hEisNone ψ i hk hk'
    · rfl
  · intro ψ i hk
    rw [hTssGet' ψ i]
    split
    · exact hTlNone ψ i hk
    · rfl
  · intro ψ i d hd
    rw [hTssGet' ψ i] at hd
    split at hd
    · next hi =>
      by_cases hk' : kindAt ks i = .reflexive
      · exact (hEisR ψ i ⟨hk', hi⟩).2.2.2.2.1 d hd
      · rw [hTlNone ψ i hk'] at hd
        exact nomatch hd
    · exact nomatch hd
  · intro ψ i d hd
    rw [hTssGet' ψ i] at hd
    split at hd
    · next hi =>
      by_cases hk' : kindAt ks i = .reflexive
      · exact (hEisR ψ i ⟨hk', hi⟩).2.2.2.2.2 d hd
      · rw [hTlNone ψ i hk'] at hd
        exact nomatch hd
    · exact nomatch hd
  · intro ψ i
    rw [hTssGet' ψ i]
    split
    · next hi =>
      by_cases hk' : kindAt ks i = .reflexive
      · exact (hreflBelow ψ i ⟨hk', hi⟩).1
      · rw [hTlNone ψ i hk']; trivial
    · trivial
  · intro ψ₁ ψ₂ hφ
    have hds := (hCD.params ψ₁ ψ₂ hφ).1
    simp only [Tss]
    apply List.map_congr_left
    intro i hi
    have hi' : i < nF := List.mem_range.mp hi
    by_cases hk' : kindAt ks i = .reflexive
    · have h1 := (hEisR ψ₁ i ⟨hk', hi'⟩).2.2.2.1
      have h2 := (hEisR ψ₂ i ⟨hk', hi'⟩).2.2.2.1
      rw [hds] at h1
      have heq := h1.symm.trans h2
      obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hlt : (Tl ψ₁ i).length = (Tl ψ₂ i).length := by
        rw [(hEisR ψ₁ i ⟨hk', hi'⟩).2.1 x hx, (hEisR ψ₂ i ⟨hk', hi'⟩).2.1 x hx]
      exact (mkPisAV_inj hlt heq).1
    · rw [hTlNone ψ₁ i hk', hTlNone ψ₂ i hk']
  · intro ψ i x hx hk
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hTssGet ψ i hi, hEissGet ψ i hi]
    obtain ⟨afvs, body, hop, hdoms, hsp⟩ := (hEisR ψ i ⟨hk, hi⟩).2.2.1 x hx
    exact ⟨afvs, body, hop, (hEisR ψ i ⟨hk, hi⟩).2.1 x hx, hdoms, hsp⟩
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEisR ψ i ⟨hk, hi⟩).1
  · intro ψ i hk hi
    rw [hTssGet ψ i hi, hEissGet ψ i hi]
    exact (hEisR ψ i ⟨hk, hi⟩).2.2.2.1

/-! ## To the uniform datum (task #315) -/

/-- `kindsOf`'s reading at ANY position: beyond the list both sides
default to `.ordinary`. -/
theorem kindsOf_getD' (ks : List (RecFieldKind × Nat)) (i : Nat) :
    (kindsOf ks).getD i .ordinary = kindAt ks i := by
  unfold kindsOf kindAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

/-- The mutual opened-form guard IS the block one at the target
readings. -/
theorem MutualOpened.toBlock {env₀ : Env} {members : List (Name × Nat × Nat)} {lps : List Name}
    {nP nF : Nat} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr} {xrest : Expr}
    (h : MutualOpened env₀ members lps nP nF ks fvsP xFvs xrest) :
    BlockOpened env₀ (fun i => mutualNameOf members (tgtAt ks i))
      (fun i => mutualNIdxOf members (tgtAt ks i)) lps nP nF (kindsOf ks) fvsP xFvs xrest :=
  ⟨h.residRes,
    fun i x hx hk => h.ord i x hx (by rwa [kindsOf_getD'] at hk),
    fun i x hx hk => h.recF i x hx (by rwa [kindsOf_getD'] at hk),
    fun i x hx hk => h.reflF i x hx (by rwa [kindsOf_getD'] at hk),
    fun i hi => by simpa only [kindsOf_getD'] using h.kinds i hi⟩

/-- **The mutual constructor's data IS the uniform datum's**
(`BlockCtorData`): the fields correspond one to one, the kinds read
through `kindsOf`, and the per-field target member through
`mutualNameOf`/`mutualNIdxOf` at `tgtAt`. -/
theorem MutualCtorDataI.toBlock {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr}
    {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss) :
    BlockCtorData m env₀ T (fun i => mutualNameOf members (tgtAt ks i))
      (fun i => mutualNIdxOf members (tgtAt ks i)) lps cvC nP nF nIdx resSort isProp large
      idxArgs ds Es srcs (kindsOf ks) fvsP xFvs xrest Eiss tss :=
  { h.toCtorDataI with
    opened := h.opened.toBlock, opens := h.opens, ksLen := kindsOf_length.trans h.ksLen
    xLen := h.xLen, pLen := h.pLen, xIdx := h.xIdx, pIdx := h.pIdx, idxEq := h.idxEq
    domRead := h.domRead, eissLen := h.eissLen
    eisRead := fun ψ i x hx hk => h.eisRead ψ i x hx (by rwa [kindsOf_getD'] at hk)
    eisLen := fun ψ i hk hi => h.eisLen ψ i (by rwa [kindsOf_getD'] at hk) hi
    recEntry := fun ψ i hk hi => h.recEntry ψ i (by rwa [kindsOf_getD'] at hk) hi
    eissParams := h.eissParams, eissBelow := h.eissBelow
    ordNone := fun ψ i h₁ h₂ =>
      h.ordNone ψ i (by rwa [kindsOf_getD'] at h₁) (by rwa [kindsOf_getD'] at h₂)
    tssLen := h.tssLen
    tssNone := fun ψ i hk => h.tssNone ψ i (by rwa [kindsOf_getD'] at hk)
    tssBits := h.tssBits, tssPiBits := h.tssPiBits, tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hx hk => h.reflOpen ψ i x hx (by rwa [kindsOf_getD'] at hk)
    eisLenRefl := fun ψ i hk hi => h.eisLenRefl ψ i (by rwa [kindsOf_getD'] at hk) hi
    reflEntry := fun ψ i hk hi => h.reflEntry ψ i (by rwa [kindsOf_getD'] at hk) hi }

end ConLeche.Model
