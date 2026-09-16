module

public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.TupleLfp
public section

/-!
# The uniform block model of a mutual block — `BlockModel.ofMutual` (task #315, M4)

`ofNative`'s twin (`BlockRepOne.lean`) for a block of `k ≥ 1` members
installed by the mutual route (`checkMutualCore`,
`Kernel/Inductives/MutualInstall.lean`): the block model's per-member and
per-constructor readings are the stages' outputs, keyed by member and
member-local constructor position; the tuple operator is the `k`-ary
fixed point's (`tupleLfpΦ`, `TupleLfp.lean` — the derived term former's
semantic operator, whose representation the block model never sees), the
injections are the sum route's tagged towers at the constructor's
GLOBAL block position (`blockMinorIdx`, the minor's index:
`injW w J ⟨f⃗, pt⟩`, what `sumMkAV` folds to and what the table stage
reads), and every member's index-tuple sort is the block's common
index universe `W` (`TupleLfpOk`: the members' index telescopes are
graded at one positive universe).

The block model's SEMANTIC clauses come from the term former's API:
`functor` is `tupleLfpΦ_functor` (`ofMutual_functor`), `leaf` is the
interp law `tupleLfpAV_fold` (`ofMutual_leaf`), `mkZero`/`mkInj` are
the injections' own laws; `fibre` and `ctor` are the recursor stage's
(M4 session 3, `tupleLfpΦ_fibre` and `sumMkAV_fold`).  The run-level
shape is `MutualBlockModelOf` (`mutualBlockModelOf_ofMutual`, by construction).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind MutualBlock MutualFormerA)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The block's index telescopes and the minor index -/

/-- Member `t`'s index telescope at the parameter frame, off its
telescope reading. -/
@[expose] def blockIds (nP : Nat) (ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (ψ : Name → Nat) (t : Nat) : List AnnotTerm :=
  ((ppsM t ψ).drop nP).map (·.2.2)

/-- Constructor `j` of member `mm`'s GLOBAL block position (the
recursors' minor index; `BlockModel.minorIdx` at the block model). -/
@[expose] def blockMinorIdx (ctorsM : Nat → List (ConstantVal × Nat)) (mm j : Nat) : Nat :=
  ((List.range mm).map fun t => (ctorsM t).length).sum + j

/-! ## The block model -/

/-- **The uniform block model of a mutual block** (see the module docstring):
the readings per member and member-local constructor, the block's
index universe `W` as every member's index-tuple sort, the tuple
operator the `k`-ary fixed point's at the block's constructor data in
GLOBAL constructor order (`mems`, `nFs`, `tgts`, `rss`, `tlss`,
`Eiss₀`, `Fss₀`, `Ess₀` — `tupleLfpAV`'s arguments), the injections the
tagged towers at the global position. -/
@[expose] noncomputable def BlockModel.ofMutual (nP k : Nat) (resSort : Level) (isProp large : Bool)
    (env₀ : Env) (memberNames : List Name) (nIdxs : List Nat)
    (ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (ctorsM : Nat → List (ConstantVal × Nat)) (idxF : Nat → Nat → List Expr)
    (dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → Nat → List (Option Nat))
    (ksF : Nat → Nat → List RecFieldKind) (tgts : Nat → Nat → Nat → Nat)
    (fvsPF xFvsF : Nat → Nat → List Expr) (xrestF : Nat → Nat → Expr)
    (eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mems nFs : List Nat) (tgtsG : List (List Nat)) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)) : BlockModel V where
  nP := nP
  k := k
  resSort := resSort
  isProp := isProp
  large := large
  env₀ := env₀
  memberNames := memberNames
  nIdxs := nIdxs
  ppsM := ppsM
  uM := fun _ ψ => W ψ
  ctorsM := ctorsM
  idxF := idxF
  dsF := dsF
  esF := esF
  srcsF := srcsF
  ksF := ksF
  tgts := tgts
  fvsPF := fvsPF
  xFvsF := xFvsF
  xrestF := xrestF
  eissF := eissF
  tssF := tssF
  Φ := fun ψ ρp =>
    tupleLfpΦ (W ψ) (resSort.eval ψ) ρp k (blockIds nP ppsM ψ) mems nFs tgtsG rss (tlss ψ) (Eiss₀ ψ)
      (Fss₀ ψ) (Ess₀ ψ)
  inj := fun ψ mm j fs => injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt]))

section Mutual

variable {nP k : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env} {memberNames : List Name}
  {nIdxs : List Nat} {ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {W : (Name → Nat) → Nat} {ctorsM : Nat → List (ConstantVal × Nat)} {idxF : Nat → Nat → List Expr}
  {dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → Nat → List (Option Nat)}
  {ksF : Nat → Nat → List RecFieldKind} {tgts : Nat → Nat → Nat → Nat}
  {fvsPF xFvsF : Nat → Nat → List Expr} {xrestF : Nat → Nat → Expr}
  {eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {mems nFs : List Nat} {tgtsG : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

local notation "D" => (BlockModel.ofMutual (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsM W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF mems nFs tgtsG rss
  tlss Eiss₀ Fss₀ Ess₀)

/-- The block model's index telescopes are the block's. -/
theorem ofMutual_IdsM (mm : Nat) (ψ : Name → Nat) : (D).IdsM mm ψ = blockIds nP ppsM ψ mm := rfl

/-- The block model's index-tuple sets: every member's over the block's
index universe. -/
theorem ofMutual_idx (ψ : Name → Nat) (ρp : Nat → V) :
    (D).idx ψ ρp = fun mm => idxSet (W ψ) ρp (blockIds nP ppsM ψ mm) := rfl

/-- The block model's operator: the `k`-ary fixed point's. -/
theorem ofMutual_Φ (ψ : Name → Nat) (ρp : Nat → V) :
    (D).Φ ψ ρp
      = tupleLfpΦ (W ψ) ((D).w ψ) ρp k (blockIds nP ppsM ψ) mems nFs tgtsG rss (tlss ψ) (Eiss₀ ψ)
          (Fss₀ ψ) (Ess₀ ψ) := rfl

/-- The block model's injections: the tagged towers at the global position. -/
theorem ofMutual_inj (ψ : Name → Nat) (mm j : Nat) (fs : List V) :
    (D).inj ψ mm j fs = injW ((D).w ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt])) := rfl

/-- The block model's minor index is the global position. -/
theorem ofMutual_minorIdx (mm j : Nat) : (D).minorIdx mm j = blockMinorIdx ctorsM mm j := rfl

/-- The block model's index tuple is the tower (the index universe is
positive). -/
theorem ofMutual_tup {ψ : Name → Nat} (hW : W ψ ≠ 0) (mm : Nat) (is : List V) :
    (D).tup ψ mm is = mkTower is :=
  tupW_pos hW is

/-- **`functor` for the block model**, from the term former's premise at the
parameter frame. -/
theorem ofMutual_functor {ψ : Name → Nat} {ρp : Nat → V}
    (h : TupleLfpOk (W ψ) ((D).w ψ) ρp k (blockIds nP ppsM ψ) mems nFs tgtsG rss (tlss ψ) (Eiss₀ ψ)
      (Fss₀ ψ) (Ess₀ ψ)) :
    MonoTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    MapsTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    ∃ L, IsClosedTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  tupleLfpΦ_functor h

/-- **`leaf` for the block model**: member `mm`'s term-level leaf
(`tupleLfpAV`) at fitting parameters and indices is the least
pre-fixed TUPLE's component `mm` at the index tuple — the interp law
`tupleLfpAV_fold`.  The parameter spine fits the MEMBER's own
telescope (`hsp`); the cross-member identification with the block's
`params` is the recursor stage's. -/
theorem ofMutual_leaf {ψ : Name → Nat} {ρ : Nat → V} {as is : List V} {mm : Nat} (hmm : mm < k)
    (h : TupleLfpOk (W ψ) ((D).w ψ) (consList as ρ) k (blockIds nP ppsM ψ) mems nFs tgtsG rss (tlss ψ)
      (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ))
    (hsp : SpineFit ρ (((ppsM mm ψ).take nP).map (·.2.2)) as)
    (hi : SpineFit (consList as ρ) ((D).IdsM mm ψ) is) :
    (as ++ is).foldl SetTheory.app (interp V ρ
        (tupleLfpAV (W ψ) ((D).w ψ) (ppsM mm ψ) ((ppsM mm ψ).drop nP).length k (blockIds nP ppsM ψ)
          mems nFs tgtsG rss (tlss ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ) mm))
      = SetTheory.app (lfpTuple ((D).w ψ) k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)) mm)
          ((D).tup ψ mm is) := by
  rw [ofMutual_tup h.W_pos]
  exact tupleLfpAV_fold hmm h rfl hsp hi

/-- `mkZero` for the block model: at a `Prop`-valued block every injection is
the point. -/
theorem ofMutual_mkZero (ψ : Name → Nat) (hw : (D).w ψ = 0) (mm j : Nat) (fs : List V) :
    (D).inj ψ mm j fs = pt := by
  show injW (resSort.eval ψ) _ _ = pt
  have hw' : resSort.eval ψ = 0 := hw
  rw [hw', injW_zero]

/-- `mkInj` for the block model, within a member: the global positions of a
member's constructors are distinct, and the towers are injective at
equal lengths. -/
theorem ofMutual_mkInj (ψ : Name → Nat) (hw : (D).w ψ ≠ 0) {mm j j' : Nat} {fs fs' : List V}
    (hlen : fs.length = (((D).Fss mm ψ).getD j []).length)
    (hlen' : fs'.length = (((D).Fss mm ψ).getD j' []).length)
    (h : (D).inj ψ mm j fs = (D).inj ψ mm j' fs') : j = j' ∧ fs = fs' := by
  have hw' : resSort.eval ψ ≠ 0 := hw
  change injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j) (mkTower (fs ++ [pt]))
    = injW (resSort.eval ψ) (blockMinorIdx ctorsM mm j') (mkTower (fs' ++ [pt])) at h
  rw [injW_pos hw', injW_pos hw'] at h
  obtain ⟨hJ, h2⟩ := inj_inj h
  have hj : j = j' := by
    unfold blockMinorIdx at hJ
    omega
  subst hj
  refine ⟨rfl, ?_⟩
  have := mkTower_inj (by simp [hlen, hlen']) h2
  exact List.append_cancel_right this

end Mutual

/-! ## The block model of a run -/

/-- **`ofMutual` at the run's block is the run's block model**
(`MutualBlockModelOf`): its arities, names, sort and constructors are the
block record's and the stages' outputs — by construction. -/
theorem mutualBlockModelOf_ofMutual (env : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) {f₀ : MutualFormerA} (hf₀ : fms[0]? = some f₀)
    (isProp : Bool) (ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (W : (Name → Nat) → Nat) (idxF : Nat → Nat → List Expr)
    (dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → Nat → List (Option Nat))
    (ksF : Nat → Nat → List RecFieldKind) (tgts : Nat → Nat → Nat → Nat)
    (fvsPF xFvsF : Nat → Nat → List Expr) (xrestF : Nat → Nat → Expr)
    (eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mems nFs : List Nat) (tgtsG : List (List Nat)) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)) :
    MutualBlockModelOf env b fms ctorsA
      (BlockModel.ofMutual (V := V) b.nP b.k f₀.s isProp b.large env (fms.map (·.cvTa.name))
        (fms.map (·.nIdx)) ppsM W (fun t => (b.ownCtors t).map fun q => ctorsA.getD q.1 default)
        idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF mems nFs tgtsG rss tlss Eiss₀
        Fss₀ Ess₀) where
  k := rfl
  nP := rfl
  env₀ := rfl
  memberNames := rfl
  nIdxs := rfl
  resSort := by
    show f₀.s = (fms.getD 0 default).s
    rw [List.getD_eq_getElem?_getD, hf₀]
    rfl
  large := rfl
  ctors := fun _ _ => rfl

end ConLeche.Model
