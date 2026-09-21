module

public import ConLeche.Model.Inductives.BlockData
import ConLeche.Verify.Inductives.BlockInv
public section

/-!
# The constructors' data functions at a block member (task #315 M3)

`FixAssemblyKit.lean`'s `fixCtorFuns_of` at `k` members: every
constructor of ONE member, picked as a function of its position, with
each field read at its TARGET member's former.

Two hypotheses are what a block costs over a single family.  `hmem`
(the one `blockCtorData_of` asks for, here stated once for EVERY
target rather than per constructor) says that every member's former is
stored, at the block's level parameters, with its OWN index count and
a result sort whose VALUE is the block's — official checks the
members' sorts with `Level.isEquiv`, not for equality.  `hFOk` is the
kinds' re-check on the STORED constructors at the member
(`blockMemberFieldsOk`, lane V's `blockMemberFieldsOk_inv`), which is
where each field's target is read positionally.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind BlockFieldKind IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- A block constructor's data, bundled for the choice. -/
structure BlockCtorPick where
  idxArgs : List Expr
  ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)
  Es : (Name → Nat) → List AnnotTerm
  srcs : List (Option Nat)
  fvsP : List Expr
  xFvs : List Expr
  xrest : Expr
  Eiss : (Name → Nat) → List (List AnnotTerm)
  tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))

/-- `blockCtorData_of`, its witnesses bundled. -/
theorem blockCtorPick_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat}
    {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ks : List RecFieldKind} {sorts : List Level}
    {sT : Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hsT : ∀ ψ : Name → Nat, sT.eval ψ = resSort.eval ψ)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT))
    (hks : ks.length = nF)
    (hmem : ∀ i : Nat, ∃ (cv : ConstantVal) (caps' : IndCaps) (s : Level)
        (bs' : List (Expr × BinderMeta)),
        env.find? (Tof i) = some (.indInfo cv caps') ∧ cv.levelParams = lps ∧
        cv.type.stripPis (nP + nIdxOf i) = some (bs', .sort s) ∧
        ∀ ψ : Name → Nat, s.eval ψ = resSort.eval ψ)
    (hopened : ∀ fvsP crest xFvs xrest, openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) →
      openPisAtFvars nF crest nP = some (xFvs, xrest) →
      BlockOpened env₀ Tof nIdxOf lps nP nF ks fvsP xFvs xrest) :
    ∃ q : BlockCtorPick, BlockCtorDataI mp.base2 env₀ T Tof nIdxOf lps cvCa nP nF nIdx resSort
      isProp large q.idxArgs q.ds q.Es q.srcs ks q.fvsP q.xFvs q.xrest q.Eiss q.tss := by
  obtain ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, tss, hD⟩ :=
    blockCtorData_of hμ mp hCtor hfT hlpsT hsT hstripT hks hmem hopened
  exact ⟨⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, tss⟩, hD⟩

/-- **The constructors' data functions at one member of a block**:
every constructor's data, its kind list the guard's and its fields'
targets read off that list. -/
theorem blockCtorFuns_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {names : List Name} {nIdxs : List Nat} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal}
    {env₀ env₁ : Env} {caps : IndCaps} {bs : List (Expr × BinderMeta)}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List BlockFieldKind)} {sT : Level}
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hsT : ∀ ψ : Name → Nat, sT.eval ψ = resSort.eval ψ)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT))
    (hmem : ∀ tgt : Nat, ∃ (cv : ConstantVal) (caps' : IndCaps) (s : Level)
        (bs' : List (Expr × BinderMeta)),
        env.find? (ConLeche.nameAt names tgt) = some (.indInfo cv caps') ∧ cv.levelParams = lps ∧
        cv.type.stripPis (nP + ConLeche.nIdxAt nIdxs tgt) = some (bs', .sort s) ∧
        ∀ ψ : Name → Nat, s.eval ψ = resSort.eval ψ)
    (hFOk : ConLeche.blockMemberFieldsOk env₀ names lps nP nIdxs ctorsA kinds = true)
    (hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx
          resSort isProp large c.1 cA.2 cvTa = .ok (cA.1, sorts)) :
    ∃ (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        BlockCtorDataI mp.base2 env₀ T (tofOf names (kinds.getD j []))
          (nIdxOfOf nIdxs (kinds.getD j [])) lps cA.1 nP cA.2 nIdx resSort isProp large
          (idxF j) (dsF j) (esF j) (srcsF j) ((kinds.getD j []).map BlockFieldKind.toRec)
          (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j) := by
  have hex : ∀ j : Nat, ∃ q : BlockCtorPick, ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      BlockCtorDataI mp.base2 env₀ T (tofOf names (kinds.getD j []))
        (nIdxOfOf nIdxs (kinds.getD j [])) lps cA.1 nP cA.2 nIdx resSort isProp large
        q.idxArgs q.ds q.Es q.srcs ((kinds.getD j []).map BlockFieldKind.toRec)
        q.fvsP q.xFvs q.xrest q.Eiss q.tss := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨⟨[], fun _ => [], fun _ => [], [], [], [], .bvar 0, fun _ => [], fun _ => []⟩,
        fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, sorts, hCtor⟩ := hrunOf j cA hj
      obtain ⟨ks, hks, hksLen, hopened⟩ := ConLeche.blockMemberFieldsOk_inv hFOk hj
      have hksD : kinds.getD j [] = ks := by rw [List.getD_eq_getElem?_getD, hks]; rfl
      obtain ⟨fvsP, crest, xFvs, xrest, hopP, hopX, hO⟩ := blockOpened_of hopened
      obtain ⟨q, hq⟩ := blockCtorPick_of (ks := ks.map BlockFieldKind.toRec) hμ mp hCtor hfT
        hlpsT hsT hstripT (by rw [List.length_map]; exact hksLen)
        (fun i => hmem ((ConLeche.blockTgtsOf ks).getD i 0))
        (fun fvsP' crest' xFvs' xrest' hp' hx' => by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp'.symm.trans hopP))
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hx'.symm.trans hopX))
          exact hO)
      refine ⟨q, fun cA' h => ?_⟩
      obtain rfl := Option.some.inj h
      rw [hksD]
      exact hq
  let q : Nat → BlockCtorPick := fun j => Classical.choose (hex j)
  exact ⟨fun j => (q j).idxArgs, fun j => (q j).ds, fun j => (q j).Es, fun j => (q j).srcs,
    fun j => (q j).fvsP, fun j => (q j).xFvs, fun j => (q j).xrest, fun j => (q j).Eiss,
    fun j => (q j).tss, fun j => Classical.choose_spec (hex j)⟩

end ConLeche.Model
