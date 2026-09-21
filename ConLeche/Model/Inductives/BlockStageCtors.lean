module

public import ConLeche.Model.Inductives.BlockCtorsLoop
public import ConLeche.Model.Inductives.BlockCaps
public import ConLeche.Model.Inductives.BlockRealChains
public import ConLeche.Model.Inductives.BlockRep
public section

/-!
# The constructors' stage at a block member (task #315 M3)

`BlockCtorsCore`: what the `k` constructor loops thread — the `k`
formers found with their leaves and their telescope readings, the
capability families still free, every member's constructors' data at
the carrier, and the constructors consed SO FAR with their leaves.
It is `declNative`'s `Inv` at `k` members, and it is exactly what a
constructor cons preserves (`BlockCtorsCore.cons`).

`stageBlockCtorsAt` is `declNative`'s member-local half at member `m`:
the fibre law of the member's own fixpoint leaf (`blockFold_of` over
the member's REAL chains, built here from the block's operator premise
and the dummy/real identification), the member's capability laws
(`blockCapsLawsAt`), and then `blockCtorsLoop` — so the stage's output
is the carrier after `consSumCtors` of that member's constructors,
with the core invariant one member further on.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  InductiveShape BlockShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The invariant the member loops thread -/

/-- **The block install's carrier invariant at the constructors'
stage**, `nc` members' constructors consed: the `k` formers with their
leaves and telescope readings, the capability families free, every
member's constructors' readings, the earlier members' constructors
stored with their leaves. -/
@[expose] def BlockCtorsCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (nc : Nat) : Prop :=
  -- the `k` formers
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  -- a capable member's projection-function family is still free
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      (ConLeche.blockCapsAt p₁ c isRec).unitlike = false →
      (ConLeche.blockCapsAt p₁ c isRec).eta = true →
      env.find? (projFnName cvTb.name 0) = none) ∧
  -- every member's constructors resolve and read
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.constsResolve env = true ∧
      (∀ e ∈ d.idxF c j, e.constsResolve env = true) ∧
      BlockCtorDataI m' d.env₀ (d.memberName c) (fun i => d.memberName (d.tgts c j i))
        (fun i => d.nIdxAt (d.tgts c j i)) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp
        d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.ksF c j) (d.fvsPF c j)
        (d.xFvsF c j) (d.xrestF c j) (d.eissF c j) (d.tssF c j)) ∧
  -- the members before `nc`: their constructors are stored with their leaves
  (∀ c, c < nc → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧ cA.1.levelParams = lps ∧
      ∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP).map (·.2.2))
            (uChains (d.Fss c ψ)))

/-- **The block's names, statically**: a member's name is its former's,
and every field's target is a member. -/
@[expose] def BlockNamesOk (d : BlockData V) (cvTasAll : List ConstantVal) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb → d.memberName c = cvTb.name) ∧
  (∀ c j i : Nat, d.tgts c j i < cvTasAll.length) ∧
  ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA → c < cvTasAll.length

/-- **The core invariant survives a constructor's cons.**  A stored
name is not the fresh one, so nothing found before is disturbed; the
readings cross by `FormerData.cross` and `BlockCtorDataI.cross`. -/
theorem BlockCtorsCore.cons {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (h : BlockCtorsCore m' d lps cvTasAll p₁ isRec A nc)
    {cA : ConstantVal × Nat} {B : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? cA.1.name = none)
    (hpshape : cA.1.name.isProjFnShape = false)
    (mC : EnvModel V ⟨.ctorInfo cA.1 d.nP cA.2 :: env.consts⟩)
    (hac : mC.acval = acvalWith m'.acval cA.1.name B) :
    BlockCtorsCore mC d lps cvTasAll p₁ isRec A nc := by
  obtain ⟨hnameOf, htgtLt, hctorLt⟩ := hN
  obtain ⟨hform, hfr, hdata, hconsed⟩ := h
  have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 d.nP cA.2) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ hh => nomatch hh)
  -- a name already stored is not the fresh one
  have hne : ∀ n : Name, (env.find? n).isSome = true → n ≠ cA.1.name := by
    intro n hn hnn
    rw [hnn, hfresh] at hn
    exact nomatch hn
  have hneOf : ∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      cvTb.name ≠ cA.1.name := by
    intro c cvTb hc
    exact hne _ (by rw [(hform c cvTb hc).1]; rfl)
  refine ⟨fun c cvTb hc => ?_, fun c cvTb hc hU he => ?_, fun c j cB hj => ?_,
    fun c hc j cB hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind,
      Expr.constsResolve_mono hres, fun ψ => ?_, ?_⟩
    · rw [hac]
      show acvalWith m'.acval cA.1.name B cvTb.name ψ = _
      rw [acvalWith_ne (hneOf c cvTb hc)]
      exact hleaf ψ
    · exact hFD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh (hcross _)
        (constsBound_of_constsResolve _ hres) mC hac
  · have hnp : ¬ ((ConstantInfo.ctorInfo cA.1 d.nP cA.2).name = projFnName cvTb.name 0) := by
      intro hh
      have hh' : cA.1.name = projFnName cvTb.name 0 := hh
      have := projFnName_isProjFnShape cvTb.name 0
      rw [← hh', hpshape] at this
      exact nomatch this
    rw [ConLeche.Env.find?_cons, if_neg hnp]
    exact hfr c cvTb hc hU he
  · obtain ⟨hres, hresI, hD⟩ := hdata c j cB hj
    refine ⟨Expr.constsResolve_mono hres, fun e he => Expr.constsResolve_mono (hresI e he), ?_⟩
    refine hD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh ?_ ?_ hcross
      (constsBound_of_constsResolve _ hres)
      (fun e he => constsBound_of_constsResolve _ (hresI e he)) mC hac
    · obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (hctorLt c j cB hj)⟩
      rw [hnameOf c cvTb hcvTb]
      exact hneOf c cvTb hcvTb
    · intro i
      obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[d.tgts c j i]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (htgtLt c j i)⟩
      rw [hnameOf _ cvTb hcvTb]
      exact hneOf _ cvTb hcvTb
  · obtain ⟨hfind, hlps, hleaf⟩ := hconsed c hc j cB hj
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, hlps, fun ψ => ?_⟩
    rw [hac]
    show acvalWith m'.acval cA.1.name B cB.1.name ψ = _
    rw [acvalWith_ne (hne _ (by rw [hfind]; rfl))]
    exact hleaf ψ

end ConLeche.Model
