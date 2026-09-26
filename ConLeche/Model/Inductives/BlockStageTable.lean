module

public import ConLeche.Model.Inductives.FixKit
public import ConLeche.Semantics.Tower.BlockTower
public section

/-!
# The projection table's cons at a BLOCK member (task #315 M3)

`stageBlockTable`: `stageFixTable` at a structure-like MEMBER of a
block — one constructor, no index — whose former's leaf is the block's
operator leaf `blockTyG` at that member (at any chains: lane HOLE2's are
the hole chains).  Nothing is re-proved: the table stage is
abstract in the former's leaf, and the only two things it reads of one
are its λ-tower shape (by `rfl` at `blockTyG`) and its FOLD, which at
a member with no index and one constructor is `blockFoldSingle`.

So a block's tables cost exactly what the one-family route's do; what
is member-specific is the FOLD, and it is the caller's: a statement
about the leaf TERM, established at the constructors' stage
(`blockFoldSingle` over the member's real chains) where the member's
data still crosses the conses.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta
  ProjEntry ProjTable RecRule)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The P step at a block member's projection table.** -/
theorem stageBlockTable (mp : EnvModelM V μ env)
    {T : Name} {lps : List Name} {nP : Nat} {resSort : Level} {isProp : Bool}
    {cvTa cvCa : ConstantVal} {nF : Nat} {sorts : List Level}
    {envOut : Env} {caps : IndCaps}
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name
      lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) 1 cvCa env = .ok envOut)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hcaps : caps.eta = true → (Level.isEquiv resSort .zero == some true) = false ∧
      caps.etaCtor = cvCa.name ∧ caps.etaParams = nP ∧ caps.etaFields = nF)
    (hlpsT : cvTa.levelParams = lps)
    (hfC : env.find? cvCa.name = some (.ctorInfo cvCa nP nF))
    (hlpsC : cvCa.levelParams = lps)
    (hstripC : (cvCa.type.stripPis (nP + nF)).isSome = true)
    (hProp : isProp = (Level.isEquiv resSort .zero == some true))
    (hTshape : T.isProjFnShape = false)
    (hCshape : cvCa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresR : ConLeche.reservedBasisNames.contains (T.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains cvCa.name = false)
    (hnp : ∀ j, NoProjEnv env T j)
    {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hCDread : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))))
    (hCDlen : ∀ ψ, (ds ψ).length = nP + nF)
    (hCDbelow : ∀ ψ, DomsBelow 0 (ds ψ))
    (hleq : ∀ i, i < nF → isProp = false → Level.leq (sorts.getD i .zero) resSort = some true)
    -- the member's leaf is the block's fixed-point leaf at its component
    {k m : Nat}
    {ufOf : (Name → Nat) → Nat → Nat} {IdssOf : (Name → Nat) → Nat → List AnnotTerm}
    {ChsOf : (Name → Nat) → Nat → List (List AnnotTerm)}
    (hleafT : ∀ ψ, mp.base2.acval T ψ
      = blockTyG k (resSort.eval ψ) (ufOf ψ) (IdssOf ψ) (ChsOf ψ) (pps ψ) m)
    (hleafC : ∀ ψ, mp.base2.acval cvCa.name ψ
      = sumMkAV (resSort.eval ψ) 0 (ds ψ) (((ds ψ).drop nP).map (·.2.2))
          (uChains [((ds ψ).drop nP).map (·.2.2)]))
    -- the member's fold at no index and one constructor (the caller's
    -- `blockFoldSingle`: the fold is a statement about the leaf TERM,
    -- so it crosses the tables' conses where the constructors' data
    -- does not)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ
          (blockTyG k (resSort.eval ψ) (ufOf ψ) (IdssOf ψ) (ChsOf ψ) (pps ψ) m))
        = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList ts ρ)
            [((ds ψ).drop nP).map (·.2.2) ++ [idxEqAV []]]))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (hboundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        isProp = false → FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)))
    (hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    ∃ (tbl : ProjTable) (mp' : EnvModelM V μ envOut),
      envOut = ⟨.projInfo tbl :: env.consts⟩ ∧ tbl.structName = T ∧
      env.find? (ConstantInfo.projInfo tbl).name = none ∧
      mp'.base2.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name
        (fun _ => .sort 0) := by
  exact stageFixTable mp hTbl hfT hcaps hlpsT hfC hlpsC hstripC hProp hTshape hCshape
    hresT hresR hresC hnp hFD hCDread hCDlen hCDbelow hleq hleafT hleafC
    (fun _ => ⟨_, rfl⟩) hfold hiff hfields hboundP hsortsF

end ConLeche.Model
