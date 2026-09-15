module

public import ConLeche.Model.Inductives.PsiRun
import ConLeche.Model.IndRepToolkit
import ConLeche.Verify.Inductives.NestedCopyStored
public section

/-!
# The DIRECT nested route at the run — step 1: the containers' map action (task #314 DR-1)

DESIGN §DR.1 (a), step 1.  The direct route builds a nested block's
carrier as the least fixed point of the COMPOSED operator — the block's
functor with the containers' leaves at the pins' readings in the nested
slots — and the one fact it needs of a container beyond its datum is
the map action in the PARAMETER: the container's functor at a frame is
below its functor at a frame that is pointwise larger at the pinned
slots.  This is `IndRepData.ParamMono` — the semantic content of the
kernel record K.26 (§DR.1 (b)) at the container's datum, NAMED here
and consumed by `pinParamMono_of_run`: for every pin of a nested run,
its container (`containerInfo?` at the pre-block environment, from
`nestedContainersOk`) has a datum (`ContainersRep` at the PRE-BLOCK
model, `ContainersRepPre` — the direct route never models the scratch
environment), and
`ParamMono` at the pin's slots gives the carrier-level inclusion at
every member of the container's group, at every fitting frame
(`IndRep.leaf_mono`).  Step 2 (`MonoFam` of the composed functor)
consumes that inclusion at the pins' readings once the composed
functor is spelled at the run (Milestone 1's (X)).

The discharge of `ParamMono` from K.26's syntactic verdict is
Milestone 1's reflection lemma; nothing here depends on the model
lane's ψ, `SectionAgree`, `CopyLeafEq` or the auxiliary block's model.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ElimState NestedPin ContainerInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

namespace IndRepData

variable (d : IndRepData V)

/-- **The map action in the parameter, at the functor level (NAMED —
the semantic content of K.26, DESIGN §DR.1 (b))**: at two fitting
frames that agree off the slots `ps` and are pointwise included at
`ps`, the index set is the same and the functor at the first frame is
below the functor at the second, at every family.  `ps` are FRAME
slots (`consList` puts the last parameter at slot `0`: parameter `p`
of an `nP`-parameter container is slot `nP - 1 - p`). -/
@[expose] def ParamMono (ps : List Nat) : Prop :=
  ∀ (ψ : Name → Nat) (ρp ρp' : Nat → V),
    Sat V (d.params ψ).reverse ρp → Sat V (d.params ψ).reverse ρp' →
    (∀ q, q ∉ ps → ρp q = ρp' q) → (∀ q ∈ ps, ρp q ⊆ˢ ρp' q) →
    d.idx ψ ρp = d.idx ψ ρp' ∧
    ∀ Y, Y ∈ˢ famSpace (d.w ψ) (d.idx ψ ρp) →
      FamLe (d.idx ψ ρp) (app (d.Φ ψ ρp) Y) (app (d.Φ ψ ρp') Y)

end IndRepData

/-- **Every container has a datum at the PRE-BLOCK model** — the direct
route's form of the model lane's `ContainersRep env envAux mpAux.base2`
(`PsiRun.lean`), with the same body at `envAux := env`: the route
never models the scratch environment, so the containers are read where
they were installed.  A named premise until the modeled route goes
(M-E), exactly as its sibling; exposed so that the milestones can
unfold it. -/
@[expose] def ContainersRepPre (env : Env) (m : EnvModel V env) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), ConLeche.containerInfo? env I = some ci →
    ∃ dJ : IndRepData V,
      dJ.ctorsC = [] ∧ dJ.kReal = dJ.k ∧ ci.nP = dJ.nP ∧ ci.members.length = dJ.k ∧
      (∀ (t : Nat) (φ : Name → Nat), dJ.pinsAV t φ = paramBvarsAt dJ.nP dJ.nP) ∧
      (∀ J, dJ.ksR J = dJ.ksF J ∧ dJ.tgtsR J = dJ.tgts J ∧ dJ.eissR J = dJ.eissF J ∧
        dJ.tssR J = dJ.tssF J) ∧
      (dJ.large = false → ∀ φ : Name → Nat, dJ.w φ = 0) ∧
      dJ.OrdNotRec ∧
      ContainerCtorsAt ci dJ ∧
      ∀ (i : Nat) (J : ConLeche.ContainerMember), ci.members[i]? = some J →
        ∃ (cvTJ cvR : ConstantVal) (capsJ : IndCaps) (mI rP : Nat) (rules : List RecRule),
          env.find? J.name = some (.indInfo cvTJ capsJ) ∧ J.type = cvTJ.type ∧
          J.lps = cvTJ.levelParams ∧ rules ≠ [] ∧
          env.find? cvR.name = some (.recInfo cvR mI rP rules) ∧
          (dJ.large = true → dJ.elim ∉ cvTJ.levelParams) ∧
          IndRep m J.name cvTJ cvR mI rP rules dJ i

/-- **The map action on the carrier, from the map action on the
functor**: `IndRep.leaf_mono` with its premises discharged from
`ParamMono` at the two frames. -/
theorem IndRep.leaf_mono_of_paramMono {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm) {ps : List Nat} (hpm : d.ParamMono ps)
    {ψ : Name → Nat} {ρ : Nat → V} {as as' : List V}
    (hsp : SpineFit ρ (d.params ψ) as) (hsp' : SpineFit ρ (d.params ψ) as')
    (hoff : ∀ q, q ∉ ps → consList as ρ q = consList as' ρ q)
    (hle : ∀ q ∈ ps, consList as ρ q ⊆ˢ consList as' ρ q)
    {is : List V} (hi : SpineFit (consList as ρ) (d.IdsM mm ψ) is)
    (hi' : SpineFit (consList as' ρ) (d.IdsM mm ψ) is) :
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      ⊆ˢ (as' ++ is).foldl app (interp V ρ (m.acval T ψ)) := by
  obtain ⟨hidx, hmono⟩ := hpm ψ _ _ (d.satOfSpine hsp) (d.satOfSpine hsp') hoff hle
  exact IndRep.leaf_mono h hsp hsp' hidx hmono hi hi'

/-- The frame slots of a pin's components that mention the block (a
member, or a copy minted so far): parameter position `i` of the pin's
argument list is frame slot `n - 1 - i`. -/
def pinnedSlots (members : List Name) (q : NestedPin) : List Nat :=
  let args := q.pin.getAppArgs
  ((List.range args.length).filter fun i =>
    match args[i]? with
    | some a => members.any (fun T => a.mentionsConst T) || a.mentionsNestedAux
    | none => false).map fun i => args.length - 1 - i

/-- **Step 1 at the run**: every pin of a nested run names a container
of the pre-block environment with a datum at the pre-block model, and
`ParamMono` of that datum at the pin's slots gives the carrier-level
inclusion at every member of the container's group and every fitting
frame.  The hypothesis `ParamMono` is the NAMED fact (K.26's semantic
content); its consumer is the implication in the conclusion. -/
theorem pinParamMono_of_run {μ : ConLeche.CheckMode} {F : Nat} {envOut : Env}
    {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (h : DeclNestedRun μ F env p envOut) (hrep : ContainersRepPre env mp.base2) :
    ∃ (st : ElimState) (b : MutualBlock) (fmsA ctorsA : List ConstantVal),
      ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st ∧
      ConLeche.auxBlock p st = some b ∧ st.pins.length = p.numNested ∧
      ∀ q ∈ st.pins, ∃ (ci : ContainerInfo) (dJ : IndRepData V),
        ConLeche.containerInfo? env q.container = some ci ∧
        dJ.ctorsC = [] ∧ dJ.kReal = dJ.k ∧ ci.nP = dJ.nP ∧ ci.members.length = dJ.k ∧
        (∀ (i : Nat) (J : ConLeche.ContainerMember), ci.members[i]? = some J →
          ∃ (cvTJ cvR : ConstantVal) (capsJ : IndCaps) (mI rP : Nat) (rules : List RecRule),
            env.find? J.name = some (.indInfo cvTJ capsJ) ∧
            IndRep mp.base2 J.name cvTJ cvR mI rP rules dJ i) ∧
        (dJ.ParamMono (pinnedSlots p.memberNames q) →
          ∀ (i : Nat) (J : ConLeche.ContainerMember), ci.members[i]? = some J →
          ∀ (ψ : Name → Nat) (ρ : Nat → V) (as as' is : List V),
            SpineFit ρ (dJ.params ψ) as → SpineFit ρ (dJ.params ψ) as' →
            (∀ s, s ∉ pinnedSlots p.memberNames q → consList as ρ s = consList as' ρ s) →
            (∀ s ∈ pinnedSlots p.memberNames q, consList as ρ s ⊆ˢ consList as' ρ s) →
            SpineFit (consList as ρ) (dJ.IdsM i ψ) is →
            SpineFit (consList as' ρ) (dJ.IdsM i ψ) is →
            (as ++ is).foldl app (interp V ρ (mp.base2.acval J.name ψ))
              ⊆ˢ (as' ++ is).foldl app (interp V ρ (mp.base2.acval J.name ψ))) := by
  obtain ⟨-, -, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA, order,
    -, -, helim, hlen, -, hcont, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  refine ⟨st, b, fmsA, ctorsA, helim, hb, hlen, fun q hq => ?_⟩
  obtain ⟨-, hci⟩ := ConLeche.nestedContainersOk_inv' hcont
  obtain ⟨ci, hci, -⟩ := hci q hq
  obtain ⟨dJ, hcC, hkR, hnP, hlenM, -, -, -, -, -, hmem⟩ := hrep q.container ci hci
  refine ⟨ci, dJ, hci, hcC, hkR, hnP, hlenM, fun i J hJ => ?_, fun hpm i J hJ => ?_⟩
  · obtain ⟨cvTJ, cvR, capsJ, mI, rP, rules, hfind, -, -, -, -, -, hrep⟩ := hmem i J hJ
    exact ⟨cvTJ, cvR, capsJ, mI, rP, rules, hfind, hrep⟩
  · intro ψ ρ as as' is hsp hsp' hoff hle hi hi'
    obtain ⟨cvTJ, cvR, capsJ, mI, rP, rules, -, -, -, -, -, -, hrep⟩ := hmem i J hJ
    exact IndRep.leaf_mono_of_paramMono hrep hpm hsp hsp' hoff hle hi hi'

end ConLeche.Model
