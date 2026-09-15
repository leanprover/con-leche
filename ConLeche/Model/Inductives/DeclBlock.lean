module

public import ConLeche.Semantics.Inductives.DeclMutual
public import ConLeche.Model.Inductives.BlockRecWD
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Verify.Inductives.SumRec
public section

/-!
# `declBlock` — the model survives a mutual block (task #315, M4)

**THE run-level consumer of M4**: the model of the pre-block
environment survives the mutual install's run (`DeclMutualRun`,
`Semantics/Inductives/DeclMutual.lean`).  Its proof is the run's stage
decomposition: stages 0–4 (the shape, the formers, the cross-member
checks, the constructors with their kinds, the recursors with their
rules) keep the model and leave THE DATUM (`BlockRepData`, DESIGN
§U.3) at every member of the recursors' environment
(`MutualCoreModeled`); stage 5 (the projection tables of the
structure-like members) keeps it from there (`MutualTablesModeled`).
The two are the named facts of this consumer (DESIGN §U.6): M4's
sessions discharge them — the core through `blockRecsAt`
(`BlockRecWD.lean`, the recursors closed modulo the run facts) and
the generic member conses (`IndCons.lean`), the tables through the
fixpoint route's table stage at the member's leaf.

The regime fact `w = 0 → ℓ = 0` (§U.4 (a)) is the kernel's
`b.large = f₀.s.isNeverZero` at stage 2, read off here
(`elimLevel_zero_of_w_zero`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  MutualParts MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4 fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The regime fact -/

/-- **`w = 0 → ℓ = 0` at a mutual block**: the eliminator's level is
`Prop` unless the block's sort is provably nonzero — the kernel's
`b.large = f₀.s.isNeverZero` (stage 2), the fact `blockCand_mem` and
`blockCand_eq` consume. -/
theorem elimLevel_zero_of_w_zero {elim : Name} {large : Bool} {s : Level}
    (hL : large = s.isNeverZero) (ψ : Name → Nat) (hw : s.eval ψ = 0) :
    (ConLeche.structElimLevel elim large).eval ψ = 0 := by
  unfold ConLeche.structElimLevel
  cases hl : large with
  | false => rfl
  | true =>
    exfalso
    rw [hl] at hL
    exact ConLeche.Level.isNeverZero_sound ψ s hL.symm hw

/-! ## The datum of a run -/

/-- **The datum is the run's block**: its arities, names, sort and
constructors are the block record's and the stages' outputs. -/
structure MutualDatumOf (env : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (d : BlockRepData V) : Prop where
  k : d.k = b.k
  nP : d.nP = b.nP
  env₀ : d.env₀ = env
  memberNames : d.memberNames = fms.map (·.cvTa.name)
  nIdxs : d.nIdxs = fms.map (·.nIdx)
  resSort : d.resSort = (fms.getD 0 default).s
  large : d.large = b.large
  ctors : ∀ t, t < b.k → d.ctorsM t = (b.ownCtors t).map fun q => ctorsA.getD q.1 default

/-! ## The named facts -/

/-- **Stages 0–4 keep the model and leave the datum at the recursors'
environment** — `declBlock`'s first named fact (M4 sessions 2–3): from
a model of the pre-block environment and the run of stages 0–4, a
model of the environment holding the formers, the constructors and
the recursors with their rules, at which the block's datum holds at
every member (`BlockReps`), with the members and constructors typed
(`FormersTyped`, `CtorsTyped`), and every other leaf the pre-block
model's.  Consumer: `declBlock`. -/
@[expose] def MutualCoreModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (b : MutualBlock) (streamRecs : Option (List (ConstantVal × List RecRule)))
    (env₁ : Env) (fms : List MutualFormerA) (f₀ : MutualFormerA) (tq₀ : List Expr × Expr)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List (RecFieldKind × Nat))) (formers4 : List MutualFormer)
    (ctors4 : List MutualCtor4) (cvRas : List ConstantVal)
    (rulesOf : List (List (MutualCtor × Expr))),
    b.blockNames.Nodup →
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true →
    b.ctors.all (fun c => c.member < b.k) = true →
    ConLeche.mutualCtorsGrouped b.ctors = true →
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (env₁, fms) →
    fms[0]? = some f₀ →
    ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀ →
    ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (fueledOps μ F) env₁ b.nP f₀
      (tq₀.1.map Expr.fvarTypeD) fms = .ok () →
    b.large = f₀.s.isNeverZero →
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ b fms
      (Level.isEquiv f₀.s .zero == some true) b.ctors = .ok (ctorsA, sortss) →
    ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds →
    ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true →
    ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4) →
    ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA env₁) b formers4 ctors4 streamRecs b.k
      = .ok cvRas →
    ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA env₁))
      b formers4 ctors4 streamRecs b.k = .ok rulesOf →
    ∃ mp₃ : EnvModelM V μ
        (ConLeche.storeMutualRecs (ConLeche.consMutualCtors b.nP ctorsA env₁) b fms rulesOf
          cvRas.zipIdx (ConLeche.consMutualCtors b.nP ctorsA env₁)),
      (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₃.base2.acval n ψ = mp.base2.acval n ψ) ∧
      ∃ d : BlockRepData V, MutualDatumOf env b fms ctorsA d ∧ BlockReps mp₃.base2 d ∧
        ∀ ψ : Name → Nat, FormersTyped mp₃.base2 d ψ ∧ CtorsTyped mp₃.base2 d ψ

/-- **Stage 5 keeps the model**: at a model of the recursors'
environment carrying the datum, the structure-like members' projection
tables cons a model of the post-block environment — `declBlock`'s
second named fact (M4 session 4).  Consumer: `declBlock`. -/
@[expose] def MutualTablesModeled (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env env₃ envOut : Env} (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (mp₃ : EnvModelM V μ env₃) (d : BlockRepData V),
    MutualDatumOf env b fms ctorsA d → BlockReps mp₃.base2 d →
    (∀ ψ : Name → Nat, FormersTyped mp₃.base2 d ψ ∧ CtorsTyped mp₃.base2 d ψ) →
    ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss fms.zipIdx env₃ = .ok envOut →
    Nonempty (EnvModelM V μ envOut)

/-! ## The consumer -/

/-- **The model survives a mutual block** (M4's run-level consumer):
the run's stages 0–4 keep the model and leave the datum
(`MutualCoreModeled`), the tables keep it from there
(`MutualTablesModeled`). -/
theorem declBlock (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : MutualParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hcore : MutualCoreModeled V μ F) (htables : MutualTablesModeled V μ)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) := by
  obtain ⟨-, b, streamRecs, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, rfl, rfl, h0, h1, h2, h3, hformers, hf₀, htq₀, hcross, hL, hctors, hkinds,
    hfo, hgd, hrectys, hrules, htbl⟩ := h
  obtain ⟨mp₃, -, d, hd, hreps, hT⟩ := hcore hμ mp hE _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3
    hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd hrectys hrules
  exact htables hμ _ _ _ sortss mp₃ d hd hreps hT htbl

end ConLeche.Model
