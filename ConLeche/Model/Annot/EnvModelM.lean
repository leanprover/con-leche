module

public import ConLeche.Model.Annot.Laws
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitClosed
public import ConLeche.Semantics.EnvFacts
public import ConLeche.Model.Annot.BlockLfp
public import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.VClosed

public section

/-!
# `EnvModelM` — the P-tier environment invariant (task #161, P4)

The install tier's target, per the P4 design note in DESIGN.md: the
environment carrier (`EnvModel`) *contained*, plus the fields the P
bundles read.

**The laws the fields are stated over live in `Model/Annot/Laws.lean`**
(`NatOps`, `DivMod`, `EqLaw`, `ReduceOps`, the caps kit, the iota kit
and the tower kit), so that the rules tier's inputs can name them
without importing the establishment surface below.  This file keeps the
structure, its namespace, the empty model, and the `Nat`-op guard law
the literal tier reads.

The fields, each a payoff of the fuel-free reading:

* **existence, not uniqueness** — `defn_reads` is `AcvalDefnInst`: a
  stored definition's or theorem's value *reads*, to the constant's own
  leaf; `denoteMeta` has no fuel, and a checked value is never out of
  fragment.
* **the stored types read, are graded, and are inhabited** —
  `type_reads`/`type_wellDenotedV`/`mem_type`, at the *uninstantiated* type
  over every ground assignment; `denotePInstLevels` (an equality)
  delivers every instantiated form, so no arity or fuel bookkeeping
  appears anywhere.
* **the leaves are bit-valid** — `acval_validV`, `acval_wellDenoted`'s
  `AnnotValid` companion; establishment at install is the P2 front
  door's own validation, transported by the claims.

The bundle-supplying layer below (`constType` the worked example; its
siblings follow the same three-field read) is what the quarter
induction consumes — the structure exists so that a `Nonempty (EnvModelM …)` carried through the declaration fold
makes the induction's hypotheses *facts*.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName RecRule)

universe w

variable (V : Type w) [SetTheory V]

/-- **A recorded block is stored**: its members are stored inductive
formers and its constructors stored constructors — which is what lets every extension transport the
clause, whose `leaf` and `ctor` read the leaf valuation at those names
(an extension never re-reads a stored name). -/
@[expose] def LfpStored {V : Type w} [SetTheory V] (env : Env) (D : LfpDatum V) : Prop :=
  (∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps)) ∧
  ∀ c, c < D.N → ∀ j, j < D.nctors c →
    ∃ cv nP nF, env.find? (D.ctorName c j) = some (.ctorInfo cv nP nF)

/-- **A recorded block's formers read as its hole telescopes** (M4):
member `mm`'s stored type reads, at every level
assignment, as the Π-tower over its own parameters and indices (the
binders of its hole value, `LfpDatum.holeVal`) ending in the block's
sort, every binder in the graph regime.  What makes a container's frame
hole — the hole value at the container's instantiation — inhabit the
container's type (the walk's context), and a group-mate's former agree
with its hole value applied to the frame's parameters. -/
@[expose] def LfpReads {V : Type w} [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (D : LfpDatum V) : Prop :=
  ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
    ∀ ψ : Name → Nat, ∃ ab : List (Nat × Nat × AnnotTerm),
      denoteMeta acval env ψ 0 cv.type = some (mkPisAV ab (.sort (D.w ψ))) ∧
      ab.map (·.2.2) = D.pars mm ψ ++ D.ids mm ψ ∧ ∀ d ∈ ab, d.2.1 ≠ 0

/-! ### The recorded constructor readings (M2)

A container frame (`nestCtors`) walks a stored constructor type with its
group's members replaced by the frame's holes and its parameters
instantiated.  The record reads the same type at a CANONICAL abstraction
— parameter `i` the variable `i`, member `m` the variable `nP + m`, every
annotation `Sort 0` (`nestAbstract` reads only names and levels, the
reading ignores fvar annotations) — as the Π-tower over the clause's
fields with holes, ending in the member's hole at the parameters and the
result index readings.  The container substitution law
(`frameCrest_read`, `Model/Inductives/ContSubst.lean`) turns that reading
into the frame's. -/

/-- The canonical parameter variables `0 ..< nP`. -/
@[expose] def canonParams (nP : Nat) : List Expr :=
  (List.range nP).map fun i => .fvar i (.sort .zero)

/-- The canonical member holes `nP ..< nP + k`. -/
@[expose] def canonHoles (nP k : Nat) : List Expr :=
  (List.range k).map fun mm => .fvar (nP + mm) (.sort .zero)

/-- The canonical abstraction context: only `names`, `lps` (read by
`nestAbstract`), `nP` and `params` matter. -/
@[expose] def canonCtx (names lps : List Name) (nP : Nat) : ConLeche.NestCtx where
  names := names
  lps := lps
  nP := nP
  nIdxs := []
  params := canonParams nP
  sort := .zero
  find? := fun _ => none

/-- A stored constructor type, member-abstracted at the canonical holes. -/
@[expose] def canonAbs (names lps : List Name) (nP k : Nat) (e : Expr) : Expr :=
  ConLeche.nestAbstract (canonCtx names lps nP) (canonHoles nP k) e

/-- **A recorded block's constructors read as their hole telescopes**
(M2): member `c`'s constructor
`j` is stored, closed, at the members' level parameters; its
member-abstracted type mentions no member constant (M2′, from the kernel's
`nestUniform`); and its canonical instantiation reads, at depth
`nP + k` and every level assignment, as a Π-tower ending in member `c`'s
hole applied to the parameters and the result index readings, whose
fields read like the clause's fields with holes at every frame
satisfying the hole context (the parameters, then each member's former
type, `Tys`).  The stored type is the DECLARED one; the fields with holes
are the positivity walk's normal form's, which reads like it there.

**The constructor's parameters are the block's.**  The stored type reads, at every level assignment, as a
Π-tower whose first `nPc` binders are satisfied wherever the block's
parameter telescope is.  It is the install's constructor check (the
constructors' frames, `ctorFramesGen`: the constructor's parameter
domains are definitionally the former's) and official's
(`check_constructors`: "arg #i of 'c' does not match inductive
datatype parameters", `inductive.cpp`).  An outside class's rule
certificates read it: the instantiated constructor's field domains are
graded because the parameters' readings fit the constructor's own
parameter binders. -/
@[expose] def LfpCtorReads {V : Type w} [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (D : LfpDatum V) : Prop :=
  D.names.length = D.k ∧
  ∀ c, c < D.k → ∀ j, j < D.nctors c → ∃ cv nPc nF,
    env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF) ∧
    cv.type.hasFvar = false ∧
    (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      cvm.levelParams = cv.levelParams) ∧
    (canonAbs D.names cv.levelParams nPc D.k cv.type).nestOcc D.names 0 0 = false ∧
    (∀ (ψ : Name → Nat) (dsC : List (Nat × Nat × AnnotTerm)) (bodyC : AnnotTerm),
      denoteMeta acval env ψ 0 cv.type = some (mkPisAV dsC bodyC) → nPc ≤ dsC.length →
      ∀ ρ : Nat → V, Sat V (D.params ψ).reverse ρ →
        Sat V ((dsC.take nPc).map (·.2.2)).reverse ρ) ∧
    ∃ A, ConLeche.instPisWith (canonParams nPc) (canonAbs D.names cv.levelParams nPc D.k cv.type)
        = some A ∧
      ∀ ψ : Name → Nat, (D.params ψ).length = nPc ∧ (D.fields ψ c j).length = nF ∧
        ∃ (ab : List (Nat × Nat × AnnotTerm)) (Tys : List AnnotTerm),
          denoteMeta acval env ψ (nPc + D.k) A
            = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
                ((List.range nPc).map (fun i => AnnotTerm.bvar (nPc + D.k + nF - 1 - i))
                  ++ D.resIdx ψ c j))) ∧
          ab.length = nF ∧ Tys.length = D.k ∧
          (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
            denoteMeta acval env ψ 0 cvm.type = some (Tys.getD mm default)) ∧
          FieldsEqOn V (D.params ψ ++ Tys).reverse (ab.map (·.2.2)) (D.fields ψ c j)

/-- **The P-tier environment invariant, at one mode** (see the module
docstring). -/
structure EnvModelM (μ : CheckMode) (env : Env) where
  /-- the environment carrier, contained -/
  base2 : EnvModel V env
  /-- every leaf is bit-valid (`acval_wellDenoted`'s `AnnotValid` half) -/
  acval_validV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValid V ρ (base2.acval n ψ)
  /-- every stored type reads, at every ground assignment -/
  type_reads : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ ta : AnnotTerm,
      denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta
  /-- the stored types' readings are graded -/
  type_wellDenotedV : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AnnotTerm),
    denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, WellDenotedV V ρ ta
  /-- stored constants inhabit their types' readings (a projection
  table's constant type is the closed dummy `Sort 1` and its leaf is
  `Sort 0`, so the row holds of tables too; that a table is not a term
  is `inferTypeCore`'s own rejection of a `.const` naming one) -/
  mem_type : ∀ c ∈ env.consts,
    ∀ (ψ : Name → Nat) (ta : AnnotTerm),
    denoteMeta base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V,
      interp V ρ (base2.acval c.name ψ) ∈ˢ interp V ρ ta
  /-- stored definition and theorem values read, to the constant's own
  leaf (existence) -/
  defn_reads : AcvalDefnInst base2
  /-- the two `Nat`-literal head facts, at every assignment -/
  nat_heads : ∀ φ : Name → Nat, NatHeads base2 φ
  /-- the structural-`Nat` recurrence laws at every assignment (the
  literal tier's supplier; established at the operations' own installs
  from the recorded runs — `Model/NatEqs.lean`) -/
  nat_ops : ∀ φ : Name → Nat, NatOps base2 φ
  /-- the pin-certified WF operations' guarded clauses at every
  assignment (the literal tier's other supplier; established at the
  operations' own installs from the recorded certificate runs —
  `Model/DivModCert.lean`) -/
  div_mod : ∀ φ : Name → Nat, DivMod base2 φ
  /-- the pinned `Eq` spine's value and grading (an *environment law*:
  the `Eq` leaf is fixed by the basis install and
  by nothing else, so the supplier is the P basis install —
  `BasisStepPB`, routed.  Consumed by the WF operations' certificate
  frame) -/
  eq_law : EqLaw base2
  /-- the stored families' fired capability laws (an *environment law* for the same reason `eq_law` is — an
  η-capable family's leaf value is fixed by the inductive install and
  by nothing else, so the supplier is the inductive install).  Consumed
  by the structure-η and unit-like rules' soundness
  (`Model/Rules/DefEqSound.lean`, through `RulesInputs.caps_ok`) -/
  caps_ok : CapsOk base2
  /-- the stored recursors' fired modeled-iota contracts (an
  *environment law* for the same reason `caps_ok` is — a
  recursor's rules are fixed by the inductive install and by nothing
  else, so the supplier is the inductive install).  Consumed by the ι rule's
  soundness (`Model/Rules/IotaSound.lean`, through
  `RulesInputs.rec_rules`) -/
  rec_rules : ∀ φ : Name → Nat, RecRules base2 φ
  /-- every stored compiler-trust opaque is the identity on its
  element type (an *environment law* for
  the same reason `eq_law` is — the opaque's leaf is fixed by its own
  install's identity certificate and by nothing else, so the supplier
  is `harvestOpaque`.  Consumed by the `ofReduce*` axiom branch) -/
  reduce_ops : ReduceOps base2
  /-- the stored tower-backed projection entries' typing and iota
  laws (an *environment law* for the same reason
  `rec_rules` is — a direct structure's entries are fixed by its
  install and by nothing else, so the supplier is the direct install
  step.  Consumed by the `.proj` rows' tower branches) -/
  tower_ok : ∀ φ : Name → Nat, TowerOk base2 φ
  /-- **the recorded blocks**: the lfp data of the
  inductive blocks whose lfp clause this carrier records — a ghost
  list, filled by the uniform block install at its constructors'
  environment (`declBlock`, `EnvModelM.addLfp`) and copied by every
  other extension -/
  lfpBlocks : List (LfpDatum V)
  /-- **the lfp clause of every recorded block** (`Annot/BlockLfp.lean`):
  its members' denotations are the least fixed point of its operator,
  whose fibres are the constructors' injections; and its members are
  stored inductive formers (which is what lets every extension
  transport the clause: an extension never re-reads a stored name) -/
  lfp_ok : ∀ D ∈ lfpBlocks, LfpClause base2.acval D ∧ LfpStored env D ∧
    LfpReads base2.acval env D ∧ LfpCtorReads base2.acval env D

namespace EnvModelM

variable {V}
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The leaf bit-validity residue, read off the field. -/
theorem acvalValid (m : EnvModelM V μ env) : AcvalValid m.base2 :=
  m.acval_validV

/-- **The `const` residue, derived — the worked example of the
bundle-supplying layer.**  The three type fields at the composed
assignment `Level.substFn φ ks us`, carried to the instantiated form
by `denotePInstLevels` (an equality: no arity premise, no fuel). -/
theorem constType (m : EnvModelM V μ env) : ConstType m.base2 φ := by
  intro d n ci us hf _hnt hlen
  have hmem := ConLeche.Semantics.Env.find?_mem hf
  have hname := ConLeche.Semantics.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.wf ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denoteMeta_closed m.base2.acval_erase m.base2.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth :
      denoteMeta m.base2.acval env
          (Level.substFn φ ci.toConstantVal.levelParams us) d
          ci.toConstantVal.type = some ta :=
    denoteMeta_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  -- the instantiated type's reading, by the crossing
  have hcross :
      denoteMeta m.base2.acval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us)
        = denoteMeta m.base2.acval env
            (Level.substFn φ ci.toConstantVal.levelParams us) d
            ci.toConstantVal.type :=
    denotePInstLevels m.base2 φ ci.toConstantVal.levelParams us d
      ci.toConstantVal.type
  refine ⟨ta, ?_, m.type_wellDenotedV ci hmem _ ta hta, ?_⟩
  · rw [hcross]; exact hdepth
  · have := m.mem_type ci hmem _ ta hta
    rwa [hname] at this

/-- **The bridge invariant, from the P invariant**.  Every field is a
projection:

| `EnvFacts` field | source |
|---|---|
| `cval`, `cval_closed`, `wf`, `proj_ok` | `base2`'s own |
| `val_params` | `acval_params`, erased |
| `ty_denotes` | `type_reads` through `denoteMeta_erase` |
| `defn_eq` | `defn_reads` through `denoteMeta_erase` (definitions only: a theorem is opaque to reduction, and the invariant keeps no equation for its value) |
| `rec_rhs_denotes`, `rec_params_le` | `rec_rules`' `RecRuleLaw`, whose first two components are exactly those two facts |
| `nat_op_guard` | `nat_ops`/`div_mod` through `natOpStored_inv` |
-/
def toEnvFacts {V : Type w} [SetTheory V] {μ : CheckMode}
    {env : Env} (m : EnvModelM V μ env) : ConLeche.Semantics.EnvFacts env where
  cval := m.base2.cvalE
  cval_closed := m.base2.cval_closed
  wf := m.base2.wf
  val_params := fun n ci hf φ₁ φ₂ hp =>
    congrArg AnnotTerm.erase (m.base2.acval_params n ci hf φ₁ φ₂ hp)
  ty_denotes := fun c hc ψ => by
    obtain ⟨ta, hta⟩ := m.type_reads c hc ψ
    exact ⟨ta.erase,
      denoteMeta_erase m.base2.acval_erase 0 c.toConstantVal.type hta⟩
  defn_eq := fun cv value hint hmem ψ =>
    denoteMeta_erase m.base2.acval_erase 0 value
      (m.defn_reads ψ cv value ⟨hint, hmem⟩)
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hus⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨Ra, hRa, -, -⟩ := hus us hlen
    exact ⟨Ra.erase, denoteMeta_erase m.base2.acval_erase 0 _ hRa⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.base2.proj_ok
  nat_op_guard := fun c hmem hst => by
    obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
    rcases hmem with hm | hm
    · exact (m.nat_ops (fun _ => 0) c hm cv v hh hf).1
    · exact (m.div_mod (fun _ => 0) c hm cv v hh hf).1

end EnvModelM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false, and the empty leaf
`.const .empty [0]` is bit-valid because a constant leaf carries no
binder. -/
@[expose] noncomputable def EnvModelM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvModelM V μ Env.empty where
  base2 := EnvModel.empty
  acval_validV := fun _ _ _ => by
    show AnnotValid V _ (.const .empty [0])
    simp
  type_reads := fun c hc => nomatch hc
  type_wellDenotedV := fun c hc => nomatch hc
  mem_type := fun c hc => nomatch hc
  defn_reads := fun ψ cv value hmem => by
    obtain ⟨hint, hdt⟩ := hmem
    exact nomatch hdt
  nat_heads := fun φ hg => by
    rw [show ConLeche.natLitSupported Env.empty = false from rfl] at hg
    exact nomatch hg
  nat_ops := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  div_mod := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  eq_law := fun hf => by
    rw [show Env.empty.find? eqName = none from rfl] at hf
    exact nomatch hf
  caps_ok := by
    refine ⟨fun T cvT caps hf => ?_, fun T cvT caps hf => ?_⟩ <;>
      · rw [show Env.empty.find? T = none from rfl] at hf
        exact nomatch hf
  rec_rules := fun _ n _ _ _ _ hf => by
    rw [show Env.empty.find? n = none from rfl] at hf
    exact nomatch hf
  reduce_ops := fun c _ cv hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  tower_ok := fun _ T i entry hf => by
    have : Env.empty.findProj? T i = none := rfl
    rw [this] at hf
    exact nomatch hf
  lfpBlocks := []
  lfp_ok := fun _ hD => nomatch hD

/-! ## The recorded lfp clauses -/

namespace EnvModelM

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **Record a block's lfp clause** — the block install's production
step (`declBlock`, at the constructors' environment).  Everything but
the recorded list is unchanged, so `(mp.addLfp …).base2 = mp.base2`
definitionally. -/
@[expose] def addLfp (mp : EnvModelM V μ env) (D : LfpDatum V)
    (hL : LfpClause mp.base2.acval D) (hst : LfpStored env D)
    (hrd : LfpReads mp.base2.acval env D) (hrdC : LfpCtorReads mp.base2.acval env D) :
    EnvModelM V μ env :=
  { mp with
    lfpBlocks := D :: mp.lfpBlocks
    lfp_ok := fun D' hD' => by
      rcases List.mem_cons.mp hD' with rfl | h
      · exact ⟨hL, hst, hrd, hrdC⟩
      · exact mp.lfp_ok D' h }


theorem mem_addLfp (mp : EnvModelM V μ env) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC) :
    D ∈ (mp.addLfp D hL hst hrd hrdC).lfpBlocks := List.mem_cons_self

/-- A recorded block's clause, read off the carrier. -/
theorem lfpClause_of_mem (mp : EnvModelM V μ env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) :
    LfpClause mp.base2.acval D :=
  (mp.lfp_ok D hD).1

/-- **The recorded clauses cross an environment extension** that keeps
every stored inductive former and its leaf, and every successful reading
of a stored former's type — the transport every construction site of
the invariant (the cons funnel, the rule-list swap) instantiates. -/
theorem lfp_ok_transport (mp : EnvModelM V μ env) {env' : Env}
    {acval' : Name → (Name → Nat) → AnnotTerm}
    (hfind : ∀ n ci, env.find? n = some ci → (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env'.find? n = some ci)
    (hag : ∀ n ci, env.find? n = some ci → (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      acval' n = mp.base2.acval n)
    (hread : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → ∀ (ψ : Name → Nat)
      (ta : AnnotTerm), denoteMeta mp.base2.acval env ψ 0 cv.type = some ta →
      denoteMeta acval' env' ψ 0 cv.type = some ta)
    (hreadT : ∀ n cv nPc nF, env.find? n = some (.ctorInfo cv nPc nF) → ∀ (ψ : Name → Nat)
      (ta : AnnotTerm), denoteMeta mp.base2.acval env ψ 0 cv.type = some ta →
      denoteMeta acval' env' ψ 0 cv.type = some ta)
    (hreadC : ∀ n cv nPc nF, env.find? n = some (.ctorInfo cv nPc nF) →
      ∀ (names : List Name) (k : Nat) (A : Expr),
      ConLeche.instPisWith (canonParams nPc) (canonAbs names cv.levelParams nPc k cv.type)
        = some A →
      ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval env ψ (nPc + k) A = some ta →
      denoteMeta acval' env' ψ (nPc + k) A = some ta) :
    ∀ D ∈ mp.lfpBlocks, LfpClause acval' D ∧ LfpStored env' D ∧ LfpReads acval' env' D ∧
      LfpCtorReads acval' env' D := by
  intro D hD
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, hnk, hrdC⟩ := mp.lfp_ok D hD
  refine ⟨hL.congr (fun mm hmm => ?_) (fun c hc j hj => ?_),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, hnk, fun c hc j hj => ?_⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact hag _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact hag _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, hfind _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, hfind _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · obtain ⟨cv, caps, hf, hab⟩ := hrd mm hmm
    refine ⟨cv, caps, hfind _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h, fun ψ => ?_⟩
    obtain ⟨ab, hta, h1, h2⟩ := hab ψ
    exact ⟨ab, hread _ _ _ hf ψ _ hta, h1, h2⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hocc, hpars, A, hA, hrdA⟩ := hrdC c hc j hj
    refine ⟨cv, nPc, nF, hfind _ _ hf fun _ _ _ _ h => ConstantInfo.noConfusion h, hcf,
      fun mm hmm => ?_, hocc, fun ψ dsC bodyC hrd' hle => ?_, A, hA, fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      exact ⟨cvm, caps, hfind _ _ hfm fun _ _ _ _ h => ConstantInfo.noConfusion h, hl⟩
    · -- the new reading is the old one (the old one exists, and crosses)
      obtain ⟨ta, hta⟩ := mp.type_reads _ (List.mem_of_find?_eq_some hf) ψ
      change denoteMeta mp.base2.acval env ψ 0 cv.type = some ta at hta
      have hta' := hreadT _ _ _ _ hf ψ _ hta
      rw [hrd'] at hta'
      obtain rfl := Option.some.inj hta'
      exact hpars ψ dsC bodyC hta hle
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, hreadC _ _ _ _ hf _ _ _ hA ψ _ hta, hlab, hlT, fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, hfm, hr⟩ := hTys mm hmm
      exact ⟨cvm, caps, hfind _ _ hfm fun _ _ _ _ h => ConstantInfo.noConfusion h,
        hread _ _ _ hfm ψ _ hr⟩

end EnvModelM

/-! ## The `Nat`-op guard law -/

section
variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The install fold's `Nat`-op invariant, in the form the literal
tier reads it**.  `reduceNat` tests `natOpStored` — one `Env.find?`;
the guard is what
the leaf analysis below needs (`natLitSupported` for the numeral
shapes, the two `Bool` constructors for the comparison shapes), and it
is carried by `NatOps`/`DivMod`, whose statement is exactly "stored
as a `defnInfo` → guard ∧ the recurrences".  So the tier reads the
guard off the environment. -/
@[expose] def NatOpGuardLaw (env : Env) : Prop :=
  ∀ c, (c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames) →
    ConLeche.natOpStored env c = true → ConLeche.natOpGuard env c = true

/-- `EnvModelM` supplies it, from `nat_ops` and `div_mod`. -/
theorem natOpGuardLaw_of (mp : EnvModelM V μ env) : NatOpGuardLaw env := by
  intro c hmem hst
  obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
  rcases hmem with hm | hm
  · exact (mp.nat_ops (fun _ => 0) c hm cv v hh hf).1
  · exact (mp.div_mod (fun _ => 0) c hm cv v hh hf).1

end

end ConLeche.Model
