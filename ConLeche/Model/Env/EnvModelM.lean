module

public import ConLeche.Model.Env.Laws
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.Closed
public import ConLeche.Semantics.EnvFacts
public import ConLeche.Model.Env.BlockLfp
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

**The laws the fields are stated over live in `Model/Env/Laws.lean`**
(`NatOps`, `DivMod`, `EqLaw`, `ReduceOps`, the caps kit, the iota kit
and the tower kit), so that the rules tier's inputs can name them
without importing the establishment surface below.  This file keeps the
structure, its namespace, the empty model, and the `Nat`-op guard law
the literal tier reads.

The fields, each a payoff of the fuel-free reading:

* **existence, not uniqueness** — `defn_reads` is `AcvalDefnInst`: a
  stored definition's or theorem's value *reads*, to the constant's own
  leaf; `denote` has no fuel, and a checked value is never out of
  fragment.
* **the stored types read, are graded types, and are inhabited** —
  `type_reads`/`type_wellDenotedTy`/`mem_type`, at the *uninstantiated* type
  over every ground assignment; `denotePInstLevels` (an equality)
  delivers every instantiated form, so no arity or fuel bookkeeping
  appears anywhere.

The bundle-supplying layer below (`constType` the worked example; its
siblings follow the same three-field read) is what the quarter
induction consumes — the structure exists so that a `Nonempty (EnvModelM …)` carried through the declaration fold
makes the induction's hypotheses *facts*.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule)

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
sort.  What makes a container's frame
hole — the hole value at the container's instantiation — inhabit the
container's type (the walk's context), and a group-mate's former agree
with its hole value applied to the frame's parameters. -/
@[expose] def LfpReads {V : Type w} [SetTheory V] (acval : Name → (Name → Nat) → Term)
    (env : Env) (D : LfpDatum V) : Prop :=
  ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
    ∀ ψ : Name → Nat, ∃ ab : List Term,
      denote acval env ψ 0 cv.type = some (mkPisAV ab (.sort (D.w ψ))) ∧
      ab = D.pars mm ψ ++ D.ids mm ψ

/-! ### The recorded constructor readings (M2)

A container frame (`nestCtors`) walks a stored constructor type with its
group's WHOLE applications replaced by the frame's holes before its
parameters are instantiated: the canonical abstraction (`nestCanonCrest`:
parameter `i` the variable `i`, member `m`'s whole application the
variable `nP + m`, every annotation `Sort 0`), then the key's parameters
and the frame's holes put in.  The record reads the canonical abstraction
at the block's own levels as the Π-tower over the clause's fields with
holes; the container substitution law (`frameCrest_read`,
`Model/Inductives/ContSubst.lean`) turns that reading into the frame's. -/

/-- The canonical parameter variables `0 ..< nP` (the kernel's `nestPhs`). -/
@[expose] def canonParams (nP : Nat) : List Expr := ConLeche.nestPhs nP

/-- **A term the records read off a stored type**: its canonical
abstraction (`nestCanonCrest`), or its instantiation at the canonical
parameters (a member hole's type). -/
@[expose] def CanonOf (ty A : Expr) : Prop :=
  (∃ names us n, ConLeche.nestCanonCrest names us n ty = some A) ∨
    ∃ n, ConLeche.instPisWith (canonParams n) ty = some A

/-- **A recorded block's constructors read as their hole telescopes**
(M2): member `c`'s constructor
`j` is stored, closed, at the members' level parameters; its canonical
abstraction (every whole member application abstracted, at the canonical
parameters) mentions no member constant (from the kernel's
`nestUniform`), and reads, at depth `nP + k` and every level assignment,
as a Π-tower ending in member `c`'s hole applied to the result index
readings, whose fields read like the clause's fields with holes at every
frame satisfying the hole context (the parameters, then each member's
hole type — its former at the canonical parameters, `Tys`).  The stored
type is the DECLARED one; the fields with holes are the positivity walk's
normal form's, which reads like it there.

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
@[expose] def LfpCtorReads {V : Type w} [SetTheory V] (acval : Name → (Name → Nat) → Term)
    (env : Env) (D : LfpDatum V) : Prop :=
  D.names.length = D.k ∧
  ∀ c, c < D.k → ∀ j, j < D.nctors c → ∃ cv nPc nF,
    env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF) ∧
    cv.type.hasFvar = false ∧
    (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      cvm.levelParams = cv.levelParams) ∧
    (∀ (ψ : Name → Nat) (dsC : List Term) (bodyC : Term),
      denote acval env ψ 0 cv.type = some (mkPisAV dsC bodyC) → nPc ≤ dsC.length →
      ∀ ρ : Nat → V, Sat V (D.params ψ).reverse ρ →
        Sat V (dsC.take nPc).reverse ρ) ∧
    ∃ A, ConLeche.nestCanonCrest D.names (cv.levelParams.map .param) nPc cv.type = some A ∧
      A.nestOcc D.names 0 0 = false ∧
      ∀ ψ : Name → Nat, (D.params ψ).length = nPc ∧ (D.fields ψ c j).length = nF ∧
        ∃ (ab : List Term) (Tys : List Term),
          denote acval env ψ (nPc + D.k) A
            = some (mkPisAV ab (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
                (D.resIdx ψ c j))) ∧
          ab.length = nF ∧ Tys.length = D.k ∧
          (∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
            ConLeche.instPisWith (canonParams nPc) cvm.type = some ty ∧
            denote acval env ψ (nPc + mm) ty = some (Tys.getD mm default)) ∧
          FieldsEqOn V (D.params ψ ++ Tys).reverse ab (D.fields ψ c j)

/-- **A recorded block's capability records and constructor shapes**
(task #342 L10): each member's stored capabilities are sound for the
datum — the sort zero-ness datum holds wherever the block's sort is
zero, and the K capability is claimed only at a single constructor —
and each constructor's stored type concludes, past its parameters and
fields, in its member at its own level parameters applied to the
parameter variables and then the index expressions (official's
`check_constructors`: the result's parameters are the parameters).  The
ι case split's facts at an outside class read them: a container's
capabilities decide its sort's zero-ness and its K rule, and its
constructor's residual is the former at the constructor's parameters. -/
@[expose] def LfpCaps {V : Type w} [SetTheory V] (env : Env) (D : LfpDatum V) : Prop :=
  (∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
    (∀ ψ : Name → Nat, D.w ψ = 0 → caps.sortZ.holds ψ = true) ∧
    (caps.ruleK = true → D.nctors mm = 1)) ∧
  ∀ c, c < D.k → ∀ j, j < D.nctors c → ∃ cv nPc nF,
    env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF) ∧
    ∃ (bs : List Expr) (es : List Expr),
      cv.type.stripPis (nPc + nF)
        = some (bs, Expr.mkAppN (.const (D.member c) (cv.levelParams.map .param))
            (ConLeche.structPsAt nF nPc ++ es))

section
variable {V}

/-- **An application along a Π-tower lands in its body**
(`app_mem_piV` per binder). -/
theorem foldl_app_mem_mkPisAV {B : Term} :
    ∀ {tl : List Term} {ρ : Nat → V} {bs : List V} {f : V},
      SpineFit ρ tl bs →
      f ∈ˢ interp V ρ (mkPisAV tl B) →
      bs.foldl SetTheory.app f ∈ˢ interp V (consList bs ρ) B
  | [], ρ, [], f, _, hf => hf
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim
  | d :: tl, ρ, b :: bs, f, h, hf => by
    have hf' : f ∈ˢ interp V ρ (.pi d (mkPisAV tl B)) := hf
    rw [interp_pi] at hf'
    have happ := app_mem_piV hf' h.1
    rw [List.foldl_cons, consList_cons]
    exact foldl_app_mem_mkPisAV h.2 happ

/-- **A Π-tower whose body is a truth value at every fitting spine is a
truth value**: each binder's fibres are (by induction), so each
function space is the truth-value regime's (`piV_eq_zero`). -/
theorem mkPisAV_mem_univZero {B : Term} :
    ∀ {tl : List Term} {ρ : Nat → V},
      (∀ bs, SpineFit ρ tl bs → interp V (consList bs ρ) B ∈ˢ (univZero : V)) →
      interp V ρ (mkPisAV tl B) ∈ˢ (univZero : V)
  | [], _, h => h [] trivial
  | d :: tl, ρ, h => by
    show interp V ρ (.pi d (mkPisAV tl B)) ∈ˢ _
    rw [interp_pi, piV_eq_zero fun x hx =>
      mkPisAV_mem_univZero fun bs hbs => h (x :: bs) ⟨hx, hbs⟩]
    exact piR_zero_mem_univZero

/-- **The body of a graded Π-tower is a type at every fitting spine**:
it is the innermost binder's fibre, which the grading makes a type. -/
theorem isTy_of_wd_mkPisAV {B : Term} :
    ∀ {tl : List Term} {ρ : Nat → V} {bs : List V}, tl ≠ [] →
      WellDenoted V ρ (mkPisAV tl B) → SpineFit ρ tl bs →
      IsTy (interp V (consList bs ρ) B)
  | [], _, _, h, _, _ => absurd rfl h
  | [_], _, [], _, _, hsp => hsp.elim
  | [d], ρ, [b], _, hwd, hsp => (cast (WellDenoted_pi V ρ d B) hwd).2.2.2 b hsp.1
  | [_], _, _ :: _ :: _, _, _, hsp => hsp.2.elim
  | _ :: _ :: _, _, [], _, _, hsp => hsp.elim
  | d :: d' :: tl, ρ, b :: _, _, hwd, hsp =>
    isTy_of_wd_mkPisAV (tl := d' :: tl) (ρ := cons b ρ) (List.cons_ne_nil _ _)
      ((cast (WellDenoted_pi V ρ d (mkPisAV (d' :: tl) B)) hwd).2.2.1 b hsp.1) hsp.2

end

/-- **The P-tier environment invariant, at one mode** (see the module
docstring). -/
structure EnvModelM (μ : CheckMode) (env : Env) where
  /-- the environment carrier, contained -/
  base2 : EnvModel V env
  /-- every stored type reads, at every ground assignment -/
  type_reads : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ ta : Term,
      denote base2.acval env ψ 0 c.toConstantVal.type = some ta
  /-- the stored types' readings are graded types -/
  type_wellDenotedTy : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : Term),
    denote base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, WellDenotedTy V ρ ta
  /-- stored constants inhabit their types' readings (a projection
  table's constant type is the closed dummy `Sort 1` and its leaf is
  `Sort 0`, so the row holds of tables too; that a table is not a term
  is `inferTypeCore`'s own rejection of a `.const` naming one) -/
  mem_type : ∀ c ∈ env.consts,
    ∀ (ψ : Name → Nat) (ta : Term),
    denote base2.acval env ψ 0 c.toConstantVal.type = some ta →
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
  /-- the stored formers' fibres above a proposition are strict (an
  *environment law* for the same reason `caps_ok` is — a former's leaf
  is fixed by its install and by nothing else, so the supplier is the
  former's install: the block's fixpoint leaf, the pinned basis
  formers; task #342 L7).  Consumed through `IndFibLaw`
  (`EnvModelM.indFibLaw`) -/
  ind_strict : IndStrictOk base2
  /-- **the recorded blocks**: the lfp data of the
  inductive blocks whose lfp clause this carrier records — a ghost
  list, filled by the uniform block install at its constructors'
  environment (`declBlock`, `EnvModelM.addLfp`) and copied by every
  other extension -/
  lfpBlocks : List (LfpDatum V)
  /-- **the lfp clause of every recorded block** (`Env/BlockLfp.lean`):
  its members' denotations are the least fixed point of its operator,
  whose fibres are the constructors' injections; and its members are
  stored inductive formers (which is what lets every extension
  transport the clause: an extension never re-reads a stored name) -/
  lfp_ok : ∀ D ∈ lfpBlocks, LfpClause base2.acval D ∧ LfpStored env D ∧
    LfpReads base2.acval env D ∧ LfpCtorReads base2.acval env D ∧ LfpCaps env D

namespace EnvModelM

variable {V}
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The `const` residue, derived — the worked example of the
bundle-supplying layer.**  The three type fields at the composed
assignment `Level.substFn φ ks us`, carried to the instantiated form
by `denotePInstLevels` (an equality: no arity premise, no fuel). -/
theorem constType (m : EnvModelM V μ env) : ConstType m.base2 φ := by
  intro d n ci us hf hlen
  have hmem := ConLeche.Env.find?_mem hf
  have hname := ConLeche.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.wf.consts ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denote_liftN_eq_self m.base2.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth :
      denote m.base2.acval env
          (Level.substFn φ ci.toConstantVal.levelParams us) d
          ci.toConstantVal.type = some ta :=
    denote_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  -- the instantiated type's reading, by the crossing
  have hcross :
      denote m.base2.acval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us)
        = denote m.base2.acval env
            (Level.substFn φ ci.toConstantVal.levelParams us) d
            ci.toConstantVal.type :=
    denotePInstLevels m.base2 φ ci.toConstantVal.levelParams us d
      ci.toConstantVal.type
  refine ⟨ta, ?_, m.type_wellDenotedTy ci hmem _ ta hta, ?_⟩
  · rw [hcross]; exact hdepth
  · have := m.mem_type ci hmem _ ta hta
    rwa [hname] at this

/-- **The fibre law of the stored families, from the P invariant**
(task #342 L7; `IndFibLaw`): at the use's levels the instantiated type
reads as the stored type at the composed assignment (the `constType`
crossing), so a fitting spine fits the stored reading.  Where the sort
is `0`, the former's membership in its graded type puts the
application in `Sort 0` (`foldl_app_mem_mkPisAV`); elsewhere the
`ind_strict` field gives a strict set. -/
theorem indFibLaw (m : EnvModelM V μ env) (φ : Name → Nat) : IndFibLaw m.base2 φ := by
  intro d I cv caps us hf _hlen ab n hread ρ vs hsp
  have hmem := ConLeche.Env.find?_mem hf
  have hname := ConLeche.Env.find?_name hf
  have hcv : (ConstantInfo.indInfo cv caps).toConstantVal = cv := rfl
  have hwf := m.base2.wf.consts _ hmem
  obtain ⟨ta, hta⟩ := m.type_reads _ hmem (Level.substFn φ cv.levelParams us)
  rw [hcv] at hta
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denote_liftN_eq_self m.base2.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth : denote m.base2.acval env (Level.substFn φ cv.levelParams us) d cv.type
      = some ta :=
    denote_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  have hcross := denotePInstLevels m.base2 φ cv.levelParams us d cv.type
  rw [hcross, hdepth] at hread
  obtain rfl := Option.some.inj hread
  have hnm : I = cv.name := hname.symm
  subst hnm
  by_cases hn : n = 0
  · subst hn
    have hin := m.mem_type _ hmem _ _ hta ρ
    have h0 := foldl_app_mem_mkPisAV hsp hin
    rw [interp_sort, univ_zero] at h0
    exact h0
  · simp only [hn, decide_false, Fib_false]
    exact m.ind_strict cv.name cv caps hf _ ab n hta hn ρ vs hsp

/-- **The bridge invariant, from the P invariant**.  Every field is a
projection:

| `EnvFacts` field | source |
|---|---|
| `cval`, `cval_closed`, `wf`, `proj_ok` | `base2`'s own |
| `val_params` | `acval_params` |
| `ty_denotes` | `type_reads` |
| `defn_eq` | `defn_reads` (definitions only: a theorem is opaque to reduction, and the invariant keeps no equation for its value) |
| `rec_rhs_denotes`, `rec_params_le` | `rec_rules`' `RecRuleLaw`, whose first two components are exactly those two facts |
| `nat_op_guard` | `nat_ops`/`div_mod` through `natOpStored_inv` |
-/
def toEnvFacts {V : Type w} [SetTheory V] {μ : CheckMode}
    {env : Env} (m : EnvModelM V μ env) : ConLeche.Semantics.EnvFacts env where
  cval := m.base2.acval
  cval_closed := m.base2.cval_closed
  wf := m.base2.wf
  val_params := fun n ci hf φ₁ φ₂ hp =>
    m.base2.acval_params n ci hf φ₁ φ₂ hp
  ty_denotes := fun c hc ψ => by
    obtain ⟨ta, hta⟩ := m.type_reads c hc ψ
    exact ⟨ta, hta⟩
  defn_eq := fun cv value hint hmem ψ =>
    (m.defn_reads ψ cv value ⟨hint, hmem⟩).elim fun t ht => ⟨t, ht.1⟩
  rec_rhs_denotes := fun n cv mI rP rules hf r hr us ψ hlen => by
    obtain ⟨-, hus, -⟩ := m.rec_rules ψ n cv mI rP rules hf r hr
    obtain ⟨Ra, hRa, -, -⟩ := hus us hlen
    exact ⟨Ra, hRa⟩
  rec_params_le := fun n cv mI rP rules hf r hr =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr).1
  proj_ok := m.base2.proj_ok
  nat_op_guard := fun c hmem hst => by
    obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
    rcases hmem with hm | hm
    · exact (m.nat_ops (fun _ => 0) c hm cv v hh hf).1
    · exact (m.div_mod (fun _ => 0) c hm cv v hh hf).1

end EnvModelM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false. -/
@[expose] noncomputable def EnvModelM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvModelM V μ Env.empty where
  base2 := EnvModel.empty
  type_reads := fun c hc => nomatch hc
  type_wellDenotedTy := fun c hc => nomatch hc
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
  ind_strict := fun I _ _ hf => by
    rw [show Env.empty.find? I = none from rfl] at hf
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
    (hrd : LfpReads mp.base2.acval env D) (hrdC : LfpCtorReads mp.base2.acval env D)
    (hcaps : LfpCaps env D) :
    EnvModelM V μ env :=
  { mp with
    lfpBlocks := D :: mp.lfpBlocks
    lfp_ok := fun D' hD' => by
      rcases List.mem_cons.mp hD' with rfl | h
      · exact ⟨hL, hst, hrd, hrdC, hcaps⟩
      · exact mp.lfp_ok D' h }


theorem mem_addLfp (mp : EnvModelM V μ env) (D : LfpDatum V) (hL) (hst) (hrd) (hrdC) (hcaps) :
    D ∈ (mp.addLfp D hL hst hrd hrdC hcaps).lfpBlocks := List.mem_cons_self

/-- A recorded block's clause, read off the carrier. -/
theorem lfpClause_of_mem (mp : EnvModelM V μ env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) :
    LfpClause mp.base2.acval D :=
  (mp.lfp_ok D hD).1

/-- **One recorded clause crosses a change of environment** that keeps,
at the block's members and constructors (the names `P` holds of), the
lookup and the leaf, and every successful reading of a member's or
constructor's type and of their canonical abstractions. -/
theorem lfpOne_transport {acval acval' : Name → (Name → Nat) → Term} {env env' : Env}
    {D : LfpDatum V} (P : Name → Prop)
    (hP : (∀ mm, mm < D.k → P (D.member mm)) ∧
      ∀ c, c < D.k ∨ c < D.N → ∀ j, j < D.nctors c → P (D.ctorName c j))
    (hD : LfpClause acval D ∧ LfpStored env D ∧ LfpReads acval env D ∧
      LfpCtorReads acval env D ∧ LfpCaps env D)
    (htr : ∀ n cv nPc nF, P n → env.find? n = some (.ctorInfo cv nPc nF) → ∀ ψ,
      ∃ ta, denote acval env ψ 0 cv.type = some ta)
    (hfind : ∀ n ci, P n → env.find? n = some ci → env'.find? n = some ci)
    (hag : ∀ n ci, P n → env.find? n = some ci → acval' n = acval n)
    (hread : ∀ n cv caps, P n → env.find? n = some (.indInfo cv caps) → ∀ (ψ : Name → Nat)
      (ta : Term), denote acval env ψ 0 cv.type = some ta →
      denote acval' env' ψ 0 cv.type = some ta)
    (hreadT : ∀ n cv nPc nF, P n → env.find? n = some (.ctorInfo cv nPc nF) → ∀ (ψ : Name → Nat)
      (ta : Term), denote acval env ψ 0 cv.type = some ta →
      denote acval' env' ψ 0 cv.type = some ta)
    (hreadC : ∀ n ci, P n → env.find? n = some ci →
      ∀ A, CanonOf ci.toConstantVal.type A →
      ∀ (ψ : Name → Nat) (d : Nat) (ta : Term),
      denote acval env ψ d A = some ta →
      denote acval' env' ψ d A = some ta) :
    LfpClause acval' D ∧ LfpStored env' D ∧ LfpReads acval' env' D ∧
      LfpCtorReads acval' env' D ∧ LfpCaps env' D := by
  obtain ⟨hPm, hPc⟩ := hP
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := hD
  refine ⟨hL.congr (fun mm hmm => ?_) (fun c hc j hj => ?_),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc j hj => ?_⟩,
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact hag _ _ (hPm mm hmm) hf
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact hag _ _ (hPc c (Or.inr hc) j hj) hf
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, hfind _ _ (hPm mm hmm) hf⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, hfind _ _ (hPc c (Or.inr hc) j hj) hf⟩
  · obtain ⟨cv, caps, hf, hab⟩ := hrd mm hmm
    refine ⟨cv, caps, hfind _ _ (hPm mm hmm) hf, fun ψ => ?_⟩
    obtain ⟨ab, hta, h1⟩ := hab ψ
    exact ⟨ab, hread _ _ _ (hPm mm hmm) hf ψ _ hta, h1⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc j hj
    have hPn := hPc c (Or.inl hc) j hj
    refine ⟨cv, nPc, nF, hfind _ _ hPn hf, hcf,
      fun mm hmm => ?_, fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc, fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      exact ⟨cvm, caps, hfind _ _ (hPm mm hmm) hfm, hl⟩
    · -- the new reading is the old one (the old one exists, and crosses)
      obtain ⟨ta, hta⟩ := htr _ _ _ _ hPn hf ψ
      have hta' := hreadT _ _ _ _ hPn hf ψ _ hta
      rw [hrd'] at hta'
      obtain rfl := Option.some.inj hta'
      exact hpars ψ dsC bodyC hta hle
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, hreadC _ _ hPn hf A (.inl ⟨_, _, _, hA⟩) ψ _ _ hta, hlab, hlT,
        fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, ty, hfm, hty, hr⟩ := hTys mm hmm
      exact ⟨cvm, caps, ty, hfind _ _ (hPm mm hmm) hfm, hty,
        hreadC _ _ (hPm mm hmm) hfm ty (.inr ⟨_, hty⟩) ψ _ _ hr⟩
  · obtain ⟨cv, caps, hf, hz, hk⟩ := hcK mm hmm
    exact ⟨cv, caps, hfind _ _ (hPm mm hmm) hf, hz, hk⟩
  · obtain ⟨cv, nPc, nF, hf, hsh⟩ := hcC c hc j hj
    exact ⟨cv, nPc, nF, hfind _ _ (hPc c (Or.inl hc) j hj) hf, hsh⟩

/-- **The recorded clauses cross an environment extension** that keeps
every stored inductive former and its leaf, and every successful reading
of a stored former's type — the transport every construction site of
the invariant (the cons funnel, the rule-list swap) instantiates. -/
theorem lfp_ok_transport (mp : EnvModelM V μ env) {env' : Env}
    {acval' : Name → (Name → Nat) → Term}
    (hfind : ∀ n ci, env.find? n = some ci → (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env'.find? n = some ci)
    (hag : ∀ n ci, env.find? n = some ci → (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      acval' n = mp.base2.acval n)
    (hread : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → ∀ (ψ : Name → Nat)
      (ta : Term), denote mp.base2.acval env ψ 0 cv.type = some ta →
      denote acval' env' ψ 0 cv.type = some ta)
    (hreadT : ∀ n cv nPc nF, env.find? n = some (.ctorInfo cv nPc nF) → ∀ (ψ : Name → Nat)
      (ta : Term), denote mp.base2.acval env ψ 0 cv.type = some ta →
      denote acval' env' ψ 0 cv.type = some ta)
    (hreadC : ∀ n ci, env.find? n = some ci → (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      ∀ A, CanonOf ci.toConstantVal.type A →
      ∀ (ψ : Name → Nat) (d : Nat) (ta : Term),
      denote mp.base2.acval env ψ d A = some ta →
      denote acval' env' ψ d A = some ta) :
    ∀ D ∈ mp.lfpBlocks, LfpClause acval' D ∧ LfpStored env' D ∧ LfpReads acval' env' D ∧
      LfpCtorReads acval' env' D ∧ LfpCaps env' D := by
  intro D hD
  have hok := mp.lfp_ok D hD
  -- the block's names are stored formers and constructors, never recursors
  let P : Name → Prop := fun n => ∃ ci, env.find? n = some ci ∧
    ∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules
  have hnr : ∀ n ci, P n → env.find? n = some ci → ∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules :=
    fun n ci ⟨ci', h1, h2⟩ hf => by rw [hf] at h1; obtain rfl := Option.some.inj h1; exact h2
  refine lfpOne_transport P ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩ hok
    (fun n cv nPc nF _ hf ψ => mp.type_reads _ (List.mem_of_find?_eq_some hf) ψ)
    (fun n ci hp hf => hfind n ci hf (hnr n ci hp hf))
    (fun n ci hp hf => hag n ci hf (hnr n ci hp hf))
    (fun n cv caps _ hf => hread n cv caps hf) (fun n cv nPc nF _ hf => hreadT n cv nPc nF hf)
    (fun n ci hp hf => hreadC n ci hf (hnr n ci hp hf))
  · obtain ⟨cv, caps, hf⟩ := hok.2.1.1 mm hmm
    exact ⟨_, hf, fun _ _ _ _ h => ConstantInfo.noConfusion h⟩
  · rcases hc with hc | hc
    · obtain ⟨cv, a, b, hf, -⟩ := hok.2.2.2.1.2 c hc j hj
      exact ⟨_, hf, fun _ _ _ _ h => ConstantInfo.noConfusion h⟩
    · obtain ⟨cv, a, b, hf⟩ := hok.2.1.2 c hc j hj
      exact ⟨_, hf, fun _ _ _ _ h => ConstantInfo.noConfusion h⟩

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
