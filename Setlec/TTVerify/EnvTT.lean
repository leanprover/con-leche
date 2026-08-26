import Setlec.TTVerify.Denote
import Setlec.TTVerify.VClosed
import Setlec.TTVerify.Tele
import Setlec.TT.Semantics.Consistency

/-!
# The environment invariant, transposed from `EnvModel`

`EnvTT env` is `Setlec/Model/Interp.lean`'s `EnvModel env` with the
set-theoretic universe replaced by the declarative type theory:

| `EnvModel` | `EnvTT` |
|---|---|
| `val : ConstVal V` | `cval : TConstVal` |
| — | `cval_closed` (**new**; see the field) |
| `wf : EnvWF env` | *the same* |
| `val_params` | *the same* |
| `mem_type`: `val c φ ∈ˢ ⟦c.type⟧` | `has_type`: `⊢ cval c φ : ⟦c.type⟧` |
| `defn_eq`: `⟦value⟧ = some (val c φ)` | *the same*, at `VExpr` |
| `thm_ok`: the same **plus `AnnotOk`** | just the equation |
| `annot_ok` | **no counterpart** |
| `ind_ok`'s `Empty` clause | `empty_pinned` |

Two of those rows are the point of the whole exercise.

**`mem_type` becomes a typing judgment.**  That is the only change of
substance: "every stored constant's value is a member of its type's
interpretation" becomes "every stored constant's denotation has a
derivation of its type's denotation".  The *induction* is unchanged —
the invariant is re-established declaration by declaration as the
checker installs, and that incremental extension **is** the
stream-ordering fact.  There is no separate ordering concept here, and
none is needed.

**`AnnotOk` disappears.**  The set model's truthfulness predicate
exists to reconstruct, at every binder, the fibre and membership facts
that a typing derivation would have supplied; in the declarative layer
the derivation supplies them, so `annot_ok` has no field and `thm_ok`
loses its second conjunct (`Setlec/TT/DESIGN.md` §6).  This is the
single largest structural saving of the bridge, and it is why the app
rule's premises can be delivered by the induction hypothesis directly
rather than through an `AppSlot`-style existential package.

## What is still to come (task #119 stage 2)

`EnvModel` has six further fields, all of them *semantic laws about
stored declarations* rather than structure.  Each transposes by the
same recipe — **replace an equation between interpretations by a
`Setlec.TT.Deq []` between denotations** — and each is added here as
the corresponding clause of the fuel induction is proved:

* `ind_ok`'s remaining conjuncts (`PairTyFacts`, `PairMkFacts`, the
  `PUnit` collapse, the pinned-valuation clause, and the two purely
  *syntactic* conjuncts `BasisBlocks`/`RecCtorsStored`, which mention
  no `V` and so transpose verbatim);
* ~~`rec_rules`~~ — **done**, as `RecRulesTT` above, in the fired form
  rather than the tower one;
* ~~`proj_ok`~~ — **done**, as `ProjOkT` above, verbatim;
* ~~`caps_ok`~~ — **done**, as `CapsOkTT` above, in the fired form;
* `nat_ops : NatOpsOk` and `div_mod : DivModOk` — the certified
  recurrences, whose TT form is exactly the hypothesis shape of
  `Setlec/TT/Nat/*` (`Deq` equations at numerals): the bridge denotes
  the checker's own certificate and hands it to `numeral_add` and
  friends, which are hypothetical over an arbitrary `f : VExpr` and
  therefore need no constant of their own in the layer;
* `reduce_ops : ReduceOpsOk` — the compiler-trust identity, likewise.

They are listed here rather than left implicit because an invariant
that is quietly missing a clause is the classic way for a bridge like
this to look finished while proving nothing.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- **The fired modeled-iota contract** (task #119; the decision and its
argument are in `Setlec/TTVerify/DESIGN.md` §8).

Every stored fireable recursor rule holds **at each instantiation the
checker can fire it at**, given that the spines are typed against their
telescopes.  Read against `iotaRec` (`Setlec/Kernel/Core.lean`), which
fires

```
mkAppN (.const n us) (args ++ [mkAppN (.const cj usj) margs])
  ↦  mkAppN (rl.rhs[us]) (args.take rP ++ margs.drop rl.ctorParams)
```

**Why this and not the set model's tower λ-equality** (`RecRulesOk`).
A closed tower has to be *fired* to be used — `congrApp` onto the
actual arguments, then β-reduce each side — and `HasType.beta` demands
`⊢ argᵢ : domainᵢ` for every argument.  So the tower does not avoid
the typing premises; it defers them to the fire site and adds a
β-apparatus on top.  Here they are hypotheses (`TeleTyped`), supplied
at the fire site by `iotaCerts` — which computes exactly them, proved
in `certs_typed` (`Setlec/TTVerify/Certs.lean`).

And the set model's reason for the tower does not transpose: it was
forced by junk-agreement between dependent-function graphs off-domain,
and **a syntactic layer has no off-domain** — a `Deq` at an
instantiation says exactly what it says.

The cost, stated: this field is *longer* than `RecRulesOk`, because the
firing conditions live in its statement.  What it buys is short proofs
at both ends — the install denotes the `_model.iota_j` theorem and
instantiates it (`TeleTyped.appN`), and the fire site already holds
the premises. -/
def RecRulesTT (env : Env) (cval : TConstVal) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
    ∀ (cvj : ConstantVal) (cnP cnF : Nat),
      env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr)
      (us usj : List Level) (args margs : List Expr)
      (xs ys : List VExpr) (restR restC : Expr) (L R : VExpr),
      args.length = mI →
      margs.length = RecRule.ctorParams rl + RecRule.nfields rl →
      -- the recursor's spine, typed against its telescope
      TeleTyped cval env φ d Δ
        (cv.type.instantiateLevelParams cv.levelParams us)
        (args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs])
        xs restR →
      -- the constructor's spine, typed against its own
      TeleTyped cval env φ d Δ
        (cvj.type.instantiateLevelParams cvj.levelParams usj) margs ys
        restC →
      denote cval env φ d
        (Expr.mkAppN (.const n us)
          (args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs])) =
        some L →
      denote cval env φ d
        (Expr.mkAppN
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
          (args.take rP ++ margs.drop (RecRule.ctorParams rl))) = some R →
      Deq Δ L R

theorem RecRulesTT.empty (cval : TConstVal) : RecRulesTT Env.empty cval := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

/-- The eta family of an eta-capable stored structure is complete:
the capability record's constructor is stored at exactly its arities,
and every documented projection function is stored.  **A deliberate duplicate, awaiting relocation.**  This restates
`Setlec/Model/Interp.lean`'s `EtaFamilyStored`, which is `V`-free and
belongs in `Setlec/Verify/*`; a relocation task tracks it, together
with `natLitSupported_congr` / `natLitSupported_inv`, which the bridge
duplicates for the same reason.  Deferred because `Model/Interp.lean`
is heavily trafficked and moving it mid-flight would collide.

**Do not "fix" the duplication by importing `Setlec/Model/*` from
here.**  That is the wrong direction: the bridge must not depend on the
set-model path (both verification routes are meant to stand alone), and
an import would couple them permanently to save a ten-line
restatement.  The fix is the relocation, when it is safe to make.

It is the *premise* under which the eta law is owed: mid-block the
former is stored before its constructor, so the premise fails and the
law is not yet owed; the family-completing install discharges it. -/
def EtaFamilyStoredT (env : Env) (T : Name) (caps : IndCaps) : Prop :=
  reservedBasisNames.contains caps.etaCtor = false ∧
  (∃ cvC, env.find? caps.etaCtor =
    some (.ctorInfo cvC caps.etaParams caps.etaFields)) ∧
  ∀ j, j < caps.etaFields → ∃ cv mI rP rules,
    env.find? (projFnName T j) = some (.recInfo cv mI rP rules)

/-- **The structural-eta law, fired.**  Transpose of `EnvModel`'s
`EtaLaw`, in the same *fired* form as `RecRulesTT` and for the same
reason (§8): the premises the layer's rules want are supplied at the
site, so quantifying over them makes them hypotheses of the contract
rather than obligations of the install.

Consumed by `majorToCtor`'s eta-rescue branch, whose
`structEtaCertWith` call supplies **both** hypotheses — the
`TeleTyped` from its own `iotaCerts` on `T`'s parameter telescope, and
the subject's typing from the `infer major` that produced `tmaj`.
That correspondence was pre-registered before this definition was
written and confirmed verbatim (`Setlec/TTVerify/DESIGN.md` §6). -/
def EtaLawTT (env : Env) (cval : TConstVal) (T : Name) (cvT : ConstantVal)
    (caps : IndCaps) : Prop :=
  ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (us : List Level)
    (ps : List Expr) (b : Expr) (xs : List VExpr) (rest : Expr)
    (B F : VExpr),
    ps.length = caps.etaParams →
    TeleTyped cval env φ d Δ
      (cvT.type.instantiateLevelParams cvT.levelParams us) ps xs rest →
    denote cval env φ d b = some B →
    HasType Δ B
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us)) xs) →
    denote cval env φ d
      (Expr.mkAppN (.const caps.etaCtor us)
        (ps ++ (List.range caps.etaFields).map fun j =>
          Expr.mkAppN (.const (projFnName T j) us) (ps ++ [b]))) = some F →
    Deq Δ B F

/-- **The unit-like law, fired.**  Transpose of `EnvModel`'s
`UnitLaw`: any two inhabitants of a unit-like family's type are
equal.  Consumed by the proof-irrelevance path and by
`majorToCtor`'s zero-field rescue. -/
def UnitLawTT (env : Env) (cval : TConstVal) (T : Name) (cvT : ConstantVal)
    (caps : IndCaps) : Prop :=
  ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (us : List Level)
    (ps : List Expr) (b b' : Expr) (xs : List VExpr) (rest : Expr)
    (B B' : VExpr),
    ps.length = caps.unitParams →
    TeleTyped cval env φ d Δ
      (cvT.type.instantiateLevelParams cvT.levelParams us) ps xs rest →
    denote cval env φ d b = some B →
    denote cval env φ d b' = some B' →
    HasType Δ B
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us)) xs) →
    HasType Δ B'
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us)) xs) →
    Deq Δ B B'

/-- The stored inductive families' capability laws.  Transpose of
`CapsOk`, and **provenance-abstract** for the same reason: the
environment remembers nothing about how a family was installed, so the
laws are stated over public names and say only what the reduction
rules consume.  Basis families are exempt (`reservedBasisNames`) —
their eta and unit facts ride the pinned clauses. -/
def CapsOkTT (env : Env) (cval : TConstVal) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    EtaFamilyStoredT env T caps → EtaLawTT env cval T cvT caps) ∧
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    reservedBasisNames.contains T = false →
    UnitLawTT env cval T cvT caps)

theorem CapsOkTT.empty (cval : TConstVal) : CapsOkTT Env.empty cval := by
  refine ⟨?_, ?_⟩ <;> (intro T cvT caps h; simp [Env.find?, Env.empty] at h)

/-- Every stored *native* projection-table entry is one of the two
pinned pair entries, with the pair block stored alongside.

**Purely syntactic, so it transposes verbatim** — it mentions no
values, no interpretation and no derivations, and the `V` of
`EnvModel`'s `ProjOk` never appears in it.  That is worth noticing
rather than glossing: a clause that survives the transposition
*unchanged* is one that was never about the model in the first place,
and it is the cheapest kind of field to carry.

Another deliberate duplicate of a `V`-free definition stranded in
`Setlec/Model/Interp.lean`; see `EtaFamilyStoredT` for the relocation
note and for why importing `Setlec/Model/*` here is the wrong fix. -/
def ProjOkT (env : Env) : Prop :=
  ∀ n entry, env.find? n = some (.projInfo entry) →
    entry.native = true →
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA

theorem ProjOkT.empty : ProjOkT Env.empty := by
  intro n entry h
  simp [Env.find?, Env.empty] at h

/-- A *derivation model* of an environment: a type-theory term for
every constant (a function of the level-parameter assignment), such
that the environment is well-formed, each valuation reads only its own
level parameters, each constant's valuation is derivably of its type's
denotation, and each definition's valuation is its body's denotation.

The transpose of `Setlec.EnvModel`; see the module docstring for the
row-by-row correspondence and for the fields still to come. -/
structure EnvTT (env : Env) where
  /-- The type-theory term of each constant. -/
  cval : TConstVal
  /-- **Every constant denotes to a closed term.**

  **This is the one field with no counterpart in `EnvModel`**, so read
  it as a *trade* rather than as an incidental well-formedness
  condition — that reading is what tells you what shape a future
  `EnvTT` field should have.

  The trade is exactly this.  `denote` needs **no free-variable
  valuation**, where `interpExpr` needs `ρ : Nat → V`, because the
  opened binder *is* a variable: `fvar d` read at depth `d'` is
  `.bvar (d' - 1 - d)`, computed rather than looked up
  (`Setlec/TTVerify/Denote.lean`).  We pay for that here: a constant's
  denotation is a **term**, and lifting and instantiation have to pass
  through it untouched, which they do only if it has no loose
  variables.  `interpExpr` owes nothing in return because `val n ψ : V`
  is a set, with nothing in it to lift.

  So this is the **syntactic shadow of `val_params`** below: that field
  says a constant's value does not depend on the ambient level
  assignment beyond its own parameters; this one says its denotation
  does not depend on the ambient *local context* at all.  Both are the
  same statement — a constant means what it means, wherever it is used —
  and every install site discharges this one the way it discharges
  `val_params`.

  Consumed by `Setlec/TTVerify/{Shift,Inst}.lean` at the `.const` and
  literal clauses; supporting facts in `Setlec/TTVerify/VClosed.lean`. -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (cval n ψ)
  /-- Stored declarations are syntactically well-formed. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every constant has a derivation of its type.**  The transpose of
  `EnvModel.mem_type`, and the whole content of the bridge: its
  incremental re-establishment as declarations install is the
  stream-ordering fact. -/
  has_type : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    ∃ t, denoteClosed cval env φ c.toConstantVal.type = some t ∧
      HasType [] (cval c.name φ) t
  /-- Every definition is denoted by its body. -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- Every theorem is denoted by its proof value.  (`EnvModel.thm_ok`
  carries a second conjunct, `AnnotOk` of the value; there is nothing to
  carry here.) -/
  thm_ok : ∀ cv value,
    ConstantInfo.thmInfo cv value ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- The pinned empty type is valued by the layer's `Empty`, at some
  level.  The transpose of `IndOk`'s last conjunct
  (`∀ ψ x, x ∈ˢ val emptyName ψ → False`), in the stronger
  *pinned-valuation* form that `IndOk`'s fourth conjunct already uses
  for the reserved basis names — from which uninhabitation follows by
  the layer's own consistency theorem, so this invariant needs no
  `SetTheory` instance and the set theory enters only at the corollary. -/
  empty_pinned : ∀ ψ : Name → Nat, ∃ u, cval emptyName ψ = emptyT u
  /-- Every stored fireable recursor rule holds at every instantiation
  the checker can fire it at (`RecRulesTT`).  The transpose of
  `EnvModel.rec_rules`, in the **fired** form rather than the set
  model's tower λ-equality — see `RecRulesTT` for why. -/
  rec_rules : RecRulesTT env cval
  /-- The stored inductive families' capability laws (eta, unit-like),
  in the fired form.  Transpose of `EnvModel.caps_ok`; consumed by
  `majorToCtor`'s rescue branches. -/
  caps_ok : CapsOkTT env cval
  /-- Every stored native projection-table entry is a pinned pair
  entry with its block stored (`ProjOkT`).  Transpose of
  `EnvModel.proj_ok`, verbatim — the clause is syntactic. -/
  proj_ok : ProjOkT env

/-- The empty environment has a (trivial) derivation model. -/
def EnvTT.empty : EnvTT Env.empty where
  cval := fun _ _ => emptyT 0
  cval_closed := fun _ _ => trivial
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  has_type := by intro c hc; cases hc
  defn_eq := by intro cv value hint h; cases h
  thm_ok := by intro cv value h; cases h
  empty_pinned := fun _ => ⟨0, rfl⟩
  rec_rules := RecRulesTT.empty _
  caps_ok := CapsOkTT.empty _
  proj_ok := ProjOkT.empty

/-! ## What the invariant delivers per declaration

The bridge's per-declaration conclusion — a `def` or `theorem`'s value
has a derivation of its stated type — is `has_type` and `defn_eq`
together, with no further work.  This is the payoff of transposing
`mem_type` rather than inventing a separate statement: the
declaration-level theorem is a two-line consequence of the environment
invariant, exactly as `EnvModel.mem_type` gives the set-model one. -/

/-- A stored definition's body has a derivation of its stated type. -/
theorem EnvTT.hasType_defn {env : Env} (m : EnvTT env) {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧ HasType [] v t := by
  obtain ⟨t, ht, hd⟩ := m.has_type _ hc φ
  exact ⟨_, t, m.defn_eq cv value hint hc φ, ht, hd⟩

/-- A stored theorem's proof value has a derivation of its statement. -/
theorem EnvTT.hasType_thm {env : Env} (m : EnvTT env) {cv : ConstantVal}
    {value : Expr} (hc : ConstantInfo.thmInfo cv value ∈ env.consts)
    (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧ HasType [] v t := by
  obtain ⟨t, ht, hd⟩ := m.has_type _ hc φ
  exact ⟨_, t, m.thm_ok cv value hc φ, ht, hd⟩

end Setlec.TTVerify
