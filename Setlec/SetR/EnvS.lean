import Setlec.SetR.Sound.Motives
import Setlec.Verify.Denote.Levels
import Setlec.Verify.Denote.Install

/-!
# `EnvS`: the [set] environment invariant (task #148, T5)

The per-environment invariant the `DeclR` fold maintains — the [set]
analogue of `EnvTT` (`Setlec/TTVerify/EnvTT.lean`), over the **same**
`cval : TConstVal`, transposed field for field per the campaign
design's §2 with the semantic fields in membership/interp-equality
form (`Setlec/SetR/DESIGN.md`, T4 architecture record: consumed in
membership form only; nothing reads an `AnnotOkV`-of-inferred-type).

| `EnvTT` | `EnvS` |
|---|---|
| `cval`, `cval_closed`, `wf`, `val_params` | *the same* |
| `has_type`: `⊢ cval c φ : ⟦c.type⟧` | `mem_type`: `⟦cval c φ⟧ ∈ˢ ⟦⟦c.type⟧⟧` **plus the denoted type's truthfulness** |
| — | `annot_okV` (**new**: every valuation leaf is truthful — the value front door's subject conjunct, `EnvModel.annot_ok`'s successor) |
| `defn_eq`, `thm_ok`, `empty_pinned` | *the same* (V-free) |
| `rec_rules : RecRulesTT` | `rec_rules : RecRulesV` (at every `φ`) |
| `caps_ok : CapsOkTT` | `caps_ok : CapsOkV` |
| `ctor_residual` | **absent by design** (#136 is tt-only; design §7 note 3) |
| `proj_ok`, `rec_ctors`, `basis_pinned` | *the same* (V-free) |
| `eq_law : EqLawTT` | `eq_lawV : EqLawV` (interp form) |
| `nat_ops`/`div_mod`/`reduce_ops` | the `*V` forms (at every `φ`) |

Two `EnvSHyp` conventions are worth naming:

* the relations (and `EnvSHyp`) fix one `φ`; the invariant quantifies
  it, and `EnvS.toHyp` instantiates — that projection is the entire
  T4/T5 interface (`EnvSHyp`'s statement shapes are frozen by T4's
  consumers, so `toHyp` must stay `exact`-shaped, and does);
* `EnvSHyp.mem_type` is keyed on I3's side conditions (a `find?` hit
  and an *instantiated* stored type); the field here is keyed on
  membership at each assignment, `EnvTT.has_type`'s shape, and the
  projection crosses via `denote_instLevels` — the same move the
  bridge's `infer_const_claimR` makes.

The design's §2 lists a separate `proj_rules` field; it is **absorbed
into `rec_rules`**: the projection functions are stored *recursors*
(`ProjFnR` stores `.recInfo` entries), R11 is the only [set] consumer
of their firing, and `RecRulesV` is keyed on every stored `recInfo` —
a separate field would state the same law twice.  (Recorded in
`Setlec/SetR/DESIGN.md`.)
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The two law shapes not already in `Sound/Motives.lean`

Stated here because their first consumers are T5's own install steps
(the div/mod and iota derivations read equations off interpreted
`Eq`-spines through `eq_lawV`; the `ofReduce*` keys read
`reduce_ops`). -/

/-- **The pinned `Eq` block's fired law**, [set] form (design §2
`eq_lawV`; the `EqLawTT` transpose with `Deq → interp`-equality and
typing premises → memberships): once `Eq` is stored, the stored
constant's **two-fold** application is the layer's truth-set
abstraction over the slot.  Supplier: the basis install — `cval
eqName` is the pinned eta-expansion over `eqE`, so this is
`eqVal_app₂` (`Model/Basis/Eq/Install.lean:77`) transposed, and no
fact beyond that install's own computation is assumed.

**Restated at the two-fold application (finding 4, task #148 T5 c5).**
The earlier form gave only the *three*-fold application's value, under
**both** sides' memberships, plus a non-`pt` fact about the bare head.
That is enough for the three iota bottoms — `checkIotaSidesTy`
certifies their sides — but not for the eta/unit laws, whose
**fabricated** side no `--set-model` check types: `checkEtaThm`/
`checkUnitThm` are pure `Bool` shape matches.  The `lamC` form is what
supplies it, by rigidity (`EqLawV.dom`), and the old form is recovered
as `EqLawV.app₃`, so the interface got *smaller*, not larger.  This is
**not** finding #1: no checker check is missing — the fact is
derivable from the basis install's existing computation; it is an
interface field stated too weakly for a consumer its designer had not
met, the same class as `EnvR.rec_rhs_denotes`. -/
def EqLawV (env : Env) (cval : TConstVal) : Prop :=
  env.find? eqName = some eqA →
  ∀ ψ : Name → Nat,
    (∀ ρ : Nat → V, interp V ρ (cval eqName ψ) ≠ pt) ∧
    ∀ (ρ : Nat → V) (A a : VExpr),
      interp V ρ A ∈ˢ univ (ψ uN) →
      interp V ρ a ∈ˢ interp V ρ A →
      SetTheory.app
          (SetTheory.app (interp V ρ (cval eqName ψ)) (interp V ρ A))
          (interp V ρ a)
        = lamC (interp V ρ A) (fun y => eqv (interp V ρ a) y)

/-- **The full `Eq` spine's value** — the law's earlier statement,
recovered by one `app_lamC`. -/
theorem EqLawV.app₃ {env : Env} {cval : TConstVal}
    (h : EqLawV V env cval) (hfind : env.find? eqName = some eqA)
    (ψ : Name → Nat) (ρ : Nat → V) (A a b : VExpr)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A)
    (hb : interp V ρ b ∈ˢ interp V ρ A) :
    interp V ρ (VExpr.mkAppN (cval eqName ψ) [A, a, b])
      = eqv (interp V ρ a) (interp V ρ b) := by
  show interp V ρ (.app (.app (.app (cval eqName ψ) A) a) b) = _
  rw [interp_app, interp_app, interp_app, (h hfind ψ).2 ρ A a hA ha,
    SetTheory.app_lamC hb]

/-- **The `Eq` slot's rigidity** (the eta/unit laws' fabricated side):
the two-fold application is a `lamC` over the slot with a non-`pt`
value, so anything the statement's own truthfulness offers it as an
argument already inhabits the slot. -/
theorem EqLawV.dom {env : Env} {cval : TConstVal}
    (h : EqLawV V env cval) (hfind : env.find? eqName = some eqA)
    (ψ : Name → Nat) (ρ : Nat → V) (A a : VExpr)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A)
    {A' : V} {B' : V → V}
    (hpi : SetTheory.app
        (SetTheory.app (interp V ρ (cval eqName ψ)) (interp V ρ A))
        (interp V ρ a) ∈ˢ piC A' B') :
    ∀ y, y ∈ˢ A' → y ∈ˢ interp V ρ A := by
  rw [(h hfind ψ).2 ρ A a hA ha] at hpi
  refine SetTheory.lamC_dom_of_ne ?_ hpi
  exact SetTheory.lamC_ne_pt_of_witness ha
    (by unfold SetTheory.eqv; exact SetTheory.truthVal_ne_pt _)

/-- **The compiler-trust opaques are the identity**, [set] form
(`ReduceOpsOk` transpose with `val := interp ∘ cval`): the stored
`Lean.reduceNat`/`Lean.reduceBool` value applied to a member of its
element type's interpretation is that member.  Established at the
opaque's install from the identity certificate; consumed at the
`ofReduce*` axioms' install (their types become trivially
inhabited). -/
def ReduceOpsV (env : Env) (cval : TConstVal) : Prop :=
  ∀ c ∈ reduceOpNames, ∀ cv, env.find? c = some (.axiomInfo cv) →
    ConstantVal.matchesPin cv (reduceOpCvA c) = true →
    (env.find? (reduceElemName c)).isSome = true ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ (cval (reduceElemName c) ψ) →
      SetTheory.app (interp V ρ (cval c ψ)) x = x

/-! ## The empty-environment law instances -/

theorem EqLawV.empty (cval : TConstVal) : EqLawV V Env.empty cval := by
  intro h
  simp [Env.find?, Env.empty] at h

theorem ReduceOpsV.empty (cval : TConstVal) :
    ReduceOpsV V Env.empty cval := by
  intro c hc cv h
  simp [Env.find?, Env.empty] at h

theorem RecRulesV.empty (cval : TConstVal) (φ : Name → Nat) :
    RecRulesV V Env.empty cval φ := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

theorem CapsOkV.empty (cval : TConstVal) : CapsOkV V Env.empty cval := by
  refine ⟨?_, ?_⟩ <;> (intro T cvT caps h; simp [Env.find?, Env.empty] at h)

theorem NatOpsV.empty (cval : TConstVal) (φ : Name → Nat) :
    NatOpsV V Env.empty cval φ := by
  intro c hc cv v hint h
  simp [Env.find?, Env.empty] at h

theorem DivModV.empty (cval : TConstVal) (φ : Name → Nat) :
    DivModV V Env.empty cval φ := by
  intro c hc cv v hint h
  simp [Env.find?, Env.empty] at h

/-! ## The invariant -/

/-- A [set] model of an environment: a term valuation of the constants
such that the environment is well-formed, each valuation leaf is
closed and truthful, each constant's interpretation inhabits its
denoted type's (which is truthful), each definition/theorem is valued
by its body's denotation, and the stored semantic laws hold in the
fired membership/interp-equality forms.  See the module docstring for
the field-by-field `EnvTT` correspondence. -/
structure EnvS (env : Env) where
  /-- The term valuation of each constant. -/
  cval : TConstVal
  /-- Every valuation leaf is closed (`EnvTT.cval_closed`, verbatim). -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (cval n ψ)
  /-- Stored declarations are syntactically well-formed. -/
  wf : EnvWF env
  /-- A constant's term only depends on its own level parameters. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂
  /-- **Every valuation leaf is truthful at every environment** —
  `EnvModel.annot_ok`'s successor, in the total-`interp` form.  For
  stored constants the supplier is the value front door's subject
  conjunct; the pinned/basis leaves are `AnnotOkV`-trivial or carry
  their packages by construction. -/
  annot_okV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkV V ρ (cval n ψ)
  /-- **Every stored constant inhabits its denoted type's
  interpretation, and the denoted type is truthful.**  The transpose of
  `EnvModel.mem_type` plus the type front door's subject conjunct
  (design §2; the truthfulness component is what I3-sound consumes
  through `EnvSHyp.mem_type`). -/
  mem_type : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    ∃ t, denoteClosed cval env φ c.toConstantVal.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (cval c.name φ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t
  /-- Every definition is denoted by its body (this is what deletes
  delta: a definition head and its unfolding are the same `VExpr`). -/
  defn_eq : ∀ cv value hint,
    ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- Every theorem is denoted by its proof value (equation only —
  `EnvModel.thm_ok`'s `AnnotOk` conjunct is `annot_okV` above). -/
  thm_ok : ∀ cv value,
    ConstantInfo.thmInfo cv value ∈ env.consts → ∀ φ : Name → Nat,
      denoteClosed cval env φ value = some (cval cv.name φ)
  /-- The pinned empty type is valued by the layer's `Empty`
  (`EnvTT.empty_pinned`, verbatim; the consistency corollary's key). -/
  empty_pinned : ∀ ψ : Name → Nat, ∃ u, cval emptyName ψ = emptyT u
  /-- The reserved basis constants are the pinned declarations, valued
  by their direct pins (V-free, shared with the TT lane). -/
  basis_pinned : BasisPinnedTT env cval
  /-- Every stored native projection-table entry is a pinned pair entry
  with its block stored (V-free, shared). -/
  proj_ok : ProjOkT env
  /-- Every stored recursor rule's constructor is stored (V-free,
  shared; consumed by `RecRulesV.cons` at every install). -/
  rec_ctors : RecCtorsStored env
  /-- The pinned `Eq` spine interprets to the layer's truth-set former
  (`EqLawV`; consumed by the div/mod and iota install derivations and
  the axiom keys). -/
  eq_lawV : EqLawV V env cval
  /-- The fired modeled-iota contract at every assignment
  (`RecRulesV`; discharges `EnvSHyp.rec_rules`). -/
  rec_rules : ∀ φ : Name → Nat, RecRulesV V env cval φ
  /-- The stored families' fired capability laws (`CapsOkV`). -/
  caps_ok : CapsOkV V env cval
  /-- The structural-`Nat` operations' semantic certificates at every
  assignment (`NatOpsV`). -/
  nat_ops : ∀ φ : Name → Nat, NatOpsV V env cval φ
  /-- The pin-certified WF-recursive operations' guarded value
  recurrences at every assignment (`DivModV`). -/
  div_mod : ∀ φ : Name → Nat, DivModV V env cval φ
  /-- Every stored compiler-trust opaque is the identity on its element
  type (`ReduceOpsV`). -/
  reduce_ops : ReduceOpsV V env cval

/-- The empty environment has a (trivial) [set] model. -/
def EnvS.empty : EnvS V Env.empty where
  cval := fun _ _ => emptyT 0
  cval_closed := fun _ _ => trivial
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  annot_okV := fun _ _ _ => trivial
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value hint h; cases h
  thm_ok := by intro cv value h; cases h
  empty_pinned := fun _ => ⟨0, rfl⟩
  basis_pinned := BasisPinnedTT.empty _
  proj_ok := ProjOkT.empty
  rec_ctors := RecCtorsStored.empty
  eq_lawV := EqLawV.empty V _
  rec_rules := RecRulesV.empty V _
  caps_ok := CapsOkV.empty V _
  nat_ops := NatOpsV.empty V _
  div_mod := DivModV.empty V _
  reduce_ops := ReduceOpsV.empty V _

/-! ## Discharging `EnvSHyp`

The T4 interface, by projection.  The only non-`exact` move is
`mem_type`'s instantiation crossing (`denote_instLevels`): the field is
keyed at each assignment on the *stored* type, `EnvSHyp` at I3's side
conditions on the *instantiated* one, and the two meet at the composed
assignment `Level.substFn φ lps us`. -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold Setlec.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold Setlec.Env.find? at h
  exact List.mem_of_find?_eq_some h

/-- `EnvS` discharges the soundness tier's hypothesis bundle at every
assignment. -/
theorem EnvS.toHyp {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) (φ : Name → Nat) :
    EnvSHyp V env m.cval φ where
  cval_closed := m.cval_closed
  annot_okV := m.annot_okV
  mem_type := by
    intro n ci hf us hlen T hden
    have hname := Env.find?_name hf
    have hmem := Env.find?_mem hf
    unfold denoteClosed at hden
    rw [denote_instLevels (env := env) (cval := m.cval)
        (hp := fun n' ci' hf' => m.val_params n' ci' hf') φ 0
        ci.toConstantVal.type] at hden
    obtain ⟨t, ht, hlaw⟩ :=
      m.mem_type ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
    unfold denoteClosed at ht
    rw [ht] at hden
    obtain rfl := Option.some.inj hden
    intro ρ
    have := hlaw ρ
    rwa [hname] at this
  basis_pinned := m.basis_pinned
  caps_ok := m.caps_ok
  proj_ok := m.proj_ok
  nat_ops := m.nat_ops φ
  div_mod := m.div_mod φ
  rec_rules := m.rec_rules φ

/-! ## What the invariant delivers per declaration

Transpose of `EnvTT.hasType_defn`/`hasType_thm`: a stored `def` or
`theorem`'s value denotes, its type denotes, and the value's
interpretation inhabits the type's — the declaration-level theorem as
a two-line consequence of the invariant. -/

/-- A stored definition's body inhabits its stated type's
interpretation. -/
theorem EnvS.memType_defn {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧
      ∀ ρ : Nat → V, interp V ρ v ∈ˢ interp V ρ t := by
  obtain ⟨t, ht, hd⟩ := m.mem_type _ hc φ
  exact ⟨_, t, m.defn_eq cv value hint hc φ, ht, fun ρ => (hd ρ).1⟩

/-- A stored theorem's proof value inhabits its statement's
interpretation. -/
theorem EnvS.memType_thm {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env)
    {cv : ConstantVal} {value : Expr}
    (hc : ConstantInfo.thmInfo cv value ∈ env.consts) (φ : Name → Nat) :
    ∃ v t, denoteClosed m.cval env φ value = some v ∧
      denoteClosed m.cval env φ cv.type = some t ∧
      ∀ ρ : Nat → V, interp V ρ v ∈ˢ interp V ρ t := by
  obtain ⟨t, ht, hd⟩ := m.mem_type _ hc φ
  exact ⟨_, t, m.thm_ok cv value hc φ, ht, fun ρ => (hd ρ).1⟩

end Setlec.SetR
