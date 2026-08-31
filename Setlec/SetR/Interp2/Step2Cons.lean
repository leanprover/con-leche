import Setlec.SetR.Interp2.Keys2Bundle
import Setlec.SetR.Interp2.EmptyPin2
import Setlec.SetR.Interp2.Denote2Closed
import Setlec.SetR.Install.ValueKinds

/-!
# The install step over `interp2`: the `cons` shape, and the value kinds

Seal 51's inhabitation table listed `DeclStep2All` as one of the four
uninhabited residues behind the fourteen swaps.  This file is the part
of it that does not wait on the junction: the **shape** of a
single-constant install at the annotated tier, generalised off the
axiom kind, plus the value kinds' own reduction — where the front
door's exposed run (seal 49) is what supplies the new leaf.

## What is derived here and what is not

`declStep2_of_cons` is `declStep2_of_axiom` (`Keys2Cond.lean`) at an
**arbitrary** `c₀`.  The axiom version could discharge `acval_defn`
and `acval_thm`'s head cases by `nomatch` — a stored axiom is neither
a `def` nor a `thm`.  At a general `c₀` those two clauses have content
and become premises, and naming them is what makes the value kinds
statable at all.

`declStep2_of_value` then **discharges three of those premises** from
the front door:

* `hAerase` — from the collapse lane's own leaf equation.  v1 values
  a stored body by its denotation, so once the extension's valuation
  agrees with the prefix's away from the new name the erasure link is
  `denote2_erase` and `Installs.denoteUp`, and nothing else.
* `hdefnA` / `hthmA` — from `Denote2EnvExtend` plus the annotation the
  front door's run guarantees at the *prefix*.  This is the
  composition seal 45 designed: the residue moved from an object no
  run has as its subject to a body every install demonstrably ran on.

**And one premise it cannot discharge, which is a finding.**
`EnvS2U.acval_defn` quantifies over **every** `CheckMode`, while the
front door ran in **one**.  `denote2` reads the mode (through
`sortOfE`/`lamSortE`, which call `inferTypeCore μ`), so the annotation
at another mode need not be the one the install stored — and nothing
in the tree says otherwise.  That gap is named here as
`Denote2ModeAgree` rather than papered over.

*The prefix/extension rule of seal 47, one axis over: a step lemma
whose premise and conclusion live at different **modes** must carry
the agreement, or it is a wish with a signature.*
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo ConstantVal
  ReducibilityHint BasisKind)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {μ : CheckMode}

/-! ## The `cons` shape -/

/-- **`DeclStep2` at any fresh single-constant install.**
`declStep2_of_axiom` generalised off the axiom kind: the two body
clauses the axiom version closed by `nomatch` are premises here, and
everything else is verbatim.

Five of the nine fields extend by `Install2.lean`'s lemmas; the two
`denote2` fields and `mem_type2` compose `denote2_acvalWith_fresh` at
the prefix with `Denote2EnvExtend` across the install. -/
theorem declStep2_of_cons (m : EnvS2U V env) {c₀ : ConstantInfo}
    {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval c₀.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal)
    (hdefnA : ∀ (ν : CheckMode) (ψ : Name → Nat) (F : Nat)
      (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint = c₀ →
      ∀ {ra : AVExpr},
        denote2 ν (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F 0 value = some ra → ra = A ψ)
    (hthmA : ∀ (ν : CheckMode) (ψ : Name → Nat) (F : Nat)
      (cv : ConstantVal) (value : Expr),
      ConstantInfo.thmInfo cv value = c₀ →
      ∀ {ra : AVExpr},
        denote2 ν (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F 0 value = some ra → ra = A ψ) :
    DeclStep2 V ⟨c₀ :: env.consts⟩ := by
  have hbound := envWF_constsBound m.base.wf
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  have hcomp : ∀ (ν : CheckMode) (ψ : Name → Nat) (F d : Nat)
      (e : Expr), ConstsBound env e →
      denote2 ν (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F d e
        = denote2 ν m.acval env ψ F d e := by
    intro ν ψ F d e hcb
    rw [← hext ν ψ F d e hcb, denote2_acvalWith_fresh hfresh d e]
  refine ⟨{
    base := hbase
    acval := acvalWith m.acval c₀.name A
    acval_erase := ?_
    acval_closed := acvalWith_closed m.acval_closed hAclosed
    acval_params := acvalWith_params m.acval_params hAparams
    acval_ok2 := acvalWith_ok2 m.acval_ok2 hAok
    acval_defn := ?_
    acval_thm := ?_
    mem_type2 := ?_ }⟩
  · -- `acval_erase`
    intro n ψ
    by_cases hn : n = c₀.name
    · subst hn; rw [acvalWith_self]; exact hAerase ψ
    · rw [acvalWith_ne hn, m.acval_erase, hag n hn]
  · -- `acval_defn`
    intro ν ψ F cv value hint hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · rw [show cv.name = c₀.name from
        congrArg ConstantInfo.name h, acvalWith_self]
      exact hdefnA ν ψ F cv value hint h hra
    · rw [hcomp ν ψ F 0 value ((hbound _ h).2.1 cv value hint rfl)]
        at hra
      rw [acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
      exact m.acval_defn ν ψ F cv value hint h hra
  · -- `acval_thm`
    intro ν ψ F cv value hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · rw [show cv.name = c₀.name from
        congrArg ConstantInfo.name h, acvalWith_self]
      exact hthmA ν ψ F cv value h hra
    · rw [hcomp ν ψ F 0 value ((hbound _ h).2.2 cv value rfl)] at hra
      rw [acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
      exact m.acval_thm ν ψ F cv value h hra
  · -- `mem_type2`
    intro ν ψ fuel c hc ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h
      obtain ⟨F', ta', hle, hden', hall⟩ := hmem ν ψ fuel
      obtain rfl : ta = ta' :=
        Option.some.inj
          ((denote2_fuelMono hle 0 _ hta).symm.trans hden')
      exact (hall ρ).1
    · rw [hcomp ν ψ fuel 0 _ (hbound _ h).1] at hta
      rw [acvalWith_ne (hne _ h)]
      exact m.mem_type2 ν ψ fuel c h ta hta ρ

/-! ## The mode gap, named

`EnvS2U.acval_defn` and `acval_thm` are stated at **every**
`CheckMode`; the install has exactly **one** run, in the mode the
stream was checked in.  On the v1 lane the question does not arise —
`denote` takes no mode — so this is a gap the annotated tier
introduces on its own, and it sits in the same family as seal 47's
prefix/extension trap. -/

/-- **The mode residue**: a stored body's annotation does not depend
on the mode the run was made in.

*Provenance*: `denote2`'s binder clauses call `sortOfE`/`lamSortE`,
which run `inferTypeCore μ` — so the numerals a λ or a `∀` carries are
a mode's output, and `EnvS2U`'s two body fields ask about all modes.

*Discharges*: unknown.  The `ν = μ` instance is
`denote2_agree_same` below, so this is **not** a vacuous `Prop`; the
open part is exactly the mode crossing.  Nothing in this tree supplies
it, and no exposure on the checker side can — the front door makes one
run, in one mode.

**TOMBSTONE (seal 53): dissolved by de-generalization, not supplied.**
The demand is *withdrawn*, not met.  Seal 53 measured that no consumer
of `acval_defn`/`acval_thm` ever reads the field outside its own mode,
so the all-mode quantification was gratuitous; `EnvS2UM`
(`Annot/EnvS2U.lean`) indexes the two fields to the install's mode and
the mode-indexed lane below carries **no** `Denote2ModeAgree` premise
anywhere — `hback` closes by `denote2_agree_same`, the very instance
that told this residue apart from a vacuous `Prop`.

The definition stays, un-weakened, because the *all-mode* lane
(`declStep2_of_value`) still consumes it and nothing here supplies it
there. -/
def Denote2ModeAgree (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (value : Expr) : Prop :=
  ∀ (ν : CheckMode) (ψ : Name → Nat) (F F' : Nat) (ra ra' : AVExpr),
    denote2 μ acval env ψ F 0 value = some ra →
    denote2 ν acval env ψ F' 0 value = some ra' → ra = ra'

/-- **The same-mode instance is free** — `denote2` is fuel-monotone,
so two successes at one mode agree.  This is what tells the residue
above apart from an assertion with no content: everything it asks for
beyond this is the mode crossing. -/
theorem denote2_agree_same {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat} {F F' : Nat} {value : Expr} {ra ra' : AVExpr}
    (h : denote2 μ acval env ψ F 0 value = some ra)
    (h' : denote2 μ acval env ψ F' 0 value = some ra') : ra = ra' := by
  have h1 := denote2_fuelMono (Nat.le_max_left F F') 0 value h
  have h2 := denote2_fuelMono (Nat.le_max_right F F') 0 value h'
  exact Option.some.inj (h1.symm.trans h2)

/-! ## The value kinds

`def`, `theorem` and `opaque` install one constant whose **body** the
front door inferred a type for, at the prefix, before the install
(`checkDefnVal`, `Kernel/Checker.lean`).  Seal 49 landed that run on
`ValueFrontR` as an exposed conjunct; here is what it buys. -/

/-- **`DeclStep2` at a value install.**  Three of `declStep2_of_cons`'s
premises are discharged rather than carried:

* `hAerase`, from `hag` and `hleaf` — `denote2_erase` puts the leaf's
  erasure where the collapse lane's own body equation already is;
* `hdefnA`/`hthmA`, from `hA` and `hext` — the annotation the front
  door's run guarantees at the prefix, transported across the install
  and identified by `hmode`.

What is left is the fresh leaf's three own laws, the new constant's
`MemberBlock2`, the frozen transport, and the mode residue. -/
theorem declStep2_of_value (m : EnvS2U V env) {c₀ : ConstantInfo}
    {value' : Expr} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hcb : ConstsBound env value')
    (hA : ∀ ψ : Name → Nat, ∃ F : Nat,
      denote2 μ m.acval env ψ F 0 value' = some (A ψ))
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hleaf : ∀ ψ : Name → Nat,
      denoteClosed hbase.cval ⟨c₀ :: env.consts⟩ ψ value'
        = some (hbase.cval c₀.name ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal)
    (hmode : Denote2ModeAgree μ env m.acval value')
    (hdb : ∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value')
    (htb : ∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value') :
    DeclStep2 V ⟨c₀ :: env.consts⟩ := by
  have hback : ∀ (ν : CheckMode) (ψ : Name → Nat) (F : Nat)
      {ra : AVExpr},
      denote2 ν (acvalWith m.acval c₀.name A)
        ⟨c₀ :: env.consts⟩ ψ F 0 value' = some ra → ra = A ψ := by
    intro ν ψ F ra hra
    rw [← hext ν ψ F 0 value' hcb,
      denote2_acvalWith_fresh hfresh 0 value'] at hra
    obtain ⟨F₀, hF₀⟩ := hA ψ
    exact (hmode ν ψ F₀ F (A ψ) ra hF₀ hra).symm
  refine declStep2_of_cons m hfresh hbase hag ?_ hAclosed hAparams hAok
    hext hmem ?_ ?_
  · -- `hAerase`
    intro ψ
    obtain ⟨F, hF⟩ := hA ψ
    have hup := (Installs.of_fresh hfresh hag).denoteUp
      (denote2_erase m.acval_erase 0 value' hF)
    exact Option.some.inj (hup.symm.trans (hleaf ψ))
  · -- `hdefnA`
    intro ν ψ F cv value hint hc ra hra
    obtain rfl := hdb cv value hint hc
    exact hback ν ψ F hra
  · -- `hthmA`
    intro ν ψ F cv value hc ra hra
    obtain rfl := htb cv value hc
    exact hback ν ψ F hra

/-- **The leaf equation is free at a `def`** — it is `EnvS.defn_eq` at
the extension.  So `declStep2_of_value`'s `hleaf` is a residue only at
the `opaque` kind, where v1 stores an axiom and keeps no equation
between the discarded body and the leaf. -/
theorem leafEq_defn {cv : ConstantVal} {value' : Expr}
    {hint : ReducibilityHint}
    (hbase : EnvS V ⟨ConstantInfo.defnInfo cv value' hint ::
      env.consts⟩) (ψ : Name → Nat) :
    denoteClosed hbase.cval
        ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ ψ value'
      = some (hbase.cval
          (ConstantInfo.defnInfo cv value' hint).name ψ) :=
  hbase.defn_eq cv value' hint List.mem_cons_self ψ

/-- …and at a `theorem`, by `EnvS.thm_ok`. -/
theorem leafEq_thm {cv : ConstantVal} {value' : Expr}
    (hbase : EnvS V ⟨ConstantInfo.thmInfo cv value' :: env.consts⟩)
    (ψ : Name → Nat) :
    denoteClosed hbase.cval
        ⟨ConstantInfo.thmInfo cv value' :: env.consts⟩ ψ value'
      = some (hbase.cval (ConstantInfo.thmInfo cv value').name ψ) :=
  hbase.thm_ok cv value' List.mem_cons_self ψ

/-! ### What the front door supplies to the value install

Two of `declStep2_of_value`'s premises are not residues at all: they
are `ValueFrontR`'s own conjuncts, spent here so that the reduction's
honest cost is the *other* six.  `hA` in particular is what seal 49's
exposure was landed for — this is its first consumer. -/

/-- `ValueFrontR`'s `constsResolve` conjunct, as the transport's side
condition.  **Inhabited from real runs.** -/
theorem constsBound_of_valueFrontR {F : Nat} {cval : TConstVal}
    {cv : ConstantVal} {value type' value' : Expr}
    (hvf : ValueFrontR μ F env cval cv value type' value') :
    ConstsBound env value' :=
  constsBound_of_constsResolve _ hvf.2.2.2.2.1

/-- **Seal 49's exposed run, spent.**  `ValueFrontR` records that the
front door inferred a type for the *annotated value* — the term that
gets stored — at the *pre-install* environment.  Feeding that run to
`Denote2BodyOfRun` names the install's leaf, and the leaf is what
`acval_defn` is about.

*This is the composition seal 45 designed and seal 47 could not write
down*, because the run was not on the pack yet. -/
theorem exists_leaf_of_valueFrontR {F : Nat} {cval : TConstVal}
    {cv : ConstantVal} {value type' value' : Expr}
    {acval : Name → (Name → Nat) → AVExpr}
    (hrun : ∀ ψ : Name → Nat, Denote2BodyOfRun μ env acval ψ)
    (hvf : ValueFrontR μ F env cval cv value type' value') :
    ∃ A : (Name → Nat) → AVExpr, ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ acval env ψ F' 0 value' = some (A ψ) := by
  obtain ⟨vtype, hvt⟩ := hvf.2.2.2.2.2.1
  exact ⟨fun ψ => (hrun ψ value' vtype F hvt).choose_spec.choose,
    fun ψ => ⟨(hrun ψ value' vtype F hvt).choose,
      (hrun ψ value' vtype F hvt).choose_spec.choose_spec⟩⟩

/-- …and the same two conjuncts are exactly `NewBodyFrontR`, so
`denote2BodiesStep_holds` applies at every value install. -/
theorem newBodyFrontR_of_valueFrontR {F : Nat} {cval : TConstVal}
    {cv : ConstantVal} {value type' value' : Expr}
    {c₀ : ConstantInfo}
    (hvf : ValueFrontR μ F env cval cv value type' value')
    (hdb : ∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      c₀ = ConstantInfo.defnInfo cv2 v2 h2 → v2 = value')
    (htb : ∀ (cv2 : ConstantVal) (v2 : Expr),
      c₀ = ConstantInfo.thmInfo cv2 v2 → v2 = value') :
    NewBodyFrontR μ env c₀ := by
  obtain ⟨vtype, hvt⟩ := hvf.2.2.2.2.2.1
  constructor
  · intro cv2 v2 h2 heq
    obtain rfl := hdb cv2 v2 h2 heq
    exact ⟨constsBound_of_valueFrontR hvf, vtype, F, hvt⟩
  · intro cv2 v2 heq
    obtain rfl := htb cv2 v2 heq
    exact ⟨constsBound_of_valueFrontR hvf, vtype, F, hvt⟩

/-! ### The value kinds' residue list, in one structure -/

/-- **What a value install still owes**, at the leaf the front door's
run already named.  Six fields; none of them is inhabited in this
tree, and each says why.

The contrast with `declStep2_of_cons`'s twelve premises is the batch's
measurement: `hfresh`, `hcb`, `hA`, `hag`, `hleaf`, `hAerase`,
`hdefnA` and `hthmA` are all supplied — by `ConstantValR`,
`ValueFrontR`, v1's own install, or by proof — and what is left is
this. -/
structure ValueResidues2 (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvS2U V env) (c₀ : ConstantInfo)
    (value' : Expr) (A : (Name → Nat) → AVExpr) where
  /-- The new leaf is closed.  *Provenance*: `denote2`'s output on a
  closed subject; v1's twin is `denote_closed`.  *Discharges*: with a
  `denote2` closedness lemma, which this tree does not have. -/
  closed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ
  /-- …reads only its own level parameters.  *Provenance*: v1's
  `denote_params_ext`.  *Discharges*: with its `denote2` twin. -/
  params : ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂
  /-- …and is truthful.  *Provenance*: v1 reads this off the value
  front door through `Infer.sound`; the annotated twin is the claims'
  `InferClaims2E`, so it lands with `CheckStep2E`. -/
  ok2 : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)
  /-- `denote2` is stable across the install.  *Provenance*:
  `Keys2.lean`.  **Frozen on Θ.** -/
  extend : ∀ (ν : CheckMode) (ψ : Name → Nat),
    Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
      (acvalWith m.acval c₀.name A) ψ
  /-- `MemberBlock2` at the new constant.  *Provenance*: the
  install-tier half seal 40 measured; no key at the prefix supplies
  it. -/
  newMember : ∀ (ν : CheckMode) (ψ : Name → Nat),
    MemberBlock2 V ν ⟨c₀ :: env.consts⟩
      (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal
  /-- The body's annotation does not depend on the mode.
  *Provenance*: this file's finding.  *Discharges*: unknown. -/
  modeAgree : Denote2ModeAgree μ env m.acval value'

/-- **The value kinds' reduction, assembled.**  Everything the front
door and v1's install supply is spent here; the hypothesis `hres` is
the honest remainder, and it is quantified over the leaf because the
leaf is chosen by the run rather than by the caller. -/
theorem declStep2_of_valueResidues (m : EnvS2U V env)
    {c₀ : ConstantInfo} {F : Nat} {cv : ConstantVal}
    {value type' value' : Expr}
    (hfresh : env.find? c₀.name = none)
    (hvf : ValueFrontR μ F env m.base.cval cv value type' value')
    (hrun : ∀ ψ : Name → Nat, Denote2BodyOfRun μ env m.acval ψ)
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hleaf : ∀ ψ : Name → Nat,
      denoteClosed hbase.cval ⟨c₀ :: env.consts⟩ ψ value'
        = some (hbase.cval c₀.name ψ))
    (hdb : ∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value')
    (htb : ∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value')
    (hres : ∀ A : (Name → Nat) → AVExpr,
      (∀ ψ : Name → Nat, ∃ F' : Nat,
        denote2 μ m.acval env ψ F' 0 value' = some (A ψ)) →
      ValueResidues2 V μ m c₀ value' A) :
    DeclStep2 V ⟨c₀ :: env.consts⟩ := by
  obtain ⟨A, hA⟩ := exists_leaf_of_valueFrontR hrun hvf
  obtain ⟨hcl, hpa, hok, hex, hme, hmo⟩ := hres A hA
  exact declStep2_of_value m hfresh (constsBound_of_valueFrontR hvf)
    hA hbase hag hleaf hcl hpa hok hex hme hmo hdb htb

/-! ## The six kinds' obligations, and the dispatch

The shape is `Install/Step.lean`'s `declStepS`, at the annotated tier:
one obligation per kind, and the dispatch itself proved because
`DeclR`'s six clauses *are* the dispatch.

Three of the six kinds share one obligation — `def`, `theorem` and
`opaque` differ only in which `ConstantInfo` they store, and
`declStep2_of_value` is stated at the stored `c₀` rather than per
kind.  The axiom kind's **fourth branch** (a tolerated axiom, which
installs nothing) is discharged here rather than assumed: it does not
move the environment, so the given `EnvS2U` answers for it. -/

/-- **The value kinds' install obligation.**  The stored constant is
`c₀`, whose body — when it has one — is the annotated value `value'`
the front door ran on.

*Reduces to*: `declStep2_of_value`'s residue list.  **Not inhabited in
this tree**: `hAclosed`, `hAparams`, `hAok`, `hmem`, `hext` and
`hmode` all remain open there. -/
def DeclValue2S (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} {cv : ConstantVal}
    {value type' value' : Expr} {c₀ : ConstantInfo}
    (m : EnvS2U V env),
    ConstantValR μ F env m.base.cval cv type' →
    ValueFrontR μ F env m.base.cval cv value type' value' →
    c₀.toConstantVal = ⟨cv.name, cv.levelParams, type'⟩ →
    (∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value') →
    (∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value') →
    DeclStep2 V ⟨c₀ :: env.consts⟩

/-- **The axiom kind's install obligation**, at the three branches
that store something.  *Reduces to*: `declStep2_of_axiom`'s residue
list (`DeclStep2Residues`, `Keys2Bundle.lean`).  **Not inhabited in
this tree.** -/
def DeclAxiom2S (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (m : EnvS2U V env),
    ConstantValR μ F env m.base.cval cv type' →
    DeclStep2 V
      ⟨ConstantInfo.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩

/-- **The pinned basis blocks' install obligation.**  *Provenance*:
v1's `DeclBasisS`.  **No interp2 counterpart exists at all** — the
pinned valuations' annotated twins are not built anywhere in this
tree. -/
def DeclBasis2S (V : Type w) [SetTheory V] : Prop :=
  ∀ {env env₂ : Env} {kind : BasisKind},
    Nonempty (EnvS2U V env) → DeclBasisR env kind env₂ →
    Nonempty (EnvS2U V env₂)

/-- **The modeled-inductive blocks' install obligation.**
*Provenance*: v1's `DeclIndS`.  **No interp2 counterpart exists at
all.**  The eta side invariant is v1's and is not re-proved here, so
it enters as it does in `declStepS`. -/
def DeclInd2S (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    (m : EnvS2U V env),
    EtaFamiliesClosed env →
    DeclIndR μ F env m.base.cval block env₂ →
    Nonempty (EnvS2U V env₂)

/-! ## The mode-indexed lane — seal 53's ruling, landed

Everything below is the lane above at `EnvS2UM` (`Annot/EnvS2U.lean`),
i.e. with the two `denote2` body fields asking only about the
install's own mode.  Two differences, and both are the point:

* `declStep2M_of_cons` takes `hdefnA`/`hthmA` at `μ` alone, because
  that is all the target field asks for;
* `declStep2M_of_value` therefore needs **no** mode residue —
  `denote2_agree_same` closes what `Denote2ModeAgree` was carrying,
  and `ValueResidues2M` has four fields where `ValueResidues2` has
  six — the sixth, `closed`, is *proved* here rather than removed
  (`valueLeaf_closed`, on `Denote2Closed.lean`'s twin).

Nothing else moved: `hext`, `hmem` and `mem_type2` stay all-mode,
since seal 53's measurement was about the two body fields and not
about them. -/

/-- `DeclStep2` (`Keys2.lean`) at the mode-indexed invariant. -/
def DeclStep2M (V : Type w) [SetTheory V] (μ : CheckMode)
    (env₂ : Env) : Prop :=
  Nonempty (EnvS2UM V μ env₂)

/-- **`declStep2_of_cons` at one mode.**  The proof is that one with
the mode binder of the two body clauses dropped; the `mem_type2`
branch is untouched because that field did not move. -/
theorem declStep2M_of_cons (m : EnvS2UM V μ env) {c₀ : ConstantInfo}
    {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval c₀.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal)
    (hdefnA : ∀ (ψ : Name → Nat) (F : Nat)
      (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint = c₀ →
      ∀ {ra : AVExpr},
        denote2 μ (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F 0 value = some ra → ra = A ψ)
    (hthmA : ∀ (ψ : Name → Nat) (F : Nat)
      (cv : ConstantVal) (value : Expr),
      ConstantInfo.thmInfo cv value = c₀ →
      ∀ {ra : AVExpr},
        denote2 μ (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F 0 value = some ra → ra = A ψ) :
    DeclStep2M V μ ⟨c₀ :: env.consts⟩ := by
  have hbound := envWF_constsBound m.base.wf
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  have hcomp : ∀ (ν : CheckMode) (ψ : Name → Nat) (F d : Nat)
      (e : Expr), ConstsBound env e →
      denote2 ν (acvalWith m.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ F d e
        = denote2 ν m.acval env ψ F d e := by
    intro ν ψ F d e hcb
    rw [← hext ν ψ F d e hcb, denote2_acvalWith_fresh hfresh d e]
  refine ⟨{
    base := hbase
    acval := acvalWith m.acval c₀.name A
    acval_erase := ?_
    acval_closed := acvalWith_closed m.acval_closed hAclosed
    acval_params := acvalWith_params m.acval_params hAparams
    acval_ok2 := acvalWith_ok2 m.acval_ok2 hAok
    acval_defn := ?_
    acval_thm := ?_
    mem_type2 := ?_ }⟩
  · -- `acval_erase`
    intro n ψ
    by_cases hn : n = c₀.name
    · subst hn; rw [acvalWith_self]; exact hAerase ψ
    · rw [acvalWith_ne hn, m.acval_erase, hag n hn]
  · -- `acval_defn`, at `μ` only
    intro ψ F cv value hint hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · rw [show cv.name = c₀.name from
        congrArg ConstantInfo.name h, acvalWith_self]
      exact hdefnA ψ F cv value hint h hra
    · rw [hcomp μ ψ F 0 value ((hbound _ h).2.1 cv value hint rfl)]
        at hra
      rw [acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
      exact m.acval_defn ψ F cv value hint h hra
  · -- `acval_thm`, at `μ` only
    intro ψ F cv value hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · rw [show cv.name = c₀.name from
        congrArg ConstantInfo.name h, acvalWith_self]
      exact hthmA ψ F cv value h hra
    · rw [hcomp μ ψ F 0 value ((hbound _ h).2.2 cv value rfl)] at hra
      rw [acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
      exact m.acval_thm ψ F cv value h hra
  · -- `mem_type2`, still at every mode
    intro ν ψ fuel c hc ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h
      obtain ⟨F', ta', hle, hden', hall⟩ := hmem ν ψ fuel
      obtain rfl : ta = ta' :=
        Option.some.inj
          ((denote2_fuelMono hle 0 _ hta).symm.trans hden')
      exact (hall ρ).1
    · rw [hcomp ν ψ fuel 0 _ (hbound _ h).1] at hta
      rw [acvalWith_ne (hne _ h)]
      exact m.mem_type2 ν ψ fuel c h ta hta ρ

/-- **`declStep2_of_axiom` (`Keys2Cond.lean`) at one mode**, and here
it is a corollary rather than a second proof: a stored axiom is
neither a `def` nor a `thm`, so the two body premises are `nomatch`. -/
theorem declStep2M_of_axiom (m : EnvS2UM V μ env) {cvA : ConstantVal}
    {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? cvA.name = none)
    (hbase : EnvS V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩)
    (hag : ∀ n, n ≠ cvA.name → m.base.cval n = hbase.cval n)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval cvA.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cvA.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env
        ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
        (acvalWith m.acval cvA.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
        (acvalWith m.acval cvA.name A) ψ cvA) :
    DeclStep2M V μ ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩ :=
  declStep2M_of_cons m hfresh hbase hag hAerase hAclosed hAparams
    hAok hext hmem (fun _ _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq)

/-- **`declStep2_of_value` at one mode, and the mode residue is
gone.**  Where the all-mode version had to cross from the front
door's `μ` to an arbitrary `ν` — and carried `Denote2ModeAgree` to do
it — this one identifies two runs *in the same mode*, which is
`denote2_agree_same`. -/
theorem declStep2M_of_value (m : EnvS2UM V μ env) {c₀ : ConstantInfo}
    {value' : Expr} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hcb : ConstsBound env value')
    (hA : ∀ ψ : Name → Nat, ∃ F : Nat,
      denote2 μ m.acval env ψ F 0 value' = some (A ψ))
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hleaf : ∀ ψ : Name → Nat,
      denoteClosed hbase.cval ⟨c₀ :: env.consts⟩ ψ value'
        = some (hbase.cval c₀.name ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨c₀ :: env.consts⟩
        (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal)
    (hdb : ∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value')
    (htb : ∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value') :
    DeclStep2M V μ ⟨c₀ :: env.consts⟩ := by
  have hback : ∀ (ψ : Name → Nat) (F : Nat) {ra : AVExpr},
      denote2 μ (acvalWith m.acval c₀.name A)
        ⟨c₀ :: env.consts⟩ ψ F 0 value' = some ra → ra = A ψ := by
    intro ψ F ra hra
    rw [← hext μ ψ F 0 value' hcb,
      denote2_acvalWith_fresh hfresh 0 value'] at hra
    obtain ⟨F₀, hF₀⟩ := hA ψ
    exact (denote2_agree_same hF₀ hra).symm
  refine declStep2M_of_cons m hfresh hbase hag ?_ hAclosed hAparams
    hAok hext hmem ?_ ?_
  · -- `hAerase`
    intro ψ
    obtain ⟨F, hF⟩ := hA ψ
    have hup := (Installs.of_fresh hfresh hag).denoteUp
      (denote2_erase m.acval_erase 0 value' hF)
    exact Option.some.inj (hup.symm.trans (hleaf ψ))
  · -- `hdefnA`
    intro ψ F cv value hint hc ra hra
    obtain rfl := hdb cv value hint hc
    exact hback ψ F hra
  · -- `hthmA`
    intro ψ F cv value hc ra hra
    obtain rfl := htb cv value hc
    exact hback ψ F hra

/-- **What a value install still owes, at one mode.**
`ValueResidues2`'s six fields **minus two**:

* `modeAgree` — removed by seal 53's de-generalization, i.e. the
  demand was withdrawn rather than met;
* `closed` — **discharged**, not removed: `denote2_closed`
  (`Denote2Closed.lean`) proves it from the front door's own
  syntactic conjuncts, and `declStep2M_of_valueResidues` spends them.

What is left is four. -/
structure ValueResidues2M (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvS2UM V μ env) (c₀ : ConstantInfo)
    (A : (Name → Nat) → AVExpr) where
  /-- The new leaf reads only its own level parameters.
  *Provenance*: v1's `denote_params_ext`.

  **Still open, and the twin does not transpose.**  `denote2_closed`
  went through `denote2_erase`, because closedness is a fact about
  the *erasure*.  This one is not: `denote2`'s binder clauses carry
  `sortOfE`/`lamSortE` numerals, which are `Level.eval ψ` of a level
  the checker computed from an **inferred type** — precisely the
  slots `erase` forgets.  Making `A ψ₁ = A ψ₂` would need every such
  level's parameters to lie in `c₀`'s, i.e. a metatheorem saying
  `inferTypeCore`/`whnf` introduce no level parameter the subject
  does not have.  The tree has no such statement, and this is the
  same clause, in the same two constructors, at which
  `Denote2InstLevels` (`Step2/Levels.lean`) is a residue rather than
  a theorem. -/
  params : ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂
  /-- …and is truthful.  *Provenance*: the claims' `InferClaims2E`. -/
  ok2 : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)
  /-- `denote2` is stable across the install.  **Frozen on Θ.** -/
  extend : ∀ (ν : CheckMode) (ψ : Name → Nat),
    Denote2EnvExtend ν env ⟨c₀ :: env.consts⟩
      (acvalWith m.acval c₀.name A) ψ
  /-- `MemberBlock2` at the new constant. -/
  newMember : ∀ (ν : CheckMode) (ψ : Name → Nat),
    MemberBlock2 V ν ⟨c₀ :: env.consts⟩
      (acvalWith m.acval c₀.name A) ψ c₀.toConstantVal

/-- **The new leaf is closed, proved.**  `ValueResidues2.closed`'s
discharge: the front door's `value` is closed and fvar-free, the
annotator preserves both (`annotate_syntax`), and `denote2_closed`
turns a closed subject's run into a lift-invariant leaf.  The
valuation premise is the invariant's own `acval_erase` composed with
`EnvS.cval_closed`. -/
theorem valueLeaf_closed (m : EnvS2UM V μ env) {F : Nat}
    {cv : ConstantVal} {value type' value' : Expr}
    {A : (Name → Nat) → AVExpr}
    (hvf : ValueFrontR μ F env m.base.cval cv value type' value')
    (hA : ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ m.acval env ψ F' 0 value' = some (A ψ))
    (ψ : Name → Nat) (k : Nat) : (A ψ).liftN 1 k = A ψ := by
  obtain ⟨F', hF'⟩ := hA ψ
  obtain ⟨hfv, hbd⟩ := annotate_syntax hvf.2.2.1 hvf.2.1 hvf.1
  exact denote2_closed m.acval_erase m.base.cval_closed hfv hbd hF' 1 k

/-- **The value kinds' reduction at one mode, assembled.**
`declStep2_of_valueResidues` with a **four**-field remainder: the
mode residue is gone by de-generalization and the leaf's closedness
is proved here from the front door's own conjuncts. -/
theorem declStep2M_of_valueResidues (m : EnvS2UM V μ env)
    {c₀ : ConstantInfo} {F : Nat} {cv : ConstantVal}
    {value type' value' : Expr}
    (hfresh : env.find? c₀.name = none)
    (hvf : ValueFrontR μ F env m.base.cval cv value type' value')
    (hrun : ∀ ψ : Name → Nat, Denote2BodyOfRun μ env m.acval ψ)
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → m.base.cval n = hbase.cval n)
    (hleaf : ∀ ψ : Name → Nat,
      denoteClosed hbase.cval ⟨c₀ :: env.consts⟩ ψ value'
        = some (hbase.cval c₀.name ψ))
    (hdb : ∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value')
    (htb : ∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value')
    (hres : ∀ A : (Name → Nat) → AVExpr,
      (∀ ψ : Name → Nat, ∃ F' : Nat,
        denote2 μ m.acval env ψ F' 0 value' = some (A ψ)) →
      ValueResidues2M V μ m c₀ A) :
    DeclStep2M V μ ⟨c₀ :: env.consts⟩ := by
  obtain ⟨A, hA⟩ := exists_leaf_of_valueFrontR hrun hvf
  obtain ⟨hpa, hok, hex, hme⟩ := hres A hA
  exact declStep2M_of_value m hfresh (constsBound_of_valueFrontR hvf)
    hA hbase hag hleaf (valueLeaf_closed m hvf hA) hpa hok hex hme
    hdb htb

/-! ### The six kinds' obligations at one mode

The four obligations, transposed.  Each is its all-mode twin with
`EnvS2U` replaced by `EnvS2UM V μ` on **both** sides — which is what
"the index threads for free" means, and it is checked here rather
than asserted. -/

/-- **The value kinds' install obligation, at one mode.**  *Reduces
to*: `declStep2M_of_value`'s residue list, which is
`ValueResidues2M` — four fields, not six. -/
def DeclValue2SM (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} {cv : ConstantVal}
    {value type' value' : Expr} {c₀ : ConstantInfo}
    (m : EnvS2UM V μ env),
    ConstantValR μ F env m.base.cval cv type' →
    ValueFrontR μ F env m.base.cval cv value type' value' →
    c₀.toConstantVal = ⟨cv.name, cv.levelParams, type'⟩ →
    (∀ (cv2 : ConstantVal) (v2 : Expr) (h2 : ReducibilityHint),
      ConstantInfo.defnInfo cv2 v2 h2 = c₀ → v2 = value') →
    (∀ (cv2 : ConstantVal) (v2 : Expr),
      ConstantInfo.thmInfo cv2 v2 = c₀ → v2 = value') →
    DeclStep2M V μ ⟨c₀ :: env.consts⟩

/-- **The axiom kind's install obligation, at one mode.** -/
def DeclAxiom2SM (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (m : EnvS2UM V μ env),
    ConstantValR μ F env m.base.cval cv type' →
    DeclStep2M V μ
      ⟨ConstantInfo.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩

/-- **The pinned basis blocks' install obligation, at one mode.** -/
def DeclBasis2SM (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env env₂ : Env} {kind : BasisKind},
    Nonempty (EnvS2UM V μ env) → DeclBasisR env kind env₂ →
    Nonempty (EnvS2UM V μ env₂)

/-- **The modeled-inductive blocks' install obligation, at one
mode.** -/
def DeclInd2SM (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    (m : EnvS2UM V μ env),
    EtaFamiliesClosed env →
    DeclIndR μ F env m.base.cval block env₂ →
    Nonempty (EnvS2UM V μ env₂)

end Setlec.SetR.Interp2
