import ConLeche.SetP.EqTowerP
import ConLeche.SetP.DivModP
import ConLeche.SetP.NatEqsP
import ConLeche.SetP.BasisTypeOk

/-!
# The basis cons, P tier: the seven rows discharged once (task #161, ENDGAME E)

`declStepPM_of_cons` (`Interp2/InstallP.lean`) takes eleven premises;
at a *basis* cons seven of them are the same proof every time, and the
ENDGAME D seal's resume-here item 4 already observed the pattern for
`caps_ok`.  This file collapses the seven into one lemma, so that a
basis block's per-constant obligation is exactly what it should be:

> the tower (`hAerase`/`hAclosed`/`hAparams`/`hAok`/`hAvalid`) and the
> **type reading** (`htyReads`/`htyOk`/`hmemNew`), and nothing else.

The rows, and where each comes from:

| row | at a basis cons |
| --- | --- |
| `hvalReads` | vacuous — a basis cons is never a `defnInfo`/`thmInfo` |
| `nat_heads` | `natHeadsP_cons_offNat` (the `Nat` block supplies its own) |
| `nat_ops` | `natOpsP_cons_fresh`, `Or.inl`: not a `defnInfo` |
| `div_mod` | `divModP_cons_fresh`, same disjunct |
| `eq_lawP` | `eqLawP_cons_fresh` (the `Eq` block supplies its own — `eqLawP_of_tower`) |
| `caps_ok` | `capsOkP_cons_basis` at a reserved name, `capsOkP_cons_fresh` at the pair's two `projInfo`s |
| `rec_rules` | `recRulesP_cons_fresh`, on `EnvS.rec_ctors` (ENDGAME D §3a) |
| `reduce_ops` | `reduceOpsP_cons_fresh`, `Or.inl` except at `Quot.sound`, where the name decides |

Three of the eight vary across the twenty-two conses and are therefore
**disjunctive premises** rather than fixed proofs — `caps_ok`'s
(reserved name vs. the pair projections' kind) and `reduce_ops`'s
(not-an-axiom vs. `Quot.sound`'s name).  The two genuinely bespoke rows
— `nat_heads` at the `Nat` block, where the literal guard *becomes*
true, and `eq_lawP` at the `Eq` block, where `eqLawP_cons_fresh` is
structurally unavailable — are excluded by this lemma's side conditions
and go through `declStepPM_of_cons` directly.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory
open ConLeche.Semantics (AVExpr)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- The install lemmas below expose the extended carrier's leaf (the
`Eq` block's chain reads it: its constants' types mention each other
and none of them is `pinnedDirectT`).  Consumers that do not need the
leaf drop it here. -/
theorem nonempty_of_exists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) :
    Nonempty α := h.elim fun x _ => ⟨x⟩

/-- **`AnnotOkP` is `BitAgree`-invariant** — both halves are
(`AVExpr.BitAgree.ok2`/`.validV`), so the P currency crosses the
bridge between a `denoteP` reading and the `BConst.type2` tower it
agrees with.  This is what makes a basis type reading's grading a
*computation* rather than a re-derivation. -/
theorem bitAgree_okP {e e' : AVExpr} (h : e.BitAgree e')
    (ρ : Nat → V) : AnnotOkP V ρ e ↔ AnnotOkP V ρ e' :=
  and_congr (h.ok2 V ρ) (h.validV V ρ)

/-- **The P step at a basis cons.**  Seven of `declStepPM_of_cons`'s
eleven premises are discharged here; what remains is the tower and its
type's reading. -/
theorem declStepPM_of_basis_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    -- a basis cons is never a value kind
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    -- the two blocks that supply their row bespoke are excluded
    (hnN : c₀.name ≠ natName) (hnZ : c₀.name ≠ natZeroName)
    (hnS : c₀.name ≠ natSuccName) (hnEq : eqName ≠ c₀.name)
    -- a basis *recursor* cons with rules establishes `rec_rules`
    -- bespoke; one with none transports (ENDGAME D §3a)
    (hnotrec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      rules = [])
    -- `caps_ok`: a reserved name, or a kind no stored family mentions
    (hcaps : ConLeche.reservedBasisNames.contains c₀.name = true ∨
      ((∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
        (∀ cv np nf, c₀ ≠ .ctorInfo cv np nf) ∧
        (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules)))
    -- `reduce_ops`: not an axiom, or not a trusted operation's name
    (hred : (∀ cv, c₀ ≠ .axiomInfo cv) ∨
      c₀.name ∉ ConLeche.reduceOpNames)
    -- the head's own obligations (task #161 S7: what the v1 base at
    -- the extension used to supply)
    (hh : ConsHeadP env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    -- the type's reading, its grading, and the tower's membership
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry := by
      intro _ h; exact nomatch h) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_cons mp (c₀ := c₀) (A := A) hfresh hh hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hvalReads`: a basis cons is never a definition or a theorem
    intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
    · exact absurd hdt.symm (hnotthm cv2 value2)
  · -- `nat_heads`: the guard reads three names, and this is none
    exact fun φ => natHeadsP_cons_offNat mp hnN hnZ hnS _ rfl φ
  · -- `nat_ops`
    exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · -- `div_mod`
    exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · -- `eq_lawP`: `Eq` is stored in the prefix, one `acvalWith_ne`
    exact eqLawP_cons_fresh mp.eq_lawP hnEq _ rfl
  · -- `caps_ok`: reserved name, or a kind no family mentions
    rcases hcaps with hres | ⟨h1, h2, h3⟩
    · exact capsOkP_cons_basis mp mp.caps_ok hfresh hh.projTower hres _ rfl
    · exact capsOkP_cons_fresh mp mp.caps_ok hfresh hh.projTower h1 h2 h3 _ rfl
  · -- `rec_rules`: `EnvS.rec_ctors` supplies the constructor
    -- disequality, so freshness is enough (ENDGAME D §3a)
    exact fun φ => recRulesP_cons_fresh mp hfresh hh.projTower hnotrec _ rfl φ
  · -- `reduce_ops`
    exact reduceOpsP_cons_fresh mp.reduce_ops hfresh hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): no tower entry is a basis cons
    exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

/-- **The P step at a basis *recursor* cons** — `declStepPM_of_basis_cons`
with its `hnotrec` premise traded for the row itself.  Six of the seven
collapsed rows still collapse; only `rec_rules` becomes bespoke, which
is exactly what the ENDGAME F seal's §3 established for all six basis
recursors (`Empty.rec` alone has no rules and so goes through the
`hnotrec` route).

The row is taken in `natHeadsP_cons_offNat`'s shape — quantified over
any carrier whose base and `acval` are the extension's — so a caller
never has to spell `declStepPM_of_cons`'s anonymous-constructor
carrier. -/
theorem declStepPM_of_basis_rec_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    (hnN : c₀.name ≠ natName) (hnZ : c₀.name ≠ natZeroName)
    (hnS : c₀.name ≠ natSuccName) (hnEq : eqName ≠ c₀.name)
    (hres : ConLeche.reservedBasisNames.contains c₀.name = true)
    (hred : (∀ cv, c₀ ≠ .axiomInfo cv) ∨
      c₀.name ∉ ConLeche.reduceOpNames)
    (hh : ConsHeadP env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    (hrec : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRulesP m₂ φ)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry := by
      intro _ h; exact nomatch h) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_cons mp (c₀ := c₀) (A := A) hfresh hh hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
    · exact absurd hdt.symm (hnotthm cv2 value2)
  · exact fun φ => natHeadsP_cons_offNat mp hnN hnZ hnS _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact eqLawP_cons_fresh mp.eq_lawP hnEq _ rfl
  · exact capsOkP_cons_basis mp mp.caps_ok hfresh hh.projTower hres _ rfl
  · exact fun φ => hrec _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): no tower entry is a basis cons
    exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

/-- **The P step at the `Eq` cons** — `declStepPM_of_basis_cons` with
its `eq_lawP` row traded for the row itself.  `eqLawP_cons_fresh`'s
side condition is `eqName ≠ c₀.name`, and at this cons the constant
*is* `Eq`, so the row is structurally unavailable and the block
supplies it from its own tower (`eqLawP_of_tower`).  Seven of the
eight rows still collapse. -/
theorem declStepPM_of_basis_cons_eqrow (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    (hnN : c₀.name ≠ natName) (hnZ : c₀.name ≠ natZeroName)
    (hnS : c₀.name ≠ natSuccName)
    (hnotrec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      rules = [])
    (hres : ConLeche.reservedBasisNames.contains c₀.name = true)
    (hred : (∀ cv, c₀ ≠ .axiomInfo cv) ∨
      c₀.name ∉ ConLeche.reduceOpNames)
    (hh : ConsHeadP env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    (heq : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → EqLawP m₂)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry := by
      intro _ h; exact nomatch h) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_cons mp (c₀ := c₀) (A := A) hfresh hh hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
    · exact absurd hdt.symm (hnotthm cv2 value2)
  · exact fun φ => natHeadsP_cons_offNat mp hnN hnZ hnS _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact heq _ rfl
  · exact capsOkP_cons_basis mp mp.caps_ok hfresh hh.projTower hres _ rfl
  · exact fun φ => recRulesP_cons_fresh mp hfresh hh.projTower hnotrec _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): no tower entry is a basis cons
    exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

/-- **The P step at a basis cons, both varying rows open.**  The `Nat`
block needs this: its first three conses *are* the three names
`nat_heads`'s guard reads, so `natHeadsP_cons_offNat` is unavailable at
every one of them, and `Nat.rec` owes a `rec_rules` row besides.  Five
rows still collapse. -/
theorem declStepPM_of_basis_cons_gen (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    (hnEq : eqName ≠ c₀.name)
    (hres : ConLeche.reservedBasisNames.contains c₀.name = true)
    (hred : (∀ cv, c₀ ≠ .axiomInfo cv) ∨
      c₀.name ∉ ConLeche.reduceOpNames)
    (hh : ConsHeadP env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    (hnh : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, NatHeadsP m₂ φ)
    (hrec : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRulesP m₂ φ)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry := by
      intro _ h; exact nomatch h) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_cons mp (c₀ := c₀) (A := A) hfresh hh hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
    · exact absurd hdt.symm (hnotthm cv2 value2)
  · exact fun φ => hnh _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact eqLawP_cons_fresh mp.eq_lawP hnEq _ rfl
  · exact capsOkP_cons_basis mp mp.caps_ok hfresh hh.projTower hres _ rfl
  · exact fun φ => hrec _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): no tower entry is a basis cons
    exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

end ConLeche.SetP
