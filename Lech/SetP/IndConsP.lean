import Lech.SetP.BasisStepP

/-!
# The inductive cons, P tier: the mechanical rows at an ind-kind head (task #161, IND TIER)

`declStepPM_of_basis_cons` (`Interp2/BasisStepP.lean`) collapses seven
of `declStepPM_of_cons`'s eleven premises at a *basis* cons.  An
*inductive-block* cons is the other side of the same coin: its name is
never reserved, so the two rows a basis cons could route by *name*
(`caps_ok` through `capsOkP_cons_basis`) are unavailable, while every
row a basis cons routes by *kind* survives — and one that a basis cons
had to supply bespoke (`nat_heads` at the `Nat` block) becomes free.

**The name finding, re-checked with an `#eval` before it was spent
(the E/F/G/H practice).**  Every block member enters through
`MemberValR` → `ConstantValR`, whose second conjunct is

> `reservedBasisNames.contains cv.name = false`

and `reservedBasisNames` is the twenty pinned names — `Nat`,
`Nat.zero`, `Nat.succ` and `Eq` among them.  So at every member cons:

* `nat_heads` goes through `natHeadsP_cons_offNat`: an inductive block
  **cannot** turn the literal-support guard on, because it cannot
  install a constant named `Nat`, `Nat.zero` or `Nat.succ`.  The
  feared obligation — a modeled family that captures the numeral
  heads, whose leaves would then owe the two membership facts — does
  not exist;
* `eq_lawP` goes through `eqLawP_cons_fresh` for the same reason: no
  block member is named `Eq`, so the pinned spine's law is untouched.

The projection conses (`ProjFnR`'s `recInfo`, `Templates`'s
`projInfo`) carry no reserved check of their own, but their names are
`projFnName T i`, and `projFnName_ne_reserved` supplies the same four
disequalities.

What is left is exactly the tier's bill: `caps_ok` and `rec_rules`,
plus the tower and its type's reading.  Both remaining rows are taken
here in `natHeadsP_cons_offNat`'s shape — quantified over any carrier
whose base and `acval` are the extension's — so a caller never spells
`declStepPM_of_cons`'s anonymous-constructor carrier.

**The `caps_ok` gap is not only at the family's own conses.**
`capsOkP_cons_fresh` descends the stored-family predicate past a cons
of a kind no family mentions, and `EtaFamilyStored` mentions three:
`indInfo` (the former), `ctorInfo` (the capability constructor) and
**`recInfo`** (a projection slot).  So the *projection-function*
install — a `recInfo` cons — can complete a family that was not
previously stored, which is why the η law's establishment sits at the
projection install in v1 too (`Install/EtaLawS.lean`, the
`etaLawKeyS` route).  `declStepPM_of_ind_cons` therefore keeps
`caps_ok` open at every ind-tier cons and never guesses a route.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- A non-reserved name differs from every reserved one.  The
inductive tier's workhorse: `ConstantValR`'s second conjunct is the
hypothesis, and the four names the mechanical rows read
(`Nat`/`Nat.zero`/`Nat.succ`/`Eq`) are all reserved. -/
theorem ne_of_notReserved {n m : Name}
    (h : Lech.reservedBasisNames.contains n = false)
    (hm : Lech.reservedBasisNames.contains m = true) : n ≠ m := by
  intro hh
  rw [hh, hm] at h
  exact nomatch h

theorem reserved_natName : Lech.reservedBasisNames.contains natName = true := by
  decide

theorem reserved_natZeroName :
    Lech.reservedBasisNames.contains natZeroName = true := by decide

theorem reserved_natSuccName :
    Lech.reservedBasisNames.contains natSuccName = true := by decide

theorem reserved_eqName : Lech.reservedBasisNames.contains eqName = true := by
  decide


/-- **The P step at an inductive-tier cons.**  Six of
`declStepPM_of_cons`'s eight collapsible rows are discharged here from
the *name* (non-reserved) and the *kind* (never a value kind, never an
axiom); `caps_ok` and `rec_rules` stay open, because those are the two
rows an inductive block genuinely establishes. -/
theorem declStepPM_of_ind_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    -- the name: `ConstantValR`'s second conjunct at a member,
    -- `projFnName_ne_reserved` at a projection slot
    (hnres : Lech.reservedBasisNames.contains c₀.name = false)
    -- the kind: an inductive block installs no value kind and no axiom
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    (hnotax : ∀ cv, c₀ ≠ .axiomInfo cv)
    -- the head's own obligations (task #161 S7)
    (hh : ConsHeadP env c₀ A)
    -- the annotated tower
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
    -- the tier's two genuine rows
    (hcaps : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOkP m₂)
    (hrec : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRulesP m₂ φ)
    -- the head is not a projection table (task #175 W4c: those get
    -- their own kit, `DeclDirectP`)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_cons mp (c₀ := c₀) (A := A) hfresh hh
    hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hvalReads`: an inductive cons is never a definition or a theorem
    intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact absurd hdt.symm (hnotdefn cv2 value2 hint2)
    · exact absurd hdt.symm (hnotthm cv2 value2)
  · -- `nat_heads`: the guard's three names are reserved, this one is not
    exact fun φ => natHeadsP_cons_offNat mp
      (ne_of_notReserved hnres reserved_natName)
      (ne_of_notReserved hnres reserved_natZeroName)
      (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun cv v hint => hnotdefn cv v hint) _ rfl
  · -- `eq_lawP`: `Eq` is reserved, so it is not this cons
    exact eqLawP_cons_fresh mp.eq_lawP
      (fun h => ne_of_notReserved hnres reserved_eqName h.symm) _ rfl
  · exact hcaps _ rfl
  · exact fun φ => hrec _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh
      (Or.inl hnotax) _ rfl
  · -- `tower_ok` (task #175 wiring W5): an ind-tier cons is never a
    -- tower entry (`hh.projTower`)
    exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower hntc _ rfl φ

/-- **The P step at a block *member* cons** — `declStepPM_of_ind_cons`
with `rec_rules` discharged too.  A member is an `indInfo` or a
`ctorInfo`, so `recRulesP_cons_fresh`'s side condition holds
vacuously: the cons is not a recursor at all, and `EnvS.rec_ctors`
carries the rest (ENDGAME D §3a).  `caps_ok` remains the member's one
open row — the block's former *is* a family head. -/
theorem declStepPM_of_ind_member_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnres : Lech.reservedBasisNames.contains c₀.name = false)
    (hknd : (∃ cv caps, c₀ = .indInfo cv caps) ∨
      ∃ cv nP nF, c₀ = .ctorInfo cv nP nF)
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
    (hcaps : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOkP m₂) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  refine declStepPM_of_ind_cons mp hfresh hnres ?_ ?_ ?_ hh
    hAclosed hAparams hAok hAvalid htyReads htyOk hmemNew
    hcaps ?_ ?_
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ _ _ h <;> exact nomatch h
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ _ h <;> exact nomatch h
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ h <;> exact nomatch h
  · refine fun m₂ hac φ => recRulesP_cons_fresh mp hfresh hh.projTower ?_ m₂ hac φ
    rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ _ _ _ h <;> exact nomatch h
  · rcases hknd with ⟨cv, caps, rfl⟩ | ⟨cv, nP, nF, rfl⟩ <;>
      intro _ h <;> exact nomatch h

/-- **The P step at a *recursor* cons** — the block's recursors and the
projection functions, both stored as `recInfo`.  Only `caps_ok` and
`rec_rules` stay open; both are the install's to establish. -/
theorem declStepPM_of_ind_rec_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnres : Lech.reservedBasisNames.contains c₀.name = false)
    (hknd : ∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules)
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
    (hcaps : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOkP m₂)
    (hrec : ∀ m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRulesP m₂ φ) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  obtain ⟨cv, mI, rP, rules, rfl⟩ := hknd
  exact declStepPM_of_ind_cons mp hfresh hnres
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ h => nomatch h) hh hAclosed hAparams hAok
    hAvalid htyReads htyOk hmemNew hcaps hrec (fun _ h => nomatch h)

end Lech.SetP
