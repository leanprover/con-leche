module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Swap
public import ConLeche.Model.Inductives.StructCaps
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The recursor stage's discharge, Model tier (task #315, milestone M5)

The stage conses the block's `k` recursors — each with its rules —
onto the CONSTRUCTORS' environment, and the P carrier has to survive
it.  At `k = 1` that is one `declStep_preserves_of_ind_rec_cons`; at
`k ≥ 2` it cannot be, for the reason `envWF_consBlockRecs`
(`Verify/Inductives/BlockWF.lean`) records: a rule of `rec_0` may name
`rec_1`, so it reads only where all `k` recursors stand, and no
intermediate environment is well-formed.

The route here is the one the group rule-list swap already paved:

1. **the `k` RULE-LESS conses** (`envModelM_consBlockRecsBare`): a
   rule-less `recInfo` owes nothing about rules, so each cons is an
   ordinary `declStep_preserves_of_ind_rec_cons` and the whole chain is
   an induction over the recursor list;
2. **the rules, attached in one step** (`EnvModelM.swapP`,
   `Model/Swap.lean`): `consBlockRecsBare` and `consBlockRecs` cons the
   same constants in the same order, differing only in the `rules`
   field, which is exactly `SwapShList`
   (`swapShList_consBlockRecs`).  The swap takes `EnvWF`,
   `RecCtorsStored`, `BasisPinnedTT`, `ProjOkT` and `RecRules` at the
   stored environment as hypotheses — the first is
   `envWF_consBlockRecs` and the last is the ι content this lane's
   consumer supplies.

`blockRecStaged_of` is the proposition `Model/Inductives/DeclBlock.lean`
consumes, stated literally.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule BlockShape consBlockRecs consBlockRecsBare)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The `k` recursors' names -/

/-- The recursor stage's stored tuple: the checked constant, its
rules' right-hand sides, its target member's index count and that
member's constructors. -/
abbrev RecDatum := ConstantVal × List Expr × Nat × List (ConstantVal × Nat)

/-- `consBlockRecsBare`'s argument list, off the stage's own. -/
@[expose] def bareOf (rs : List RecDatum) : List (ConstantVal × Nat) :=
  rs.map fun r => (r.1, r.2.2.1)

theorem bareOf_map_name (rs : List RecDatum) :
    (bareOf rs).map (·.1.name) = rs.map (·.1.name) := by
  simp [bareOf]

theorem mem_bareOf {rs : List RecDatum} {x : ConstantVal × Nat} (h : x ∈ bareOf rs) :
    ∃ r ∈ rs, x.1 = r.1 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  exact ⟨r, hr, rfl⟩

/-! ## `CapsOk` at a rule-less recursor cons

A block recursor is `isProjFnShape`-free (`checkConstantVal`'s own
rejection), so it can complete no η family's projection slot, and it
is not an `indInfo`, so it is no family's former either; the whole
capability row therefore crosses with nothing supplied.  It is
`capsOk_cons_native` at `T := c₀.name`, whose two branches are then
both refuted by the head's KIND. -/
theorem capsOk_cons_recFresh {env : Env} (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    {cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hfresh : env.find? c₀.name = none)
    (hkind : c₀ = .recInfo cvR mI rP rules)
    (hpshape : c₀.name.isProjFnShape = false)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  refine capsOk_cons_native (T := c₀.name) mp hfresh
    (ConsCrossEnv.ofNtc (fun tbl h => by rw [hkind] at h; exact nomatch h))
    hpshape (Or.inr (fun cv caps h => by rw [hkind] at h; exact nomatch h))
    ?_ m₂ hac ?_
  · -- no stored family's capability constructor is this recursor
    intro T' cvT' caps' hf hne hres hcape hfam hh
    obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
    rw [hh, ConLeche.Env.find?_cons_self, hkind] at hfC
    exact nomatch hfC
  · -- the head is not an `indInfo`, so it is no family's former
    intro cvT caps hf _
    rw [ConLeche.Env.find?_cons_self, hkind] at hf
    exact nomatch hf

end ConLeche.Model
