import Setlec.SetR.Interp2.Step2.StuckP

/-!
# The pinned projection table, at the P currency (task #161, PROJ/STR
install tier)

The shared kit of the four projection rows.  Everything here is a
consequence of **`projEntry_pins`** (`SetR/ProjPins.lean`): a `native`
table entry is one of the two pinned pair entries, so `structName`,
`idx`, `numParams`, `numFields`, `ctor`, the level-parameter arity and
the entry type are all *concrete*.  That is what makes the projection
rows **pinned-basis** work rather than stored-family work — there is no
`EnvS2PM` field anywhere in this tier.

Two pieces:

* `projPinsP` — the entry's numeric and name data, packaged once so
  neither row repeats the `rcases hpin with rfl | rfl` sweep;
* `piResidual_pairFstA`/`piResidual_pairSndA` and their packaging
  `projResidualP` — the `.proj` inference clause's returned type,
  **computed**.  v1 needs the generic `denote_piResidualR` walk here
  because its rule states the conclusion with `piResidualV`; the P rows
  state it with a `denoteP` reading, and at a pinned entry with a
  two-parameter spine the residual is just `A` (first component) or
  `B (pe.1)` (second), so the walk collapses to two `simp`s.  The only
  side condition is that the two parameters carry no loose `bvar`s,
  which is a frame fact of the reduced type they are the spine of.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ProjEntry)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The entry's data -/

/-- **The pinned entry's numbers and names**, packaged.  `projEntry_pins`
plus one `rcases` over the two pins; every conjunct is `rfl` in each
branch. -/
theorem projPinsP {sn : Name} {i : Nat} {entry : ProjEntry}
    (hpo : Setlec.ProjOkT env)
    (hfe : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    sn = Setlec.psigmaName ∧ entry.idx = i ∧ i < 2 ∧
      entry.numParams = 2 ∧ entry.numFields = 2 ∧
      entry.ctor = Setlec.psigmaMkName ∧
      entry.levelParams.length = 2 ∧
      (entry = Setlec.pairFstEntry ∨ entry = Setlec.pairSndEntry) ∧
      env.find? Setlec.psigmaName = some Setlec.psigmaA ∧
      env.find? Setlec.psigmaMkName = some Setlec.psigmaMkA := by
  obtain ⟨hpin, hsn, hidx, hpsig, hpsigMk⟩ :=
    Setlec.SetR.projEntry_pins hpo hfe hnat
  refine ⟨hsn, hidx, ?_, ?_, ?_, ?_, ?_, hpin, hpsig, hpsigMk⟩ <;>
    rcases hpin with rfl | rfl <;>
      first
      | rfl
      | (rw [← hidx]; decide)

/-- A member of a read spine reads (`DenoteSpineP`'s membership form —
the shape the projection clause's `getD` selection needs). -/
theorem DenoteSpineP.mem {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) :
    ∀ x ∈ as, ∃ v, denoteP acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, ha⟩
    · exact ih x hx'

/-! ## The residual, computed — RETIRED (task #161 item B2)

This section held `piResidual_pairFstA`/`piResidual_pairSndA` and their
packaging `projResidualP`: at a pinned entry with a two-parameter spine
the `.proj` inference clause's `piResidual` walk collapses to `A` or
`B (pe.1)`.  De-gating item B2 (harvest site 21 / list entry P10) moved
that collapse into the **checker**: the clause now returns the branch
outright, so `inferTypeCore_proj_inv` delivers `projResidualP`'s
conclusion verbatim and the derivation has no consumer left.

The v1 relational tier still states its `.proj` conclusion with the
walk (`piResidualV`), so the *converse* direction — the walk, from the
computed residual — lives on as `piResidual_of_computed`
(`Setlec/SetR/ProjPins.lean`), with the same two `simp`s and the same
single side condition (the two parameters carry no loose `bvar`s). -/

end Setlec.SetR.Interp2
