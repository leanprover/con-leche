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

/-! ## The residual, computed -/

/-- The first pinned entry's residual at a full spine is the type
argument (`piResidualV_pairFst`'s syntactic counterpart). -/
theorem piResidual_pairFstA (l0 l1 : Level) {A B pe : Expr}
    (hA : ∀ k, Expr.looseBVarsBounded k A = true) :
    Setlec.piResidual
      (Setlec.pairFstEntry.ty.instantiateLevelParams
        Setlec.pairFstEntry.levelParams [l0, l1]) [A, B, pe] = some A := by
  simp +decide [Setlec.piResidual, Setlec.pairFstEntry, Setlec.pairFstTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go,
    Expr.instantiate1]
  rw [Setlec.Expr.instantiate1_eq_self (hA 1),
    Setlec.Expr.instantiate1_eq_self (hA 0)]

/-- The second pinned entry's residual at a full spine is the fibre at
the first projection (`piResidualV_pairSnd`'s syntactic counterpart). -/
theorem piResidual_pairSndA (l0 l1 : Level) {A B pe : Expr}
    (hB : ∀ k, Expr.looseBVarsBounded k B = true) :
    Setlec.piResidual
      (Setlec.pairSndEntry.ty.instantiateLevelParams
        Setlec.pairSndEntry.levelParams [l0, l1]) [A, B, pe]
      = some (.app B (.proj Setlec.psigmaName 0 pe)) := by
  simp +decide [Setlec.piResidual, Setlec.pairSndEntry, Setlec.pairSndTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go,
    Expr.instantiate1]
  rw [Setlec.Expr.instantiate1_eq_self (hB 0)]

/-- **The `.proj` inference clause's returned type, identified.**  At a
pinned entry the parameter spine has exactly two members and the
residual is one of two concrete expressions. -/
theorem projResidualP {sn : Name} {i : Nat} {entry : ProjEntry}
    {us : List Level} {args : List Expr} {t pe : Expr}
    (hpo : Setlec.ProjOkT env)
    (hfe : env.findProj? sn i = some entry) (hnat : entry.native = true)
    (hlenArgs : args.length = entry.numParams)
    (hlenUs : us.length = entry.levelParams.length)
    (hbargs : ∀ x ∈ args, Expr.looseBVarsBounded 0 x = true)
    (hres : Setlec.piResidual
      (entry.ty.instantiateLevelParams entry.levelParams us) (args ++ [pe])
      = some t) :
    ∃ A B, args = [A, B] ∧
      ((i = 0 ∧ t = A) ∨
        (i = 1 ∧ t = .app B (.proj Setlec.psigmaName 0 pe))) := by
  obtain ⟨-, hidx, -, hnP, -, -, hlU, hpin, -, -⟩ := projPinsP hpo hfe hnat
  obtain ⟨A, B, rfl⟩ := Setlec.List.length_two (by rw [hlenArgs, hnP])
  obtain ⟨l0, l1, rfl⟩ := Setlec.List.length_two (by rw [hlenUs, hlU])
  have hAk : ∀ k, Expr.looseBVarsBounded k A = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k)
      (hbargs A (by simp))
  have hBk : ∀ k, Expr.looseBVarsBounded k B = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k)
      (hbargs B (by simp))
  refine ⟨A, B, rfl, ?_⟩
  rcases hpin with rfl | rfl
  · refine Or.inl ⟨by rw [← hidx]; rfl, ?_⟩
    rw [show ([A, B] ++ [pe] : List Expr) = [A, B, pe] from rfl,
      piResidual_pairFstA l0 l1 hAk] at hres
    exact (Option.some.inj hres).symm
  · refine Or.inr ⟨by rw [← hidx]; rfl, ?_⟩
    rw [show ([A, B] ++ [pe] : List Expr) = [A, B, pe] from rfl,
      piResidual_pairSndA l0 l1 hBk] at hres
    exact (Option.some.inj hres).symm

end Setlec.SetR.Interp2
