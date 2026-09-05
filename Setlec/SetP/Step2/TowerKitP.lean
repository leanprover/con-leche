import Setlec.SetP.Annot.EnvS2P
import Setlec.SetP.Step2.StuckP
import Setlec.SetP.Step2.ProjAVKitP

/-!
# The tower-entry kit for the P `.proj` rows (task #175 wiring, W5 S3)

What the `.proj` rows need at a **tower-backed** entry, beyond the
law itself (`TowerOkP`, `Annot/EnvS2P.lean`):

* the reading's tower clause and its inversion
  (`denoteP_proj_tower`, `denoteP_proj_inv_tower`) — the `projAV`
  branch of `denoteP`'s entry-kind match, isolated;
* the **fit-free residual**: the checker's `instPisAt` peel of the
  entry type along the parameters and the subject reads to the
  syntactic peel of the entry type's reading along the readings
  (`denoteP_instPisAt_peel` — `teleFitPA_residual`'s spine with the
  memberships dropped, which is exactly why the typing law is stated
  over `AVExpr.peelPis`);
* the stored entry type is closed (`EnvWF`), so its reading at depth
  `0` is its reading at every depth (`towerEntry_ty_at_depth`);
* `projAV`'s grading under equal-valued subjects lives one module
  down (`ProjAVKitP`, which `DefEqP` — below the law — also reads).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ProjEntry)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The reading at a tower entry -/

/-- The clause at a tower-backed entry: the uniform iterated
projection of the subject's reading. -/
theorem denoteP_proj_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : AVExpr}
    (hfe : env.findProj? s i = some entry) (htw : entry.tower = true)
    (he : denoteP acval env φ d e = some ia) :
    denoteP acval env φ d (.proj s i e) = some (projAV i ia) := by
  rw [denoteP_proj, he]
  show (match env.findProj? s i with
    | some entry => if entry.tower = true then some (projAV i ia)
        else if i < 2 then some (AVExpr.proj i ia) else none
    | none => if i < 2 then some (AVExpr.proj i ia) else none)
      = some (projAV i ia)
  rw [hfe]
  dsimp only
  rw [if_pos htw]

/-- The inversion at a tower-backed entry. -/
theorem denoteP_proj_inv_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ea : AVExpr}
    (hfe : env.findProj? s i = some entry) (htw : entry.tower = true)
    (h : denoteP acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteP acval env φ d e = some ia ∧ ea = projAV i ia := by
  obtain ⟨ia, hia, hcase⟩ := denoteP_proj_inv h
  rcases hcase with ⟨entry', hfe', -, rfl⟩ | ⟨hnt, -, -⟩
  · obtain rfl : entry' = entry := Option.some.inj (hfe'.symm.trans hfe)
    exact ⟨ia, hia, rfl⟩
  · exact absurd htw (by simp [hnt entry hfe])

/-- A read spine extended by one read argument. -/
theorem DenoteSpineP.snoc {d : Nat} {as : List Expr} {vs : List AVExpr}
    {a : Expr} {v : AVExpr}
    (h : DenoteSpineP acval env φ d as vs)
    (ha : denoteP acval env φ d a = some v) :
    DenoteSpineP acval env φ d (as ++ [a]) (vs ++ [v]) := by
  induction h with
  | nil => exact .cons ha .nil
  | cons h1 _ ih => exact .cons h1 ih

/-- The `k`-th argument of a read spine reads to the `k`-th reading. -/
theorem DenoteSpineP.getD_read {d : Nat} :
    ∀ {as : List Expr} {vs : List AVExpr}, DenoteSpineP acval env φ d as vs →
      ∀ {k : Nat}, k < as.length →
        denoteP acval env φ d (as.getD k (.bvar 0))
          = some (vs.getD k default)
  | _, _, .nil, k, hk => absurd hk (Nat.not_lt_zero k)
  | _, _, .cons ha _, 0, _ => by simpa [List.getD] using ha
  | _, _, .cons _ hsp, k + 1, hk => by
    simpa [List.getD] using
      DenoteSpineP.getD_read hsp (Nat.lt_of_succ_lt_succ hk)

/-! ## The fit-free residual -/

/-- **The checker's `instPisAt` peel reads to the syntactic peel of
the type's reading** — `teleFitPA_residual` without the fit: the two
walks step in lockstep (`body.instantiate1 a` against `B.inst a`), and
the per-step content is `denoteP_beta`, once. -/
theorem denoteP_instPisAt_peel
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AVExpr) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {ds : List Expr} {Ta : AVExpr}
      {vs : List AVExpr},
      Expr.instPisAt args ty = some (ds, rest) →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteP acval env φ d ty = some Ta →
      DenoteSpineP acval env φ d args vs →
      ∃ restA, denoteP acval env φ d rest = some restA ∧
        AVExpr.peelPis Ta vs = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest ds Ta vs hpr _ _ hty hsp
    obtain ⟨-, rfl⟩ : ds = [] ∧ rest = ty := by
      simpa [Expr.instPisAt] using hpr.symm
    cases hsp
    exact ⟨Ta, hty, rfl⟩
  | cons a as ih =>
    intro ty rest ds Ta vs hpr hwty hargs hty hsp
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE n dom body mb, hpr, hwty, hty => ?_
    -- the peel's own step
    simp only [Expr.instPisAt, Option.map_eq_some_iff] at hpr
    obtain ⟨⟨ds', rest'⟩, hpr', heq⟩ := hpr
    obtain ⟨-, rfl⟩ : dom :: ds' = ds ∧ rest' = rest := by
      simpa using heq
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteP_forallE_inv hty
    have hbody' : denoteP acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteP_beta hacl hainst (n := n) (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    obtain ⟨restA, hrestA, hpeel⟩ := ih hpr'
      (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hbody' hsp'
    exact ⟨restA, hrestA, hpeel⟩

/-! ## The stored entry type is closed -/

/-- A stored table entry's type is closed and resolves (`EnvWF`'s
`ConstWF` at the `projInfo` member). -/
theorem towerEntry_ty_wf (hwf : Setlec.EnvWF env) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry) :
    entry.ty.hasFvar = false ∧ entry.ty.looseBVarsBounded 0 = true ∧
      entry.ty.constsResolve env = true := by
  obtain ⟨h1, -, h3, h4, -⟩ :=
    hwf _ (Setlec.SetR.Env.find?_mem (Setlec.Env.findProj?_some hfe))
  exact ⟨h1, h4, h3⟩

/-- The entry type's level instantiation is closed. -/
theorem towerEntry_tyI_closed (hwf : Setlec.EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    (us : List Level) :
    (entry.ty.instantiateLevelParams entry.levelParams us).hasFvar = false ∧
      (entry.ty.instantiateLevelParams entry.levelParams us).looseBVarsBounded 0
        = true := by
  obtain ⟨h1, h2, -⟩ := towerEntry_ty_wf hwf hfe
  exact ⟨by rw [Expr.hasFvar_instantiateLevelParams]; exact h1,
    by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact h2⟩

/-- **The entry type's reading is depth-free** — closed subject,
closed reading, `denoteP_depth_of_closed`. -/
theorem towerEntry_ty_at_depth {m : EnvS2Core V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AVExpr}
    (hTa : denoteP m.acval env φ 0
      (entry.ty.instantiateLevelParams entry.levelParams us) = some Ta) :
    (∀ d : Nat, denoteP m.acval env φ d
      (entry.ty.instantiateLevelParams entry.levelParams us) = some Ta) ∧
    ∀ k : Nat, Ta.liftN 1 k = Ta := by
  obtain ⟨hnf, hb⟩ := towerEntry_tyI_closed m.wf hfe us
  have hcl : ∀ k : Nat, Ta.liftN 1 k = Ta := fun k =>
    denoteP_closed m.acval_erase m.cval_closed hnf hb hTa 1 k
  exact ⟨denoteP_depth_of_closed m.acval_closed hnf hcl hTa, hcl⟩

end Setlec.SetR.Interp2
