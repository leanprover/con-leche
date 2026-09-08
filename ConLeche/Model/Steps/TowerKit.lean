module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Steps.Stuck
public import ConLeche.Model.Steps.ProjAVKit
public import ConLeche.Verify.ProjTele

public section

/-!
# The tower-entry kit for the P `.proj` rows (task #175 wiring, W5 S3)

What the `.proj` rows need at a **tower-backed** entry, beyond the
law itself (`TowerOk`, `Annot/EnvModelM.lean`):

* the reading's tower clause and its inversion
  (`denoteMeta_proj_tower`, `denoteMeta_proj_inv_tower`) — the `projAV`
  branch of `denoteMeta`'s entry-kind match, isolated;
* the **fit-free residual**: the checker's `instPisAt` peel of the
  entry type along the parameters and the subject reads to the
  syntactic peel of the entry type's reading along the readings
  (`denoteMeta_instPisAt_peel` — `teleFitPA_residual`'s spine with the
  memberships dropped, which is exactly why the typing law is stated
  over `AnnotTerm.peelPis`);
* the stored entry type is closed (`EnvWF`), so its reading at depth
  `0` is its reading at every depth (`towerEntry_ty_at_depth`);
* `projAV`'s grading under equal-valued subjects lives one module
  down (`ProjAVKitP`, which `DefEqP` — below the law — also reads).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ProjEntry)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The reading at a tower entry -/

/-- The clause at a stored entry: the uniform iterated projection of
the subject's reading. -/
theorem denoteMeta_proj_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (he : denoteMeta acval env φ d e = some ia) :
    denoteMeta acval env φ d (.proj s i e) = some (projAV (i + entry.off) ia) := by
  rw [denoteMeta_proj, he]
  show (match env.findProj? s i with
    | some entry => some (projAV (i + entry.off) ia)
    | none => AnnotTerm.projPair? i ia)
      = some (projAV (i + entry.off) ia)
  rw [hfe]

/-- The inversion at a stored entry. -/
theorem denoteMeta_proj_inv_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ea : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧ ea = projAV (i + entry.off) ia := by
  obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
  rcases hcase with ⟨entry', hfe', rfl⟩ | ⟨hnt, -⟩
  · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
    exact ⟨ia, hia, rfl⟩
  · rw [hnt] at hfe; exact nomatch hfe

/-- A read spine extended by one read argument. -/
theorem DenoteMetaSpine.snoc {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    {a : Expr} {v : AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs)
    (ha : denoteMeta acval env φ d a = some v) :
    DenoteMetaSpine acval env φ d (as ++ [a]) (vs ++ [v]) := by
  induction h with
  | nil => exact .cons ha .nil
  | cons h1 _ ih => exact .cons h1 ih

/-- The `k`-th argument of a read spine reads to the `k`-th reading. -/
theorem DenoteMetaSpine.getD_read {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      ∀ {k : Nat}, k < as.length →
        denoteMeta acval env φ d (as.getD k (.bvar 0))
          = some (vs.getD k default)
  | _, _, .nil, k, hk => absurd hk (Nat.not_lt_zero k)
  | _, _, .cons ha _, 0, _ => by simpa [List.getD] using ha
  | _, _, .cons _ hsp, k + 1, hk => by
    simpa [List.getD] using
      DenoteMetaSpine.getD_read hsp (Nat.lt_of_succ_lt_succ hk)

/-! ## The fit-free residual -/

/-- **The checker's `instPisAt` peel reads to the syntactic peel of
the type's reading** — `teleFitPA_residual` without the fit: the two
walks step in lockstep (`body.instantiate1 a` against `B.inst a`), and
the per-step content is `denoteMeta_beta`, once. -/
theorem denoteMeta_instPisAt_peel
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {ds : List Expr} {Ta : AnnotTerm}
      {vs : List AnnotTerm},
      Expr.instPisAt args ty = some (ds, rest) →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteMeta acval env φ d ty = some Ta →
      DenoteMetaSpine acval env φ d args vs →
      ∃ restA, denoteMeta acval env φ d rest = some restA ∧
        AnnotTerm.peelPis Ta vs = some restA := by
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
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body mb, hpr, hwty, hty => ?_
    -- the peel's own step
    simp only [Expr.instPisAt, Option.map_eq_some_iff] at hpr
    obtain ⟨⟨ds', rest'⟩, hpr', heq⟩ := hpr
    obtain ⟨-, rfl⟩ : dom :: ds' = ds ∧ rest' = rest := by
      simpa using heq
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hty
    have hbody' : denoteMeta acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteMeta_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    obtain ⟨restA, hrestA, hpeel⟩ := ih hpr'
      (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hbody' hsp'
    exact ⟨restA, hrestA, hpeel⟩

/-! ## The stored body's telescope is closed (task #175 S1) -/

/-- A stored tower entry's body telescope is closed: the body is
fvar-free and scoped at the parameters and the subject (`EnvWF`'s
table clause), and `projTele` binds exactly those. -/
theorem towerEntry_tele_closed (hwf : ConLeche.EnvWF env) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry) (us : List Level) :
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).hasFvar = false ∧
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).looseBVarsBounded 0
      = true := by
  rw [ConLeche.projTele_hasFvar, ConLeche.projTele_looseBVarsBounded, Nat.zero_add]
  exact ⟨ConLeche.projEntry_body_hasFvar hwf hfe us,
    ConLeche.projEntry_body_looseBVars hwf hfe us⟩

/-- **The body telescope's reading is depth-free** — closed subject,
closed reading, `denoteMeta_depth_of_closed`. -/
theorem towerEntry_tele_at_depth {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) :
    (∀ d : Nat, denoteMeta m.acval env φ d
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) ∧
    ∀ k : Nat, Ta.liftN 1 k = Ta := by
  obtain ⟨hnf, hb⟩ := towerEntry_tele_closed m.wf hfe us
  have hcl : ∀ k : Nat, Ta.liftN 1 k = Ta := fun k =>
    denoteMeta_closed m.acval_erase m.cval_closed hnf hb hTa 1 k
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf hcl hTa, hcl⟩

/-- **The checker's projection type reads as the telescope's peel**
(task #175 S1): `ProjEntry.typeAt` is the `instPisAt` peel of the body
telescope along the arguments and the subject, so its reading is the
syntactic peel of the telescope's reading along the readings. -/
theorem denoteMeta_typeAt_peel {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm} {d : Nat}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta)
    {targs : List Expr} {pe : Expr} (hlen : targs.length = entry.numParams)
    (hframes : ∀ a ∈ targs ++ [pe], Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    {vs : List AnnotTerm}
    (hsp : DenoteMetaSpine m.acval env φ d (targs ++ [pe]) vs) :
    ∃ restA, denoteMeta m.acval env φ d (entry.typeAt us targs pe) = some restA ∧
      AnnotTerm.peelPis Ta vs = some restA := by
  obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
  exact denoteMeta_instPisAt_peel m.acval_closed (acval_inst_self m) (targs ++ [pe])
    (ConLeche.instPisAt_typeAt entry us hlen pe)
    (Expr.WScoped.of_not_hasFvar (towerEntry_tele_closed m.wf hfe us).1)
    hframes (hTad d) hsp

end ConLeche.Model
