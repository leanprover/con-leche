module

public import ConLeche.Verify.Cached.GuardsC
public import ConLeche.Verify.Cached.IndWalksC

public section

/-!
# The cached driver's walker and tables are the plain ones (tasks #214, #497)

`structWalkersC` — the memoised constant-resolution gate the cached
driver hands the direct installers (`StructWalkers`,
`ConLeche/Kernel/Inductives/StructInstallF.lean`) — is equal to the
specification record `StructWalkers.plain`, by `constsResolveFC_spec`
(task #171).  Every bridge lemma about the driver rewrites by
`structWalkersC_eq_plain` once and then reads the plain installer.  The
projection tables the driver builds (`blockTablesC`, over the memoised
`instantiateLiftC`) are the plain `blockTables` by `blockTablesC_eq`,
through `instantiateLiftC_spec` (`OpsC.lean`).
-/

namespace ConLeche.Cached

open ConLeche

/-- **The driver's walker is the plain one.** -/
theorem structWalkersC_eq_plain : structWalkersC = StructWalkers.plain := by
  unfold structWalkersC StructWalkers.plain
  congr 1
  funext fe e; exact constsResolveFC_spec

/-- **The cached error of an unresolved constant is the specification's.** -/
theorem unresolvedConstsErrorLC_eq : unresolvedConstsErrorLC = unresolvedConstsErrorL := by
  funext strOk where_ e
  simp only [unresolvedConstsErrorLC, unresolvedConstsErrorL, unresolvedConstsError,
    Expr.mentionsAnyConstC_spec]

/-- **The cached constant check is the index mirror at the cached operations**
(task #497): the same steps, the guards' cached walks equal to the plain ones. -/
theorem checkConstantValC_eq (mode : CheckMode) (fe : FEnv) (cv : ConstantVal) (a : Bool) :
    checkConstantValC mode fe cv a = checkConstantValF (sharedOpsC mode fe) fe cv a := by
  simp only [checkConstantValC, checkConstantValF, Expr.allLevelParamsDefinedC_spec,
    constsResolveFC_spec, unresolvedConstsErrorLC_eq]
  rfl

theorem structProjBodiesGoC_eq (T : Name) : ∀ (vs : List Expr) (k i : Nat) (r : Expr),
    structProjBodiesGoC T vs k i r = structProjBodiesGo T vs k i r
  | _, 0, _, _ => rfl
  | _, _ + 1, _, .bvar _ => rfl
  | _, _ + 1, _, .fvar .. => rfl
  | _, _ + 1, _, .sort _ => rfl
  | _, _ + 1, _, .const .. => rfl
  | _, _ + 1, _, .app .. => rfl
  | _, _ + 1, _, .lam .. => rfl
  | _, _ + 1, _, .letE .. => rfl
  | _, _ + 1, _, .lit _ => rfl
  | _, _ + 1, _, .proj .. => rfl
  | vs, k + 1, i, .forallE fdom body => by
    simp only [structProjBodiesGoC, structProjBodiesGo, Expr.instantiateLiftC_spec]
    rw [structProjBodiesGoC_eq T _ k (i + 1)]

/-- **The cached projection bodies are the plain ones** (task #497). -/
theorem structProjBodiesC_eq (T : Name) (nP nF : Nat) (cty : Expr) :
    structProjBodiesC T nP nF cty = structProjBodies T nP nF cty := by
  unfold structProjBodiesC structProjBodies
  cases cty.stripPis nP with
  | none => rfl
  | some r => simp only [structProjBodiesGoC_eq]

/-- **The cached tables are the plain ones** (task #497). -/
theorem blockTablesC_eq (p : BlockShape) :
    ∀ ms : List MemberShape, blockTablesC p ms = blockTables p ms
  | [] => rfl
  | ms :: rest => by
    simp only [blockTablesC, blockTables, structProjBodiesC_eq, blockTablesC_eq p rest]
    cases ms.structCtor? <;> rfl

theorem declTablesC_eq (pd : Declaration) : declTablesC pd = declTables pd := by
  cases pd with
  | indDecl block nP =>
    simp only [declTablesC, declTables, blockTablesC_eq]
    cases readBlock nP block <;> rfl
  | _ => rfl

/-! ## The twins of the inductive check (task #498) -/

/-- **The cached telescope loop is the specification's at the shared
operations.** -/
theorem whnfTelescopeC_eq (mode : CheckMode) (fe : FEnv) :
    ∀ (i n : Nat) (e : Expr),
      whnfTelescopeC mode fe i n e = whnfTelescope (sharedOpsC mode fe) fe.env i n e
  | i, 0, e => rfl
  | i, n + 1, e => by
    simp only [whnfTelescopeC, whnfTelescope, Expr.instantiate1C_spec, whnfTelescopeC_eq mode fe]
    rfl

/-- **The cached reduced former is `reducedFormer` at the shared
operations.** -/
theorem reducedFormerC_eq (mode : CheckMode) (fe : FEnv) (cv : ConstantVal) (n : Nat) :
    reducedFormerC mode fe cv n = reducedFormer (sharedOpsC mode fe) fe.env cv n := by
  simp only [reducedFormerC, reducedFormer, whnfTelescopeC_eq, Expr.closeTelescopeC_eq]

/-- **The cached `is_rec` is `blockIsRec`.** -/
theorem blockIsRecC_eq (p : BlockShape) : blockIsRecC p = blockIsRec p := by
  simp only [blockIsRecC, blockIsRec, Expr.piDomsMentionAnyC_spec]

theorem blockConstantsC_eq (p : BlockShape) : blockConstantsC p = blockConstants p := by
  simp only [blockConstantsC, blockConstants, blockIsRecC_eq]

theorem declConstantsC_eq (pd : Declaration) : declConstantsC pd = declConstants pd := by
  cases pd with
  | indDecl block nP =>
    simp only [declConstantsC, declConstants, blockConstantsC_eq]
    cases readBlock nP block <;> rfl
  | _ => rfl

end ConLeche.Cached
