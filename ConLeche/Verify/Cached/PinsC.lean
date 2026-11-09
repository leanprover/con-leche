module

public import ConLeche.Cached.ParsedC
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The cached `Nat.div`/`Nat.mod` pin check is the specification's (task #497)

`checkDivModPinC` (`ConLeche/Cached/ParsedC.lean`) substitutes each
variant's certificate proofs once with the sharing-preserving
`substConstAllC` and guards them with the cached walks;
`checkDivModPinC_eq` is its equation to `checkDivModPinF` at the shared
operations (`sharedOpsC`): the twin calls the cached core directly, and
the shared operations are that core.
-/

namespace ConLeche.Cached

open ConLeche

/-- **`substConstAllC` is `Expr.substConstAll`**: each entry of the walk
proves its node's image under the specification itself. -/
theorem substConstAllC_spec {n : Name} {r e : Expr} :
    Expr.substConstAllC n r e = Expr.substConstAll n r e :=
  Expr.resTerm_eq _

theorem divModCertGuardC_eq (fe : FEnv) (c : Name) (annVal : Expr) (hyps : List Expr)
    (eqE proof : Expr) :
    divModCertGuardC fe c annVal hyps eqE (Expr.substConstAllC c annVal proof)
      = divModCertGuardF fe c annVal hyps eqE proof := by
  simp only [divModCertGuardC, divModCertGuardF, substConstAllC_spec,
    Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec]

theorem divModPinGuardC_eq (ps : NatOpPinSet) (fe : FEnv) (c : Name) :
    divModPinGuardC ps fe c = divModPinGuardF ps fe c := by
  simp only [divModPinGuardC, divModPinGuardF, Expr.allLevelParamsDefinedC_spec,
    constsResolveFC_spec]

theorem divModCertsGuardC_eq (ps : NatOpPinSet) (fe : FEnv) (c : Name) (annVal : Expr) :
    ((divModCertStmts c).zip ((divModCertProofs ps c).map (Expr.substConstAllC c annVal))).all
        (fun p => divModCertGuardC fe c annVal p.1.1 p.1.2 p.2)
      = divModCertsGuardF ps fe c annVal := by
  simp only [divModCertsGuardF, List.zip_map_right, List.all_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, divModCertGuardC_eq]

variable (mode : CheckMode)

theorem checkTypePinsC_eq (fe : FEnv) :
    ∀ ps : List (Name × Expr),
      checkTypePinsC mode fe ps = checkTypePinsF (sharedOpsC mode fe) fe ps
  | [] => rfl
  | p :: rest => by
    simp only [checkTypePinsC, checkTypePinsF, checkTypePinsC_eq fe rest]
    rfl

theorem checkDivModCertsC_eq (fe : FEnv) (c : Name) (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      checkDivModCertsC mode fe c annVal stmts (proofs.map (Expr.substConstAllC c annVal))
        = checkDivModCertsF (sharedOpsC mode fe) fe c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [List.map_cons, checkDivModCertsC, checkDivModCertsF, divModCertGuardC_eq]
    simp only [substConstAllC_spec, checkDivModCertsC_eq fe c annVal srest prest]
    rfl

theorem checkDivModPinAtC_eq (fe : FEnv) (c : Name) (value' : Expr) (ps : NatOpPinSet) :
    checkDivModPinAtC mode fe c value' ps
        ((divModCertProofs ps c).map (Expr.substConstAllC c value'))
      = checkDivModPinAtF (sharedOpsC mode fe) fe c value' ps := by
  simp only [checkDivModPinAtC, checkDivModPinAtF, checkDivModCertsC_eq, checkTypePinsC_eq]
  rfl

theorem checkDivModPinLoopC_eq (fe : FEnv) (c : Name) (value' : Expr) :
    ∀ (pins : List NatOpPinSet) (tried : List String),
      checkDivModPinLoopC mode fe c value' pins tried
        = checkDivModPinLoopF (sharedOpsC mode fe) fe c value' pins tried
  | [], _ => rfl
  | ps :: rest, tried => by
    simp only [checkDivModPinLoopC, checkDivModPinLoopF, divModPinGuardC_eq,
      divModCertsGuardC_eq, checkDivModPinAtC_eq, checkDivModPinLoopC_eq fe c value' rest]

/-- **The cached pin check is the specification's at the shared operations.** -/
theorem checkDivModPinC_eq (pins : List NatOpPinSet) (fe fe2 : FEnv) (c : Name) :
    checkDivModPinC mode pins fe fe2 c = checkDivModPinF (sharedOpsC mode fe) pins fe fe2 c := by
  unfold checkDivModPinC checkDivModPinF
  split
  · cases fe2.find? c with
    | none => rfl
    | some ci => cases ci <;> first | rfl | simp only [checkDivModPinLoopC_eq]
  · rfl

theorem reducePinGuardC_eq (fe : FEnv) (c : Name) :
    reducePinGuardC fe c = reducePinGuardF fe c := by
  simp only [reducePinGuardC, reducePinGuardF, Expr.allLevelParamsDefinedC_spec,
    constsResolveFC_spec]

/-- **The cached reduce-pin check is the specification's at the shared operations.** -/
theorem checkReducePinC_eq (fe fe2 : FEnv) (c : Name) (value : Expr) :
    checkReducePinC mode fe fe2 c value = checkReducePinF (sharedOpsC mode fe) fe fe2 c value := by
  simp only [checkReducePinC, checkReducePinF, reducePinGuardC_eq]
  rfl

end ConLeche.Cached
