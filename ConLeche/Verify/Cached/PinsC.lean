module

public import ConLeche.Cached.ParsedC
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The cached `Nat.div`/`Nat.mod` pin check is the specification's (task #497)

`checkDivModPinC` (`ConLeche/Cached/ParsedC.lean`) substitutes each
variant's certificate proofs once with the sharing-preserving
`substConstAllC` and guards them with the cached walks;
`checkDivModPinC_eq` is its equation to `checkDivModPinF`, at any
operations and in any monad.
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

section Pins

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

omit [MonadExceptOf CheckError m] in
theorem checkDivModCertsC_eq (ops : CheckerOps m) (fe : FEnv) (c : Name) (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      checkDivModCertsC ops fe c annVal stmts (proofs.map (Expr.substConstAllC c annVal))
        = checkDivModCertsF ops fe c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [List.map_cons, checkDivModCertsC, checkDivModCertsF, divModCertGuardC_eq]
    simp only [substConstAllC_spec, checkDivModCertsC_eq ops fe c annVal srest prest]

omit [MonadExceptOf CheckError m] in
theorem checkDivModPinAtC_eq (ops : CheckerOps m) (fe : FEnv) (c : Name) (value' : Expr)
    (ps : NatOpPinSet) :
    checkDivModPinAtC ops fe c value' ps
        ((divModCertProofs ps c).map (Expr.substConstAllC c value'))
      = checkDivModPinAtF ops fe c value' ps := by
  simp only [checkDivModPinAtC, checkDivModPinAtF, checkDivModCertsC_eq]

theorem checkDivModPinLoopC_eq (ops : CheckerOps m) (fe : FEnv) (c : Name) (value' : Expr) :
    ∀ (pins : List NatOpPinSet) (tried : List String),
      checkDivModPinLoopC ops fe c value' pins tried
        = checkDivModPinLoopF ops fe c value' pins tried
  | [], _ => rfl
  | ps :: rest, tried => by
    simp only [checkDivModPinLoopC, checkDivModPinLoopF, divModPinGuardC_eq,
      divModCertsGuardC_eq, checkDivModPinAtC_eq, checkDivModPinLoopC_eq ops fe c value' rest]

/-- **The cached pin check is the specification's.** -/
theorem checkDivModPinC_eq (ops : CheckerOps m) (pins : List NatOpPinSet) (fe fe2 : FEnv)
    (c : Name) :
    checkDivModPinC ops pins fe fe2 c = checkDivModPinF ops pins fe fe2 c := by
  unfold checkDivModPinC checkDivModPinF
  split
  · cases fe2.find? c with
    | none => rfl
    | some ci => cases ci <;> first | rfl | simp only [checkDivModPinLoopC_eq]
  · rfl

end Pins

end ConLeche.Cached
