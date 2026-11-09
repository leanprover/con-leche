module

public import ConLeche.Verify.EnvBound
import ConLeche.Kernel.DeclCheck

public section

/-!
# The indexed checker mirrors agree with the generic checker (task #63)

Under `mkFEnv` every `F`-mirror (`ConLeche/Kernel/DeclCheck.lean`,
`FEnv.lean`) *is* its generic counterpart: the mirrors differ only
in pure lookup subterms (`FEnv.find?` for `Env.find?`,
`Expr.constsResolveF` for `Expr.constsResolve`, and the compound
guards built from them), each of which `mkFEnv_find?` rewrites away.
Environment-*extending* mirrors return the pushed
index and are related run-wise by the cached tier's bridge
(`ConLeche/Verify/Cached/BridgeCS4.lean`) — here only the value-level
pieces are proven equal.
-/

namespace ConLeche

/-- `FEnv.find?` under `mkFEnv`, as a function equation. -/
theorem mkFEnv_find?_fun (env : Env) :
    FEnv.find? (mkFEnv env) = env.find? :=
  funext (mkFEnv_find? env)

theorem mkFEnv_env (env : Env) : (mkFEnv env).env = env := rfl

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

theorem constsResolveF_eq (env : Env) :
    ∀ (e : Expr), e.constsResolveF (mkFEnv env) = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .lit (.strVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .const n _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .fvar _ ty => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty]
  | .app f a => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env f, constsResolveF_eq env a]
  | .lam ty body => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .forallE ty body => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .letE ty val body => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env val,
      constsResolveF_eq env body]
  | .proj s _ e => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?,
      constsResolveF_eq env e]

theorem natOpCodF_eq (env : Env) (c : Name) (e : Expr) :
    natOpCodF (mkFEnv env) c e = natOpCod env c e := by
  simp only [natOpCodF, natOpCod, mkFEnv_find?] <;> rfl

theorem natOpTyPinnedF_eq (env : Env) (c : Name) (ty : Expr) :
    natOpTyPinnedF (mkFEnv env) c ty = natOpTyPinned env c ty := by
  simp only [natOpTyPinnedF, natOpTyPinned, natOpCodF_eq] <;> rfl

theorem natOpStoredOkF_eq (env : Env) (n : Name) :
    natOpStoredOkF (mkFEnv env) n = natOpStoredOk env n := by
  simp only [natOpStoredOkF, natOpStoredOk, mkFEnv_find?,
    natOpTyPinnedF_eq] <;> rfl

theorem stdAxiomOkF_eq (env : Env) (cv : ConstantVal) :
    stdAxiomOkF (mkFEnv env) cv = stdAxiomOk env cv := by
  simp only [stdAxiomOkF, stdAxiomOk, mkFEnv_find?] <;> rfl

theorem trustCompilerOkF_eq (env : Env) (cv : ConstantVal) :
    trustCompilerOkF (mkFEnv env) cv = trustCompilerOk env cv := by
  simp only [trustCompilerOkF, trustCompilerOk, mkFEnv_find?] <;> rfl

theorem reduceStoredOkF_eq (env : Env) (c : Name) :
    reduceStoredOkF (mkFEnv env) c = reduceStoredOk env c := by
  simp only [reduceStoredOkF, reduceStoredOk, mkFEnv_find?] <;> rfl

theorem reduceElemOkF_eq (env : Env) (c : Name) :
    reduceElemOkF (mkFEnv env) c = reduceElemOk env c := by
  simp only [reduceElemOkF, reduceElemOk, mkFEnv_find?] <;> rfl

theorem ofReduceAxOkF_eq (env : Env) (cv : ConstantVal) :
    ofReduceAxOkF (mkFEnv env) cv = ofReduceAxOk env cv := by
  simp only [ofReduceAxOkF, ofReduceAxOk, mkFEnv_find?,
    reduceElemOkF_eq, reduceStoredOkF_eq] <;> rfl

theorem reducePinGuardF_eq (env : Env) (c : Name) :
    reducePinGuardF (mkFEnv env) c = reducePinGuard env c := by
  simp only [reducePinGuardF, reducePinGuard, constsResolveF_eq] <;> rfl

theorem natOpStoredOkF_eq_fun (env : Env) :
    natOpStoredOkF (mkFEnv env) = natOpStoredOk env :=
  funext (natOpStoredOkF_eq env)

theorem divModEnvGuardF_eq (env : Env) (c : Name) :
    divModEnvGuardF (mkFEnv env) c = divModEnvGuard env c := by
  simp only [divModEnvGuardF, divModEnvGuard, mkFEnv_find?,
    natOpGuardF_eq, natOpStoredOkF_eq_fun] <;> rfl

theorem divModCertGuardF_eq (env : Env) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) :
    divModCertGuardF (mkFEnv env) c annVal hyps eqE proof
      = divModCertGuard env c annVal hyps eqE proof := by
  simp only [divModCertGuardF, divModCertGuard, constsResolveF_eq] <;> rfl

theorem typePinStoredF_eq (env : Env) (n : Name) :
    typePinStoredF (mkFEnv env) n = typePinStored env n := by
  simp only [typePinStoredF, typePinStored, mkFEnv_find?]
  cases env.find? n <;> rfl

theorem divModPinGuardF_eq (ps : NatOpPinSet) (env : Env) (c : Name) :
    divModPinGuardF ps (mkFEnv env) c = divModPinGuard ps env c := by
  simp only [divModPinGuardF, divModPinGuard, constsResolveF_eq, mkFEnv_find?,
    typePinStoredF_eq] <;> rfl

theorem divModCertsGuardF_eq (ps : NatOpPinSet) (env : Env) (c : Name)
    (annVal : Expr) :
    divModCertsGuardF ps (mkFEnv env) c annVal
      = divModCertsGuard ps env c annVal := by
  simp only [divModCertsGuardF, divModCertsGuard, divModCertGuardF_eq] <;> rfl

/-! ## Monadic mirrors (non-extending: plain program equalities) -/

section Monadic

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkConstantValF_eq (ops : CheckerOps m) (env : Env)
    (cv : ConstantVal) {a : Bool} :
    checkConstantValF ops (mkFEnv env) cv a = checkConstantVal ops env cv a := by
  simp only [checkConstantValF, checkConstantVal, mkFEnv_find?,
    constsResolveF_eq, strLitStoredF_eq] <;> rfl

omit [MonadExceptOf CheckError m] in
theorem checkDivModCertsF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      checkDivModCertsF ops (mkFEnv env) c annVal stmts proofs
        = checkDivModCerts ops env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | (_, _) :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCertsF, checkDivModCerts, divModCertGuardF_eq,
      mkFEnv_env, checkDivModCertsF_eq ops env c annVal srest prest]

omit [MonadExceptOf CheckError m] in
theorem checkTypePinsF_eq (ops : CheckerOps m) (env : Env) :
    ∀ (tps : List (Name × Expr)),
      checkTypePinsF ops (mkFEnv env) tps = checkTypePins ops env tps
  | [] => rfl
  | p :: rest => by
    simp only [checkTypePinsF, checkTypePins, mkFEnv_env, typePinStoredF_eq,
      checkTypePinsF_eq ops env rest]

omit [MonadExceptOf CheckError m] in
theorem checkDivModPinAtF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) (ps : NatOpPinSet) :
    checkDivModPinAtF ops (mkFEnv env) c value' ps
      = checkDivModPinAt ops env c value' ps := by
  simp only [checkDivModPinAtF, checkDivModPinAt, mkFEnv_env,
    checkDivModCertsF_eq, checkTypePinsF_eq]

theorem checkDivModPinLoopF_eq (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) :
    ∀ (pss : List NatOpPinSet) (tried : List String),
      checkDivModPinLoopF ops (mkFEnv env) c value' pss tried
        = checkDivModPinLoop ops env c value' pss tried
  | [], _ => rfl
  | ps :: rest, tried => by
    simp only [checkDivModPinLoopF, checkDivModPinLoop, divModPinGuardF_eq,
      divModCertsGuardF_eq, checkDivModPinAtF_eq,
      checkDivModPinLoopF_eq ops env c value' rest]

theorem checkDivModPinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) :
    checkDivModPinF ops pins (mkFEnv env) (mkFEnv env2) c
      = checkDivModPin ops pins env env2 c := by
  simp only [checkDivModPinF, checkDivModPin, mkFEnv_find?,
    divModEnvGuardF_eq, checkDivModPinLoopF_eq] <;> rfl

theorem checkReducePinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) (value : Expr) :
    checkReducePinF ops (mkFEnv env) (mkFEnv env2) c value
      = checkReducePin ops env env2 c value := by
  simp only [checkReducePinF, checkReducePin, mkFEnv_env,
    reduceStoredOkF_eq, reduceElemOkF_eq, reducePinGuardF_eq] <;> rfl

end Monadic

/-! ## Environment-extending mirrors: the push equation

Each extending mirror is its generic counterpart followed by `mkFEnv`
— the pushed index of the cons-extended environment *is* `mkFEnv` of
it.  The monadic `_push` equations that consume it are stated at the
executing monad, in `ConLeche/Verify/Cached/BridgeCSDecl.lean`. -/

theorem push_mkFEnv (env : Env) (ci : ConstantInfo) :
    (mkFEnv env).push ci = mkFEnv ⟨ci :: env.consts, env.tables⟩ := rfl

end ConLeche
