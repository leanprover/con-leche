import Setlec.Kernel.CheckerS
import Setlec.Verify.IExprOps

/-!
# The indexed checker mirrors agree with the generic checker (task #63)

Under `mkFEnv` every `F`-mirror of `Setlec/Kernel/CheckerS.lean` *is*
its `Setlec/Kernel/Checker.lean` counterpart: the mirrors differ only
in pure lookup subterms (`FEnv.find?` for `Env.find?`,
`Expr.constsResolveF` for `Expr.constsResolve`, and the compound
guards built from them), each of which `mkFEnv_find?` rewrites away.
Environment-*extending* mirrors (`checkDefnValF` …) return the pushed
index and are related run-wise in `Setlec/Model/BridgeS.lean` — here
only the value-level pieces are proven equal.
-/

namespace Setlec

/-- `FEnv.find?` under `mkFEnv`, as a function equation. -/
theorem mkFEnv_find?_fun (env : Env) :
    FEnv.find? (mkFEnv env) = env.find? :=
  funext (mkFEnv_find? env)

theorem mkFEnv_env (env : Env) : (mkFEnv env).env = env := rfl

theorem mkFEnv_findCV? (env : Env) (n : Name) :
    (mkFEnv env).findCV? n = env.findCV? n := by
  simp only [FEnv.findCV?, Env.findCV?, mkFEnv_find?] <;> rfl

theorem constsResolveF_eq (env : Env) :
    ∀ (e : Expr), e.constsResolveF (mkFEnv env) = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .lit (.strVal _) => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .const n _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?]
  | .fvar _ _ ty => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty]
  | .app f a => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env f, constsResolveF_eq env a]
  | .lam _ ty body _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .forallE _ ty body _ => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env body]
  | .letE _ ty val body => by
    simp only [Expr.constsResolveF, Expr.constsResolve,
      constsResolveF_eq env ty, constsResolveF_eq env val,
      constsResolveF_eq env body]
  | .proj s _ e => by
    simp only [Expr.constsResolveF, Expr.constsResolve, mkFEnv_find?,
      constsResolveF_eq env e]

/-- `constsResolveF` under `mkFEnv`, as a function equation. -/
theorem constsResolveF_eq_fun (env : Env) :
    (Expr.constsResolveF (mkFEnv env)) = (Expr.constsResolve env ·) :=
  funext (constsResolveF_eq env)

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

theorem stdAxiomOkF_eq (env : Env) (cvA : ConstantVal) :
    stdAxiomOkF (mkFEnv env) cvA = stdAxiomOk env cvA := by
  simp only [stdAxiomOkF, stdAxiomOk, mkFEnv_find?] <;> rfl

theorem trustCompilerOkF_eq (env : Env) (cvA : ConstantVal) :
    trustCompilerOkF (mkFEnv env) cvA = trustCompilerOk env cvA := by
  simp only [trustCompilerOkF, trustCompilerOk, mkFEnv_find?] <;> rfl

theorem reduceStoredOkF_eq (env : Env) (c : Name) :
    reduceStoredOkF (mkFEnv env) c = reduceStoredOk env c := by
  simp only [reduceStoredOkF, reduceStoredOk, mkFEnv_find?] <;> rfl

theorem reduceElemOkF_eq (env : Env) (c : Name) :
    reduceElemOkF (mkFEnv env) c = reduceElemOk env c := by
  simp only [reduceElemOkF, reduceElemOk, mkFEnv_find?] <;> rfl

theorem ofReduceAxOkF_eq (env : Env) (cvA : ConstantVal) :
    ofReduceAxOkF (mkFEnv env) cvA = ofReduceAxOk env cvA := by
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

theorem divModPinGuardF_eq (env : Env) (c : Name) :
    divModPinGuardF (mkFEnv env) c = divModPinGuard env c := by
  simp only [divModPinGuardF, divModPinGuard, constsResolveF_eq] <;> rfl

theorem divModCertsGuardF_eq (env : Env) (c : Name) (annVal : Expr) :
    divModCertsGuardF (mkFEnv env) c annVal
      = divModCertsGuard env c annVal := by
  simp only [divModCertsGuardF, divModCertsGuard, divModCertGuardF_eq] <;> rfl

theorem checkEtaThmF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) :
    checkEtaThmF (mkFEnv env) T ctorName lps nP nF
      = checkEtaThm env T ctorName lps nP nF := by
  simp only [checkEtaThmF, checkEtaThm, mkFEnv_find?] <;> rfl

theorem checkUnitThmF_eq (env : Env) (T : Name) (lps : List Name)
    (nP : Nat) :
    checkUnitThmF (mkFEnv env) T lps nP = checkUnitThm env T lps nP := by
  simp only [checkUnitThmF, checkUnitThm, mkFEnv_find?] <;> rfl

theorem indBlockCapsF_eq (env : Env) (cvT cvC : ConstantVal)
    (nP nF : Nat) :
    indBlockCapsF (mkFEnv env) cvT cvC nP nF
      = indBlockCaps env cvT cvC nP nF := by
  simp only [indBlockCapsF, indBlockCaps, checkEtaThmF_eq,
    checkUnitThmF_eq] <;> rfl

theorem nestedRuleShapeF_eq (env' envS : Env) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    nestedRuleShapeF (mkFEnv env') (mkFEnv envS) cvName lps tyA
        mI rP cnP j
      = nestedRuleShape env' envS cvName lps tyA mI rP cnP j := by
  simp only [nestedRuleShapeF, nestedRuleShape, mkFEnv_findCV?,
    constsResolveF_eq] <;> rfl

theorem directNonRecF_eq (env : Env) (p : DirectParts) :
    directNonRecF (mkFEnv env) p = directNonRec env p := by
  simp only [directNonRecF, directNonRec, constsResolveF_eq] <;> rfl

theorem directNoModelF_eq (env : Env) (p : DirectParts) :
    directNoModelF (mkFEnv env) p = directNoModel env p := by
  simp only [directNoModelF, directNoModel, mkFEnv_find?] <;> rfl

/-- The direct-structure recognition through the index is the pure
one (task #82). -/
theorem directPartsF?_eq (env : Env) (block : List ConstantInfo) :
    directPartsF? (mkFEnv env) block = directParts? env block := by
  simp only [directPartsF?, directParts?, directNonRecF_eq,
    directNoModelF_eq] <;> rfl

/-! ## Monadic mirrors (non-extending: plain program equalities) -/

section Monadic

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkConstantValF_eq (ops : CheckerOps m) (env : Env)
    (cv : ConstantVal) :
    checkConstantValF ops (mkFEnv env) cv = checkConstantVal ops env cv := by
  simp only [checkConstantValF, checkConstantVal, mkFEnv_find?,
    constsResolveF_eq] <;> rfl

theorem checkMemberValF_eq (ops : CheckerOps m) (blockNames : List Name)
    (env : Env) (cv : ConstantVal) :
    checkMemberValF ops blockNames (mkFEnv env) cv
      = checkMemberVal ops blockNames env cv := by
  simp only [checkMemberValF, checkMemberVal, mkFEnv_find?,
    checkConstantValF_eq] <;> rfl

theorem checkIotaThmF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    checkIotaThmF ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThm ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmF, checkIotaThm, mkFEnv_findCV?] <;> rfl

theorem checkIotaThmNF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    checkIotaThmNF ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
      = checkIotaThmN ops env' envS f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA := by
  simp only [checkIotaThmNF, checkIotaThmN, mkFEnv_findCV?,
    nestedRuleShapeF_eq] <;> rfl

theorem checkIotaRuleF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) :
    checkIotaRuleF ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
        mI rP j r
      = checkIotaRule ops env' envS f cvName lps tyA mI rP j r := by
  simp only [checkIotaRuleF, checkIotaRule, mkFEnv_find?,
    constsResolveF_eq, checkIotaThmF_eq, checkIotaThmNF_eq] <;> rfl

theorem checkIotaRulesF_eq (ops : CheckerOps m) (env' envS : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) :
    ∀ (j : Nat) (rs : List RecRule),
      checkIotaRulesF ops (mkFEnv env') (mkFEnv envS) f cvName lps tyA
          mI rP j rs
        = checkIotaRules ops env' envS f cvName lps tyA mI rP j rs
  | _, [] => rfl
  | j, r :: rest => by
    simp only [checkIotaRulesF, checkIotaRules, checkIotaRuleF_eq,
      checkIotaRulesF_eq ops env' envS f cvName lps tyA mI rP
        (j + 1) rest]

theorem checkProjLookupsF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    (checkProjLookupsF (mkFEnv env) T ctorName lps nP nF i : m _)
      = checkProjLookups env T ctorName lps nP nF i := by
  simp only [checkProjLookupsF, checkProjLookups, mkFEnv_find?] <;> rfl

theorem checkProjTyF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (mty : Expr) (nP nF : Nat) :
    (checkProjTyF (mkFEnv env) T ctorName lps mty nP nF : m _)
      = checkProjTy env T ctorName lps mty nP nF := by
  simp only [checkProjTyF, checkProjTy, constsResolveF_eq] <;> rfl

theorem checkProjRuleF_eq (ops : CheckerOps m) (env : Env) (pty : Expr)
    (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    checkProjRuleF ops (mkFEnv env) pty cvj lps nP nF i
      = checkProjRule ops env pty cvj lps nP nF i := by
  simp only [checkProjRuleF, checkProjRule, constsResolveF_eq] <;> rfl

theorem checkProjIotaF_eq (env : Env) (T ctorName : Name)
    (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    (checkProjIotaF (mkFEnv env) T ctorName lps cvj nP nF i : m _)
      = checkProjIota env T ctorName lps cvj nP nF i := by
  simp only [checkProjIotaF, checkProjIota, mkFEnv_find?] <;> rfl

/-! ### The direct simple-structure path (task #82) -/

theorem checkDirectFieldUnivF_eq (ops : CheckerOps m) (env : Env)
    (s : Level) (nP : Nat) (fvs : List Expr) :
    ∀ (j : Nat),
      checkDirectFieldUnivF ops (mkFEnv env) s nP fvs j
        = checkDirectFieldUniv ops env s nP fvs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkDirectFieldUnivF, checkDirectFieldUniv, mkFEnv_env,
      checkDirectFieldUnivF_eq ops env s nP fvs j]

theorem checkDirectDomsAtF_eq (ops : CheckerOps m) (env : Env)
    (off : Nat) (fvs doms : List Expr) :
    ∀ (j : Nat),
      checkDirectDomsAtF ops (mkFEnv env) off fvs doms j
        = checkDirectDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkDirectDomsAtF, checkDirectDomsAt, mkFEnv_env,
      checkDirectDomsAtF_eq ops env off fvs doms j]

theorem checkDirectRecTyF_eq (ops : CheckerOps m) (env : Env)
    (p : DirectParts) (cvTa cvCa cvRa : ConstantVal) :
    checkDirectRecTyF ops (mkFEnv env) p cvTa cvCa cvRa
      = checkDirectRecTy ops env p cvTa cvCa cvRa := by
  simp only [checkDirectRecTyF, checkDirectRecTy, mkFEnv_env,
    checkDirectDomsAtF_eq] <;> rfl

theorem checkDirectRuleF_eq (ops : CheckerOps m) (env : Env)
    (p : DirectParts) (cvCa cvRa : ConstantVal) :
    checkDirectRuleF ops (mkFEnv env) p cvCa cvRa
      = checkDirectRule ops env p cvCa cvRa := by
  simp only [checkDirectRuleF, checkDirectRule, mkFEnv_env,
    constsResolveF_eq] <;> rfl

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

theorem checkDivModPinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) :
    checkDivModPinF ops (mkFEnv env) (mkFEnv env2) c
      = checkDivModPin ops env env2 c := by
  simp only [checkDivModPinF, checkDivModPin, mkFEnv_find?,
    divModEnvGuardF_eq, divModPinGuardF_eq, divModCertsGuardF_eq,
    checkDivModCertsF_eq] <;> rfl

theorem checkReducePinF_eq (ops : CheckerOps m) (env env2 : Env)
    (c : Name) (value : Expr) :
    checkReducePinF ops (mkFEnv env) (mkFEnv env2) c value
      = checkReducePin ops env env2 c value := by
  simp only [checkReducePinF, checkReducePin, mkFEnv_env,
    reduceStoredOkF_eq, reduceElemOkF_eq, reducePinGuardF_eq] <;> rfl

end Monadic

/-! ## Environment-extending mirrors: push form

At `CheckIM` (where the monad laws and `throw`-bind hold
definitionally), each extending mirror is its generic counterpart
followed by `mkFEnv` — the pushed index of the cons-extended
environment *is* `mkFEnv` of it (`push_mkFEnv`, definitional). -/

theorem push_mkFEnv (env : Env) (ci : ConstantInfo) :
    (mkFEnv env).push ci = mkFEnv ⟨ci :: env.consts⟩ := rfl

theorem throwI_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckIM β) : ((throw e : CheckIM α) >>= f) = throw e := rfl

theorem bindI_congr {α β : Type} {x : CheckIM α} {f g : α → CheckIM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindI {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckIM α) (f : α → CheckIM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem checkDefnValF_push (ops : CheckerOps CheckIM) (env : Env)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint) :
    checkDefnValF ops (mkFEnv env) cv value hint
      = checkDefnVal ops env cv value hint
          >>= fun e => pure (mkFEnv e) := by
  unfold checkDefnValF checkDefnVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindI, throwI_bind_eq] <;> rfl

theorem checkThmValF_push (ops : CheckerOps CheckIM) (env : Env)
    (cv : ConstantVal) (value : Expr) :
    checkThmValF ops (mkFEnv env) cv value
      = checkThmVal ops env cv value >>= fun e => pure (mkFEnv e) := by
  unfold checkThmValF checkThmVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindI, throwI_bind_eq] <;> rfl

theorem checkOpaqueValF_push (ops : CheckerOps CheckIM) (env : Env)
    (cv : ConstantVal) (value : Expr) :
    checkOpaqueValF ops (mkFEnv env) cv value
      = checkOpaqueVal ops env cv value >>= fun e => pure (mkFEnv e) := by
  unfold checkOpaqueValF checkOpaqueVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindI, throwI_bind_eq] <;> rfl

theorem installBasisDeclF_push (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckIM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindI,
    throwI_bind_eq] <;> rfl

theorem installBasisFoldF_push :
    ∀ (l : List ConstantInfo) (env : Env),
      (l.foldlM installBasisDeclF (mkFEnv env) : CheckIM FEnv)
        = l.foldlM installBasisDecl env >>= fun e => pure (mkFEnv e)
  | [], env => by
    simp only [List.foldlM_nil, pure_bind]
  | ci :: l, env => by
    rw [List.foldlM_cons, List.foldlM_cons, installBasisDeclF_push,
      bind_assoc, bind_assoc]
    refine bindI_congr fun e => ?_
    rw [pure_bind, installBasisFoldF_push l e]

/-! ### The direct simple-structure path's extending stages -/

theorem checkDirectIndF_push (ops : CheckerOps CheckIM) (env : Env)
    (p : DirectParts) :
    checkDirectIndF ops (mkFEnv env) p
      = checkDirectInd ops env p
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectIndF checkDirectInd
  simp only [checkConstantValF_eq, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindI, throwI_bind_eq] <;> rfl

theorem checkDirectCtorF_push (ops : CheckerOps CheckIM) (env₀ env : Env)
    (p : DirectParts) (cvTa : ConstantVal) :
    checkDirectCtorF ops (mkFEnv env₀) (mkFEnv env) p cvTa
      = checkDirectCtor ops env₀ env p cvTa
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectCtorF checkDirectCtor
  simp only [checkConstantValF_eq, checkDirectDomsAtF_eq,
    checkDirectFieldUnivF_eq, constsResolveF_eq, push_mkFEnv,
    bind_assoc, pure_bind, ite_bindI, throwI_bind_eq] <;> rfl

theorem checkDirectProjF_push (ops : CheckerOps CheckIM) (T C : Name)
    (lps : List Name) (nP nF : Nat) (cvTa cvCa : ConstantVal) (env : Env)
    (i : Nat) :
    checkDirectProjF ops T C lps nP nF cvTa cvCa (mkFEnv env) i
      = checkDirectProj ops T C lps nP nF cvTa cvCa env i
          >>= fun e => pure (mkFEnv e) := by
  unfold checkDirectProjF checkDirectProj
  simp only [checkProjRuleF_eq, constsResolveF_eq, mkFEnv_find?,
    mkFEnv_env, push_mkFEnv, bind_assoc, pure_bind, ite_bindI,
    throwI_bind_eq] <;> rfl

/-- The non-inductive branches of `checkDeclSF` are the generic
`checkDecl` (at the shared operations) followed by `mkFEnv`. -/
theorem checkDeclSF_nonind (env : Env) (d : Declaration)
    (hnotind : ∀ block, d ≠ .indDecl block) :
    checkDeclSF (mkFEnv env) d
      = checkDecl (sharedOps (mkFEnv env)) env d
          >>= fun e => pure (mkFEnv e) := by
  cases d with
  | indDecl block => exact absurd rfl (hnotind block)
  | defnDecl cv value hint =>
    show (do
        let cv ← checkConstantValF (sharedOps (mkFEnv env))
          (mkFEnv env) cv
        if natOpNames.contains cv.name ||
            natDivModNames.contains cv.name then
          let fe2 ← checkDefnValF (sharedOps (mkFEnv env)) (mkFEnv env)
            cv value hint
          if natOpNames.contains cv.name then
            unless natOpGuardF fe2 cv.name &&
                (natOpDeps cv.name).all (natOpStoredOkF fe2) do
              throw (.notImplemented
                s!"nonstandard structural Nat operation environment ({cv.name})")
            match fe2.find? cv.name with
            | some (.defnInfo _ value' _) =>
              let ok ← certifyNatEqs (sharedOps (mkFEnv env))
                (mkFEnv env).env
                ((natOpEquations 0 cv.name).map fun eq =>
                  (Expr.substConst0 cv.name value' eq.1,
                   Expr.substConst0 cv.name value' eq.2))
              unless ok do
                throw (.notImplemented
                  s!"nonstandard structural Nat operation ({cv.name})")
            | _ => throw (.internal
                s!"structural Nat operation not stored ({cv.name})")
          if natDivModNames.contains cv.name then
            checkDivModPinF (sharedOps (mkFEnv env)) (mkFEnv env) fe2
              cv.name
          pure fe2
        else
          checkDefnValF (sharedOps (mkFEnv env)) (mkFEnv env)
            cv value hint : CheckIM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, mkFEnv_env, bind_assoc]
    refine bindI_congr fun cvA => ?_
    by_cases hb : (natOpNames.contains cvA.name ||
        natDivModNames.contains cvA.name) = true
    case neg =>
      obtain ⟨h1, h4⟩ : ¬(natOpNames.contains cvA.name = true) ∧
          ¬(natDivModNames.contains cvA.name = true) := by
        simpa [not_or] using hb
      rw [if_neg hb, checkDefnValF_push]
      simp only [if_neg h1, if_neg h4, pure_bind]
    simp only [if_pos hb]
    rw [checkDefnValF_push]
    simp only [bind_assoc, pure_bind]
    refine bindI_congr fun env2 => ?_
    simp only [natOpGuardF_eq, natOpStoredOkF_eq_fun, mkFEnv_find?,
      checkDivModPinF_eq, bind_assoc, pure_bind,
      ite_bindI, throwI_bind_eq]
    by_cases hnat : natOpNames.contains cvA.name = true
    case neg => simp only [if_neg hnat] <;> rfl
    simp only [if_pos hnat]
    by_cases hg : (natOpGuard env2 cvA.name &&
        (natOpDeps cvA.name).all (natOpStoredOk env2)) = true
    case neg => simp only [if_neg hg] <;> rfl
    simp only [if_pos hg]
    cases env2.find? cvA.name with
    | none => rfl
    | some ci =>
      cases ci <;>
        simp only [bind_assoc, pure_bind, ite_bindI, throwI_bind_eq] <;>
        rfl
  | thmDecl cv value =>
    show (do
        let cv ← checkConstantValF (sharedOps (mkFEnv env))
          (mkFEnv env) cv
        checkThmValF (sharedOps (mkFEnv env)) (mkFEnv env) cv value :
        CheckIM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, checkThmValF_push, bind_assoc]
  | opaqueDecl cv value =>
    show (do
        let cv ← checkConstantValF (sharedOps (mkFEnv env))
          (mkFEnv env) cv
        let fe2 ← checkOpaqueValF (sharedOps (mkFEnv env)) (mkFEnv env)
          cv value
        if reduceOpNames.contains cv.name then
          checkReducePinF (sharedOps (mkFEnv env)) (mkFEnv env) fe2
            cv.name value
        pure fe2 : CheckIM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, bind_assoc]
    refine bindI_congr fun cvA => ?_
    rw [checkOpaqueValF_push]
    simp only [bind_assoc, pure_bind]
    refine bindI_congr fun env2 => ?_
    simp only [checkReducePinF_eq, bind_assoc, pure_bind,
      ite_bindI] <;> rfl
  | axiomDecl cv =>
    show (do
        let cvA ← checkConstantValF (sharedOps (mkFEnv env))
          (mkFEnv env) cv
        if stdAxiomOkF (mkFEnv env) cvA then
          pure ((mkFEnv env).push (.axiomInfo cvA))
        else if cvA.name = trustCompilerName then
          if trustCompilerOkF (mkFEnv env) cvA then
            pure ((mkFEnv env).push (.axiomInfo cvA))
          else throw (.notImplemented
            s!"unsupported Lean.trustCompiler shape ({cv.name})")
        else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
          if ofReduceAxOkF (mkFEnv env) cvA then
            pure ((mkFEnv env).push (.axiomInfo cvA))
          else throw (.notImplemented
            s!"unsupported compiler-trust axiom environment ({cv.name})")
        else if cvA.name = propextName ∨ cvA.name = choiceName then
          throw (.notImplemented
            s!"standard axiom shape mismatch ({cv.name})")
        else if toleratedAxiomNames.contains cvA.name then
          pure (mkFEnv env)
        else
          throw (.notImplemented s!"non-standard axiom ({cv.name})") :
        CheckIM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, stdAxiomOkF_eq, trustCompilerOkF_eq,
      ofReduceAxOkF_eq, push_mkFEnv,
      bind_assoc, pure_bind, ite_bindI, throwI_bind_eq] <;> rfl
  | basisDecl kind =>
    show (do
        if kind = .quotK then
          unless (mkFEnv env).find? eqName = some eqA do
            throw (.notImplemented
              "quotient basis requires the pinned Eq basis")
        kind.declsA.foldlM installBasisDeclF (mkFEnv env) :
        CheckIM FEnv) = _
    unfold checkDecl
    simp only [mkFEnv_find?, installBasisFoldF_push, ite_bindI,
      throwI_bind_eq] <;> rfl

end Setlec
