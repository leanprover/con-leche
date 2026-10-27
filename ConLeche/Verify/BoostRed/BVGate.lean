module

public import ConLeche.Verify.BoostRed.Kit
public meta import Lean
public meta import ConLeche.Verify.BoostRed.Boost

/-!
# From the checker's gate to the boost premises (task #368)

The checker's gate (`Kernel/BVUnsat.lean`) runs `boostCheckOk` on every
entry of `bvBoostChecks`; each entry is one boost premise kind over the
same pinned data (`BoostPins.*`).  The lemmas below turn an accepted
check into its premise; `#boost_assemble` builds, for an instance lemma
of the boost translation, its `Good` from the gate alone: every pin and
fact premise from the gate (the entry found by its index in the list),
every callee `Good` by the same assembly.
-/

public section

namespace ConLeche.Rules.BoostRed

open ConLeche

theorem bvCheck_of_gate {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry}
    (h : BVUnsat.pinsOk find? findProj? = true) {c : BoostCheck} (hc : c ∈ bvBoostChecks) :
    BVUnsat.boostCheckOk find? findProj? c = true := by
  simp only [BVUnsat.pinsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 c hc

theorem defPin_of_check {env : Env} {n : Name} {lps : List Name} {v : Expr}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.defn n lps v) = true) :
    DefPin env n lps v := by
  simp only [BVUnsat.boostCheckOk] at h
  split at h
  · rename_i cv v' hint hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨cv, hint, hf, h1⟩
  · exact nomatch h

theorem recPin_of_check {env : Env} {n : Name} {lps : List Name} {ty : Expr} {mI rP : Nat}
    {rules : List RecRule}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.recr n lps ty mI rP rules) = true) :
    RecPin env n lps ty mI rP rules := by
  simp only [BVUnsat.boostCheckOk] at h
  split at h
  · rename_i cv mI' rP' rules' hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨cv, hf, h1, h2⟩
  · exact nomatch h

theorem ctorPin_of_check {env : Env} {n : Name} {lps : List Name} {ty : Expr}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.ctor n lps ty) = true) :
    CtorPin env n lps ty := by
  simp only [BVUnsat.boostCheckOk] at h
  split at h
  · rename_i cv nP nF hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨cv, nP, nF, hf, h.1, h.2⟩
  · exact nomatch h

theorem indNeverProp_of_check {env : Env} {T : Name} {k : Nat}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.indNever T k) = true) :
    IndNeverProp env T k := by
  simp only [BVUnsat.boostCheckOk] at h
  split at h
  · rename_i cvT caps hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨cvT, caps, hf, h.1, fun us _ => ?_⟩
    simp [capsNeverZero, Level.substPW, h.2, PropWhen.bindZ, PropWhen.isNever]
  · exact nomatch h

theorem projPin_of_check {env : Env} {sn : Name} {i : Nat} {ctor : Name} {lps : List Name}
    {nP nF : Nat}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.proj sn i ctor lps nP nF) = true) :
    ProjPin env sn i ctor lps nP nF := by
  simp only [BVUnsat.boostCheckOk] at h
  split at h
  · rename_i e hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨e, hf, h1, h2, h3, h4, fun us => ?_⟩
    simp [ProjEntry.fireOk, h5]
  · exact nomatch h

theorem natLit_of_check {env : Env}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? .natLit = true) :
    natLitSupported env = true := h

theorem natOp_of_check {env : Env} {c : Name}
    (h : BVUnsat.boostCheckOk env.find? env.findProj? (.natOp c) = true) :
    natOpStored env c = true := by
  simp only [BVUnsat.boostCheckOk] at h
  unfold natOpStored
  split at h
  · rename_i cv v hint hf; rw [hf]
  · exact nomatch h

end ConLeche.Rules.BoostRed

end

public meta section

namespace BVGateGen

open Lean Meta Elab Term Command
open BoostGen

/-- The entries of `bvBoostChecks`, as terms. -/
def checkEntries : MetaM (Array Expr) := do
  let ci ← getConstInfo `ConLeche.bvBoostChecks
  let some v := ci.value? | throwError "bvBoostChecks has no value"
  let mut out := #[]
  let mut e := v
  while e.isAppOfArity ``List.cons 3 do
    out := out.push e.appFn!.appArg!
    e := e.appArg!
  return out

def kitL (s : String) : Name := (`ConLeche.Rules.BoostRed).str s

/-- A pin or fact premise from the gate. -/
def discharge (entries : Array Expr) (env hgate : Expr) (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  let mk (ctor : Name) (xs : Array Expr) (lem : String) : MetaM Expr := do
    let chk := mkAppN (Lean.mkConst ctor) xs
    let some i := entries.findIdx? (· == chk) | throwError "#boost_assemble: no gate check for{indentExpr t}"
    let chkT := Lean.mkConst ``ConLeche.BoostCheck
    let hget := mkApp2 (Lean.mkConst ``Eq.refl [1]) (mkApp (Lean.mkConst ``Option [0]) chkT)
      (mkApp2 (Lean.mkConst ``Option.some [0]) chkT chk)
    let hmem ← mkAppM ``List.mem_of_getElem? #[(← mkExpectedTypeHint hget
      (← mkEq (← mkAppM ``GetElem?.getElem? #[Lean.mkConst `ConLeche.bvBoostChecks, mkRawNatLit i])
        (mkApp2 (Lean.mkConst ``Option.some [0]) chkT chk)))]
    let hc := mkAppN (Lean.mkConst (kitL "bvCheck_of_gate"))
      #[mkApp (Lean.mkConst ``ConLeche.Env.find?) env, mkApp (Lean.mkConst ``ConLeche.Env.findProj?) env,
        hgate, chk, hmem]
    mkAppM (kitL lem) #[hc]
  match t.getAppFn.constName? with
  | some n =>
    if n == kitL "DefPin" then mk ``ConLeche.BoostCheck.defn (args.extract 1 4) "defPin_of_check"
    else if n == kitL "RecPin" then mk ``ConLeche.BoostCheck.recr (args.extract 1 7) "recPin_of_check"
    else if n == kitL "CtorPin" then mk ``ConLeche.BoostCheck.ctor (args.extract 1 4) "ctorPin_of_check"
    else if n == kitL "IndNeverProp" then
      mk ``ConLeche.BoostCheck.indNever (args.extract 1 3) "indNeverProp_of_check"
    else if n == kitL "ProjPin" then mk ``ConLeche.BoostCheck.proj (args.extract 1 7) "projPin_of_check"
    else if n == ``Eq then
      let lhs := args[1]!
      match lhs.getAppFn.constName? with
      | some ``ConLeche.natLitSupported => mk ``ConLeche.BoostCheck.natLit #[] "natLit_of_check"
      | some ``ConLeche.natOpStored => mk ``ConLeche.BoostCheck.natOp #[lhs.appArg!] "natOp_of_check"
      | _ => throwError "#boost_assemble: unknown fact{indentExpr t}"
    else throwError "#boost_assemble: unknown premise{indentExpr t}"
  | none => throwError "#boost_assemble: unknown premise{indentExpr t}"

syntax (name := boostAssembleCmd) "#boost_assemble " ident " as " ident : command

/-- `#boost_assemble L as T`: `T : ∀ env d, pinsOk env.find? env.findProj? = true → L.Good env d`. -/
@[command_elab boostAssembleCmd] def elabBoostAssemble : CommandElab := fun stx => liftTermElabM do
  let root := stx[1].getId
  let target := stx[3].getId
  let ((), (order, _)) ← (topo root).run (#[], {})
  let entries ← checkEntries
  let envT := Lean.mkConst ``ConLeche.Env
  withLocalDeclD `env envT fun env => withLocalDeclD `d (Lean.mkConst ``Nat) fun d => do
    let gateTy ← mkEq (mkApp2 (Lean.mkConst `ConLeche.BVUnsat.pinsOk)
      (mkApp (Lean.mkConst ``ConLeche.Env.find?) env) (mkApp (Lean.mkConst ``ConLeche.Env.findProj?) env))
      (Lean.mkConst ``Bool.true)
    withLocalDeclD `hgate gateTy fun hgate => do
      let mut goods : Std.HashMap Name Expr := {}
      let mut lets : Array (Name × Expr × Expr) := #[]
      for n in order do
        let ci ← getConstInfo (n ++ `R)
        let t ← instantiateForall ci.type #[env, d]
        let hs ← forallTelescope t fun xs _ => xs.mapM fun x => inferType x
        let mut args := #[env, d]
        for h in hs do
          match goodOf? h with
          | some g => args := args.push goods[g]!
          | none => args := args.push (← discharge entries env hgate h)
        let v := mkAppN (Lean.mkConst (n ++ `R)) args
        let fv := mkFVar (← mkFreshFVarId)
        goods := goods.insert n fv
        lets := lets.push (Name.mkSimple s!"g{lets.size}", mkApp2 (Lean.mkConst (n ++ `Good)) env d, v)
      let fvs := order.map fun n => goods[n]!
      let mut body := goods[root]!.abstract fvs
      for i in (List.range lets.size).reverse do
        let (nm, ty, v) := lets[i]!
        body := .letE nm (ty.abstract (fvs.extract 0 i)) (v.abstract (fvs.extract 0 i)) body false
      let goal := mkApp2 (Lean.mkConst (root ++ `Good)) env d
      let ty ← mkForallFVars #[env, d, hgate] goal
      let val ← instantiateMVars (← mkLambdaFVars #[env, d, hgate] body)
      addDecl (.thmDecl { name := target, levelParams := [], type := ty, value := val })

end BVGateGen

end
