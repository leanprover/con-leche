module

public import ConLeche.Model.Rules.Inputs

public section

/-!
# The soundness of the three list walks (task #305, lane S-red)

`Certs` (`certs_teleLic`, `Model/Steps/IotaGate.lean:123`, one step
per constructor), `DefEqList` (`map_interp_of_defEqListFueled`,
`Stuck.lean:223`) and `EtaProjCerts` (pointwise).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Certs.nil_sound {d : Nat} {lic : Bool} {T : Expr} :
    CertsSem m φ d lic T [] := by
  intro _ Δa Ta _ vs _ _ hgT _ hsp _ _
  cases hsp
  exact ⟨Ta, fun _ _ => .nil, hgT⟩

/-- The licensed slot: `iota_slot_transfer` (`Steps/IotaGate.lean:63`). -/
theorem Certs.skip_sound (hin : RulesInputs V m φ) {d : Nat} {lic : Bool}
    {ty body arg : Expr} {mb : BinderMeta} {rest : List Expr}
    (hlic : lic = true) (hnev : mb.pw.isNever = true)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  sorry

/-- The certified slot: `certs_telePA`'s step (`Steps/IotaKit.lean:246`). -/
theorem Certs.cert_sound (hin : RulesInputs V m φ) {d : Nat} {lic : Bool}
    {ty body arg ta : Expr} {mb : BinderMeta} {rest : List Expr}
    (hta : InferSemIO m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  sorry

theorem DefEqList.nil_sound {d : Nat} : DefEqListSem m φ d [] [] := by
  intro Δa asa bsa _ _ hsa hsb _ _ _ _
  cases hsa
  cases hsb
  rfl

theorem DefEqList.cons_sound {d : Nat} {a b : Expr} {as bs : List Expr}
    (h : DefEqSem m φ d a b) (hs : DefEqListSem m φ d as bs) :
    DefEqListSem m φ d (a :: as) (b :: bs) := by
  sorry

theorem EtaProjCerts.nil_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} :
    EtaProjCertsSem m φ d T us' targs b lpsT [] := by
  intro i hi
  exact nomatch hi

theorem EtaProjCerts.cons_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} {i : Nat}
    {rest : List Nat} {cvp : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hf : env.find? (projFnName T i) = some (.recInfo cvp mI rP rules))
    (hlps : cvp.levelParams = lpsT)
    (hstrip : (cvp.type.stripPis (targs.length + 1)).isSome = true)
    (hcerts : CertsSem m φ d false
      (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b]))
    (hrest : EtaProjCertsSem m φ d T us' targs b lpsT rest) :
    EtaProjCertsSem m φ d T us' targs b lpsT (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ⟨cvp, mI, rP, rules, hf, hlps, hstrip, hcerts⟩
  · exact hrest j hj'

end ConLeche.Model.Rules
