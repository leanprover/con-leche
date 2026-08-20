import Setlec.Model.Extend

/-!
# Consistency of the checker

The headline results:

* `checkDecl_sound`: checking a declaration preserves having a model.
* `checkDecls_sound`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).

Both are parametric in a model `V` of the target set theory: assuming
Tarski–Grothendieck set theory is consistent (i.e. a `SetTheory` instance
exists), no accepted environment can prove `False` — the concrete
"no proof of `Empty` is accepted" corollary lands once `Empty` is in the
supported fragment.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The common inversion + semantic-fact assembly for a checked value
against a checked (annotated) type. -/
private theorem value_facts {env : Env} (m : EnvModel V env)
    {value value' type vtype : Expr}
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotate env 0 value = .ok value')
    (hvt : inferType env 0 value' = .ok vtype)
    (hde : isDefEq env 0 vtype type = .ok true)
    (htf : type.hasFvar = false)
    (htb : type.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T) :
    value'.hasFvar = false ∧
    (∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value') ∧
    (∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value' = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T) := by
  have hwv : WScoped 0 value := WScoped.of_not_hasFvar hivf
  have hvf' : value'.hasFvar = false := by
    rw [← Expr.LeafEquiv.hasFvar_eq value value' (annotate_leafEquiv value hannv hwv hlbv)]
    exact hivf
  have hbv' : value'.looseBVarsBounded 0 = true := annotate_looseBVars value hannv hlbv
  have hAv : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value' := fun ψ =>
    annotate_sound m value hannv hwv hlbv (Expr.LeavesBounded.of_not_hasFvar hivf)
      (rho0 V) (FvarsOk.of_not_hasFvar hivf)
  refine ⟨hvf', hAv, fun ψ => ?_⟩
  obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hAvt⟩ :=
    inferType_sound (φ := ψ) m hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
      (FvarsOk.of_not_hasFvar hvf') (hAv ψ)
  obtain ⟨T, hT⟩ := hkeyT ψ
  have hbvt : vtype.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
  have hLbvt : Expr.LeavesBounded vtype := fun l hl =>
    Expr.LeavesBounded.of_not_hasFvar hvf' l
      (inferTypeCore_fvarLeaves m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') l hl)
  have htveq : tv = T :=
    isDefEq_sound (φ := ψ) m hde hwvt (WScoped.of_not_hasFvar htf)
      hbvt htb hLbvt (Expr.LeavesBounded.of_not_hasFvar htf)
      (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hvt
        (WScoped.of_not_hasFvar hvf')) (FvarsOk.of_not_hasFvar hvf'))
      (FvarsOk.of_not_hasFvar htf)
      hAvt (hAty ψ) htv hT
  exact ⟨v, T, hv, hT, htveq ▸ hmem⟩

private theorem max_ne_zero_r'' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

/-- Checking a declaration preserves having a model. -/
theorem checkDecl_sound {env env' : Env} {d : Declaration}
    (h : checkDecl env d = .ok env') (m : EnvModel V env) : Nonempty (EnvModel V env') := by
  cases d with
  | axiomDecl cv => exact nomatch h
  | indDecl block => exact checkIndDecl_sound h m
  | basisDecl kind =>
    match kind, h with
    | .natK, h => ?_
    | .psigmaK, h => ?_
    | .eqK, h => ?_
    | .punitK, h => ?_
    | .emptyK, h => ?_
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Nat
      by_cases h1 : (env.find? natA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Nat.zero
      by_cases h2 : ((⟨natA :: env.consts⟩ : Env).find? natZeroA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Nat.succ
      by_cases h3 : ((⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 4: Nat.rec
      by_cases h4 : ((⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? natRecA.name).isNone
      case neg => simp [h4, pure, Except.pure] at h
      simp only [h4, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the four model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m natA (fun _ => omega)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => nat_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 natZeroA
        (fun _ => natzero)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natZeroA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natZeroA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natZero_key rfl (fun ψ' => hval1 ψ'))
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natZeroA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natZeroA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natZeroA]))
      have hvalN2 : ∀ ψ' : Name → Nat, m2.val natName ψ' = omega := fun ψ' => by
        rw [hpres2 natName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 natSuccA
        (fun ψ => natSuccVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natSuccA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natSuccA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natSucc_key rfl hvalN2)
        (fun _ _ _ => rfl)
        (fun ψ => annotOk_natSucc_type rfl hvalN2)
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natSuccA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natSuccA]))
      have hvalN3 : ∀ ψ' : Name → Nat, m3.val natName ψ' = omega := fun ψ' => by
        rw [hpres3 natName ψ' (by decide)]
        exact hvalN2 ψ'
      have hvalZ3 : ∀ ψ' : Name → Nat, m3.val natZeroName ψ' = natzero := fun ψ' => by
        rw [hpres3 natZeroName ψ' (by decide)]
        exact hval2 ψ'
      obtain ⟨m4, hval4, hpres4⟩ := extend_basis_one m3 natRecA
        (fun ψ => natRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h4)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [natRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natRec_key rfl hvalN3 rfl hvalZ3 rfl (fun ψ' => hval3 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [natRecVal]
          rw [hψ uN (by simp [natRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_natRec_type rfl hvalN3 rfl hvalZ3 rfl
          (fun ψ' => hval3 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_neg (by decide), Env.find?_cons, if_pos (by decide)],
            by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalN' : ∀ ψ' : Name → Nat, val' natName ψ' = omega := by
            intro ψ'
            rw [hv2 natName ψ' (by decide)]
            exact hvalN3 ψ'
          have hvalZ' : ∀ ψ' : Name → Nat, val' natZeroName ψ' = natzero := by
            intro ψ'
            rw [hv2 natZeroName ψ' (by decide)]
            exact hvalZ3 ψ'
          have hvalSc' : ∀ ψ' : Name → Nat,
              val' natSuccName ψ' = natSuccVal V ψ' := by
            intro ψ'
            rw [hv2 natSuccName ψ' (by decide)]
            exact hval3 ψ'
          have hvalRc' : ∀ ψ' : Name → Nat,
              val' (natName.str "rec") ψ' = natRecVal V ψ' :=
            fun ψ' => hv1 ψ'
          have hfN' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natName = some natA := rfl
          have hfZ' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natZeroName = some natZeroA := rfl
          have hfSc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natSuccName = some natSuccA := rfl
          have hfRc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              (natName.str "rec") = some natRecA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · -- zero rule
            refine ⟨fun ψ => annotOk_natRecZero_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natZeroA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            have htv' : tv = natzero := by
              rw [htv, hv2 _ _ (by decide)]
              exact hvalZ3 ψj
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩⟩ :=
              natZeroIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3 htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩, trivial⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · -- successor rule
            refine ⟨fun ψ => annotOk_natRecSucc_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc' hfRc' hvalRc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natSuccA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y1, _ | ⟨y2, ys⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            obtain ⟨hms1, -⟩ := hmch
            obtain ⟨vE', A', B', hq', hn', hf'⟩ := hms1
            have hsucceq : ∀ ψ'' : Name → Nat,
                val' ((Name.anonymous.str "Nat").str "succ") ψ'' =
                natSuccVal V ψ := by
              intro ψ''
              rw [hv2 _ _ (by decide)]
              exact hval3 ψ''
            rw [hsucceq] at hq'
            have htv' : tv = SetTheory.app (natSuccVal V ψ) y1 := by
              rw [htv, show SpineFold V (val'
                  ((Name.anonymous.str "Nat").str "succ") ψj) [y1] =
                  SetTheory.app (val'
                    ((Name.anonymous.str "Nat").str "succ") ψj) y1 from rfl,
                hsucceq]
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              natSuccIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc' hfRc' hvalRc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE' := vE') (A' := A') (B' := B') hq' hn' htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "zero") = some natZeroA := by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "succ") = some natSuccA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m4⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: PSigma'
      by_cases h1 : (env.find? psigmaA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: PSigma'.mk
      by_cases h2 : ((⟨psigmaA :: env.consts⟩ : Env).find? psigmaMkA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: PSigma'.rec
      by_cases h3 : ((⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- the semantic pair facts the environment invariant records
      have htyfacts : ∀ ψ' : Name → Nat,
          PairTyFacts V (psigmaVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_⟩
        · intro vE A₀ B₀ x hmem hx
          simp only [psigmaVal] at hmem
          exact lam_pi_dom hmem
            (max_ne_zero_r'' (Nat.succ_ne_zero (Nat.max (ψ' uN) (ψ' vN)))) hx
        · intro vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaVal_app hvA] at hmem
          exact lam_pi_dom hmem (Nat.succ_ne_zero _) hx
        · intro vA vB hvA hvB
          exact psigmaVal_fold hvA hvB
      have hmkfacts : ∀ ψ' : Name → Nat,
          PairMkFacts V (psigmaMkVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hw vE A₀ B₀ x hmem hx
          simp only [psigmaMkVal] at hmem
          refine lam_pi_dom hmem ?_ hx
          rw [if_neg hw]
          exact max_ne_zero_r'' (Nat.succ_ne_zero (ψ' vN))
        · intro hw vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaMkVal_app hvA] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB vE A₂ B₂ x hvA hvB hmem hx
          rw [psigmaMkVal_app₂ hvA hvB] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB va vE A₃ B₃ x hvA hvB hva hmem hx
          rw [psigmaMkVal_app₃ hvA hvB hva] at hmem
          exact lam_pi_dom hmem hw hx
        · intro vA vB va vb hvA hvB hva hvb
          exact psigmaMkVal_fold hvA hvB hva hvb
        · intro hw x y z w'
          simp only [psigmaMkVal]
          rw [if_pos hw, lam_zero, app_pt, app_pt, app_pt, app_pt]
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m psigmaA
        (fun ψ => psigmaVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigma_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaVal]
          rw [hψ uN (by simp [psigmaA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigma_type)
        (fun cv hx _ => ⟨by cases hx; rfl, htyfacts⟩)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 psigmaMkA
        (fun ψ => psigmaMkVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaMkA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaMkA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaMk_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaMkVal]
          rw [hψ uN (by simp [psigmaMkA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaMkA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaMk_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => by
          cases hx
          exact ⟨rfl, rfl, rfl, hmkfacts⟩)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaMkA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaMkA]))
      have hvalS2 : ∀ ψ' : Name → Nat, m2.val psigmaName ψ' = psigmaVal V ψ' :=
        fun ψ' => by
          rw [hpres2 psigmaName ψ' (by decide)]
          exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 psigmaRecA
        (fun ψ => psigmaRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [psigmaRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaRec_key rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaRecVal]
          rw [hψ uN (by simp [psigmaRecA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaRecA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaRec_type rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalS' : ∀ ψ' : Name → Nat,
              val' psigmaName ψ' = psigmaVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaName ψ' (by decide)]
            exact hvalS2 ψ'
          have hvalM' : ∀ ψ' : Name → Nat,
              val' psigmaMkName ψ' = psigmaMkVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaMkName ψ' (by decide)]
            exact hval2 ψ'
          have hfS' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaName = some psigmaA := rfl
          have hfM' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaMkName = some psigmaMkA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_psigmaRec_rhs (cval := val') (ψ := ψ)
              rfl hvalS' rfl hvalM', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [psigmaMkA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨Bv, _ | ⟨Mv, _ | ⟨mkv,
              _ | ⟨x, rest⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨av, _ | ⟨bv,
              _ | ⟨y, ys⟩⟩⟩⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨hms1, hms2, hms3, hms4, -⟩ := hmch
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hms3
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hms4
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
              ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
              ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩⟩ :=
              psigmaIota_claims (cval := val') (ψ := ψ)
                (Av := Av) (Bv := Bv) (Mv := Mv) (mkv := mkv) (tv := tv)
                (av := av) (bv := bv)
                hfS' hvalS' hfM' hvalM' hm1 hm2 hm3 hm4 hm5 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' psigmaRecA.name ψ)
                  ([Av, Bv, Mv, mkv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (val' psigmaRecA.name ψ) Av) Bv)
                    Mv) mkv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
                ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
                ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env)
                ((Name.anonymous.str "PSigma'").str "mk") =
                some psigmaMkA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Eq
      by_cases h1 : (env.find? eqA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Eq.refl
      by_cases h2 : ((⟨eqA :: env.consts⟩ : Env).find? eqReflA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Eq.rec
      by_cases h3 : ((⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m eqA (fun ψ => eqVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eq_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqVal]
          rw [hψ uN (by simp [eqA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eq_type)
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 eqReflA
        (fun ψ => eqReflVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqReflA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqReflA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRefl_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqReflVal]
          rw [hψ uN (by simp [eqReflA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRefl_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqReflA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqReflA]))
      have hvalE2 : ∀ ψ' : Name → Nat, m2.val eqName ψ' = eqVal V ψ' := fun ψ' => by
        rw [hpres2 eqName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 eqRecA
        (fun ψ => eqRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [eqRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRec_key rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqRecVal]
          rw [hψ u1N (by simp [eqRecA, ConstantInfo.toConstantVal, u1N]),
            hψ uN (by simp [eqRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRec_type rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalE' : ∀ ψ' : Name → Nat, val' eqName ψ' = eqVal V ψ' := by
            intro ψ'
            rw [hv2 eqName ψ' (by decide)]
            exact hvalE2 ψ'
          have hvalR' : ∀ ψ' : Name → Nat,
              val' eqReflName ψ' = eqReflVal V ψ' := by
            intro ψ'
            rw [hv2 eqReflName ψ' (by decide)]
            exact hval2 ψ'
          have hfE' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqName = some eqA := rfl
          have hfR' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqReflName = some eqReflA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_eqRec_rhs (cval := val') (ψ := ψ)
              rfl hvalE' rfl hvalR', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [eqReflA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨av, _ | ⟨Mv, _ | ⟨rv,
              _ | ⟨bv, _ | ⟨x, rest⟩⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ys⟩⟩⟩ <;>
              simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hs5
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hs6
            rw [hv1] at hp1 hp2 hp3 hp4 hp5 hp6
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              eqIota_claims (cval := val') (ψ := ψ)
                hfE' hvalE' hfR' hvalR'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE4 := vE4) (A4 := A4) (B4 := B4) hp4 hm4
                (vE5 := vE5) (A5 := A5) (B5 := B5) hp5 hm5
                (vE6 := vE6) (A6 := A6) (B6 := B6) hp6 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' eqRecA.name ψ)
                  ([Av, av, Mv, rv, bv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' eqRecA.name ψ) Av) av) Mv) rv) bv) tv
                  from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨eqReflA :: eqA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Eq").str "refl") = some eqReflA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m3⟩
    simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
    -- step 1: PUnit
    by_cases h1 : (env.find? punitA.name).isNone
    case neg => simp [h1, pure, Except.pure] at h
    simp only [h1, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 2: PUnit.unit
    by_cases h2 : ((⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name).isNone
    case neg => simp [h2, pure, Except.pure] at h
    simp only [h2, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 3: PUnit.rec
    by_cases h3 : ((⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitRecA.name).isNone
    case neg => simp [h3, pure, Except.pure] at h
    simp only [h3, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    -- chain the three model extensions
    obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m punitA (fun _ => unitSet)
      (Option.isNone_iff_eq_none.mp h1)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punit_key)
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx hn => absurd hn (by decide))
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv _ _ ψ x hx => mem_unitSet hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitA]))
    obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 punitUnitA (fun _ => pt)
      (Option.isNone_iff_eq_none.mp h2)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitUnitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitUnitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitUnit_key rfl (fun ψ' => hval1 ψ'))
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitUnitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx hn => absurd hn (by decide))
      (fun cv hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitUnitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitUnitA]))
    have hvalP2 : ∀ ψ' : Name → Nat, m2.val punitName ψ' = unitSet := fun ψ' => by
      rw [hpres2 punitName ψ' (by decide)]
      exact hval1 ψ'
    obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 punitRecA
      (fun ψ => punitRecVal V ψ)
      (Option.isNone_iff_eq_none.mp h3)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [punitRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitRec_key rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun ψ₁ ψ₂ hψ => by
        simp only [punitRecVal]
        rw [hψ u1N (by simp [punitRecA, ConstantInfo.toConstantVal, u1N]),
          hψ uN (by simp [punitRecA, ConstantInfo.toConstantVal, uN])])
      (fun ψ => annotOk_punitRec_type rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩⟩)
      (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        have hvalP' : ∀ ψ' : Name → Nat, val' punitName ψ' = unitSet := by
          intro ψ'
          rw [hv2 punitName ψ' (by decide)]
          exact hvalP2 ψ'
        have hvalU' : ∀ ψ' : Name → Nat, val' punitUnitName ψ' = pt := by
          intro ψ'
          rw [hv2 punitUnitName ψ' (by decide)]
          exact hval2 ψ'
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨fun ψ => annotOk_punitRec_rhs (cval := val') (ψ := ψ)
            rfl hvalP' rfl hvalU', ?_⟩
          intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
            htv _hpeq _hlev _hfit
          have hje := Option.some.inj hfj
          simp only [punitUnitA] at hje
          injection hje with hj1 hj2 hj3
          subst hj1 hj2 hj3
          rcases args with _ | ⟨Mv, _ | ⟨mv, _ | ⟨x, rest⟩⟩⟩ <;>
            simp at hlen
          rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
          obtain ⟨hs1, hs2, hs3, -⟩ := hch
          obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
          obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
          rw [hv1] at hp1 hp2
          have htv' : tv = pt := by
            rw [htv, hv2 _ _ (by decide)]
            exact hval2 ψj
          have hfP' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitName = some punitA := rfl
          have hfU' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitUnitName = some punitUnitA := rfl
          obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
            ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩⟩ :=
            punitIota_claims (cval := val') (ψ := ψ) hfP' hvalP' hfU' hvalU'
              (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
              (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2 htv'
          refine ⟨R, hRi, ?_, ?_⟩
          · rw [show SpineFold V (val' punitRecA.name ψ)
                ([Mv, mv] ++ [tv]) = SetTheory.app (SetTheory.app
                  (SetTheory.app (val' punitRecA.name ψ) Mv) mv) tv
                from rfl]
            rw [hv1]
            exact hfold
          · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩, trivial⟩
        · cases hr)
      (fun cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · have hf : Env.find?
              (⟨punitUnitA :: punitA :: env.consts⟩ : Env)
              ((Name.anonymous.str "PUnit").str "unit") =
              some punitUnitA := by
            rw [Env.find?_cons, if_pos (by decide)]
          exact ⟨_, _, _, hf⟩
        · cases hr)
    exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind] at h
      -- step 1: Empty
      by_cases h1 : (env.find? emptyA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Empty.rec
      by_cases h2 : ((⟨emptyA :: env.consts⟩ : Env).find?
        emptyRecA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m emptyA
        (fun _ => SetTheory.empty)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [emptyA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => empty_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [emptyA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun _ ψ x hx' => not_mem_empty x hx')
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [emptyA]))
        (fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA]))
      have hvalE1 : ∀ ψ' : Name → Nat, m1.val emptyName ψ' =
          SetTheory.empty := fun ψ' => hval1 ψ'
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 emptyRecA
        (fun ψ => emptyRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [emptyRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [emptyRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h6
            cases hr⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => emptyRec_key rfl (fun ψ' => hvalE1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [emptyRecVal]
          rw [hψ uN (by simp [emptyRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_emptyRec_type rfl (fun ψ' => hvalE1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
      exact ⟨m2⟩
  | defnDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    -- semantic facts about the annotated type
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.defnInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => by injection heq with h1 h2; exact ⟨h1.symm, h2.symm⟩)
      rfl
      hres'
  | thmDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    -- the theorem-specific proposition check re-runs inference on the type
    cases hst2 : inferType env 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSort env 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.thmInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => nomatch heq)
      rfl
      hres'

private theorem foldlM_sound {env' : Env} :
    ∀ (ds : List Declaration) (env : Env), Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' → Nonempty (EnvModel V env')
  | [], env, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_sound ds env1 (checkDecl_sound hd m) h

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem checkDecls_sound {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env') : Nonempty (EnvModel V env') :=
  foldlM_sound ds Env.empty ⟨EnvModel.empty V⟩ h

/-- Model-level core of the consistency corollary: a modeled
environment stores no constant of type `Empty`. -/
private theorem no_constant_of_Empty {env : Env} (m : EnvModel V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨T, hTi, hmem⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty] at hTi
  simp only [interpClosed, interpExpr] at hTi
  split at hTi
  · split at hTi
    · obtain rfl := Option.some.inj hTi
      exact m.ind_ok.right.right.right.right.right.right _ _ hmem
    · exact nomatch hTi
  · exact nomatch hTi

/-- A checked `def` or `theorem` stores a constant carrying the
annotated declared type. -/
private theorem checkDecl_stores {env env₁ : Env} {cv : ConstantVal}
    {value : Expr} {d : Declaration}
    (h : checkDecl env d = .ok env₁)
    (hd : d = .defnDecl cv value ∨ d = .thmDecl cv value) :
    ∃ type, annotate env 0 cv.type = .ok type ∧
      ∃ c ∈ env₁.consts, c.toConstantVal = ⟨cv.name, cv.levelParams, type⟩ := by
  rcases hd with rfl | rfl
  · simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩
  · simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    cases hst2 : inferType env 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSort env 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩

/-- If any `def`/`theorem` in the input claims type `Empty`, the fold
rejects: at the step that checks it, the extended environment would
store a constant of type `Empty`, contradicting its model. -/
private theorem foldlM_no_Empty_decl :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' →
      ∀ {cv : ConstantVal} {value : Expr},
        (Declaration.defnDecl cv value ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds) →
        cv.type = .const emptyName [] → False
  | [], _, _, _, _, _, _, hd, _ => by
    rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, cv, value, hd, hty => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨m⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore env checkFuel 0 (.const emptyName []) =
            .ok type := hann
        rw [show checkFuel = 99999 + 1 from rfl] at h1
        simpa [annotateCore, pure, Except.pure] using h1
      obtain ⟨m1⟩ := checkDecl_sound hdd m
      exact no_constant_of_Empty m1 c hc (by rw [hcv])
    · have hd' : Declaration.defnDecl cv value ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds := by
        rcases hd with hd | hd
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inl rfl) hdis
          · exact Or.inl hmem
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inr rfl) hdis
          · exact Or.inr hmem
      exact foldlM_no_Empty_decl ds env1 (checkDecl_sound hdd m) h hd' hty

/-- **Input-level consistency corollary**: the checker never accepts a
declaration list containing a `def` or `theorem` whose stated type is
`Empty` — no reference to the resulting environment needed. -/
theorem no_proof_of_Empty_input (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env')
    {cv : ConstantVal} {value : Expr}
    (hd : Declaration.defnDecl cv value ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_decl ds Env.empty ⟨EnvModel.empty V⟩ h hd hty

/-- **No proof of `Empty` is ever accepted.**  If the checker accepts a
declaration list, then no constant in the resulting environment has
type `Empty`.  The name `Empty` is reserved: input declarations cannot
redefine it, so the only thing it can ever denote is the pinned empty
inductive, modeled by the empty set.  Together with the realizability
of the `SetTheory` interface this is the consistency statement: an
accepted proof of the empty type would exhibit a member of the empty
set. -/
theorem no_proof_of_Empty (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound (V := V) h
  exact no_constant_of_Empty m c hc hty

end Setlec
