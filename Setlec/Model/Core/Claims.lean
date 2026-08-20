import Setlec.Model.NatLit
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLeaves
import Setlec.Model.BasisIota
import Setlec.Model.TeleElim

/-!
# Checker-core soundness: Claims

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- `whnfCore` preserves the local-context assumptions (a leaf-subset
argument). -/
theorem whnf_FvarsOk {cval : ConstVal V} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : whnfCore env fuel d e = .ok e')
    (hok : FvarsOk V cval env φ d ρ e) : FvarsOk V cval env φ d ρ e' :=
  FvarsOk.of_subset (whnf_fvarLeaves henv fuel h) hok

/-- The whnf part of the mutual soundness claims. -/
def WhnfClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ρ : Nat → V},
    whnfCore env fuel d e = .ok e' →
    WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e'

/-- The defeq part of the mutual soundness claims. -/
def DefEqClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {ρ : Nat → V},
    isDefEqCore env fuel d a b = .ok true →
    WScoped d a → WScoped d b →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a → Expr.LeavesBounded b →
    FvarsOk V m.val env φ d ρ a → FvarsOk V m.val env φ d ρ b →
    AnnotOk V m.val env φ d ρ a → AnnotOk V m.val env φ d ρ b →
    ∀ {va vb : V}, interpExpr V m.val env φ d ρ a = some va →
      interpExpr V m.val env φ d ρ b = some vb → va = vb

/-- The inference part of the mutual soundness claims. -/
def InferClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {ρ : Nat → V},
    inferTypeCore env fuel d e = .ok t →
    WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    AnnotOk V m.val env φ d ρ t

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A whnf result of `.sort u` identifies the interpretation with a
universe (the inlined-`ensureSort` pattern of the inference rules). -/
theorem sort_result (hwc : WhnfClaims m φ fuel) {d : Nat} {t : Expr} {u : Level}
    {ρ : Nat → V}
    (h : whnfCore env fuel d t = .ok (.sort u))
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  obtain ⟨hi, -⟩ := hwc h hw hb hLb hok ha
  rw [← hi]
  simp [interpExpr]

/-- If an expression's type's sort evaluates to `0` at the current level
assignment (established by a sort-certification chain), its
interpretation is the proof point. -/
theorem sortCert_pt {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihi : InferClaims m φ fuel)
    {d : Nat} {x tx stx : Expr} {uT : Level} {ρ : Nat → V}
    (hti : inferTypeCore env fuel d x = .ok tx)
    (hsti : inferTypeCore env fuel d tx = .ok stx)
    (hwst : whnfCore env fuel d stx = .ok (.sort uT))
    (hu0 : Level.eval φ uT = 0)
    (hw : WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x)
    (hok : FvarsOk V m.val env φ d ρ x) (ha : AnnotOk V m.val env φ d ρ x) :
    interpExpr V m.val env φ d ρ x = some pt := by
  obtain ⟨⟨vx, vtx, hxi, htxi, hmemx⟩, hAtx⟩ := ihi hti hw hb hLb hok ha
  have hwtx := inferTypeCore_WScoped m.wf fuel hti hw
  have hbtx := inferTypeCore_looseBVars m.wf fuel hti hw hb hLb
  have hLbtx : Expr.LeavesBounded tx := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hti hw l hl)
  have hoktx : FvarsOk V m.val env φ d ρ tx :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hti hw) hok
  obtain ⟨⟨vtx₂, vstx, htxi₂, hstxi, hmemtx⟩, hAstx⟩ := ihi hsti hwtx hbtx hLbtx hoktx hAtx
  have hvtx : vtx₂ = vtx := by
    rw [htxi] at htxi₂
    exact (Option.some.inj htxi₂).symm
  have hwstx := inferTypeCore_WScoped m.wf fuel hsti hwtx
  have hbstx := inferTypeCore_looseBVars m.wf fuel hsti hwtx hbtx hLbtx
  have hLbstx : Expr.LeavesBounded stx := fun l hl =>
    hLbtx l (inferTypeCore_fvarLeaves m.wf fuel hsti hwtx l hl)
  have hokstx : FvarsOk V m.val env φ d ρ stx :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hsti hwtx) hoktx
  obtain ⟨hist, -⟩ := ihw hwst hwstx hbstx hLbstx hokstx hAstx
  have hstx0 : vstx = univ 0 := by
    rw [← hist] at hstxi
    simp only [interpExpr, Option.some.injEq] at hstxi
    rw [← hstxi, hu0]
  have : vtx ∈ˢ univ 0 := by
    rw [← hstx0]
    exact hvtx ▸ hmemtx
  have hpt : vx = pt := mem_univ_zero this hmemx
  rw [hxi, hpt]

/-- A successful proof-irrelevance certification collapses both sides
to the proof point. -/
theorem proofIrrel_pt {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : proofIrrel env (fuel + 1) d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b) :
    interpExpr V m.val env φ d ρ a = some pt ∧
    interpExpr V m.val env φ d ρ b = some pt := by
  obtain ⟨ta, tb, wta0, hta, htb, -, hwta0, hcase⟩ := proofIrrel_inv h
  rcases hcase with ⟨hu, wtb, hwtb, hub⟩ |
    ⟨sta, uT, stb, vT, hsta, hwta, hequ, hstb, hwtb, heqv⟩
  · -- unit branch: every inhabitant of the basis unit type is `pt`
    have unitSide : ∀ (x tx wtx : Expr),
        inferTypeCore env fuel d x = .ok tx →
        whnfCore env fuel d tx = .ok wtx →
        isUnitLikeTy env wtx = true →
        WScoped d x → x.looseBVarsBounded 0 = true → Expr.LeavesBounded x →
        FvarsOk V m.val env φ d ρ x → AnnotOk V m.val env φ d ρ x →
        interpExpr V m.val env φ d ρ x = some pt := by
      intro x tx wtx htx hwtx hux hwx hbx hLbx hokx hax
      obtain ⟨⟨vx, Tx, hxi, hTxi, hmemx⟩, hATx⟩ := ihi htx hwx hbx hLbx hokx hax
      have hwtxW := inferTypeCore_WScoped m.wf fuel htx hwx
      have hbtx := inferTypeCore_looseBVars m.wf fuel htx hwx hbx hLbx
      have hLbtx : Expr.LeavesBounded tx := fun l hl =>
        hLbx l (inferTypeCore_fvarLeaves m.wf fuel htx hwx l hl)
      have hoktx : FvarsOk V m.val env φ d ρ tx :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htx hwx) hokx
      obtain ⟨hiw, -⟩ := ihw hwtx hwtxW hbtx hLbtx hoktx hATx
      obtain ⟨c, us, cvi, capsi, cvr, nP, nM, nm, r, rfl, hfind, hfr, hrf,
        hgres⟩ := isUnitLikeTy_inv hux
      -- identify the unit type through the pinned recursor
      obtain ⟨hpr, -⟩ :=
        m.ind_ok.right.right.right.left _ _ hfr rfl hgres
      have hcn : c = punitName := by
        rcases pinnedInfo_recInfo_cases hpr.symm with hc | hc | hc | hc | hc
        · rw [hc] at hpr
          exact nomatch (congrArg ConstantInfo.recNi hpr)
        · rw [hc] at hpr
          exact nomatch
            (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
        · rw [hc] at hpr
          have h2 : r.nfields = 2 :=
            congrArg (fun ci =>
              ((ConstantInfo.recRules ci).getD 0 default).nfields) hpr
          rw [hrf] at h2
          exact nomatch h2
        · injection hc
        · rw [hc] at hpr
          exact nomatch
            (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
      subst hcn
      obtain ⟨-, hval⟩ :=
        m.ind_ok.right.right.right.left _ _ hfind rfl (by decide)
      rw [hTxi] at hiw
      simp only [interpExpr, hfind] at hiw
      by_cases hlen : us.length =
          (ConstantInfo.indInfo cvi capsi).toConstantVal.levelParams.length
      · rw [if_pos hlen] at hiw
        have hTx : Tx = m.val punitName
            (Level.substFn φ (ConstantInfo.indInfo cvi capsi).toConstantVal.levelParams us) :=
          (Option.some.inj hiw).symm
        rw [hxi]
        have hTx' : Tx = (unitSet : V) := by
          rw [hTx, hval]
          rfl
        have hpt := mem_unitSet (hTx' ▸ hmemx)
        rw [hpt]
      · rw [if_neg hlen] at hiw
        exact nomatch hiw
    exact ⟨unitSide a ta wta0 hta hwta0 hu hwa hba hLba hoka haa,
      unitSide b tb wtb htb hwtb hub hwb hbb hLbb hokb hab⟩
  · -- Prop branch: both sides collapse to the proof point
    have hu0 : Level.eval φ uT = 0 := by
      have := Level.isEquiv_sound hequ φ
      simpa [Level.eval] using this
    have hv0 : Level.eval φ vT = 0 := by
      have := Level.isEquiv_sound heqv φ
      simpa [Level.eval] using this
    exact ⟨sortCert_pt ihw ihi hta hsta hwta hu0 hwa hba hLba hoka haa,
      sortCert_pt ihw ihi htb hstb hwtb hv0 hwb hbb hLbb hokb hab⟩


end Claims

end Setlec
