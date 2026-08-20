import Setlec.Kernel.TypeChecker
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves
import Setlec.Model.BasisIota
import Setlec.Model.TeleElim

/-!
# Soundness of the type checker functions

All statements are relative to a model `m : EnvModel V env` of the current
environment and interpret with `m.val`.  Reduction, definitional equality
and inference are mutually recursive on a shared fuel (the beta rule
certifies possibly-Prop redexes by inference + defeq), so their soundness
is one mutual fuel induction, `check_sound`:

* whnf claims: reduction preserves the interpretation and annotation
  truthfulness (delta via `m.defn_eq`; beta via the substitution lemma,
  `SetTheory.app_lam`, and — for the guarded path — the proof-point
  axioms; the certified path gets `⟦a⟧ ∈ ⟦ty⟧` from the runtime check).
* defeq claims: a positive verdict means the interpretations agree
  whenever both are defined.
* infer claims: a successful inference means expression and type are
  interpreted and `⟦e⟧ ∈ ⟦t⟧`, and the inferred type carries truthful
  annotations.

The `*_sound` wrappers at the end instantiate the fuel.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo}
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
private theorem sort_result (hwc : WhnfClaims m φ fuel) {d : Nat} {t : Expr} {u : Level}
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
private theorem sortCert_pt {m : EnvModel V env} {fuel : Nat}
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
private theorem proofIrrel_pt {m : EnvModel V env} {fuel : Nat}
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
  obtain ⟨ta, wta0, hta, hwta0, hcase⟩ := proofIrrel_inv h
  rcases hcase with ⟨hu, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwta, hequ, htb, hstb, hwtb, heqv⟩
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


/-- A successful pair-eta certification identifies the constructor
application's interpretation with the stuck side's: both are the pair
of the stuck side's components (or the proof point at the Prop
collapse). -/
private theorem pairEta_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : pairEtaCert env (fuel + 1) d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    nPr, nMr, nmr, r, rfl, hfindM, htb, hwtb, hfindI, hfr, hrc, hrf,
    hgres, hlev, hd1, hd2⟩ := pairEtaCert_inv h
  -- identify the structure through the pinned recursor, then the
  -- constructor through the recursor's rule
  obtain ⟨hpr, -⟩ := m.ind_ok.right.right.right.left _ _ hfr rfl hgres
  have hcn' : c' = psigmaName := by
    rcases pinnedInfo_recInfo_cases hpr.symm with hc' | hc' | hc' | hc' | hc'
    · rw [hc'] at hpr
      exact nomatch (congrArg ConstantInfo.recNi hpr)
    · rw [hc'] at hpr
      exact nomatch
        (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
    · injection hc'
    · rw [hc'] at hpr
      have hr : r.nfields = 0 :=
        congrArg (fun ci =>
          ((ConstantInfo.recRules ci).getD 0 default).nfields) hpr
      rw [hrf] at hr
      exact nomatch hr
    · rw [hc'] at hpr
      exact nomatch
        (congrArg (fun ci => (ConstantInfo.recRules ci).length) hpr)
  subst hcn'
  have hcn : c = psigmaMkName := by
    have hr : r.ctor = psigmaMkName :=
      congrArg (fun ci =>
        ((ConstantInfo.recRules ci).getD 0 default).ctor) hpr
    rw [← hrc]
    exact hr
  subst hcn
  -- b's type reduces to the pair type; extract the sigma facts
  obtain ⟨⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ := ihi htb hwb hbb hLbb hokb hab
  have hvbeq : vb' = vb := by
    rw [hvb] at hbi
    exact (Option.some.inj hbi).symm
  rw [hvbeq] at hmemb
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiw, haPi⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hPii : interpExpr V m.val env φ d ρ
      (.app (.app (.const psigmaName us') A) B) = some vtb := by
    rw [hiw]; exact htbi
  try simp only [AnnotOk] at haPi
  obtain ⟨haCA, haB, vf₁, vB, vE₁, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁, hfib₁⟩ := haPi
  try simp only [AnnotOk] at haCA
  obtain ⟨hac, haA, vf₀, vA, vE₀, A₀, B₀, hci, hAi, hpi₀, hvA₀, hfib₀⟩ := haCA
  obtain ⟨hlpI, htyf⟩ := m.ind_ok.1 cvi capsi hfindI
  obtain ⟨ψt, hψt⟩ : ∃ ψt, ψt = Level.substFn φ cvi.levelParams us' := ⟨_, rfl⟩
  have hci' := hci
  rw [interpExpr, hfindI] at hci'
  dsimp only [ConstantInfo.toConstantVal] at hci'
  rw [← hψt] at hci'
  by_cases halI : us'.length = cvi.levelParams.length
  case neg => simp only [halI, if_false] at hci'; exact nomatch hci'
  simp only [halI, if_true] at hci'
  have hvalI : interpExpr V m.val env φ d ρ (.const psigmaName us') =
      some (m.val psigmaName ψt) := by
    rw [interpExpr, hfindI]
    dsimp only [ConstantInfo.toConstantVal]
    rw [← hψt]
    simp only [halI, if_true]
  have hvf₀ : vf₀ = m.val psigmaName ψt := (Option.some.inj hci').symm
  have hfacts := htyf ψt
  have hAmem : vA ∈ˢ univ (ψt uN) := hfacts.dom₀ (hvf₀ ▸ hpi₀) hvA₀
  have hf₁ : vf₁ = app (m.val psigmaName ψt) vA := by
    rw [interpExpr, hvalI, hAi] at hf₁i
    dsimp only at hf₁i
    exact (Option.some.inj hf₁i).symm
  have hBmem : vB ∈ˢ pi (ψt vN + 1) vA (fun _ => univ (ψt vN)) :=
    hfacts.dom₁ hAmem (hf₁ ▸ hpi₁) hvB₁
  have hfold : vtb = sigmaSet (Nat.max (ψt uN) (ψt vN)) vA
      (fun x => app vB x) := by
    rw [interpExpr, hf₁i, hBi] at hPii
    dsimp only at hPii
    have := Option.some.inj hPii
    rw [← this, hf₁, hfacts.fold hAmem hBmem]
  have hvbmem : vb ∈ˢ sigmaSet (Nat.max (ψt uN) (ψt vN)) vA
      (fun x => app vB x) := by
    rw [← hfold]
    exact hmemb
  have hfibB : ∀ x, x ∈ˢ vA → app vB x ∈ˢ univ (ψt vN) := fun x hx =>
    app_mem hBmem hx fun _ _ => univ_mem_univ _
  -- decompose the constructor application's annotations
  simp only [AnnotOk] at haa
  obtain ⟨haa3, has₂, vf₃, vs₂, vE₃, A₃, B₃, hf₃i, hs₂i, hpi₃, hvs₂, hfib₃⟩ := haa
  try simp only [AnnotOk] at haa3
  obtain ⟨haa2, has₁, vf₂, vs₁, vE₂, A₂, B₂, hf₂i, hs₁i, hpi₂, hvs₁, hfib₂⟩ := haa3
  try simp only [AnnotOk] at haa2
  obtain ⟨haa1, hapβ, vf₁m, vpβ, vE₁m, A₁m, B₁m, hf₁mi, hpβi, hpi₁m, hvpβ, hfib₁m⟩ := haa2
  try simp only [AnnotOk] at haa1
  obtain ⟨hacm, hapα, vf₀m, vpα, vE₀m, A₀m, B₀m, hcmi, hpαi, hpi₀m, hvpα, hfib₀m⟩ := haa1
  obtain ⟨hnP2, hnF2, hlpM, hmkfAll⟩ := m.ind_ok.right.left cvm 2 2 hfindM
  obtain ⟨ψk, hψk⟩ : ∃ ψk, ψk = Level.substFn φ cvm.levelParams us := ⟨_, rfl⟩
  have hcmi' := hcmi
  rw [interpExpr, hfindM] at hcmi'
  dsimp only [ConstantInfo.toConstantVal] at hcmi'
  rw [← hψk] at hcmi'
  by_cases halM : us.length = cvm.levelParams.length
  case neg => simp only [halM, if_false] at hcmi'; exact nomatch hcmi'
  simp only [halM, if_true] at hcmi'
  have hvf₀m : vf₀m = m.val psigmaMkName ψk := (Option.some.inj hcmi').symm
  have hmkf := hmkfAll ψk
  have hψeq : ψk = ψt := by
    rw [hψk, hψt, hlpM, hlpI]
    exact Level.substFn_congr (Level.isEquivList_sound hlev φ)
  -- the application chain of values
  have hvf₁m : vf₁m = app (m.val psigmaMkName ψk) vpα := by
    rw [interpExpr, hcmi, hpαi] at hf₁mi
    dsimp only at hf₁mi
    rw [hvf₀m] at hf₁mi
    exact (Option.some.inj hf₁mi).symm
  have hvf₂ : vf₂ = app vf₁m vpβ := by
    rw [interpExpr, hf₁mi, hpβi] at hf₂i
    dsimp only at hf₂i
    exact (Option.some.inj hf₂i).symm
  have hvf₃ : vf₃ = app vf₂ vs₁ := by
    rw [interpExpr, hf₂i, hs₁i] at hf₃i
    dsimp only at hf₃i
    exact (Option.some.inj hf₃i).symm
  have hva' : va = app vf₃ vs₂ := by
    rw [interpExpr, hf₃i, hs₂i] at hva
    dsimp only at hva
    exact (Option.some.inj hva).symm
  have hva'' : va = app (app (app (app (m.val psigmaMkName ψk) vpα) vpβ)
      vs₁) vs₂ := by
    rw [hva', hvf₃, hvf₂, hvf₁m]
  -- the components are the stuck side's projections
  have hproj0i : interpExpr V m.val env φ d ρ (.proj psigmaName 0 b) =
      some (sfst vb) := by
    simp only [interpExpr, hvb]
    rfl
  have hproj1i : interpExpr V m.val env φ d ρ (.proj psigmaName 1 b) =
      some (ssnd vb) := by
    simp only [interpExpr, hvb]
    rfl
  have hwp : ∀ i, WScoped d (Expr.proj psigmaName i b) := fun _ => by
    simp only [WScoped]
    exact hwb
  have hbp : ∀ i, (Expr.proj psigmaName i b).looseBVarsBounded 0 = true := by
    intro i
    simpa [looseBVarsBounded] using hbb
  have hLbp : ∀ i, Expr.LeavesBounded (Expr.proj psigmaName i b) := fun i l hl =>
    hLbb l (by simpa [fvarLeaves] using hl)
  have hokp : ∀ i, FvarsOk V m.val env φ d ρ (Expr.proj psigmaName i b) :=
    fun i => FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hokb
  have hap : ∀ i, i < 2 → AnnotOk V m.val env φ d ρ (Expr.proj psigmaName i b) := by
    intro i hi
    simp only [AnnotOk]
    exact ⟨hab, hi, vb, ψt uN, ψt vN, vA, (fun x => app vB x),
      hvb, hvbmem, hAmem, hfibB⟩
  -- hypothesis sets for the components
  simp only [WScoped] at hwa
  obtain ⟨⟨⟨⟨-, hwpα⟩, hwpβ⟩, hws₁⟩, hws₂⟩ := hwa
  simp only [looseBVarsBounded, Bool.and_eq_true] at hba
  obtain ⟨⟨⟨⟨-, hbpα⟩, hbpβ⟩, hbs₁⟩, hbs₂⟩ := hba
  have hLbs₁ : Expr.LeavesBounded s₁ := fun l hl =>
    hLba l (by simp [fvarLeaves, hl])
  have hLbs₂ : Expr.LeavesBounded s₂ := fun l hl =>
    hLba l (by simp [fvarLeaves, hl])
  have hoks₁ : FvarsOk V m.val env φ d ρ s₁ :=
    FvarsOk.of_subset (fun l hl => by simp [fvarLeaves, hl]) hoka
  have hoks₂ : FvarsOk V m.val env φ d ρ s₂ :=
    FvarsOk.of_subset (fun l hl => by simp [fvarLeaves, hl]) hoka
  have hs₁eq : vs₁ = sfst vb :=
    ihd hd1 hws₁ (hwp 0) hbs₁ (hbp 0) hLbs₁ (hLbp 0) hoks₁ (hokp 0)
      has₁ (hap 0 (by omega)) hs₁i hproj0i
  have hs₂eq : vs₂ = ssnd vb :=
    ihd hd2 hws₂ (hwp 1) hbs₂ (hbp 1) hLbs₂ (hLbp 1) hoks₂ (hokp 1)
      has₂ (hap 1 (by omega)) hs₂i hproj1i
  by_cases hw : Nat.max (ψk uN) (ψk vN) = 0
  · -- Prop collapse: both sides are the proof point
    rw [hva'', hmkf.zero hw vpα vpβ vs₁ vs₂]
    obtain ⟨a', b', -, -, hpt0, -⟩ := mem_sigma_elim hvbmem
    have hw' : Nat.max (ψt uN) (ψt vN) = 0 := hψeq ▸ hw
    rw [hpt0 hw']
  · -- the pair of the stuck side's components
    have hα : vpα ∈ˢ univ (ψk uN) := hmkf.dom₀ hw (hvf₀m ▸ hpi₀m) hvpα
    have hβ : vpβ ∈ˢ pi (ψk vN + 1) vpα (fun _ => univ (ψk vN)) :=
      hmkf.dom₁ hw hα (hvf₁m ▸ hpi₁m) hvpβ
    have hs₁m : vs₁ ∈ˢ vpα :=
      hmkf.dom₂ hw hα hβ ((hvf₂.trans (by rw [hvf₁m])) ▸ hpi₂) hvs₁
    have hs₂m : vs₂ ∈ˢ app vpβ vs₁ :=
      hmkf.dom₃ hw hα hβ hs₁m
        ((hvf₃.trans (by rw [hvf₂, hvf₁m])) ▸ hpi₃) hvs₂
    rw [hva'', hmkf.fold hα hβ hs₁m hs₂m, if_neg hw, hs₁eq, hs₂eq]
    obtain ⟨a', b', -, -, -, hpair⟩ := mem_sigma_elim hvbmem
    have hw' : ¬ Nat.max (ψt uN) (ψt vN) = 0 := by
      rw [← hψeq]
      exact hw
    rw [hpair hw', sfst_spair, ssnd_spair]

/-- Pointwise interpretation of an expression spine. -/
def InterpSpine (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : List Expr → List V → Prop
  | [], [] => True
  | x :: xs, v :: vs =>
    interpExpr V cval env φ d ρ x = some v ∧
    InterpSpine cval env φ d ρ xs vs
  | _, _ => False

theorem InterpSpine.length {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs → vs.length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: vs, h => by
    simp only [List.length_cons]
    exact congrArg (· + 1) (InterpSpine.length h.2)

theorem InterpSpine.append_inv {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {d : Nat} {ρ : Nat → V} :
    ∀ {xs ys : List Expr} {ws : List V},
      InterpSpine cval env φ d ρ (xs ++ ys) ws →
      ∃ vs us, ws = vs ++ us ∧ InterpSpine cval env φ d ρ xs vs ∧
        InterpSpine cval env φ d ρ ys us
  | [], ys, ws, h => ⟨[], ws, rfl, trivial, h⟩
  | x :: xs, ys, [], h => nomatch h
  | x :: xs, ys, w :: ws, h => by
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨vs, us, rfl, h1, h2⟩ := InterpSpine.append_inv hrest
    exact ⟨w :: vs, us, rfl, ⟨hx, h1⟩, h2⟩

theorem InterpSpine.take {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (n : Nat) {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ (xs.take n) (vs.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, InterpSpine.take n h.2⟩

theorem InterpSpine.drop {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (n : Nat) {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ (xs.drop n) (vs.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | n + 1, _ :: _, _ :: _, h => InterpSpine.drop n h.2

theorem InterpSpine.append {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs ys : List Expr} {vs us : List V},
      InterpSpine cval env φ d ρ xs vs → InterpSpine cval env φ d ρ ys us →
      InterpSpine cval env φ d ρ (xs ++ ys) (vs ++ us)
  | [], _, [], _, _, h2 => h2
  | [], _, _ :: _, _, h1, _ => nomatch h1
  | _ :: _, _, [], _, h1, _ => nomatch h1
  | _ :: _, _, _ :: _, _, h1, h2 =>
    ⟨h1.1, InterpSpine.append h1.2 h2⟩

/-- Inversion of an application spine's `AnnotOk`: the head and every
argument are `AnnotOk`, the head interprets, and the argument values
form a typed chain interpreting the whole spine. -/
theorem annotOk_spine_inv {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr), xs ≠ [] →
      AnnotOk V cval env φ d ρ (Expr.mkAppN f xs) →
      AnnotOk V cval env φ d ρ f ∧
      (∀ x ∈ xs, AnnotOk V cval env φ d ρ x) ∧
      ∃ vf vs, interpExpr V cval env φ d ρ f = some vf ∧
        InterpSpine cval env φ d ρ xs vs ∧ ChainSlots V vf vs ∧
        interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
          some (SpineFold V vf vs)
  | [], _, hne, _ => absurd rfl hne
  | [x], f, _, ha => by
    simp only [Expr.mkAppN, AnnotOk] at ha ⊢
    obtain ⟨hf, hx, vf, vx, vE, A, B, hif, hix, hp, hm, hfib⟩ := ha
    refine ⟨hf, by simpa using hx, vf, [vx], hif, ⟨hix, trivial⟩,
      ⟨⟨vE, A, B, hp, hm, hfib⟩, trivial⟩, ?_⟩
    rw [interpExpr, hif, hix]
    rfl
  | x :: y :: xs, f, _, ha => by
    have hstep : Expr.mkAppN f (x :: y :: xs) =
        Expr.mkAppN (Expr.app f x) (y :: xs) := rfl
    rw [hstep] at ha
    obtain ⟨hfx, hrest, vfx, vs, hifx, hisp, hchain, hifold⟩ :=
      annotOk_spine_inv (y :: xs) (Expr.app f x) (by simp) ha
    simp only [AnnotOk] at hfx
    obtain ⟨hf, hx, vf, vx, vE, A, B, hif, hix, hp, hm, hfib⟩ := hfx
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf vx) := by
      rw [interpExpr, hif, hix]
    rw [happ] at hifx
    obtain rfl := Option.some.inj hifx
    refine ⟨hf, ?_, vf, vx :: vs, hif, ⟨hix, hisp⟩,
      ⟨⟨vE, A, B, hp, hm, hfib⟩, hchain⟩, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hrest z hz
    · rw [hstep]
      exact hifold

/-- Interpreting an application spine is folding set application: no
side conditions, the `app` case of the interpretation composes
unconditionally. -/
theorem interp_mkAppN {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr) {vf : V} {vs : List V},
      interpExpr V cval env φ d ρ f = some vf →
      InterpSpine cval env φ d ρ xs vs →
      interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
        some (SpineFold V vf vs)
  | [], f, vf, [], hif, _ => hif
  | [], f, vf, _ :: _, _, hsp => nomatch hsp
  | x :: xs, f, vf, [], _, hsp => nomatch hsp
  | x :: xs, f, vf, v :: vs, hif, hsp => by
    obtain ⟨hix, hsp'⟩ := hsp
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf v) := by
      rw [interpExpr, hif, hix]
    rw [show Expr.mkAppN f (x :: xs) = Expr.mkAppN (Expr.app f x) xs from rfl,
      interp_mkAppN xs (Expr.app f x) happ hsp']
    rfl

/-- Forward construction of an application spine's `AnnotOk` and
interpretation from its parts. -/
theorem annotOk_spine {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr) {vf : V} {vs : List V},
      AnnotOk V cval env φ d ρ f →
      interpExpr V cval env φ d ρ f = some vf →
      (∀ x ∈ xs, AnnotOk V cval env φ d ρ x) →
      InterpSpine cval env φ d ρ xs vs → ChainSlots V vf vs →
      AnnotOk V cval env φ d ρ (Expr.mkAppN f xs) ∧
      interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
        some (SpineFold V vf vs)
  | [], f, vf, [], hf, hif, _, _, _ => ⟨hf, hif⟩
  | [], f, vf, _ :: _, _, _, _, hsp, _ => nomatch hsp
  | x :: xs, f, vf, [], _, _, _, hsp, _ => nomatch hsp
  | x :: xs, f, vf, v :: vs, hf, hif, hxs, hsp, hchain => by
    obtain ⟨hix, hsp'⟩ := hsp
    obtain ⟨hslot, hchain'⟩ := hchain
    obtain ⟨vE, A, B, hp, hm, hfib⟩ := hslot
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf v) := by
      rw [interpExpr, hif, hix]
    have hafx : AnnotOk V cval env φ d ρ (Expr.app f x) := by
      simp only [AnnotOk]
      exact ⟨hf, hxs x List.mem_cons_self, vf, v, vE, A, B, hif, hix,
        hp, hm, hfib⟩
    exact annotOk_spine xs (Expr.app f x) (vf := SetTheory.app vf v)
      (vs := vs) hafx happ
      (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) hsp' hchain'

/-- A list of length `n + 1` splits off its last element at `n`. -/
private theorem take_concat_of_length {α : Type _} :
    ∀ {l : List α} {n : Nat}, l.length = n + 1 →
      ∃ x, l = l.take n ++ [x] ∧ l[n]? = some x
  | [], n, h => nomatch h
  | [x], 0, _ => ⟨x, rfl, rfl⟩
  | x :: y :: l, 0, h => by simp at h
  | x :: y :: l, n + 1, h => by
    obtain ⟨z, hz, hg⟩ := take_concat_of_length
      (l := y :: l) (n := n) (by simpa using h)
    refine ⟨z, ?_, ?_⟩
    · have : x :: y :: l = x :: (y :: l) := rfl
      rw [this, List.take_succ_cons, List.cons_append, ← hz]
    · simpa using hg

/-- Pairwise definitional equality of two interpreted spines yields
pointwise equal values. -/
private theorem defEqList_values {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f) :
    ∀ (fl : Nat), fl ≤ fuelTop → ∀ {d : Nat} {ρ : Nat → V}
      (as bs : List Expr) (vs us : List V),
      defEqList env fl d as bs = .ok true →
      (∀ x ∈ as, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      (∀ x ∈ bs, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      InterpSpine m.val env φ d ρ as vs →
      InterpSpine m.val env φ d ρ bs us →
      vs = us := by
  intro fl hfl d ρ as
  induction as generalizing fl with
  | nil =>
    intro bs vs us h _ _ hs1 hs2
    match fl, bs, h with
    | fl + 1, [], h =>
      match vs, hs1, us, hs2 with
      | [], _, [], _ => rfl
    | fl + 1, _ :: _, h => exact nomatch h
  | cons a as ih =>
    intro bs vs us h ha hb hs1 hs2
    match fl, bs, h with
    | fl + 1, b :: bs, h =>
      obtain ⟨hde, hrest⟩ := defEqList_step_inv h
      match vs, hs1, us, hs2 with
      | v :: vs, ⟨hiv, hs1'⟩, u :: us, ⟨hiu, hs2'⟩ =>
        obtain ⟨haw, hab, haL, haF, haA⟩ := ha a List.mem_cons_self
        obtain ⟨hbw, hbb, hbL, hbF, hbA⟩ := hb b List.mem_cons_self
        have hflle : fl ≤ fuelTop := Nat.le_trans (Nat.le_succ fl) hfl
        have hvu : v = u := (ihAll fl hflle).2.1 hde haw hbw hab hbb
          haL hbL haF hbF haA hbA hiv hiu
        rw [hvu, ih fl hflle bs vs us hrest
          (fun x hx => ha x (List.mem_cons_of_mem _ hx))
          (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hs1' hs2']

/-- The iota certificates build an expression-spine telescope fit:
each certified argument's inferred type is definitionally equal to the
corresponding (progressively instantiated) domain, so its interpreted
value is a member of the interpreted domain. -/
private theorem certs_fit {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f) :
    ∀ (fl : Nat), fl ≤ fuelTop → ∀ {d : Nat} {ρ : Nat → V}
      (ty : Expr) (args : List Expr) (vs : List V) (T : V),
      iotaCerts env fl d ty args = .ok true →
      WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → FvarsOk V m.val env φ d ρ ty →
      AnnotOk V m.val env φ d ρ ty →
      interpExpr V m.val env φ d ρ ty = some T →
      (∀ x ∈ args, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      InterpSpine m.val env φ d ρ args vs →
      ∃ rest, TeleFitI V m.val env φ d ρ ty args vs rest := by
  intro fl hfl d ρ ty args
  induction args generalizing fl ty with
  | nil =>
    intro vs T hc hwty hbty hLty hFty hAty hity hargs hsp
    match vs, hsp with
    | [], _ => exact ⟨ty, TeleFitI.nil⟩
  | cons a as ih =>
    intro vs T hc hwty hbty hLty hFty hAty hity hargs hsp
    match vs, hsp with
    | v :: vs, ⟨hia, hsp'⟩ =>
    match fl, hc with
    | fl + 1, hc =>
    match ty, hc with
    | .bvar _, hc => exact nomatch hc
    | .fvar _ _ _, hc => exact nomatch hc
    | .sort _, hc => exact nomatch hc
    | .const _ _, hc => exact nomatch hc
    | .app _ _, hc => exact nomatch hc
    | .lam _ _ _ _, hc => exact nomatch hc
    | .letE _ _ _ _, hc => exact nomatch hc
    | .lit _, hc => exact nomatch hc
    | .proj _ _ _, hc => exact nomatch hc
    | .forallE n dom body mt, hc =>
    obtain ⟨ta, hta, hde, hrest⟩ := iotaCerts_step_inv hc
    have hflle : fl ≤ fuelTop := Nat.le_trans (Nat.le_succ fl) hfl
    obtain ⟨haw, hab, haL, haF, haA⟩ := hargs a List.mem_cons_self
    -- the domain interprets (the ∀-tower interp forces it)
    simp only [AnnotOk] at hAty
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hAty
    rw [interpExpr, hcod] at hity
    obtain ⟨A, hidom, hpieq⟩ : ∃ A,
        interpExpr V m.val env φ d ρ dom = some A ∧
        T = pi (cod.eval φ) A fun x =>
          (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n dom))).getD SetTheory.empty := by
      revert hity
      cases hd : interpExpr V m.val env φ d ρ dom with
      | none => intro hity; exact nomatch hity
      | some A =>
        intro hity
        dsimp only at hity
        exact ⟨A, rfl, (Option.some.inj hity).symm⟩
    -- the inferred type's value equals the domain's
    obtain ⟨⟨va, tva, hiva, hita, hmemta⟩, hAta⟩ :=
      (ihAll fl hflle).2.2 hta haw hab haL haF haA
    obtain rfl : va = v := by rw [hiva] at hia; exact Option.some.inj hia
    have htaw : WScoped d ta := inferTypeCore_WScoped m.wf fl hta haw
    have htab : ta.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fl hta haw hab haL
    have htaL : Expr.LeavesBounded ta := fun l hl =>
      haL l (inferTypeCore_fvarLeaves m.wf fl hta haw l hl)
    have htaF : FvarsOk V m.val env φ d ρ ta :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fl hta haw) haF
    have hwty' : WScoped d dom ∧ WScoped d body := by
      simpa [WScoped] using hwty
    have hdomw : WScoped d dom := hwty'.1
    have hdomb : dom.looseBVarsBounded 0 = true := by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbty
      exact hbty.1
    have hdomL : Expr.LeavesBounded dom := fun l hl =>
      hLty l (by simp [Expr.fvarLeaves, hl])
    have hdomF : FvarsOk V m.val env φ d ρ dom :=
      FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hFty
    have hveq : tva = A := (ihAll fl hflle).2.1 hde htaw hdomw htab hdomb
      htaL hdomL htaF hdomF hAta hAdom hita hidom
    have hvA : va ∈ˢ A := hveq ▸ hmemta
    -- the instantiated body interprets and stays truthful
    obtain ⟨hbodyA, hwfact⟩ := hcond va A hidom hvA
    obtain ⟨w, hwi, -⟩ := hwfact cod hcod
    have hfb : Expr.fvarsBelow d body := hwty'.2.fvarsBelow
    have hibody : interpExpr V m.val env φ d ρ (body.instantiate1 a) =
        some w := by
      rw [interp_beta (n := n) (ty := dom) hfb haw hab hia 0]
      exact hwi
    have hAbody : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
      AnnotOk_beta hfb haw hab hia haA 0 hbodyA
    have hwbody : WScoped d (body.instantiate1 a) :=
      WScoped.instantiate1_gen haw 0 hwty'.2
    have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true := by
      refine looseBVarsBounded_instantiate1_gen hab ?_
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbty
      exact hbty.2
    have hLbody : Expr.LeavesBounded (body.instantiate1 a) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hLty l (by simp [Expr.fvarLeaves, hl'])
      · exact haL l hl'
    have hFbody : FvarsOk V m.val env φ d ρ (body.instantiate1 a) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hFty l (by simp [Expr.fvarLeaves, hl'])
      · exact haF l hl'
    obtain ⟨rest, hfit⟩ := ih fl hflle (body.instantiate1 a) vs w hrest
      hwbody hbbody hLbody hFbody hAbody hibody
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hsp'
    exact ⟨rest, TeleFitI.cons hidom hia hvA hfb haw hab haA hfit⟩

set_option maxHeartbeats 6400000 in
/-- A successful structural eta certification (in its `With` form,
against a separately derived weak-head-normal type of the stuck side)
identifies the constructor application's interpretation with the stuck
side's: the stored eta law reconstructs the member through the
projection models, and the value bridges identify the public
constants' values with the models'. -/
private theorem structEtaWith_sound {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {fuel : Nat} (hfle : fuel ≤ fuelTop)
    {fl2 : Nat} (hfl2 : fl2 ≤ fuelTop)
    {d : Nat} {a b tb wtb : Expr} {ρ : Nat → V} {va vb : V}
    (h : structEtaCertWith env (fuel + 1) d a b wtb = .ok true)
    (htb : inferTypeCore env fl2 d b = .ok tb)
    (hwtb : whnfCore env fl2 d tb = .ok wtb)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨ihw, ihd, ihi⟩ := ihAll fuel hfle
  obtain ⟨ihw2, ihd2, ihi2⟩ := ihAll fl2 hfl2
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
    hfn, hfc, hal, hwfn, hfT, hce, hcc, hcp, hcf, hres,
    hresC, htal, hulen, hclps, hTstrip, hlev, hic, hpc, hd1, hd2⟩ :=
    structEtaCertWith_inv h
  -- level assignments
  obtain ⟨ψ', hψ'⟩ : ∃ x, x = Level.substFn φ cvT.levelParams us' :=
    ⟨_, rfl⟩
  have hψc : Level.substFn φ cvc.levelParams us = ψ' := by
    rw [hψ', hclps]
    exact Level.substFn_congr (Level.isEquivList_sound hlev φ)
  -- b's type reduces to the structure type; extract the spine facts
  obtain ⟨⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ :=
    ihi2 htb hwb hbb hLbb hokb hab
  obtain rfl : vb = vb' := by
    rw [hvb] at hbi
    exact Option.some.inj hbi
  have hwtbW := inferTypeCore_WScoped m.wf fl2 htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fl2 htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fl2 htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fl2 htb hwb) hokb
  obtain ⟨hiw, hAwtb⟩ := ihw2 hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hvtbI : interpExpr V m.val env φ d ρ wtb = some vtb := by
    rw [hiw]
    exact htbi
  have hwtbW' := whnf_WScoped m.wf fl2 hwtb hwtbW
  have hbwtb := whnf_looseBVars m.wf fl2 hwtb hbtb
  have hLwtb : Expr.LeavesBounded wtb := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fl2 hwtb l hl)
  have hokwtb : FvarsOk V m.val env φ d ρ wtb :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fl2 hwtb) hoktb
  -- the head's interpretation
  have hvalT : interpExpr V m.val env φ d ρ (.const T us') =
      some (m.val T ψ') := by
    simp only [interpExpr, hfT]
    rw [if_pos (show us'.length =
      (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hulen)]
    rw [hψ']
    rfl
  have hwtb_eq : Expr.mkAppN (.const T us') wtb.getAppArgs = wtb := by
    rw [← hwfn]
    exact Expr.mkAppN_getApp wtb
  have hAwtb' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const T us') wtb.getAppArgs) := by
    rw [hwtb_eq]
    exact hAwtb
  -- the type-argument spine and the type's value fold
  obtain ⟨psv, hspT, hAtargs, hvtb⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ wtb.getAppArgs psv ∧
      (∀ x ∈ wtb.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      vtb = SpineFold V (m.val T ψ') psv := by
    cases hcase : wtb.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hwtbc : wtb = .const T us' := by
          rw [← Expr.mkAppN_getApp wtb, hwfn, hcase]
          rfl
        rw [hwtbc, hvalT] at hvtbI
        exact (Option.some.inj hvtbI).symm
    | cons t ts =>
      rw [← hcase]
      have hne : wtb.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hne hAwtb'
      obtain rfl : m.val T ψ' = vf := by
        rw [hvalT] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [hwtb_eq] at hfold
      rw [hfold] at hvtbI
      exact (Option.some.inj hvtbI).symm
  have hpslen : psv.length = wtb.getAppArgs.length :=
    InterpSpine.length hspT
  -- fit the type arguments through the type former's telescope
  obtain ⟨hTtf, -, -, hTtb, -, -⟩ := m.wf _ (find?_mem hfT)
  have hThf : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hTtf
  have hTw : WScoped d (cvT.type.instantiateLevelParams cvT.levelParams
      us') := WScoped.of_not_hasFvar hThf
  have hTb : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hTtb
  have hTA : AnnotOk V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    exact AnnotOk.closed_invariant hThf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TT, hTT⟩ : ∃ TT, interpExpr V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TT := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hThf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have htargswf : ∀ x ∈ wtb.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwtbW'.getAppArgs x hx, looseBVarsBounded_getAppArgs hbwtb x hx,
      ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact hLwtb l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hokwtb
  obtain ⟨restT, hfitIT⟩ := certs_fit ihAll fuel hfle _ _ _ TT hic hTw hTb
    (Expr.LeavesBounded.of_not_hasFvar hThf)
    (FvarsOk.of_not_hasFvar hThf) hTA hTT htargswf hspT
  obtain ⟨dT, ρT, restT', hfitT⟩ := TeleFitI.toTeleFit hfitIT hTw (by
    rw [htal]
    exact stripPis_instantiateLevelParams_isSome _ _ _ hTstrip)
  -- the stored eta law
  obtain ⟨hmsC, hmsP, hlaw⟩ := m.modeled_ok.2.2.2.1 T cvT caps hfT hce hres
  have hmemb' : vb ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [hvtb] at hmemb
    exact hmemb
  have hvbEq := hlaw φ us' psv vb d ρ dT ρT restT'
    (by rw [hpslen, htal, hcp]) hmemb' hfitT
  rw [hcf] at hvbEq
  -- the constructor application's spine
  have ha_eq : Expr.mkAppN (.const c us) a.getAppArgs = a := by
    rw [← hfn]
    exact Expr.mkAppN_getApp a
  have haa' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) a.getAppArgs) := by
    rw [ha_eq]
    exact haa
  have huslen : us.length = cvc.levelParams.length := by
    rw [hclps, ← hulen]
    exact Level.isEquivList_length hlev
  have hvalC : interpExpr V m.val env φ d ρ (.const c us) =
      some (m.val c ψ') := by
    simp only [interpExpr, hfc]
    rw [if_pos (show us.length =
      (ConstantInfo.ctorInfo cvc cnP cnF).toConstantVal.levelParams.length
      from huslen)]
    rw [show (ConstantInfo.ctorInfo cvc cnP cnF).toConstantVal.levelParams
      = cvc.levelParams from rfl, hψc]
  obtain ⟨avs, hspA, haargsA, hva'⟩ : ∃ avs,
      InterpSpine m.val env φ d ρ a.getAppArgs avs ∧
      (∀ x ∈ a.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      va = SpineFold V (m.val c ψ') avs := by
    cases hcase : a.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hac : a = .const c us := by
          rw [← Expr.mkAppN_getApp a, hfn, hcase]
          rfl
        rw [hac, hvalC] at hva
        exact (Option.some.inj hva).symm
    | cons t ts =>
      rw [← hcase]
      have hane : a.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hane haa'
      obtain rfl : m.val c ψ' = vf := by
        rw [hvalC] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [ha_eq] at hfold
      rw [hfold] at hva
      exact (Option.some.inj hva).symm
  have haargswf : ∀ x ∈ a.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwa.getAppArgs x hx, looseBVarsBounded_getAppArgs hba x hx,
      ?_, ?_, haargsA x hx⟩
    · intro l hl
      exact hLba l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hoka
  -- the parameter prefix matches the type's arguments
  have hpref : avs.take cnP = psv := by
    refine defEqList_values ihAll fuel hfle _ _ _ _ hd1 ?_ htargswf
      (InterpSpine.take cnP hspA) hspT
    intro x hx
    exact haargswf x (List.mem_of_mem_take hx)
  -- the projection certificates at the decremented fuel
  have hpcFacts : ∀ i, i < cnF → ∃ (fl : Nat) (cvp : ConstantVal)
      (nPp nMp nmp nip : Nat) (rulesp : List RecRule),
      fl ≤ fuel ∧
      env.find? (projFnName T i) =
        some (.recInfo cvp nPp nMp nmp nip rulesp) ∧
      cvp.levelParams = cvT.levelParams ∧
      (cvp.type.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
      iotaCerts env fl d
        (cvp.type.instantiateLevelParams cvp.levelParams us')
        (wtb.getAppArgs ++ [b]) = .ok true := by
    intro i hi
    match fuel, hpc with
    | 0, hpc => exact nomatch hpc
    | fuel' + 1, hpc =>
      obtain ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp, hfl, hfpj, hplps,
        hpstrip, hicj⟩ := structEtaProjCerts_inv (List.range cnF) fuel'
        hpc i (List.mem_range.mpr hi)
      exact ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp,
        Nat.le_trans hfl (Nat.le_succ _), hfpj, hplps, hpstrip, hicj⟩
  -- each projection application's chain facts
  have hprojFacts : ∀ j, j < cnF →
      AnnotOk V m.val env φ d ρ
        (Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b])) ∧
      interpExpr V m.val env φ d ρ
        (Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b])) =
      some (SpineFold V (m.val (projFnName T j) ψ') (psv ++ [vb])) := by
    intro j hj
    obtain ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp, hfl, hfpj, hplps,
      hpstrip, hicj⟩ := hpcFacts j hj
    have hpname : cvp.name = projFnName T j := by
      have h1 := List.find?_some hfpj
      exact eq_of_beq h1
    have hplen : us'.length = cvp.levelParams.length := by
      rw [hplps]
      exact hulen
    have hψp : Level.substFn φ cvp.levelParams us' = ψ' := by
      rw [hplps, hψ']
    have hvalP : interpExpr V m.val env φ d ρ
        (.const (projFnName T j) us') =
        some (m.val (projFnName T j) ψ') := by
      simp only [interpExpr, hfpj]
      rw [if_pos (show us'.length =
        (ConstantInfo.recInfo cvp nPp nMp nmp nip
          rulesp).toConstantVal.levelParams.length from hplen)]
      rw [show (ConstantInfo.recInfo cvp nPp nMp nmp nip
        rulesp).toConstantVal.levelParams = cvp.levelParams from rfl, hψp]
    -- the projection function's type facts
    obtain ⟨hPtf, -, -, hPtb, -, -⟩ := m.wf _ (find?_mem hfpj)
    have hPhf : (cvp.type.instantiateLevelParams cvp.levelParams
        us').hasFvar = false := by
      rw [hasFvar_instantiateLevelParams]
      exact hPtf
    have hPw : WScoped d (cvp.type.instantiateLevelParams cvp.levelParams
        us') := WScoped.of_not_hasFvar hPhf
    have hPb : (cvp.type.instantiateLevelParams cvp.levelParams
        us').looseBVarsBounded 0 = true := by
      rw [looseBVarsBounded_instantiateLevelParams]
      exact hPtb
    have hPA : AnnotOk V m.val env φ d ρ
        (cvp.type.instantiateLevelParams cvp.levelParams us') := by
      obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfpj)
        (Level.substFn φ cvp.levelParams us')
      exact AnnotOk.closed_invariant hPhf d ρ
        (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
    obtain ⟨PT, hPT, hPmem⟩ : ∃ PT, interpExpr V m.val env φ d ρ
        (cvp.type.instantiateLevelParams cvp.levelParams us') = some PT ∧
        m.val (projFnName T j) (Level.substFn φ cvp.levelParams us')
          ∈ˢ PT := by
      obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfpj)
        (Level.substFn φ cvp.levelParams us')
      refine ⟨T0, ?_, ?_⟩
      · rw [interp_closed_invariant hPhf d ρ]
        unfold interpClosed
        rw [interp_instLevels m.val_params]
        exact hT0
      · rw [← hpname]
        exact hTm
    have hargs5 : ∀ x ∈ wtb.getAppArgs ++ [b],
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact htargswf x hx
      · obtain rfl : x = b := by simpa using hx
        exact ⟨hwb, hbb, hLbb, hokb, hab⟩
    have hspPB : InterpSpine m.val env φ d ρ (wtb.getAppArgs ++ [b])
        (psv ++ [vb]) :=
      InterpSpine.append hspT ⟨hvb, trivial⟩
    obtain ⟨restP, hfitIP⟩ := certs_fit ihAll fl
      (Nat.le_trans hfl hfle) _ _ _ PT hicj hPw hPb
      (Expr.LeavesBounded.of_not_hasFvar hPhf)
      (FvarsOk.of_not_hasFvar hPhf) hPA hPT hargs5 hspPB
    obtain ⟨dP, ρP, restP', hfitP⟩ := TeleFitI.toTeleFit hfitIP hPw (by
      rw [show (wtb.getAppArgs ++ [b]).length = wtb.getAppArgs.length + 1
        from by simp]
      exact stripPis_instantiateLevelParams_isSome _ _ _ hpstrip)
    have hψpmem : m.val (projFnName T j) ψ' ∈ˢ PT := by
      rw [← hψp]
      exact hPmem
    have hch := TeleFit.chainSlots hfitP hPA hPT hψpmem
    have hconstA : AnnotOk V m.val env φ d ρ
        (.const (projFnName T j) us') := by
      simp [AnnotOk]
    obtain ⟨hA1, hI1⟩ := annotOk_spine (wtb.getAppArgs ++ [b])
      (.const (projFnName T j) us') hconstA hvalP
      (fun x hx => (hargs5 x hx).2.2.2.2) hspPB hch
    exact ⟨hA1, hI1⟩
  -- the field values are the projections'
  have hprojSpine : InterpSpine m.val env φ d ρ
      ((List.range cnF).map fun i =>
        Expr.mkAppN (.const (projFnName T i) us')
          (wtb.getAppArgs ++ [b]))
      ((List.range cnF).map fun i =>
        SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb])) := by
    have hgen : ∀ (l : List Nat), (∀ i ∈ l, i < cnF) →
        InterpSpine m.val env φ d ρ
          (l.map fun i => Expr.mkAppN (.const (projFnName T i) us')
            (wtb.getAppArgs ++ [b]))
          (l.map fun i =>
            SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb])) := by
      intro l
      induction l with
      | nil => intro _; exact trivial
      | cons i l ih =>
        intro hl
        exact ⟨(hprojFacts i (hl i List.mem_cons_self)).2,
          ih (fun i' hi' => hl i' (List.mem_cons_of_mem _ hi'))⟩
    exact hgen (List.range cnF) (fun i hi => List.mem_range.mp hi)
  have hflds : avs.drop cnP = (List.range cnF).map fun i =>
      SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb]) := by
    refine defEqList_values ihAll fuel hfle _ _ _ _ hd2 ?_ ?_
      (InterpSpine.drop cnP hspA) hprojSpine
    · intro x hx
      exact haargswf x (List.mem_of_mem_drop hx)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hif := hprojFacts i (List.mem_range.mp hi)
      refine ⟨?_, ?_, ?_, ?_, hif.1⟩
      · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwtbW'.getAppArgs x hx
        · obtain rfl : x = b := by simpa using hx
          exact hwb
      · refine looseBVarsBounded_mkAppN (by rfl) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact looseBVarsBounded_getAppArgs hbwtb x hx
        · obtain rfl : x = b := by simpa using hx
          exact hbb
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact hLwtb l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = b := by simpa using hx
            exact hLbb l hlx
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact hokwtb l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = b := by simpa using hx
            exact hokb l hlx
  -- assembly through the value bridges
  obtain ⟨-, hveqC⟩ := m.modeled_ok.2.1 c cvc cnP cnF hfc hresC
  have hvalPM : ∀ i, i < cnF →
      m.val (projFnName T i) ψ' = m.val (projModelName T i) ψ' := by
    intro i hi
    obtain ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp, -, hfpj, -, -, -⟩ :=
      hpcFacts i hi
    obtain ⟨-, hveqP⟩ := m.modeled_ok.2.2.1 T i _ hfpj
    exact hveqP ψ'
  have hfldsM : ((List.range cnF).map fun i =>
      SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb])) =
      ((List.range cnF).map fun i =>
      SpineFold V (m.val (projModelName T i) ψ') (psv ++ [vb])) := by
    refine List.map_congr_left ?_
    intro i hi
    rw [hvalPM i (List.mem_range.mp hi)]
  rw [hcc] at hvbEq
  rw [hva', ← List.take_append_drop cnP avs, hpref, hflds, hfldsM,
    hveqC ψ']
  rw [hψ']
  exact hvbEq.symm

/-- A successful structural eta certification (whole-certificate form,
deriving the stuck side's type itself). -/
private theorem structEta_sound {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {fuel : Nat} (hfle : fuel ≤ fuelTop)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : structEtaCert env (fuel + 1) d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨tb, wtb, htb, hwtb, hW⟩ := structEtaCert_inv h
  match fuel, hfle, htb, hwtb, hW with
  | fuel' + 1, hfle, htb, hwtb, hW =>
    exact structEtaWith_sound ihAll
      (Nat.le_trans (Nat.le_succ fuel') hfle) hfle hW htb hwtb
      hwa hwb hba hbb hLba hLbb hoka hokb haa hab hva hvb

set_option maxHeartbeats 3200000 in
/-- A successful unit-likeness certification identifies the two
interpretations: both values inhabit the same interpreted unit-like
family, whose stored law makes any two members equal. -/
private theorem structUnit_sound {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {fuel : Nat} (hfle : fuel ≤ fuelTop)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : structUnitCert env (fuel + 1) d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨ihw, ihd, ihi⟩ := ihAll fuel hfle
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hwfn, hfT,
    hcu, hres, htal, hulen, hTstrip, htb, hwtb, hde, hic⟩ :=
    structUnitCert_inv h
  obtain ⟨ψ', hψ'⟩ : ∃ x, x = Level.substFn φ cvT.levelParams us' :=
    ⟨_, rfl⟩
  -- a's type facts
  obtain ⟨⟨va', vta, hai, htai, hmema⟩, hAta⟩ :=
    ihi hta hwa hba hLba hoka haa
  obtain rfl : va = va' := by
    rw [hva] at hai
    exact Option.some.inj hai
  have hwtaW := inferTypeCore_WScoped m.wf fuel hta hwa
  have hbta := inferTypeCore_looseBVars m.wf fuel hta hwa hba hLba
  have hLbta : Expr.LeavesBounded ta := fun l hl =>
    hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hwa l hl)
  have hokta : FvarsOk V m.val env φ d ρ ta :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hwa) hoka
  obtain ⟨hiwa, hAwta⟩ := ihw hwta hwtaW hbta hLbta hokta hAta
  have hvtaI : interpExpr V m.val env φ d ρ wta = some vta := by
    rw [hiwa]
    exact htai
  have hwtaW' := whnf_WScoped m.wf fuel hwta hwtaW
  have hbwta := whnf_looseBVars m.wf fuel hwta hbta
  have hLwta : Expr.LeavesBounded wta := fun l hl =>
    hLbta l (whnf_fvarLeaves m.wf fuel hwta l hl)
  have hokwta : FvarsOk V m.val env φ d ρ wta :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel hwta) hokta
  -- b's type facts
  obtain ⟨⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ :=
    ihi htb hwb hbb hLbb hokb hab
  obtain rfl : vb = vb' := by
    rw [hvb] at hbi
    exact Option.some.inj hbi
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiwb, hAwtb⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hvtbI : interpExpr V m.val env φ d ρ wtb = some vtb := by
    rw [hiwb]
    exact htbi
  have hwtbW' := whnf_WScoped m.wf fuel hwtb hwtbW
  have hbwtb := whnf_looseBVars m.wf fuel hwtb hbtb
  have hLwtb : Expr.LeavesBounded wtb := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hokwtb : FvarsOk V m.val env φ d ρ wtb :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hoktb
  -- the two types interpret equally
  have htyeq : vta = vtb :=
    ihd hde hwtaW' hwtbW' hbwta hbwtb hLwta hLwtb hokwta hokwtb
      hAwta hAwtb hvtaI hvtbI
  -- decompose the family application
  have hvalT : interpExpr V m.val env φ d ρ (.const T us') =
      some (m.val T ψ') := by
    simp only [interpExpr, hfT]
    rw [if_pos (show us'.length =
      (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hulen)]
    rw [hψ']
    rfl
  have hwta_eq : Expr.mkAppN (.const T us') wta.getAppArgs = wta := by
    rw [← hwfn]
    exact Expr.mkAppN_getApp wta
  have hAwta' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const T us') wta.getAppArgs) := by
    rw [hwta_eq]
    exact hAwta
  obtain ⟨psv, hspT, hAtargs, hvta⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ wta.getAppArgs psv ∧
      (∀ x ∈ wta.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      vta = SpineFold V (m.val T ψ') psv := by
    cases hcase : wta.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hwtac : wta = .const T us' := by
          rw [← Expr.mkAppN_getApp wta, hwfn, hcase]
          rfl
        rw [hwtac, hvalT] at hvtaI
        exact (Option.some.inj hvtaI).symm
    | cons t ts =>
      rw [← hcase]
      have hne : wta.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hne hAwta'
      obtain rfl : m.val T ψ' = vf := by
        rw [hvalT] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [hwta_eq] at hfold
      rw [hfold] at hvtaI
      exact (Option.some.inj hvtaI).symm
  have hpslen : psv.length = wta.getAppArgs.length :=
    InterpSpine.length hspT
  -- fit the type arguments through the family's telescope
  obtain ⟨hTtf, -, -, hTtb, -, -⟩ := m.wf _ (find?_mem hfT)
  have hThf : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hTtf
  have hTw : WScoped d (cvT.type.instantiateLevelParams cvT.levelParams
      us') := WScoped.of_not_hasFvar hThf
  have hTb : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hTtb
  have hTA : AnnotOk V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    exact AnnotOk.closed_invariant hThf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TT, hTT⟩ : ∃ TT, interpExpr V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TT := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hThf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have htargswf : ∀ x ∈ wta.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwtaW'.getAppArgs x hx,
      looseBVarsBounded_getAppArgs hbwta x hx, ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact hLwta l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hokwta
  obtain ⟨restT, hfitIT⟩ := certs_fit ihAll fuel hfle _ _ _ TT hic hTw
    hTb (Expr.LeavesBounded.of_not_hasFvar hThf)
    (FvarsOk.of_not_hasFvar hThf) hTA hTT htargswf hspT
  obtain ⟨dT, ρT, restT', hfitT⟩ := TeleFitI.toTeleFit hfitIT hTw (by
    rw [htal]
    exact stripPis_instantiateLevelParams_isSome _ _ _ hTstrip)
  -- the stored unit law
  have hlaw := m.modeled_ok.2.2.2.2 T cvT caps hfT hcu hres
  have hmema' : va ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [hvta] at hmema
    exact hmema
  have hmemb' : vb ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [← htyeq, hvta] at hmemb
    exact hmemb
  exact hlaw φ us' psv va vb d ρ dT ρT restT'
    (by rw [hpslen, htal]) hmema' hmemb' hfitT

/-- Soundness of the stuck-term fallback: pair eta in either direction,
else proof irrelevance. -/
private theorem stuckIrrel_sound {m : EnvModel V env} {fuel : Nat}
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : stuckIrrel env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  cases fuel with
  | zero => exact nomatch h
  | succ f =>
  simp only [stuckIrrel, Bind.bind, Except.bind] at h
  cases hp1 : pairEtaCert env f d a b with
  | error e => rw [hp1] at h; exact nomatch h
  | ok r₁ =>
  rw [hp1] at h
  dsimp only at h
  cases r₁ with
  | true =>
    cases f with
    | zero => exact nomatch hp1
    | succ f' =>
    obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
    exact pairEta_sound ihwL ihdL ihiL hp1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hp2 : pairEtaCert env f d b a with
  | error e => rw [hp2] at h; exact nomatch h
  | ok r₂ =>
  rw [hp2] at h
  dsimp only at h
  cases r₂ with
  | true =>
    cases f with
    | zero => exact nomatch hp2
    | succ f' =>
    obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
    exact (pairEta_sound ihwL ihdL ihiL hp2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs1 : structEtaCert env f d a b with
  | error e => rw [hs1] at h; exact nomatch h
  | ok r₃ =>
  rw [hs1] at h
  dsimp only at h
  cases r₃ with
  | true =>
    cases f with
    | zero => exact nomatch hs1
    | succ f' =>
    exact structEta_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hs1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs2 : structEtaCert env f d b a with
  | error e => rw [hs2] at h; exact nomatch h
  | ok r₄ =>
  rw [hs2] at h
  dsimp only at h
  cases r₄ with
  | true =>
    cases f with
    | zero => exact nomatch hs2
    | succ f' =>
    exact (structEta_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hs2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hu1 : structUnitCert env f d a b with
  | error e => rw [hu1] at h; exact nomatch h
  | ok r₅ =>
  rw [hu1] at h
  dsimp only at h
  cases r₅ with
  | true =>
    cases f with
    | zero => exact nomatch hu1
    | succ f' =>
    exact structUnit_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hu1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases f with
  | zero => exact nomatch h
  | succ f' =>
  obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
  obtain ⟨hpa, hpb⟩ := proofIrrel_pt ihwL ihiL h hwa hwb hba hbb
    hLba hLbb hoka hokb haa hab
  rw [hva] at hpa
  rw [hvb] at hpb
  exact (Option.some.inj hpa).trans (Option.some.inj hpb).symm

/-- A successful eta certification identifies the λ's interpretation
with the stuck side's (`SetTheory.lam_eta`). -/
private theorem etaCert_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {n₁ : Name} {ty₁ body₁ b : Expr} {m₁ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (hec : etaCert env (fuel + 1) d n₁ ty₁ body₁ m₁ b = .ok true)
    (hwa : WScoped d (Expr.lam n₁ ty₁ body₁ m₁)) (hwb : WScoped d b)
    (hba : (Expr.lam n₁ ty₁ body₁ m₁).looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded (Expr.lam n₁ ty₁ body₁ m₁))
    (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁) = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨tb, n₂, ty₂, fb, m₂, v₁, v₂, htb, hwtb, hm₁, hm₂, hlev, hdty, hdbody⟩ :=
    etaCert_inv hec
  -- λ-side components
  simp only [WScoped] at hwa
  obtain ⟨hwty₁, hwbody₁⟩ := hwa
  simp only [looseBVarsBounded, Bool.and_eq_true] at hba
  obtain ⟨hbty₁, hbbody₁⟩ := hba
  have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba l (by simp [fvarLeaves, hl])
  obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_lam hoka
  simp only [AnnotOk] at haa
  obtain ⟨haty₁, ⟨v₁', hv₁'⟩, hconds⟩ := haa
  -- b's inferred type
  obtain ⟨⟨vb', Tb, hvb', hTbi, hmemb⟩, hATb⟩ := ihi htb hwb hbb hLbb hokb hab
  have hvbeq : vb' = vb := by
    rw [hvb] at hvb'
    exact (Option.some.inj hvb').symm
  rw [hvbeq] at hmemb
  -- transport through whnf of the type
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiwtb, hAwtb⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hATb
  have hwWS := whnf_WScoped m.wf fuel hwtb hwtbW
  have hwB := whnf_looseBVars m.wf fuel hwtb hbtb
  have hwLb : Expr.LeavesBounded (Expr.forallE n₂ ty₂ fb m₂) := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hwOk : FvarsOk V m.val env φ d ρ (Expr.forallE n₂ ty₂ fb m₂) :=
    whnf_FvarsOk m.wf fuel hwtb hoktb
  simp only [WScoped] at hwWS
  obtain ⟨hwty₂, hwfb⟩ := hwWS
  simp only [looseBVarsBounded, Bool.and_eq_true] at hwB
  obtain ⟨hbty₂, hbfb⟩ := hwB
  have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hwLb l (by simp [fvarLeaves, hl])
  obtain ⟨hokty₂, hokfb⟩ := FvarsOk.of_forallE hwOk
  simp only [AnnotOk] at hAwtb
  obtain ⟨haty₂, ⟨v₂', hv₂'⟩, hcondf⟩ := hAwtb
  -- the whnf'd type interprets to `Tb`
  have hTfi : interpExpr V m.val env φ d ρ (Expr.forallE n₂ ty₂ fb m₂) = some Tb := by
    rw [hiwtb, hTbi]
  simp only [interpExpr, hm₂] at hTfi
  cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
  | none => rw [hA2] at hTfi; exact nomatch hTfi
  | some A₂ =>
  rw [hA2] at hTfi
  dsimp only at hTfi
  simp only [Option.some.injEq] at hTfi
  -- λ interp
  simp only [interpExpr, hm₁] at hva
  cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
  | none => rw [hA1] at hva; exact nomatch hva
  | some A₁ =>
  rw [hA1] at hva
  dsimp only at hva
  simp only [Option.some.injEq] at hva
  -- domain agreement
  have hAeq : A₂ = A₁ :=
    ihd hdty hwty₂ hwty₁ hbty₂ hbty₁ hLbty₂ hLbty₁ hokty₂ hokty₁ haty₂ haty₁ hA2 hA1
  subst hAeq
  -- membership of `b`'s value in the pi over the λ's domain
  have hmem' : vb ∈ˢ pi (Level.eval φ v₂) A₂ (fun x =>
      (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (fb.instantiate1 (.fvar d n₂ ty₂))).getD SetTheory.empty) := by
    rw [hTfi]
    exact hmemb
  -- pointwise: the λ's body is `b` applied
  have hpoint : ∀ x, x ∈ˢ A₂ →
      ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body₁.instantiate1 (.fvar d n₁ ty₁))).getD SetTheory.empty) =
      SetTheory.app vb x := by
    intro x hx
    obtain ⟨habody₁, hwfact₁⟩ := hconds x A₂ hA1 hx
    obtain ⟨w₁, B₁, hw₁, -, -⟩ := hwfact₁ v₁' hv₁'
    have happI : interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) = some (SetTheory.app vb x) := by
      simp only [interpExpr]
      rw [interp_weaken_top hwb, hvb]
      simp [updV]
    have hwapp : WScoped (d + 1) (Expr.app b (.fvar d n₁ ty₁)) := by
      simp only [WScoped]
      exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwty₁⟩
    have hbapp : (Expr.app b (.fvar d n₁ ty₁)).looseBVarsBounded 0 = true := by
      simp [looseBVarsBounded, hbb, hbty₁]
    have hLbapp : Expr.LeavesBounded (Expr.app b (.fvar d n₁ ty₁)) := by
      intro l hl
      simp only [fvarLeaves, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | hl
      · exact hLbb l hl
      · exact hbty₁
      · exact hLbty₁ l hl
    have hokapp : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) := by
      have h0 : (Expr.app b (Expr.bvar 0)).instantiate1 (.fvar d n₁ ty₁) 0 =
          Expr.app b (.fvar d n₁ ty₁) := by
        simp [Expr.instantiate1, instantiate1_eq_self hbb]
      rw [← h0]
      exact FvarsOk.instantiate1 hwty₁ hokty₁ haty₁ hA1 hx
        (Expr.app b (Expr.bvar 0)) 0 (by simp only [WScoped]; exact ⟨hwb, trivial⟩)
        (fun l hl => hokb l (by simpa [fvarLeaves] using hl))
    have haapp : AnnotOk V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) := by
      simp only [AnnotOk]
      refine ⟨AnnotOk.weaken_top hwb hab, trivial, vb, x,
        Level.eval φ v₂, A₂,
        (fun y => (interpExpr V m.val env φ (d + 1) (updV V ρ d y)
          (fb.instantiate1 (.fvar d n₂ ty₂))).getD SetTheory.empty),
        ?_, ?_, hmem', hx, ?_⟩
      · rw [interp_weaken_top hwb]
        exact hvb
      · simp [interpExpr, updV]
      · intro y hy
        obtain ⟨-, hwf⟩ := hcondf y A₂ hA2 hy
        obtain ⟨w, hwi, hwu⟩ := hwf v₂' hv₂'
        dsimp only
        rw [hwi]
        have hv₂eq : v₂' = v₂ := by
          rw [hm₂] at hv₂'
          exact (Option.some.inj hv₂').symm
        rw [← hv₂eq]
        simpa using hwu
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbty₁
        · exact hLbty₁ l hl'
    have heq := ihd hdbody
      (hwty₁.instantiate1 0 hwbody₁) hwapp
      (looseBVarsBounded_instantiate1 body₁ 0 hbbody₁) hbapp
      hLbo₁ hLbapp
      (FvarsOk.instantiate1 hwty₁ hokty₁ haty₁ hA1 hx body₁ 0 hwbody₁ hokbody₁)
      hokapp habody₁ haapp hw₁ happI
    rw [hw₁]
    simpa using heq
  -- assemble via congruence and eta
  rw [← hva]
  have hstep : SetTheory.lam (Level.eval φ v₁) A₂
      (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body₁.instantiate1 (.fvar d n₁ ty₁))).getD SetTheory.empty) =
      SetTheory.lam (Level.eval φ v₁) A₂ (fun x => SetTheory.app vb x) :=
    lam_congr (fun x hx => hpoint x hx)
  rw [hstep]
  have hveq : Level.eval φ v₁ = Level.eval φ v₂ := Level.isEquiv_sound hlev φ
  rw [hveq]
  exact lam_eta hmem'

/-- Soundness of the one-sided-λ branch of `isDefEqCore` (λ on the
left): eta, else proof irrelevance. -/
private theorem etaBranch_sound {m : EnvModel V env} {fuel : Nat}
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {d : Nat} {n₁ : Name} {ty₁ body₁ b : Expr} {m₁ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (h : (do
      if ← etaCert env fuel d n₁ ty₁ body₁ m₁ b then pure true
      else stuckIrrel env fuel d (Expr.lam n₁ ty₁ body₁ m₁) b :
        CheckM Bool) = .ok true)
    (hwa : WScoped d (Expr.lam n₁ ty₁ body₁ m₁)) (hwb : WScoped d b)
    (hba : (Expr.lam n₁ ty₁ body₁ m₁).looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded (Expr.lam n₁ ty₁ body₁ m₁))
    (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁) = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  simp only [Bind.bind, Except.bind] at h
  cases hec : etaCert env fuel d n₁ ty₁ body₁ m₁ b with
  | error e => rw [hec] at h; exact nomatch h
  | ok r =>
  rw [hec] at h
  dsimp only at h
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact stuckIrrel_sound ihAll h hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | true =>
  cases fuel with
  | zero => exact nomatch hec
  | succ f =>
  obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f (Nat.le_succ f)
  exact etaCert_sound ihwL ihdL ihiL hec hwa hwb hba hbb hLba hLbb
    hoka hokb haa hab hva hvb

/-- Soundness of the one-sided-λ branch of `isDefEqCore` (λ on the
right). -/
private theorem etaBranch_sound' {m : EnvModel V env} {fuel : Nat}
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {d : Nat} {n₂ : Name} {ty₂ body₂ a : Expr} {m₂ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (h : (do
      if ← etaCert env fuel d n₂ ty₂ body₂ m₂ a then pure true
      else stuckIrrel env fuel d a (Expr.lam n₂ ty₂ body₂ m₂) :
        CheckM Bool) = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d (Expr.lam n₂ ty₂ body₂ m₂))
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : (Expr.lam n₂ ty₂ body₂ m₂).looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a)
    (hLbb : Expr.LeavesBounded (Expr.lam n₂ ty₂ body₂ m₂))
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂))
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂))
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂) = some vb) :
    va = vb := by
  simp only [Bind.bind, Except.bind] at h
  cases hec : etaCert env fuel d n₂ ty₂ body₂ m₂ a with
  | error e => rw [hec] at h; exact nomatch h
  | ok r =>
  rw [hec] at h
  dsimp only at h
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact stuckIrrel_sound ihAll h hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | true =>
  cases fuel with
  | zero => exact nomatch hec
  | succ f =>
  obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f (Nat.le_succ f)
  exact (etaCert_sound ihwL ihdL ihiL hec hwb hwa hbb hba hLbb hLba
    hokb hoka hab haa hvb hva).symm

set_option maxHeartbeats 6400000 in
/-- Claims for the stuck-major rescue's result: the substituted major
interprets to the same value as the stuck one (identity trivially; the
K fabrication by proof irrelevance — both are proofs of propositions;
the eta fabrication by the structure-eta law), and it satisfies the
full claims package the iota continuation threads.  The fabricated
constructor application's own claims are assembled from the iota
certificates the reduction then runs on it (`certs_fit` +
`annotOk_spine`); its arguments' claims come from the reduced type's
spine and, for eta, the projection certificates. -/
private theorem majorToCtor_claims {m : EnvModel V env} {fuelTop : Nat}
    (ihAll : ∀ f, f ≤ fuelTop →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {fuel : Nat} (hfle : fuel ≤ fuelTop)
    {d : Nat} {recName cj : Name} {rules : List RecRule}
    {major₀ major : Expr} {ρ : Nat → V} {usj : List Level}
    {cvj : ConstantVal} {cnP cnF : Nat}
    (hsub : majorToCtor env fuel d recName rules major₀ = .ok major)
    (hmfn : major.getAppFn = .const cj usj)
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hml1 : major.getAppArgs.length = cnP + cnF)
    (har2 : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hmcerts : iotaCerts env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs = .ok true)
    (hw : WScoped d major₀) (hb : major₀.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded major₀)
    (hok : FvarsOk V m.val env φ d ρ major₀)
    (hA : AnnotOk V m.val env φ d ρ major₀) :
    interpExpr V m.val env φ d ρ major =
      interpExpr V m.val env φ d ρ major₀ ∧
    AnnotOk V m.val env φ d ρ major ∧ WScoped d major ∧
    major.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded major ∧
    FvarsOk V m.val env φ d ρ major := by
  match fuel, hfle, hsub, hmcerts with
  | fuelS + 1, hfle, hsub, hmcerts =>
  have hfuelle : fuelS ≤ fuelTop := Nat.le_trans (Nat.le_succ fuelS) hfle
  obtain ⟨ihw, ihd, ihi⟩ := ihAll fuelS hfuelle
  rcases majorToCtor_inv hsub with rfl | ⟨hwsc, hbM, hall, r, cvj', cnP',
    cnF', tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrs, hfj', hpr', hfT,
    hti, htw, hth, hcase⟩
  · exact ⟨rfl, hA, hw, hb, hLb, hok⟩
  -- fabrication: scoping from the guard
  have hwM : WScoped d major := WScoped.of_wscopedB hwsc
  have hsubL : ∀ l ∈ major.fvarLeaves, l ∈ major₀.fvarLeaves := by
    intro l hl
    have := List.all_eq_true.mp hall l hl
    simpa using this
  have hLbM : Expr.LeavesBounded major := fun l hl => hLb l (hsubL l hl)
  have hokM : FvarsOk V m.val env φ d ρ major := FvarsOk.of_subset hsubL hok
  -- the stuck major's type chain
  obtain ⟨⟨vM, TM, hMi, hTMi, hmemM⟩, hAtm₀⟩ := ihi hti hw hb hLb hok hA
  have htm0w := inferTypeCore_WScoped m.wf fuelS hti hw
  have htm0b := inferTypeCore_looseBVars m.wf fuelS hti hw hb hLb
  have htm0L : Expr.LeavesBounded tmaj₀ := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuelS hti hw l hl)
  have htm0F : FvarsOk V m.val env φ d ρ tmaj₀ :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuelS hti hw) hok
  obtain ⟨htieq, hAtm⟩ := ihw htw htm0w htm0b htm0L htm0F hAtm₀
  have htmw : WScoped d tmaj := whnf_WScoped m.wf fuelS htw htm0w
  have htmb : tmaj.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuelS htw htm0b
  have htmL : Expr.LeavesBounded tmaj := fun l hl =>
    htm0L l (whnf_fvarLeaves m.wf fuelS htw l hl)
  have htmF : FvarsOk V m.val env φ d ρ tmaj :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuelS htw) htm0F
  have htmaj_eq : Expr.mkAppN (.const T ust) tmaj.getAppArgs = tmaj := by
    rw [← hth]
    exact Expr.mkAppN_getApp tmaj
  -- the type's argument spine
  obtain ⟨psv, hspT, hAtargs⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ tmaj.getAppArgs psv ∧
      ∀ x ∈ tmaj.getAppArgs, AnnotOk V m.val env φ d ρ x := by
    cases hcaseT : tmaj.getAppArgs with
    | nil => exact ⟨[], trivial, fun x hx => absurd hx List.not_mem_nil⟩
    | cons t ts =>
      rw [← hcaseT]
      have hne : tmaj.getAppArgs ≠ [] := by rw [hcaseT]; simp
      have hAtm' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const T ust) tmaj.getAppArgs) := by
        rw [htmaj_eq]
        exact hAtm
      obtain ⟨-, hAargs, vf, vs, -, hsp, -, -⟩ :=
        annotOk_spine_inv _ _ hne hAtm'
      exact ⟨vs, hsp, hAargs⟩
  have htargswf : ∀ x ∈ tmaj.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨htmw.getAppArgs x hx, looseBVarsBounded_getAppArgs htmb x hx,
      ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact htmL l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        htmF
  -- the constructor's telescope facts
  have hcjname : cvj.name = cj := by
    have := find?_name hfj
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
  obtain ⟨hCtf, -, -, hCtb, -, -⟩ := m.wf _ (find?_mem hfj)
  have hChf : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hCtf
  have hCw : WScoped d (cvj.type.instantiateLevelParams cvj.levelParams
      usj) := WScoped.of_not_hasFvar hChf
  have hCb : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hCtb
  have hCA : AnnotOk V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    exact AnnotOk.closed_invariant hChf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TC, hCT, hCmem⟩ : ∃ TC, interpExpr V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC ∧
      m.val cj (Level.substFn φ cvj.levelParams usj) ∈ˢ TC := by
    obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    refine ⟨T0, ?_, ?_⟩
    · rw [interp_closed_invariant hChf d ρ]
      unfold interpClosed
      rw [interp_instLevels m.val_params]
      exact hT0
    · rw [← hcjname]
      exact hTm
  have hmspine : Expr.mkAppN (.const cj usj) major.getAppArgs = major := by
    rw [← hmfn]
    exact Expr.mkAppN_getApp major
  have hconstA : AnnotOk V m.val env φ d ρ (.const cj usj) := by
    simp [AnnotOk]
  -- branch on the fabrication kind
  rcases hcase with ⟨hKrule, hcnF0, hlvlK, hfabeq, hpi⟩ |
    ⟨hEeta, hEctor, hEproj, hplenE, hlvlE, hfabeq, hse⟩
  · -- ── K: the fabricated `refl`-like application ──
    have heqc : cj = r.ctor ∧ usj = ust := by
      have hgfn := congrArg Expr.getAppFn hfabeq
      rw [Expr.getAppFn_mkAppN, hmfn] at hgfn
      exact ⟨(Expr.const.inj hgfn).1, (Expr.const.inj hgfn).2⟩
    rw [← heqc.1, ← heqc.2] at hfabeq
    rw [← heqc.1] at hfj'
    obtain ⟨heqv, heqp, heqf⟩ : cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
      rw [hfj'] at hfj
      injection hfj with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    rw [heqp] at hfabeq
    rw [heqv] at hlvlK
    have hmargs : major.getAppArgs = tmaj.getAppArgs.take cnP := by
      have hgargs := congrArg Expr.getAppArgs hfabeq
      rw [Expr.getAppArgs_mkAppN] at hgargs
      simpa [Expr.getAppArgs] using hgargs
    have hlenj : usj.length = cvj.levelParams.length := by
      rw [heqc.2]
      exact hlvlK.symm
    have hvalC : interpExpr V m.val env φ d ρ (.const cj usj) =
        some (m.val cj (Level.substFn φ cvj.levelParams usj)) := by
      simp only [interpExpr, hfj]
      rw [if_pos (show usj.length =
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
        from hlenj)]
      rfl
    have hmargswf : ∀ x ∈ major.getAppArgs,
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      rw [hmargs]
      intro x hx
      exact htargswf x (List.mem_of_mem_take hx)
    have hspM : InterpSpine m.val env φ d ρ major.getAppArgs
        (psv.take cnP) := by
      rw [hmargs]
      exact InterpSpine.take cnP hspT
    obtain ⟨restC, hfitIC⟩ := certs_fit ihAll (fuelS + 1) hfle _ _ _ TC
      hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
      (FvarsOk.of_not_hasFvar hChf) hCA hCT hmargswf hspM
    obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC hCw (by
      rw [hml1]
      exact stripPis_instantiateLevelParams_isSome _ _ _ har2)
    have hch := TeleFit.chainSlots hfitC hCA hCT hCmem
    obtain ⟨hAfab, hIfab⟩ := annotOk_spine major.getAppArgs
      (.const cj usj) hconstA hvalC
      (fun x hx => (hmargswf x hx).2.2.2.2) hspM hch
    rw [hmspine] at hAfab hIfab
    -- proof irrelevance identifies the values
    cases fuelS with
    | zero => exact nomatch hpi
    | succ fuelS' =>
    obtain ⟨ihw', ihd', ihi'⟩ := ihAll fuelS'
      (Nat.le_trans (Nat.le_succ fuelS')
        (Nat.le_trans (Nat.le_succ (fuelS' + 1)) hfle))
    obtain ⟨hptM, hptM0⟩ := proofIrrel_pt ihw' ihi' hpi hwM hw hbM hb
      hLbM hLb hokM hok hAfab hA
    exact ⟨by rw [hptM, hptM0], hAfab, hwM, hbM, hLbM, hokM⟩
  · -- ── eta: the fabricated constructor of the projections ──
    have heqc : cj = caps.etaCtor ∧ usj = ust := by
      have hgfn := congrArg Expr.getAppFn hfabeq
      rw [Expr.getAppFn_mkAppN, hmfn] at hgfn
      exact ⟨(Expr.const.inj hgfn).1, (Expr.const.inj hgfn).2⟩
    rw [← heqc.1, ← heqc.2] at hfabeq
    rw [← heqc.2] at hth
    cases fuelS with
    | zero => exact nomatch hse
    | succ fuelS' =>
    have hfleS : fuelS' + 1 ≤ fuelTop :=
      Nat.le_trans (Nat.le_succ (fuelS' + 1)) hfle
    have hfleS' : fuelS' ≤ fuelTop := Nat.le_trans (Nat.le_succ fuelS') hfleS
    obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, us'2, cvT2, caps2,
      hfn2, hfc2, hal2, hwfn2, hfT2, hce2, hcc2, hcp2, hcf2, hres2,
      hresC2, htal2, hulen2, hclps2, hTstrip2, hlev2, hic2, hpc2,
      hd1, hd2⟩ := structEtaCertWith_inv hse
    -- identify the certificate's constants with the continuation's
    obtain ⟨rfl, rfl⟩ : cj = c2 ∧ usj = us2 := by
      rw [hmfn] at hfn2
      exact ⟨(Expr.const.inj hfn2).1, (Expr.const.inj hfn2).2⟩
    obtain ⟨rfl, rfl⟩ : T = T2 ∧ usj = us'2 := by
      rw [hth] at hwfn2
      exact ⟨(Expr.const.inj hwfn2).1, (Expr.const.inj hwfn2).2⟩
    obtain ⟨rfl, rfl⟩ : cvT = cvT2 ∧ caps = caps2 := by
      rw [hfT] at hfT2
      injection hfT2 with h1
      injection h1 with h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨rfl, rfl, rfl⟩ : cvj = cvc2 ∧ cnP = cnP2 ∧ cnF = cnF2 := by
      rw [hfj] at hfc2
      injection hfc2 with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hlenj : usj.length = cvj.levelParams.length := by
      rw [hclps2]
      exact hulen2
    have hvalC : interpExpr V m.val env φ d ρ (.const cj usj) =
        some (m.val cj (Level.substFn φ cvj.levelParams usj)) := by
      simp only [interpExpr, hfj]
      rw [if_pos (show usj.length =
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
        from hlenj)]
      rfl
    -- the projection certificates at their fuel
    have hpcFacts : ∀ i, i < cnF → ∃ (fl : Nat) (cvp : ConstantVal)
        (nPp nMp nmp nip : Nat) (rulesp : List RecRule),
        fl ≤ fuelS' ∧
        env.find? (projFnName T i) =
          some (.recInfo cvp nPp nMp nmp nip rulesp) ∧
        cvp.levelParams = cvT.levelParams ∧
        (cvp.type.stripPis (tmaj.getAppArgs.length + 1)).isSome = true ∧
        iotaCerts env fl d
          (cvp.type.instantiateLevelParams cvp.levelParams usj)
          (tmaj.getAppArgs ++ [major₀]) = .ok true := by
      intro i hi
      match fuelS', hpc2 with
      | 0, hpc2 => exact nomatch hpc2
      | flp + 1, hpc2 =>
        obtain ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp, hfl, hfpj, hplps,
          hpstrip, hicj⟩ := structEtaProjCerts_inv (List.range cnF) flp
          hpc2 i (List.mem_range.mpr hi)
        exact ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp,
          Nat.le_trans hfl (Nat.le_succ _), hfpj, hplps, hpstrip, hicj⟩
    -- each projection application's claims
    have hprojFacts : ∀ j, j < cnF →
        AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const (projFnName T j) usj)
            (tmaj.getAppArgs ++ [major₀])) ∧
        interpExpr V m.val env φ d ρ
          (Expr.mkAppN (.const (projFnName T j) usj)
            (tmaj.getAppArgs ++ [major₀])) =
        some (SpineFold V (m.val (projFnName T j)
          (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      intro j hj
      obtain ⟨fl, cvp, nPp, nMp, nmp, nip, rulesp, hfl, hfpj, hplps,
        hpstrip, hicj⟩ := hpcFacts j hj
      have hpname : cvp.name = projFnName T j := by
        have h1 := find?_name hfpj
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h1
      have hplen : usj.length = cvp.levelParams.length := by
        rw [hplps]
        exact hulen2
      have hψp : Level.substFn φ cvp.levelParams usj =
          Level.substFn φ cvT.levelParams usj := by
        rw [hplps]
      have hvalP : interpExpr V m.val env φ d ρ
          (.const (projFnName T j) usj) =
          some (m.val (projFnName T j)
            (Level.substFn φ cvT.levelParams usj)) := by
        simp only [interpExpr, hfpj]
        rw [if_pos (show usj.length =
          (ConstantInfo.recInfo cvp nPp nMp nmp nip
            rulesp).toConstantVal.levelParams.length from hplen)]
        rw [show (ConstantInfo.recInfo cvp nPp nMp nmp nip
          rulesp).toConstantVal.levelParams = cvp.levelParams from rfl, hψp]
      obtain ⟨hPtf, -, -, hPtb, -, -⟩ := m.wf _ (find?_mem hfpj)
      have hPhf : (cvp.type.instantiateLevelParams cvp.levelParams
          usj).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact hPtf
      have hPw : WScoped d (cvp.type.instantiateLevelParams
          cvp.levelParams usj) := WScoped.of_not_hasFvar hPhf
      have hPb : (cvp.type.instantiateLevelParams cvp.levelParams
          usj).looseBVarsBounded 0 = true := by
        rw [looseBVarsBounded_instantiateLevelParams]
        exact hPtb
      have hPA : AnnotOk V m.val env φ d ρ
          (cvp.type.instantiateLevelParams cvp.levelParams usj) := by
        obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfpj)
          (Level.substFn φ cvp.levelParams usj)
        exact AnnotOk.closed_invariant hPhf d ρ
          (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
      obtain ⟨PT, hPT, hPmem⟩ : ∃ PT, interpExpr V m.val env φ d ρ
          (cvp.type.instantiateLevelParams cvp.levelParams usj) =
            some PT ∧
          m.val (projFnName T j) (Level.substFn φ cvp.levelParams usj)
            ∈ˢ PT := by
        obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfpj)
          (Level.substFn φ cvp.levelParams usj)
        refine ⟨T0, ?_, ?_⟩
        · rw [interp_closed_invariant hPhf d ρ]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          exact hT0
        · rw [← hpname]
          exact hTm
      have hargs5 : ∀ x ∈ tmaj.getAppArgs ++ [major₀],
          WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
          AnnotOk V m.val env φ d ρ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact htargswf x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact ⟨hw, hb, hLb, hok, hA⟩
      have hspPB : InterpSpine m.val env φ d ρ
          (tmaj.getAppArgs ++ [major₀]) (psv ++ [vM]) :=
        InterpSpine.append hspT ⟨hMi, trivial⟩
      obtain ⟨restP, hfitIP⟩ := certs_fit ihAll fl
        (Nat.le_trans hfl hfleS') _ _ _ PT hicj hPw hPb
        (Expr.LeavesBounded.of_not_hasFvar hPhf)
        (FvarsOk.of_not_hasFvar hPhf) hPA hPT hargs5 hspPB
      obtain ⟨dP, ρP, restP', hfitP⟩ := TeleFitI.toTeleFit hfitIP hPw (by
        rw [show (tmaj.getAppArgs ++ [major₀]).length =
          tmaj.getAppArgs.length + 1 from by simp]
        exact stripPis_instantiateLevelParams_isSome _ _ _ hpstrip)
      have hψpmem : m.val (projFnName T j)
          (Level.substFn φ cvT.levelParams usj) ∈ˢ PT := by
        rw [← hψp]
        exact hPmem
      have hch := TeleFit.chainSlots hfitP hPA hPT hψpmem
      have hconstP : AnnotOk V m.val env φ d ρ
          (.const (projFnName T j) usj) := by
        simp [AnnotOk]
      exact annotOk_spine (tmaj.getAppArgs ++ [major₀])
        (.const (projFnName T j) usj) hconstP hvalP
        (fun x hx => (hargs5 x hx).2.2.2.2) hspPB hch
    -- the fabricated spine and its values
    have hmargs : major.getAppArgs = tmaj.getAppArgs ++
        (List.range cnF).map (fun i => Expr.mkAppN
          (.const (projFnName T i) usj)
          (tmaj.getAppArgs ++ [major₀])) := by
      have hgargs := congrArg Expr.getAppArgs hfabeq
      rw [Expr.getAppArgs_mkAppN] at hgargs
      rw [hcf2] at hgargs
      simpa [Expr.getAppArgs] using hgargs
    have hprojSpine : InterpSpine m.val env φ d ρ
        ((List.range cnF).map fun i =>
          Expr.mkAppN (.const (projFnName T i) usj)
            (tmaj.getAppArgs ++ [major₀]))
        ((List.range cnF).map fun i =>
          SpineFold V (m.val (projFnName T i)
            (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      have hgen : ∀ (l : List Nat), (∀ i ∈ l, i < cnF) →
          InterpSpine m.val env φ d ρ
            (l.map fun i => Expr.mkAppN (.const (projFnName T i) usj)
              (tmaj.getAppArgs ++ [major₀]))
            (l.map fun i =>
              SpineFold V (m.val (projFnName T i)
                (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
        intro l
        induction l with
        | nil => intro _; exact trivial
        | cons i l ih =>
          intro hl
          exact ⟨(hprojFacts i (hl i List.mem_cons_self)).2,
            ih (fun i' hi' => hl i' (List.mem_cons_of_mem _ hi'))⟩
      exact hgen (List.range cnF) (fun i hi => List.mem_range.mp hi)
    have hprojwf : ∀ x ∈ (List.range cnF).map (fun i => Expr.mkAppN
        (.const (projFnName T i) usj) (tmaj.getAppArgs ++ [major₀])),
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hif := hprojFacts i (List.mem_range.mp hi)
      refine ⟨?_, ?_, ?_, ?_, hif.1⟩
      · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact htmw.getAppArgs x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact hw
      · refine looseBVarsBounded_mkAppN (by rfl) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact looseBVarsBounded_getAppArgs htmb x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact hb
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact htmL l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = major₀ := by simpa using hx
            exact hLb l hlx
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact htmF l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = major₀ := by simpa using hx
            exact hok l hlx
    have hmargswf : ∀ x ∈ major.getAppArgs,
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      rw [hmargs]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact htargswf x hx
      · exact hprojwf x hx
    have hspM : InterpSpine m.val env φ d ρ major.getAppArgs
        (psv ++ (List.range cnF).map fun i =>
          SpineFold V (m.val (projFnName T i)
            (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      rw [hmargs]
      exact InterpSpine.append hspT hprojSpine
    obtain ⟨restC, hfitIC⟩ := certs_fit ihAll (fuelS' + 1 + 1) hfle _ _ _
      TC hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
      (FvarsOk.of_not_hasFvar hChf) hCA hCT hmargswf hspM
    obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC hCw (by
      rw [hml1]
      exact stripPis_instantiateLevelParams_isSome _ _ _ har2)
    have hch := TeleFit.chainSlots hfitC hCA hCT hCmem
    obtain ⟨hAfab, hIfab⟩ := annotOk_spine major.getAppArgs
      (.const cj usj) hconstA hvalC
      (fun x hx => (hmargswf x hx).2.2.2.2) hspM hch
    rw [hmspine] at hAfab hIfab
    -- the eta law identifies the values
    have hveq := structEtaWith_sound ihAll hfleS' hfleS hse hti htw
      hwM hw hbM hb hLbM hLb hokM hok hAfab hA hIfab hMi
    exact ⟨by rw [hIfab, hMi, hveq], hAfab, hwM, hbM, hLbM, hokM⟩

/-- Soundness of one iota step: the reduct's interpretation matches the
original application spine's, its annotations are truthful, and it stays
well-scoped — everything the whnf recursion needs to continue.  Fully
generic: the fold facts come from the environment model's `rec_rules`,
never from identifying the recursor by name. -/
private theorem iota_sound {m : EnvModel V env} {fuel : Nat}
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {d : Nat} {fe ae e'' : Expr} {ρ : Nat → V}
    (hio : iotaRec env fuel d (.app fe ae) = .ok (some e''))
    (hw : WScoped d (Expr.app fe ae))
    (hb : (Expr.app fe ae).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (Expr.app fe ae))
    (hok : FvarsOk V m.val env φ d ρ (Expr.app fe ae))
    (ha : AnnotOk V m.val env φ d ρ (Expr.app fe ae)) :
    (interpExpr V m.val env φ d ρ e'' =
      interpExpr V m.val env φ d ρ (Expr.app fe ae) ∧
     AnnotOk V m.val env φ d ρ e'') ∧
    WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded e'' ∧ FvarsOk V m.val env φ d ρ e'' := by
  match fuel, ihAll, hio with
  | 0, ihAll, hio => exact nomatch hio
  | fuel + 1, ihAll, hio =>
  obtain ⟨c, us, cv, nP, nM, nm, ni, rules, major₀, major, cj, usj, cvj,
    cnP, cnF, r, hfn, hfc, hlen, hmaj, hsub, hmfn, hfj, hrule, hml1, hml2,
    har1, har2, hlev, hpeq, hcerts, hmcerts, heout⟩ :=
    iotaRec_inv hio
  obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll fuel (Nat.le_succ fuel)
  obtain rfl : cj = r.ctor :=
    (eq_of_beq (by simpa using List.find?_some hrule)).symm
  -- generic well-scopedness of the reduct
  have hargsW : ∀ x ∈ (Expr.app fe ae).getAppArgs, WScoped d x :=
    fun x hx => hw.getAppArgs x hx
  have hargsB : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      x.looseBVarsBounded 0 = true :=
    fun x hx => looseBVarsBounded_getAppArgs hb x hx
  have hargsL : ∀ x ∈ (Expr.app fe ae).getAppArgs, Expr.LeavesBounded x :=
    fun x hx l hl => hLb l (fvarLeaves_getAppArgs hx l hl)
  have hargsO : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      FvarsOk V m.val env φ d ρ x :=
    fun x hx => FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
      hok
  have hmajarg := getD_mem (l := (Expr.app fe ae).getAppArgs)
    (i := nP + nM + nm + ni) (dflt := Expr.bvar 0) (by omega)
  have hmaj0W : WScoped d major₀ := whnf_WScoped m.wf fuel hmaj
    (hargsW _ hmajarg)
  have hmaj0B : major₀.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hmaj (hargsB _ hmajarg)
  have hmaj0Lsub := whnf_fvarLeaves m.wf fuel hmaj
  have hmaj0L : Expr.LeavesBounded major₀ :=
    fun l hl => hargsL _ hmajarg l (hmaj0Lsub l hl)
  have hmaj0O : FvarsOk V m.val env φ d ρ major₀ :=
    FvarsOk.of_subset hmaj0Lsub (hargsO _ hmajarg)
  -- the stuck major's claims, then the substituted major's
  have hspine0 : Expr.app fe ae =
      Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs) := by
    have := (Expr.mkAppN_getApp (Expr.app fe ae)).symm
    rw [hfn] at this
    exact this
  have hane0 : (Expr.app fe ae).getAppArgs ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  have ha0' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs)) :=
    hspine0 ▸ ha
  obtain ⟨-, hxsA0, -⟩ := annotOk_spine_inv _ _ hane0 ha0'
  obtain ⟨hmieq0, hmA0⟩ := ihwL hmaj (hargsW _ hmajarg) (hargsB _ hmajarg)
    (hargsL _ hmajarg) (hargsO _ hmajarg) (hxsA0 _ hmajarg)
  obtain ⟨hmieqS, hmA, hmajW, hmajB, hmajL, hmajO⟩ :=
    majorToCtor_claims ihAll (Nat.le_succ fuel) hsub hmfn hfj hml1 har2
      hmcerts hmaj0W hmaj0B hmaj0L hmaj0O hmA0
  obtain ⟨-, -, -, -, -, hrules⟩ := m.wf _ (find?_mem hfc)
  obtain ⟨hrf, hrlp, hrres, hrlb⟩ := hrules cv nP nM nm ni rules rfl r
    (List.mem_of_find?_eq_some hrule)
  have hclInst : (r.rhs.instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]; exact hrf
  have hrhsW : WScoped d (r.rhs.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar hclInst
  have hallW : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), WScoped d x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsW _ (List.mem_of_mem_take hx)
    · exact hmajW.getAppArgs _ (List.mem_of_mem_drop hx)
  have hallB : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsB _ (List.mem_of_mem_take hx)
    · exact looseBVarsBounded_getAppArgs hmajB _ (List.mem_of_mem_drop hx)
  have hallL : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), Expr.LeavesBounded x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsL _ (List.mem_of_mem_take hx)
    · exact fun l hl => hmajL l
        (fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hl)
  have hallO : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), FvarsOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsO _ (List.mem_of_mem_take hx)
    · exact FvarsOk.of_subset
        (fun l hl => fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hl)
        hmajO
  have hscoped : WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e'' ∧ FvarsOk V m.val env φ d ρ e'' := by
    subst heout
    refine ⟨Expr.WScoped.mkAppN hrhsW hallW,
      looseBVarsBounded_mkAppN
        (by rw [looseBVarsBounded_instantiateLevelParams]; exact hrlb)
        hallB, ?_, ?_⟩
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar hclInst] at hl'
        cases hl'
      · exact hallL x hx l hlx
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar hclInst] at hl'
        cases hl'
      · exact hallO x hx l hlx
  refine ⟨?_, hscoped⟩
  -- the spine's annotation chain
  have hspine : Expr.app fe ae =
      Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs) := by
    have := (Expr.mkAppN_getApp (Expr.app fe ae)).symm
    rw [hfn] at this
    exact this
  have hane : (Expr.app fe ae).getAppArgs ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  have ha' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs)) :=
    hspine ▸ ha
  obtain ⟨-, hxsA, vf0, vs, hif0, hisp, hchain, hifold⟩ :=
    annotOk_spine_inv _ _ hane ha'
  -- head value
  simp only [interpExpr, hfc] at hif0
  split at hif0
  case isFalse => exact nomatch hif0
  obtain hv0 := (Option.some.inj hif0)
  -- split off the major argument
  obtain ⟨xl, hxeq, hxg⟩ := take_concat_of_length
    (l := (Expr.app fe ae).getAppArgs) (n := nP + nM + nm + ni) hlen
  have hxlmem : xl ∈ (Expr.app fe ae).getAppArgs := by
    rw [hxeq]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hmieq : interpExpr V m.val env φ d ρ major =
      interpExpr V m.val env φ d ρ xl := by
    rw [hmieqS]
    rw [show (Expr.app fe ae).getAppArgs.getD (nP + nM + nm + ni)
        (Expr.bvar 0) = xl from by
      rw [List.getD_eq_getElem?_getD, hxg]
      rfl] at hmieq0
    exact hmieq0
  -- values along the spine, split at the major
  rw [hxeq] at hisp
  obtain ⟨vsi, vst, rfl, hspi, hspl⟩ := InterpSpine.append_inv hisp
  obtain ⟨tvv, rfl⟩ : ∃ tvv, vst = [tvv] := by
    match vst, hspl with
    | [tvv], _ => exact ⟨tvv, rfl⟩
    | [], h => exact nomatch h
    | _ :: _ :: _, h => exact nomatch h.2
  obtain ⟨hixl, -⟩ := hspl
  -- the major's constructor spine
  have hmspine : major = Expr.mkAppN (.const (RecRule.ctor r) usj) major.getAppArgs := by
    have := (Expr.mkAppN_getApp major).symm
    rw [hmfn] at this
    exact this
  have himaj : interpExpr V m.val env φ d ρ major = some tvv := by
    rw [hmieq, hixl]
  have hctor : ∃ ws, (∀ x ∈ major.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      InterpSpine m.val env φ d ρ major.getAppArgs ws ∧
      ChainSlots V (m.val (RecRule.ctor r)
        (Level.substFn φ (ConstantInfo.ctorInfo cvj cnP
          cnF).toConstantVal.levelParams usj)) ws ∧
      tvv = SpineFold V (m.val (RecRule.ctor r)
        (Level.substFn φ (ConstantInfo.ctorInfo cvj cnP
          cnF).toConstantVal.levelParams usj)) ws ∧
      ws.length = cnP + cnF := by
    by_cases hm0 : major.getAppArgs = []
    · refine ⟨[], by simp [hm0], by simp [hm0, InterpSpine], trivial,
        ?_, by rw [hm0] at hml1; exact hml1⟩
      rw [hmspine, hm0] at himaj
      simp only [Expr.mkAppN, interpExpr, hfj] at himaj
      split at himaj
      · exact (Option.some.inj himaj).symm
      · exact nomatch himaj
    · have hmA' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const (RecRule.ctor r) usj) major.getAppArgs) :=
        hmspine ▸ hmA
      obtain ⟨-, hmxsA, w0, ws, hiw0, hmsp, hmchain, hmfold⟩ :=
        annotOk_spine_inv _ _ hm0 hmA'
      simp only [interpExpr, hfj] at hiw0
      split at hiw0
      · obtain hw0 := (Option.some.inj hiw0)
        subst hw0
        refine ⟨ws, hmxsA, hmsp, hmchain, ?_,
          by rw [InterpSpine.length hmsp, hml1]⟩
        rw [hmspine] at himaj
        rw [hmfold] at himaj
        exact (Option.some.inj himaj).symm
      · exact nomatch hiw0
  obtain ⟨ws, hmxsA, hmsp, hmchain, htveq, hwslen⟩ := hctor
  -- the certified telescope fits
  obtain ⟨hRtf, -, -, hRtb, -, -⟩ := m.wf _ (find?_mem hfc)
  have hRhf : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hRtf
  have hRw : WScoped d (cv.type.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar hRhf
  have hRb : (cv.type.instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]; exact hRtb
  have hRA : AnnotOk V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfc)
      (Level.substFn φ cv.levelParams us)
    exact AnnotOk.closed_invariant hRhf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨T, hRT⟩ : ∃ T, interpExpr V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us) = some T := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfc)
      (Level.substFn φ cv.levelParams us)
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hRhf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have hcertargs : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take
      (nP + nM + nm + ni) ++ [major]),
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxm := List.mem_of_mem_take hx
      exact ⟨hargsW _ hxm, hargsB _ hxm, hargsL _ hxm, hargsO _ hxm,
        hxsA _ hxm⟩
    · obtain rfl : x = major := by simpa using hx
      exact ⟨hmajW, hmajB, hmajL, hmajO, hmA⟩
  have hspR : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni) ++ [major])
      (vsi ++ [tvv]) :=
    InterpSpine.append hspi ⟨himaj, trivial⟩
  obtain ⟨restR, hfitIR⟩ := certs_fit ihAll fuel (Nat.le_succ fuel)
    _ _ _ T hcerts hRw hRb (Expr.LeavesBounded.of_not_hasFvar hRhf)
    (FvarsOk.of_not_hasFvar hRhf) hRA hRT hcertargs hspR
  obtain ⟨dR, ρR, restR', hfitR⟩ := TeleFitI.toTeleFit hfitIR hRw (by
    rw [show ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni) ++
        [major]).length = nP + nM + nm + ni + 1 from by
      rw [List.length_append, List.length_take]
      simp [hlen]]
    exact stripPis_instantiateLevelParams_isSome _ _ _ har1)
  obtain ⟨hCtf, -, -, hCtb, -, -⟩ := m.wf _ (find?_mem hfj)
  have hChf : (cvj.type.instantiateLevelParams cvj.levelParams usj).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hCtf
  have hCw : WScoped d (cvj.type.instantiateLevelParams cvj.levelParams
      usj) := WScoped.of_not_hasFvar hChf
  have hCb : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]; exact hCtb
  have hCA : AnnotOk V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    exact AnnotOk.closed_invariant hChf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TC, hCT⟩ : ∃ TC, interpExpr V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hChf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have hcertmargs : ∀ x ∈ major.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x := by
    intro x hxm
    exact ⟨hmajW.getAppArgs _ hxm,
      looseBVarsBounded_getAppArgs hmajB _ hxm,
      fun l hl => hmajL l (fvarLeaves_getAppArgs hxm l hl),
      FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hxm l hl) hmajO,
      hmxsA _ hxm⟩
  obtain ⟨restC, hfitIC⟩ := certs_fit ihAll fuel (Nat.le_succ fuel)
    _ _ _ TC hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
    (FvarsOk.of_not_hasFvar hChf) hCA hCT hcertmargs hmsp
  -- rebase the constructor fit at the recursor fit's final frame
  obtain ⟨hdR, hagrR, -⟩ := TeleFit.toTeleFitI hfitR hRw
  have hfitIC' := TeleFitI.lift hfitIC hCw hdR hagrR
  obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC'
    (hCw.mono hdR) (by
    rw [show major.getAppArgs.length = cnP + cnF from hml1]
    exact stripPis_instantiateLevelParams_isSome _ _ _ har2)
  -- the rule's fold facts
  obtain ⟨hrhsA, hfolds⟩ := m.rec_rules c cv nP nM nm ni rules hfc r
    (List.mem_of_find?_eq_some hrule)
  have hchain' : ChainSlots V (m.val c
      (Level.substFn φ (ConstantInfo.recInfo cv nP nM nm ni
        rules).toConstantVal.levelParams us)) (vsi ++ [tvv]) := by
    rw [hv0]
    exact hchain
  have hvsilen : vsi.length = nP + nM + nm + ni := by
    have := InterpSpine.length hspi
    rw [this, List.length_take]
    rw [hxeq] at hlen
    simp at hlen
    omega
  have hparameq : ws.take cnP = (vsi ++ [tvv]).take cnP := by
    have hspT1 : InterpSpine m.val env φ d ρ
        (major.getAppArgs.take cnP) (ws.take cnP) :=
      InterpSpine.take _ hmsp
    have hspT2 : InterpSpine m.val env φ d ρ
        ((Expr.app fe ae).getAppArgs.take cnP)
        ((vsi ++ [tvv]).take cnP) := by
      have := InterpSpine.take cnP hisp
      rw [← hxeq] at this
      exact this
    refine defEqList_values ihAll fuel (Nat.le_succ fuel)
      _ _ _ _ hpeq ?_ ?_ hspT1 hspT2
    · intro x hx
      have hxm := List.mem_of_mem_take hx
      exact ⟨hmajW.getAppArgs _ hxm,
        looseBVarsBounded_getAppArgs hmajB _ hxm,
        fun l hl => hmajL l (fvarLeaves_getAppArgs hxm l hl),
        FvarsOk.of_subset
          (fun l hl => fvarLeaves_getAppArgs hxm l hl) hmajO,
        hmxsA _ hxm⟩
    · intro x hx
      have hxm := List.mem_of_mem_take hx
      exact ⟨hargsW _ hxm, hargsB _ hxm, hargsL _ hxm, hargsO _ hxm,
        hxsA _ hxm⟩
  have hψeq : ∀ p ∈ cvj.levelParams,
      Level.substFn φ
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams usj p =
      Level.substFn φ
        (ConstantInfo.recInfo cv nP nM nm ni rules).toConstantVal.levelParams
        us p := by
    intro p hp
    have h1 : Level.substFn φ cvj.levelParams usj =
        Level.substFn φ cvj.levelParams
          (cvj.levelParams.map fun q =>
            Level.subst cv.levelParams us (.param q)) :=
      Level.substFn_congr (Level.isEquivList_sound hlev φ)
    have h2 : (cvj.levelParams.map fun q =>
        Level.subst cv.levelParams us (.param q)) =
        (cvj.levelParams.map Level.param).map
          (Level.subst cv.levelParams us) := by
      simp [List.map_map, Function.comp]
    have h3 := Level.substFn_map_subst (φ := φ) (ks := cv.levelParams)
      (vs := us) (ks' := cvj.levelParams)
      (ws := cvj.levelParams.map Level.param) (by simp) hp
    show Level.substFn φ cvj.levelParams usj p = _
    rw [h1, h2, h3, Level.substFn_map_param]
    rfl
  obtain ⟨R, hRi, hfoldEq, hRchain⟩ := hfolds cvj cnP cnF hfj _ _
    vsi ws tvv hvsilen hwslen hchain' hmchain htveq hparameq hψeq
    ⟨φ, us, usj, d, ρ, dR, ρR, restR', dC, ρC, restC', rfl, rfl,
      hfitR, hfitC⟩
  -- the reduct's interpretation and annotation chain
  have hRinst : interpExpr V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) = some R := by
    rw [interp_closed_invariant hclInst d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hRi
  have hArhs : AnnotOk V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    have h1 := AnnotOk.instLevels (ks := cv.levelParams) (vs := us)
      m.val_params r.rhs 0 (rho0 V)
      (hrhsA (Level.substFn φ cv.levelParams us))
    exact AnnotOk.closed_invariant hclInst d ρ h1
  have htake : (Expr.app fe ae).getAppArgs.take (nP + nM + nm) =
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni)).take
        (nP + nM + nm) := by
    rw [List.take_take]
    congr 1
    omega
  have hspR : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
        major.getAppArgs.drop cnP)
      (vsi.take (nP + nM + nm) ++ ws.drop cnP) := by
    refine InterpSpine.append ?_ (InterpSpine.drop cnP hmsp)
    rw [htake]
    exact InterpSpine.take _ hspi
  have hxsAR : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), AnnotOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxsA _ (List.mem_of_mem_take hx)
    · exact hmxsA _ (List.mem_of_mem_drop hx)
  obtain ⟨hAe, hie⟩ := annotOk_spine _ _ hArhs hRinst hxsAR hspR hRchain
  rw [← heout] at hAe hie
  refine ⟨?_, hAe⟩
  have hifold' : interpExpr V m.val env φ d ρ (Expr.app fe ae) =
      some (SpineFold V vf0 (vsi ++ [tvv])) := by
    rw [← hspine] at hifold
    exact hifold
  rw [hie, hifold', ← hv0, hfoldEq]

private theorem whnf_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f) :
    WhnfClaims m φ (fuel + 1) := by
  intro d e e' ρ h hw hb hLb hok ha
  match e, h with
  | .sort u, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .fvar idx n ty, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .forallE n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .lam n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .const n ws, h =>
    simp only [whnfCore] at h
    cases hf : env.find? n with
    | none => rw [hf] at h; exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv value =>
        dsimp only at h
        split at h
        next hal =>
          obtain ⟨-, -, -, -, hval, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
          obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
          have hcl : (value.instantiateLevelParams cv.levelParams ws).hasFvar = false := by
            rw [hasFvar_instantiateLevelParams]; exact hvc
          have hstored := (m.annot_ok _ (List.mem_of_find?_eq_some hf)
            (Level.substFn φ cv.levelParams ws)).2 cv value rfl
          have hinst := AnnotOk.instLevels m.val_params value 0 (rho0 V) hstored
          obtain ⟨hi, ha'⟩ := ihw h
            (WScoped.of_not_hasFvar hcl)
            (by rw [looseBVarsBounded_instantiateLevelParams]; exact hvb)
            (Expr.LeavesBounded.of_not_hasFvar hcl)
            (FvarsOk.of_not_hasFvar hcl)
            (AnnotOk.closed_invariant hcl d ρ hinst)
          refine ⟨?_, ha'⟩
          rw [hi]
          rw [interp_closed_invariant hcl]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          have hmem : ConstantInfo.defnInfo cv value ∈ env.consts :=
            List.mem_of_find?_eq_some hf
          have hde := m.defn_eq cv value hmem (Level.substFn φ cv.levelParams ws)
          unfold interpClosed at hde
          rw [hde]
          have hname : cv.name = n := by
            have := find?_name hf
            simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
          rw [interp_const hf hal, hname]
          rfl
        next hal => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | axiomInfo cv => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | thmInfo cv value => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | indInfo cv _ => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | ctorInfo cv nP nF => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | recInfo cv nP nM nm ni rules => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
  | .app f a, h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hvA, hfib⟩ := ha
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨hif, haf'⟩ := ihw hwf hw.1 hb.1 hLbf hokf haf
    rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, hcert⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- beta (guarded or certified)
      have hwlam := whnf_WScoped m.wf fuel hwf hw.1
      have hblam := whnf_looseBVars m.wf fuel hwf hb.1
      have hLblam : Expr.LeavesBounded (Expr.lam n ty body mm) := fun l hl =>
        hLbf l (whnf_fvarLeaves m.wf fuel hwf l hl)
      have hoklam : FvarsOk V m.val env φ d ρ (.lam n ty body mm) :=
        whnf_FvarsOk m.wf fuel hwf hokf
      simp only [WScoped] at hwlam
      simp only [looseBVarsBounded, Bool.and_eq_true] at hblam
      have hfi' : interpExpr V m.val env φ d ρ (.lam n ty body mm) = some vf := by
        rw [hif]; exact hfi
      rw [interpExpr, hc] at hfi'
      dsimp only at hfi'
      cases hty : interpExpr V m.val env φ d ρ ty with
      | none => rw [hty] at hfi'; exact nomatch hfi'
      | some Aty =>
      rw [hty] at hfi'
      simp only [Option.some.injEq] at hfi'
      simp only [AnnotOk] at haf'
      obtain ⟨haty, -, hcond⟩ := haf'
      -- the argument is in the λ's domain
      have hdom : va ∈ˢ Aty := by
        rcases hcert with hnz | ⟨ta, hta, hde⟩
        · -- guarded: certainly non-Prop, so the graph determines its domain
          have hnz' : Level.eval φ v ≠ 0 := Level.isNonZero_sound hnz φ
          by_cases hvE : vE = 0
          · subst hvE
            exact absurd (hfi'.trans (mem_pi_zero hpi)) (lam_ne_pt hnz')
          · have hpil : SetTheory.lam (v.eval φ) Aty
                (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
                  (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
                pi vE A B := by
              rw [hfi']; exact hpi
            exact lam_dom hpil hvE hnz' va hvA
        · -- certified: the runtime check hands the fact directly
          obtain ⟨⟨va₂, vta, hai₂, htai, hmema⟩, hAta⟩ :=
            ihi hta hw.2 hb.2 hLba hoka haa
          have hva₂ : va₂ = va := by
            rw [hai] at hai₂
            exact (Option.some.inj hai₂).symm
          subst hva₂
          have hLbta : Expr.LeavesBounded ta := fun l hl =>
            hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
          have hLbty : Expr.LeavesBounded ty := fun l hl =>
            hLblam l (by simp [fvarLeaves, hl])
          have heqA : vta = Aty :=
            ihd hde
              (inferTypeCore_WScoped m.wf fuel hta hw.2) hwlam.1
              (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hblam.1
              hLbta hLbty
              (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
              ((FvarsOk.of_lam hoklam).1)
              hAta haty htai hty
          exact heqA ▸ hmema
      obtain ⟨hbodyA, hwfact⟩ := hcond va Aty hty hdom
      obtain ⟨w, Bl, hwi, hwB, hBu⟩ := hwfact v hc
      have hfb : fvarsBelow d body := hwlam.2.fvarsBelow
      have hred_w : WScoped d (body.instantiate1 a) :=
        WScoped.instantiate1_gen hw.2 0 hwlam.2
      have hred_b : (body.instantiate1 a).looseBVarsBounded 0 = true :=
        looseBVarsBounded_instantiate1_gen hb.2 hblam.2
      have hred_Lb : Expr.LeavesBounded (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hLblam l (by simp [fvarLeaves, hl'])
        · exact hLba l hl'
      have hred_ok : FvarsOk V m.val env φ d ρ (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact (FvarsOk.of_lam hoklam).2 l hl'
        · exact hoka l hl'
      have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
        (n := n) (ty := ty) hfb hw.2 hb.2 hai 0
      have hred_A : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
        AnnotOk_beta hfb hw.2 hb.2 hai haa 0 hbodyA
      obtain ⟨hi2, ha2⟩ := ihw hbeta hred_w hred_b hred_Lb hred_ok hred_A
      refine ⟨?_, ha2⟩
      have hfibres : ∀ x, x ∈ˢ Aty →
          ∃ B', ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ B' ∧
            B' ∈ˢ univ (v.eval φ) := by
        intro x hx
        obtain ⟨-, hwfact_x⟩ := hcond x Aty hty hx
        obtain ⟨w_x, B_x, hwi_x, hwB_x, hBu_x⟩ := hwfact_x v hc
        exact ⟨B_x, by rw [hwi_x]; exact hwB_x, hBu_x⟩
      obtain ⟨Bf, hBf1, hBf2⟩ := choose_fibres (V := V) hfibres
      have happi : interpExpr V m.val env φ d ρ (.app f a) =
          some (SetTheory.app vf va) := by
        rw [interpExpr, hfi, hai]
      rw [hi2, hbeta_eq, hwi, happi]
      simp only [Option.some.injEq]
      rw [← hfi', app_lam hdom hBf1 hBf2]
      simp [hwi]
    · -- iota step
      have hw' : WScoped d (Expr.app f' a) := by
        simp only [WScoped]
        exact ⟨whnf_WScoped m.wf fuel hwf hw.1, hw.2⟩
      have hb' : (Expr.app f' a).looseBVarsBounded 0 = true := by
        simp only [looseBVarsBounded, Bool.and_eq_true]
        exact ⟨whnf_looseBVars m.wf fuel hwf hb.1, hb.2⟩
      have hLb' : Expr.LeavesBounded (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLbf l (whnf_fvarLeaves m.wf fuel hwf l hl)
        · exact hLba l hl
      have hok' : FvarsOk V m.val env φ d ρ (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact whnf_FvarsOk m.wf fuel hwf hokf l hl
        · exact hoka l hl
      have ha' : AnnotOk V m.val env φ d ρ (Expr.app f' a) := by
        simp only [AnnotOk]
        exact ⟨haf', haa, vf, va, vE, A, B, hif.trans hfi, hai, hpi, hvA,
          hfib⟩
      obtain ⟨⟨hie, hae''⟩, hwE, hbE, hLbE, hokE⟩ :=
        iota_sound ihAll hio hw' hb' hLb' hok' ha'
      obtain ⟨hi2, ha2⟩ := ihw hwe'' hwE hbE hLbE hokE hae''
      refine ⟨?_, ha2⟩
      rw [hi2, hie]
      simp only [interpExpr]
      rw [hif]
    · -- stuck application
      refine ⟨?_, ?_⟩
      · simp only [interpExpr]
        rw [hif]
      · simp only [AnnotOk]
        refine ⟨haf', haa, vf, va, vE, A, B, ?_, hai, hpi, hvA, hfib⟩
        rw [hif]; exact hfi
  | .proj sn i e, h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded] at hb
    have hLbe : Expr.LeavesBounded e := fun l hl => hLb l (by
      simp only [fvarLeaves]; exact hl)
    have hoke : FvarsOk V m.val env φ d ρ e := fun l hl => hok l (by
      simp only [fvarLeaves]; exact hl)
    simp only [AnnotOk] at ha
    obtain ⟨hae, hilt, veC, uC, vC, AC, BfC, hveiC, hsigC, hAuC, hBfC⟩ := ha
    obtain ⟨e₂, he, hcase⟩ := whnf_proj_inv h
    obtain ⟨hie, hae₂⟩ := ihw he hw hb hLbe hoke hae
    rcases hcase with rfl | ⟨us, cv, nP, nF, hfn, hf, hi2, hlen, hus, hred, hcert⟩
    · -- stuck projection
      refine ⟨?_, ?_⟩
      · simp only [interpExpr]
        rw [hie]
      · simp only [AnnotOk]
        refine ⟨hae₂, hilt, veC, uC, vC, AC, BfC, ?_, hsigC, hAuC, hBfC⟩
        rw [hie]; exact hveiC
    · -- projection of the pair constructor
      obtain ⟨hnP, hnF, hlp, hmkfacts⟩ := m.ind_ok.right.left cv nP nF hf
      subst hnP; subst hnF
      obtain ⟨l0, l1, rfl⟩ := List.length_two hus
      obtain ⟨α, β, a, b, hargs⟩ := List.length_four hlen
      have he₂ : e₂ = .app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b := by
        have h0 := Expr.mkAppN_getApp e₂
        rw [hfn, hargs] at h0
        exact h0.symm
      have hargd : e₂.getAppArgs.getD (2 + i) (.bvar 0) = if i = 0 then a else b := by
        rw [hargs]
        match i, hi2 with
        | 0, _ => rfl
        | 1, _ => rfl
      -- pristine invariants of the whnf'd struct (for the certificates)
      have hwC := whnf_WScoped m.wf fuel he hw
      have hbC := whnf_looseBVars m.wf fuel he hb
      have hLbC : Expr.LeavesBounded e₂ := fun l hl =>
        hLbe l (whnf_fvarLeaves m.wf fuel he l hl)
      have hokC := whnf_FvarsOk m.wf fuel he hoke
      have haC := hae₂
      -- decomposed (substituted) forms
      have hwe₂ := hwC
      have hbe₂ := hbC
      have hLbe₂ := hLbC
      have hoke₂ := hokC
      rw [he₂] at hwe₂ hbe₂ hLbe₂ hoke₂ hae₂
      have hien : interpExpr V m.val env φ d ρ
          (.app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b) =
          interpExpr V m.val env φ d ρ e := by
        rw [← he₂]; exact hie
      simp only [WScoped] at hwe₂
      obtain ⟨⟨⟨⟨-, hwα⟩, hwβ⟩, hwa⟩, hwb⟩ := hwe₂
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbe₂
      obtain ⟨⟨⟨⟨-, hbα⟩, hbβ⟩, hba⟩, hbb⟩ := hbe₂
      have hLba : Expr.LeavesBounded a := fun l hl => hLbe₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inl (Or.inr hl))
      have hLbb : Expr.LeavesBounded b := fun l hl => hLbe₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inr hl)
      have hoka : FvarsOk V m.val env φ d ρ a := fun l hl => hoke₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inl (Or.inr hl))
      have hokb : FvarsOk V m.val env φ d ρ b := fun l hl => hoke₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inr hl)
      -- decompose the spine's clauses
      try simp only [AnnotOk] at hae₂
      obtain ⟨ha3, hab, vf₃, vb, vE₃, A₃, B₃, hf₃i, hbi, hpi₃, hvb₃, hfib₃⟩ := hae₂
      try simp only [AnnotOk] at ha3
      obtain ⟨ha2, haa, vf₂, va, vE₂, A₂, B₂, hf₂i, hai, hpi₂, hva₂, hfib₂⟩ := ha3
      try simp only [AnnotOk] at ha2
      obtain ⟨ha1, haβ, vf₁, vβ, vE₁, A₁, B₁, hf₁i, hβi, hpi₁, hvβ₁, hfib₁⟩ := ha2
      try simp only [AnnotOk] at ha1
      obtain ⟨hac, haα, vf₀, vα, vE₀, A₀, B₀, hci, hαi, hpi₀, hvα₀, hfib₀⟩ := ha1
      -- the head constant's value
      rw [interpExpr, hf] at hci
      dsimp only [ConstantInfo.toConstantVal] at hci
      obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cv.levelParams [l0, l1] := ⟨_, rfl⟩
      rw [← hψ'] at hci
      by_cases hal : ([l0, l1] : List Level).length = cv.levelParams.length
      case neg => simp only [hal, if_false] at hci; exact nomatch hci
      simp only [hal, if_true] at hci
      have hval : interpExpr V m.val env φ d ρ (.const psigmaMkName [l0, l1]) =
          some (m.val psigmaMkName ψ') := by
        rw [interpExpr, hf]
        dsimp only [ConstantInfo.toConstantVal]
        rw [← hψ']
        simp only [hal, if_true]
      have hvf₀ : vf₀ = m.val psigmaMkName ψ' := (Option.some.inj hci).symm
      -- level bookkeeping
      have hne : uN ≠ vN := by decide
      have hψu : ψ' uN = Level.eval φ l0 := by
        rw [hψ', hlp]
        simp [Level.substFn]
      have hψv : ψ' vN = Level.eval φ l1 := by
        rw [hψ', hlp]
        simp [Level.substFn, hne]
      -- partial-fold equations
      have hf₁ : vf₁ = app (m.val psigmaMkName ψ') vα := by
        rw [interpExpr, hval, hαi] at hf₁i
        dsimp only at hf₁i
        exact (Option.some.inj hf₁i).symm
      have hf₂ : vf₂ = app vf₁ vβ := by
        rw [interpExpr, hf₁i, hβi] at hf₂i
        dsimp only at hf₂i
        exact (Option.some.inj hf₂i).symm
      have hf₃ : vf₃ = app vf₂ va := by
        rw [interpExpr, hf₂i, hai] at hf₃i
        dsimp only at hf₃i
        exact (Option.some.inj hf₃i).symm
      have hnesti : interpExpr V m.val env φ d ρ
          (.app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b) =
          some (app vf₃ vb) := by
        rw [interpExpr, hf₃i, hbi]
      have hveC' : veC = app vf₃ vb := by
        have : some veC = some (app vf₃ vb) := by
          rw [← hveiC, ← hien, hnesti]
        exact Option.some.inj this
      by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
      · -- collapse: everything is the proof point (certified)
        have hnz : ¬ (Level.max l0 l1).isNonZero = true := by
          intro hnz'
          have := Level.isNonZero_sound hnz' φ
          simp only [Level.eval] at this
          rw [← hψu, ← hψv] at this
          exact this hw0
        rcases hcert with hcert | hcert
        case inl => exact absurd hcert hnz
        cases fuel with
        | zero => simp [projCert] at hcert
        | succ f =>
        obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f (by omega)
        obtain ⟨ta, sta, uT, te, ste, wT, hta, hsta, hwta, heq1, hte, hste, hwte, heq2⟩ :=
          projCert_inv hcert
        have hwT0 : Level.eval φ wT = 0 := by
          rw [Level.isEquiv_sound heq2 φ]
          simp only [Level.eval, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [← hψu, ← hψv]
          exact hw0
        have hept : interpExpr V m.val env φ d ρ e₂ = some pt :=
          sortCert_pt ihwL ihiL hte hste hwte hwT0 hwC hbC hLbC hokC haC
        have hveCpt : veC = pt := by
          have : some veC = some pt := by
            rw [← hveiC, ← hie, hept]
          exact Option.some.inj this
        -- the projected argument is a proof point too
        rw [hargd] at hta
        have huT0 : Level.eval φ uT = 0 := by
          rw [Level.isEquiv_sound heq1 φ]
          have hu0 : ψ' uN = 0 :=
            Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw0))
          have hv0 : ψ' vN = 0 :=
            Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw0))
          match i, hi2 with
          | 0, _ =>
            simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
            rw [← hψu]
            exact hu0
          | 1, _ =>
            simp only [List.getD, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some]
            rw [← hψv]
            exact hv0
        match i, hi2, hred, hargd, hta with
        | 0, _, hred, hargd, hta =>
          rw [if_pos rfl] at hargd
          rw [hargd] at hred
          have hapt : interpExpr V m.val env φ d ρ a = some pt :=
            sortCert_pt ihwL ihiL hta hsta hwta huT0 hwa hba hLba hoka haa
          obtain ⟨hired, hared⟩ := ihw hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hapt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, sfst_pt]
          simp
        | 1, _, hred, hargd, hta =>
          rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          have hbpt : interpExpr V m.val env φ d ρ b = some pt :=
            sortCert_pt ihwL ihiL hta hsta hwta huT0 hwb hbb hLbb hokb hab
          obtain ⟨hired, hared⟩ := ihw hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbpt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, ssnd_pt]
          simp
      · -- no collapse: the fold is a genuine pair
        have hfacts := hmkfacts ψ'
        have hαmem : vα ∈ˢ univ (ψ' uN) := hfacts.dom₀ hw0 (hvf₀ ▸ hpi₀) hvα₀
        have hpi₁' : app (m.val psigmaMkName ψ') vα ∈ˢ pi vE₁ A₁ B₁ := by
          rw [← hf₁]; exact hpi₁
        have hβmem : vβ ∈ˢ pi (ψ' vN + 1) vα (fun _ => univ (ψ' vN)) :=
          hfacts.dom₁ hw0 hαmem hpi₁' hvβ₁
        have hpi₂' : app (app (m.val psigmaMkName ψ') vα) vβ ∈ˢ pi vE₂ A₂ B₂ := by
          rw [← hf₁, ← hf₂]; exact hpi₂
        have hamem : va ∈ˢ vα := hfacts.dom₂ hw0 hαmem hβmem hpi₂' hva₂
        have hpi₃' : app (app (app (m.val psigmaMkName ψ') vα) vβ) va ∈ˢ pi vE₃ A₃ B₃ := by
          rw [← hf₁, ← hf₂, ← hf₃]; exact hpi₃
        have hbmem : vb ∈ˢ app vβ va := hfacts.dom₃ hw0 hαmem hβmem hamem hpi₃' hvb₃
        have hfold : app vf₃ vb = spair va vb := by
          rw [hf₃, hf₂, hf₁]
          rw [hfacts.fold hαmem hβmem hamem hbmem]
          simp [hw0]
        match i, hi2, hred, hargd with
        | 0, _, hred, hargd =>
          rw [if_pos rfl] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihw hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hai]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, sfst_spair]
          simp
        | 1, _, hred, hargd =>
          rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihw hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbi]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, ssnd_spair]
          simp


private theorem defeq_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (_ihi : InferClaims m φ fuel)
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f) :
    DefEqClaims m φ (fuel + 1) := by
  intro d a b ρ h hwa hwb hba hbb hLba hLbb hoka hokb haa hab va vb hva hvb
  unfold isDefEqCore at h
  simp only [Bind.bind, Except.bind] at h
  cases hwha : whnfCore env fuel d a with
  | error e => rw [hwha] at h; exact nomatch h
  | ok a' =>
  rw [hwha] at h
  dsimp only at h
  cases hwhb : whnfCore env fuel d b with
  | error e => rw [hwhb] at h; exact nomatch h
  | ok b' =>
  rw [hwhb] at h
  dsimp only at h
  -- transfer facts through reduction
  obtain ⟨hia, haa'⟩ := ihw hwha hwa hba hLba hoka haa
  obtain ⟨hib, hab'⟩ := ihw hwhb hwb hbb hLbb hokb hab
  rw [← hia] at hva
  rw [← hib] at hvb
  have hwa' := whnf_WScoped m.wf fuel hwha hwa
  have hwb' := whnf_WScoped m.wf fuel hwhb hwb
  have hba' := whnf_looseBVars m.wf fuel hwha hba
  have hbb' := whnf_looseBVars m.wf fuel hwhb hbb
  have hLba' : Expr.LeavesBounded a' := fun l hl =>
    hLba l (whnf_fvarLeaves m.wf fuel hwha l hl)
  have hLbb' : Expr.LeavesBounded b' := fun l hl =>
    hLbb l (whnf_fvarLeaves m.wf fuel hwhb l hl)
  have hoka' := whnf_FvarsOk m.wf fuel hwha hoka
  have hokb' := whnf_FvarsOk m.wf fuel hwhb hokb
  clear hwha hwhb hwa hwb haa hab hia hib hba hbb hLba hLbb hoka hokb
  have hPI : stuckIrrel env fuel d a' b' = .ok true → va = vb := fun hp =>
    stuckIrrel_sound ihAll hp hwa' hwb' hba' hbb' hLba' hLbb'
      hoka' hokb' haa' hab' hva hvb
  match a', b', h with
  | Expr.sort u, Expr.sort v, h =>
    dsimp only at h
    simp only [interpExpr, Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have : Level.isEquiv u v = some true := by
      revert h
      cases hEq : Level.isEquiv u v with
      | none => simp [liftFueled]
      | some x => cases x <;> simp [liftFueled, pure, Except.pure]
    rw [Level.isEquiv_sound this φ]
  | Expr.fvar i ni tyi, Expr.fvar j nj tyj, h =>
    dsimp only at h
    split at h
    next hij =>
      have hij' : i = j := by simpa using hij
      subst hij'
      simp only [interpExpr, Option.some.injEq] at hva hvb
      subst hva; subst hvb
      rfl
    next _ => exact hPI h
  | Expr.const n us, Expr.const n' us', h =>
    dsimp only at h
    split at h
    case _ hnn =>
      subst hnn
      try simp only [Bind.bind, Except.bind] at h
      cases hEq : Level.isEquivList us us' with
      | none => rw [hEq] at h; simp [liftFueled] at h
      | some r =>
      rw [hEq] at h
      dsimp only [liftFueled] at h
      try simp only [pure, Except.pure] at h
      try dsimp only at h
      cases r with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact hPI h
      | true =>
      have hlev : Level.isEquivList us us' = some true := hEq
      simp only [interpExpr] at hva hvb
      cases hf : env.find? n with
      | none => rw [hf] at hva; exact nomatch hva
      | some ci =>
      rw [hf] at hva hvb
      dsimp only at hva hvb
      by_cases hal : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal] at hva
        have hal' : us'.length = ci.toConstantVal.levelParams.length := by
          have := Level.isEquivList_length hlev
          omega
        rw [if_pos hal'] at hvb
        simp only [Option.some.injEq] at hva hvb
        subst hva; subst hvb
        rw [Level.substFn_congr (Level.isEquivList_sound hlev φ)]
      · rw [if_neg hal] at hva
        exact nomatch hva
    case _ hnn => exact hPI h
  | Expr.forallE n₁ ty₁ body₁ m₁, Expr.forallE n₂ ty₂ body₂ m₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_forallE hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_forallE hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haty₁, ⟨v₁, hv₁⟩, hcond₁⟩ := haa'
    obtain ⟨haty₂, ⟨v₂, hv₂⟩, hcond₂⟩ := hab'
    cases hd1 : isDefEqCore env fuel d ty₁ ty₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    cases hd2 : isDefEqCore env fuel (d + 1)
        (body₁.instantiate1 (.fvar d n₁ ty₁)) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    dsimp only at h
    cases r₂ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    rw [hv₁, hv₂] at h
    dsimp only at h
    have hlev : Level.isEquiv v₁ v₂ = some true := by
      revert h
      cases hEq : Level.isEquiv v₁ v₂ with
      | none => simp [liftFueled]
      | some x => cases x <;> simp [liftFueled, pure, Except.pure]
    simp only [interpExpr, hv₁, hv₂] at hva hvb
    cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
    | none => rw [hA1] at hva; exact nomatch hva
    | some A₁ =>
    rw [hA1] at hva
    cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
    | none => rw [hA2] at hvb; exact nomatch hvb
    | some A₂ =>
    rw [hA2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hAeq : A₁ = A₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
    rw [← hveq]
    refine pi_congr fun x hx => ?_
    obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
    obtain ⟨w₁, hw₁, -⟩ := hwfact₁ v₁ hv₁
    obtain ⟨w₂, hw₂, -⟩ := hwfact₂ v₂ hv₂
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_lam hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_lam hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haty₁, ⟨v₁, hv₁⟩, hcond₁⟩ := haa'
    obtain ⟨haty₂, ⟨v₂, hv₂⟩, hcond₂⟩ := hab'
    cases hd1 : isDefEqCore env fuel d ty₁ ty₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    cases hd2 : isDefEqCore env fuel (d + 1)
        (body₁.instantiate1 (.fvar d n₁ ty₁)) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    dsimp only at h
    cases r₂ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    rw [hv₁, hv₂] at h
    dsimp only at h
    have hlev : Level.isEquiv v₁ v₂ = some true := by
      revert h
      cases hEq : Level.isEquiv v₁ v₂ with
      | none => simp [liftFueled]
      | some x => cases x <;> simp [liftFueled, pure, Except.pure]
    simp only [interpExpr, hv₁, hv₂] at hva hvb
    cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
    | none => rw [hA1] at hva; exact nomatch hva
    | some A₁ =>
    rw [hA1] at hva
    cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
    | none => rw [hA2] at hvb; exact nomatch hvb
    | some A₂ =>
    rw [hA2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hAeq : A₁ = A₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
    rw [← hveq]
    refine lam_congr fun x hx => ?_
    obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
    obtain ⟨w₁, B₁, hw₁, -, -⟩ := hwfact₁ v₁ hv₁
    obtain ⟨w₂, B₂, hw₂, -, -⟩ := hwfact₂ v₂ hv₂
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.app f₁ a₁, Expr.app f₂ a₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbf₁ : Expr.LeavesBounded f₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbf₂ : Expr.LeavesBounded f₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    have hLba₁ : Expr.LeavesBounded a₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLba₂ : Expr.LeavesBounded a₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokf₁, hoka₁⟩ := FvarsOk.of_app hoka'
    obtain ⟨hokf₂, hoka₂⟩ := FvarsOk.of_app hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haf₁, haa₁, -⟩ := haa'
    obtain ⟨haf₂, haa₂, -⟩ := hab'
    try simp only [Bind.bind, Except.bind] at h
    cases hd1 : isDefEqCore env fuel d f₁ f₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact hPI h
    | true =>
    simp only [↓reduceIte] at h
    cases hd2 : isDefEqCore env fuel d a₁ a₂ with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    dsimp only at h
    cases r₂ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact hPI h
    | true =>
    simp only [interpExpr] at hva hvb
    cases hf1 : interpExpr V m.val env φ d ρ f₁ with
    | none => rw [hf1] at hva; exact nomatch hva
    | some vf₁ =>
    rw [hf1] at hva
    cases ha1 : interpExpr V m.val env φ d ρ a₁ with
    | none => rw [ha1] at hva; exact nomatch hva
    | some va₁ =>
    rw [ha1] at hva
    cases hf2 : interpExpr V m.val env φ d ρ f₂ with
    | none => rw [hf2] at hvb; exact nomatch hvb
    | some vf₂ =>
    rw [hf2] at hvb
    cases ha2 : interpExpr V m.val env φ d ρ a₂ with
    | none => rw [ha2] at hvb; exact nomatch hvb
    | some va₂ =>
    rw [ha2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hfe : vf₁ = vf₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbf₁ hLbf₂ hokf₁ hokf₂ haf₁ haf₂ hf1 hf2
    have hae : va₁ = va₂ :=
      ihd hd2 hwa'.2 hwb'.2 hba'.2 hbb'.2 hLba₁ hLba₂ hoka₁ hoka₂ haa₁ haa₂ ha1 ha2
    rw [hfe, hae]
  | Expr.sort _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.sort _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.sort _, Expr.const _ _, h => exact hPI h
  | Expr.sort u, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.sort _, Expr.app _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.sort _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.fvar i ni tyi, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.fvar _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.sort _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.forallE n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.forallE _ _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.const _ _, Expr.sort _, h => exact hPI h
  | Expr.const _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.const n us, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.const _ _, Expr.app _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.sort u, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.fvar j nj tyj, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.forallE n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.const n' us', h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.app f₂ a₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.sort _, h => exact hPI h
  | Expr.app _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.app _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.app _ _, Expr.const _ _, h => exact hPI h
  | Expr.app f₁ a₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.bvar i₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.bvar _, Expr.sort _, h => exact hPI h
  | Expr.bvar _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.const _ _, h => exact hPI h
  | Expr.bvar _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.app _ _, h => exact hPI h
  | Expr.bvar _, Expr.bvar _, h => exact hPI h
  | Expr.bvar _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.lit _, h => exact hPI h
  | Expr.bvar _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.bvar _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.const _ _, Expr.bvar _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.bvar i₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.bvar _, h => exact hPI h
  | Expr.letE n₁ ty₁ v₁ body₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.letE _ _ _ _, Expr.sort _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.lit _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.letE n₂ ty₂ v₂ body₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lit l₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lit _, Expr.sort _, h => exact hPI h
  | Expr.lit _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.lit _, Expr.const _ _, h => exact hPI h
  | Expr.lit _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.lit _, Expr.app _ _, h => exact hPI h
  | Expr.lit _, Expr.bvar _, h => exact hPI h
  | Expr.lit _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lit _, Expr.lit _, h => exact hPI h
  | Expr.lit _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.lit _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.lit _, h => exact hPI h
  | Expr.const _ _, Expr.lit _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.lit _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.lit l₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.lit _, h => exact hPI h
  | Expr.proj s₁ i₁ e₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.proj _ _ _, Expr.sort _, h => exact hPI h
  | Expr.proj _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.proj _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.lit _, h => exact hPI h
  | Expr.proj s₁ i₁ e₁, Expr.proj s₂ i₂ e₂, h =>
    dsimp only at h
    split at h
    case _ hi =>
      try simp only [Bind.bind, Except.bind] at h
      cases hd : isDefEqCore env fuel d e₁ e₂ with
      | error e => rw [hd] at h; exact nomatch h
      | ok r =>
      rw [hd] at h
      dsimp only at h
      cases r with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact hPI h
      | true =>
      have hieq : i₁ = i₂ := by simpa using hi
      subst hieq
      simp only [WScoped] at hwa' hwb'
      simp only [looseBVarsBounded] at hba' hbb'
      have hLbe₁ : Expr.LeavesBounded e₁ := fun l hl =>
        hLba' l (by simp [fvarLeaves, hl])
      have hLbe₂ : Expr.LeavesBounded e₂ := fun l hl =>
        hLbb' l (by simp [fvarLeaves, hl])
      have hoke₁ : FvarsOk V m.val env φ d ρ e₁ :=
        FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hoka'
      have hoke₂ : FvarsOk V m.val env φ d ρ e₂ :=
        FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hokb'
      simp only [AnnotOk] at haa' hab'
      simp only [interpExpr] at hva hvb
      cases he₁ : interpExpr V m.val env φ d ρ e₁ with
      | none => rw [he₁] at hva; exact nomatch hva
      | some ve₁ =>
      rw [he₁] at hva
      dsimp only at hva
      cases he₂ : interpExpr V m.val env φ d ρ e₂ with
      | none => rw [he₂] at hvb; exact nomatch hvb
      | some ve₂ =>
      rw [he₂] at hvb
      dsimp only at hvb
      have hee : ve₁ = ve₂ :=
        ihd hd hwa' hwb' hba' hbb' hLbe₁ hLbe₂ hoke₁ hoke₂
          haa'.1 hab'.1 he₁ he₂
      subst hee
      exact Option.some.inj (hva.symm.trans hvb)
    case _ _ => exact hPI h
  | Expr.sort _, Expr.proj _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.proj s₂ i₂ e₂, h =>
    exact etaBranch_sound ihAll h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.proj _ _ _, h => exact hPI h

private theorem infer_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    InferClaims m φ (fuel + 1) := by
  intro d e t ρ h hw hb hLb hok ha
  match e, h with
  | .sort u, h =>
    simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨⟨univ (u.eval φ), univ (u.eval φ + 1), ?_, ?_, univ_mem_univ _⟩, ?_⟩ <;>
      simp [interpExpr, Level.eval, AnnotOk]
  | .fvar idx n ty, h =>
    simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨⟨hidx, hAty, T, hT, hmem⟩, hFty⟩ := FvarsOk.of_fvar hok
    exact ⟨⟨ρ idx, T, by simp [interpExpr], hT, hmem⟩, hAty⟩
  | .const n ws, h =>
    simp only [inferTypeCore] at h
    cases hf : env.find? n with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      next hal =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨htc, -, -, -, -, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
        have hcl : (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ws).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]; exact htc
        obtain ⟨T, hT, hmem⟩ :=
          m.mem_type ci (List.mem_of_find?_eq_some hf)
            (Level.substFn φ ci.toConstantVal.levelParams ws)
        have hAstored := (m.annot_ok ci (List.mem_of_find?_eq_some hf)
          (Level.substFn φ ci.toConstantVal.levelParams ws)).1
        refine ⟨⟨m.val n (Level.substFn φ ci.toConstantVal.levelParams ws), T, ?_, ?_, ?_⟩, ?_⟩
        · simp only [interpExpr, hf]
          rw [if_pos hal]
        · rw [interp_closed_invariant hcl]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          exact hT
        · have hname : ci.name = n := find?_name hf
          simp only [ConstantInfo.name] at hname
          rw [← hname]
          exact hmem
        · exact AnnotOk.closed_invariant hcl d ρ
            (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hAstored)
      next hal => exact nomatch h
  | .forallE n ty body m', h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_forallE hok
    simp only [AnnotOk] at ha
    obtain ⟨haty, ⟨v₀, hv₀⟩, hcond⟩ := ha
    obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hv₀ h
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨⟨A, tA, hA, htA, hmemA⟩, hAtA⟩ :=
      ihi hty hw.1 hb.1 hLbty hokty haty
    have hwtty := inferTypeCore_WScoped m.wf fuel hty hw.1
    have hbtty := inferTypeCore_looseBVars m.wf fuel hty hw.1 hb.1 hLbty
    have hLbtty : Expr.LeavesBounded tty := fun l hl =>
      hLbty l (inferTypeCore_fvarLeaves m.wf fuel hty hw.1 l hl)
    have hoktty : FvarsOk V m.val env φ d ρ tty :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hty hw.1) hokty
    rw [sort_result ihw hwt hwtty hbtty hLbtty hoktty hAtA] at htA
    obtain rfl := Option.some.inj htA
    refine ⟨⟨pi (v₀.eval φ) A (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      univ ((Level.imax u v₀).eval φ), ?_, ?_, ?_⟩, by simp [AnnotOk]⟩
    · simp only [interpExpr, hv₀, hA]
    · simp only [interpExpr]
    · have hpi := pi_mem_univ (V := V) (v := v₀.eval φ)
        (B := fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
        hmemA
        (fun x hx => by
          obtain ⟨-, hwfact⟩ := hcond x A hA hx
          obtain ⟨w, hwi, hmem⟩ := hwfact v₀ hv₀
          simpa [hwi] using hmem)
      have heq : Level.eval φ (.imax u v₀) =
          if v₀.eval φ = 0 then 0 else Nat.max (u.eval φ) (v₀.eval φ) := rfl
      rw [heq]
      exact hpi
  | .lam n ty body m', h =>
    obtain ⟨v, tty, u, bt, tbt, v', hc, htyi, hu, hbt, htbt, hwv, heqv, rfl⟩ :=
      inferTypeCore_lam_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
    simp only [AnnotOk] at ha
    obtain ⟨haty, -, hcond⟩ := ha
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    -- the domain interprets (via its own inference)
    obtain ⟨⟨A, tA, hA, -, -⟩, -⟩ :=
      ihi htyi hw.1 hb.1 hLbty hokty haty
    -- facts about the opened body
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
      hw.1.instantiate1 0 hw.2
    have hbo : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
      · exact hLb l (by simp [fvarLeaves, hb'])
      · simp only [fvarLeaves, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact hb.1
        · exact hLbty l hb'
    -- the abstraction roundtrip
    have hwbt := inferTypeCore_WScoped m.wf fuel hbt hwo
    have hrt : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
      abstract1_instantiate1 bt 0
        (Expr.fvarConsistent_of_leafCond bt (fun l hl hld =>
          Expr.LeafCond_opened hw.1 hw.2 0 l
            (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl) hld))
        (inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo)
    -- per-member facts about the body and its type
    have hfacts : ∀ x, x ∈ˢ A →
        (∃ w tw, interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          interpExpr V m.val env φ (d + 1) (updV V ρ d x) bt = some tw ∧
          w ∈ˢ tw ∧ tw ∈ˢ univ (v.eval φ)) ∧
        AnnotOk V m.val env φ (d + 1) (updV V ρ d x) bt := by
      intro x hx
      obtain ⟨hbodyA⟩ := hcond x A hA hx
      have hoko : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty)) :=
        FvarsOk.instantiate1 hw.1 hokty haty hA hx body 0 hw.2 hokbody
      obtain ⟨⟨w, tw, hwi, hbti, hmem⟩, hAbt⟩ :=
        ihi hbt hwo hbo hLbo hoko hbodyA
      -- the re-check gives the fibre's universe
      have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hbt hwo) hoko
      have hbbt : bt.looseBVarsBounded 0 = true :=
        inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo
      have hLbbt : Expr.LeavesBounded bt := fun l hl =>
        hLbo l (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl)
      obtain ⟨⟨vbt, tvbt, hbti2, htbti, hmem2⟩, hAtbt⟩ :=
        ihi htbt hwbt hbbt hLbbt hokbt hAbt
      have hwtbt := inferTypeCore_WScoped m.wf fuel htbt hwbt
      have hbtbt := inferTypeCore_looseBVars m.wf fuel htbt hwbt hbbt hLbbt
      have hLbtbt : Expr.LeavesBounded tbt := fun l hl =>
        hLbbt l (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt l hl)
      have hoktbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) tbt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt) hokbt
      rw [sort_result ihw hwv hwtbt hbtbt hLbtbt hoktbt hAtbt] at htbti
      obtain rfl := Option.some.inj htbti
      rw [hbti] at hbti2
      have hvbt : tw = vbt := Option.some.inj hbti2
      refine ⟨⟨w, tw, hwi, hbti, hmem, ?_⟩, hAbt⟩
      rw [Level.isEquiv_sound heqv φ, hvbt]
      exact hmem2
    -- assemble
    refine ⟨⟨SetTheory.lam (v.eval φ) A (fun x =>
        (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      pi (v.eval φ) A (fun x =>
        (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          ((bt.abstract1 d).instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      ?_, ?_, ?_⟩, ?_⟩
    · simp only [interpExpr, hc, hA]
    · simp only [interpExpr, hA]
    · refine lam_mem fun x hx => ?_
      obtain ⟨⟨w, tw, hwi, hbti, hmem, -⟩, -⟩ := hfacts x hx
      rw [hrt, hwi, hbti]
      simpa using hmem
    · -- annotation truthfulness of the inferred Π-type
      simp only [AnnotOk]
      refine ⟨haty, ⟨v, rfl⟩, ?_⟩
      intro x A' hA' hx
      rw [hA] at hA'
      obtain rfl := Option.some.inj hA'
      obtain ⟨⟨w, tw, hwi, hbti, hmem, htwu⟩, hAbt⟩ := hfacts x hx
      rw [hrt]
      refine ⟨hAbt, ?_⟩
      intro v'' hv''
      obtain rfl : v = v'' := by injection hv''
      exact ⟨tw, hbti, htwu⟩
  | .app f a, h =>
    obtain ⟨tf, n', ty', body', mPi, ta, htf, hwh, hta, hde, rfl⟩ :=
      inferTypeCore_app_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, -⟩ := ha
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    -- infer f, reduce its type to a Π
    obtain ⟨⟨vf, vtf, hfi, htfi, hmemf⟩, hAtf⟩ :=
      ihi htf hw.1 hb.1 hLbf hokf haf
    have hwtf := inferTypeCore_WScoped m.wf fuel htf hw.1
    have hbtf := inferTypeCore_looseBVars m.wf fuel htf hw.1 hb.1 hLbf
    have hLbtf : Expr.LeavesBounded tf := fun l hl =>
      hLbf l (inferTypeCore_fvarLeaves m.wf fuel htf hw.1 l hl)
    have hoktf : FvarsOk V m.val env φ d ρ tf :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htf hw.1) hokf
    obtain ⟨hiw, haPi⟩ := ihw hwh hwtf hbtf hLbtf hoktf hAtf
    have hwPi := whnf_WScoped m.wf fuel hwh hwtf
    have hbPi := whnf_looseBVars m.wf fuel hwh hbtf
    have hLbPi : Expr.LeavesBounded (Expr.forallE n' ty' body' mPi) := fun l hl =>
      hLbtf l (whnf_fvarLeaves m.wf fuel hwh l hl)
    have hokPi : FvarsOk V m.val env φ d ρ (.forallE n' ty' body' mPi) :=
      whnf_FvarsOk m.wf fuel hwh hoktf
    simp only [WScoped] at hwPi
    simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
    -- interpret the Π
    have hPii : interpExpr V m.val env φ d ρ (.forallE n' ty' body' mPi) = some vtf := by
      rw [hiw]; exact htfi
    rw [interpExpr] at hPii
    cases hcPi : mPi.cod with
    | none => rw [hcPi] at hPii; exact nomatch hPii
    | some vPi =>
    rw [hcPi] at hPii
    dsimp only at hPii
    cases htyPi : interpExpr V m.val env φ d ρ ty' with
    | none => rw [htyPi] at hPii; exact nomatch hPii
    | some A' =>
    rw [htyPi] at hPii
    simp only [Option.some.injEq] at hPii
    -- infer a; its type is defeq to the domain
    obtain ⟨⟨va, vta, hai, htai, hmema⟩, hAta⟩ :=
      ihi hta hw.2 hb.2 hLba hoka haa
    simp only [AnnotOk] at haPi
    obtain ⟨haty', -, hcond'⟩ := haPi
    have hLbta : Expr.LeavesBounded ta := fun l hl =>
      hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
    have hLbty' : Expr.LeavesBounded ty' := fun l hl =>
      hLbPi l (by simp [fvarLeaves, hl])
    have hAeq : vta = A' :=
      ihd hde
        (inferTypeCore_WScoped m.wf fuel hta hw.2) hwPi.1
        (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hbPi.1
        hLbta hLbty'
        (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
        ((FvarsOk.of_forallE hokPi).1)
        hAta haty' htai htyPi
    have hva : va ∈ˢ A' := hAeq ▸ hmema
    obtain ⟨hAopened, hwfact'⟩ := hcond' va A' htyPi hva
    obtain ⟨w', hwi', hmem'⟩ := hwfact' vPi hcPi
    have hfb' : fvarsBelow d body' := hwPi.2.fvarsBelow
    have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
      (n := n') (ty := ty') hfb' hw.2 hb.2 hai 0
    refine ⟨⟨SetTheory.app vf va, w', ?_, ?_, ?_⟩, ?_⟩
    · simp only [interpExpr]
      rw [hfi, hai]
    · rw [hbeta_eq]
      exact hwi'
    · have hpiM : vf ∈ˢ pi (vPi.eval φ) A'
          (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) := by
        rw [hPii]; exact hmemf
      have hfib : ∀ x, x ∈ˢ A' →
          ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) ∈ˢ
            univ (vPi.eval φ) := by
        intro x hx
        obtain ⟨-, hwf_x⟩ := hcond' x A' htyPi hx
        obtain ⟨w_x, hwi_x, hm_x⟩ := hwf_x vPi hcPi
        rw [hwi_x]
        simpa using hm_x
      have happ := app_mem hpiM hva hfib
      rw [hwi'] at happ
      simpa using happ
    · exact AnnotOk_beta hfb' hw.2 hb.2 hai haa 0 hAopened
  | .proj sn i e, h =>
    obtain ⟨te, us, A, B, cv, caps, hte, hwt, hfind, hcase⟩ := inferTypeCore_proj_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded] at hb
    have hLbe : Expr.LeavesBounded e := fun l hl => hLb l (by
      simp only [fvarLeaves]; exact hl)
    have hoke : FvarsOk V m.val env φ d ρ e := fun l hl => hok l (by
      simp only [fvarLeaves]; exact hl)
    simp only [AnnotOk] at ha
    obtain ⟨hae, -⟩ := ha
    obtain ⟨⟨ve, vte, hei, htei, hmem⟩, hAte⟩ := ihi hte hw hb hLbe hoke hae
    -- reduce the type to the pair form and transfer facts
    have hwte := inferTypeCore_WScoped m.wf fuel hte hw
    have hbte := inferTypeCore_looseBVars m.wf fuel hte hw hb hLbe
    have hLbte : Expr.LeavesBounded te := fun l hl =>
      hLbe l (inferTypeCore_fvarLeaves m.wf fuel hte hw l hl)
    have hokte : FvarsOk V m.val env φ d ρ te :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hte hw) hoke
    obtain ⟨hiw, haPi⟩ := ihw hwt hwte hbte hLbte hokte hAte
    have hPii : interpExpr V m.val env φ d ρ
        (.app (.app (.const psigmaName us) A) B) = some vte := by
      rw [hiw]; exact htei
    try simp only [AnnotOk] at haPi
    obtain ⟨haCA, haB, vf₁, vB, vE₁, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁, hfib₁⟩ := haPi
    try simp only [AnnotOk] at haCA
    obtain ⟨hac, haA, vf₀, vA, vE₀, A₀, B₀, hci, hAi, hpi₀, hvA₀, hfib₀⟩ := haCA
    -- the head is the pair former's value
    rw [interpExpr, hfind] at hci
    dsimp only [ConstantInfo.toConstantVal] at hci
    obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cv.levelParams us := ⟨_, rfl⟩
    rw [← hψ'] at hci
    by_cases hal : us.length = cv.levelParams.length
    case neg => simp only [hal, if_false] at hci; exact nomatch hci
    simp only [hal, if_true] at hci
    have hval : interpExpr V m.val env φ d ρ (.const psigmaName us) =
        some (m.val psigmaName ψ') := by
      rw [interpExpr, hfind]
      dsimp only [ConstantInfo.toConstantVal]
      rw [← hψ']
      simp only [hal, if_true]
    have hvf₀ : vf₀ = m.val psigmaName ψ' := (Option.some.inj hci).symm
    have hfacts := ((m.ind_ok.1 cv caps hfind).2 ψ')
    have hAmem : vA ∈ˢ univ (ψ' uN) := hfacts.dom₀ (hvf₀ ▸ hpi₀) hvA₀
    -- the partial application and its second argument
    have hf₁ : vf₁ = app (m.val psigmaName ψ') vA := by
      rw [interpExpr, hval, hAi] at hf₁i
      dsimp only at hf₁i
      exact (Option.some.inj hf₁i).symm
    have hBmem : vB ∈ˢ pi (ψ' vN + 1) vA (fun _ => univ (ψ' vN)) :=
      hfacts.dom₁ hAmem (hf₁ ▸ hpi₁) hvB₁
    -- the type's interpretation is the sigma set
    have hfold : vte = sigmaSet (Nat.max (ψ' uN) (ψ' vN)) vA (fun x => app vB x) := by
      rw [interpExpr, hf₁i, hBi] at hPii
      dsimp only at hPii
      have := Option.some.inj hPii
      rw [← this, hf₁, hfacts.fold hAmem hBmem]
    have hvemem : ve ∈ˢ sigmaSet (Nat.max (ψ' uN) (ψ' vN)) vA (fun x => app vB x) := by
      rw [← hfold]; exact hmem
    obtain ⟨a', b', ha', hb', hpt0, hpair⟩ := mem_sigma_elim hvemem
    have hu0 : Nat.max (ψ' uN) (ψ' vN) = 0 → ψ' uN = 0 := fun hw0 =>
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw0))
    have hv0 : Nat.max (ψ' uN) (ψ' vN) = 0 → ψ' vN = 0 := fun hw0 =>
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw0))
    have hsfst : sfst ve ∈ˢ vA := by
      by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
      · rw [hpt0 hw0, sfst_pt]
        have hA0 : vA ∈ˢ univ 0 := (hu0 hw0) ▸ hAmem
        have := mem_univ_zero hA0 ha'
        rwa [← this]
      · rw [hpair hw0, sfst_spair]
        exact ha'
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- i = 0 : the first component
      refine ⟨⟨sfst ve, vA, ?_, hAi, hsfst⟩, haA⟩
      simp only [interpExpr, hei]
      rfl
    · -- i = 1 : the second component
      have hproj0 : interpExpr V m.val env φ d ρ (.proj sn 0 e) = some (sfst ve) := by
        simp only [interpExpr, hei]
        rfl
      have hfib : ∀ x, x ∈ˢ vA → app vB x ∈ˢ univ (ψ' vN) := fun x hx =>
        app_mem hBmem hx fun _ _ => univ_mem_univ _
      have hssnd : ssnd ve ∈ˢ app vB (sfst ve) := by
        by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
        · rw [hpt0 hw0, ssnd_pt, sfst_pt]
          have hA0 : vA ∈ˢ univ 0 := (hu0 hw0) ▸ hAmem
          have hapt : a' = pt := mem_univ_zero hA0 ha'
          have hb'' : b' ∈ˢ app vB pt := hapt ▸ hb'
          have hB0 : app vB pt ∈ˢ univ 0 := (hv0 hw0) ▸ hfib pt (hapt ▸ ha')
          have hbpt : b' = pt := mem_univ_zero hB0 hb''
          exact hbpt ▸ hb''
        · rw [hpair hw0, ssnd_spair, sfst_spair]
          exact hb'
      refine ⟨⟨ssnd ve, app vB (sfst ve), ?_, ?_, hssnd⟩, ?_⟩
      · simp only [interpExpr, hei]
        rfl
      · simp only [interpExpr, hBi, hproj0]
      · -- AnnotOk of `app B (proj sn 0 e)`
        simp only [AnnotOk]
        refine ⟨haB, ?_, vB, sfst ve, ψ' vN + 1, vA, (fun _ => univ (ψ' vN)),
          hBi, hproj0, hBmem, hsfst, fun _ _ => univ_mem_univ _⟩
        exact ⟨hae, by omega, ve, ψ' uN, ψ' vN, vA, (fun x => app vB x),
          hei, hvemem, hAmem, hfib⟩
  | .bvar i, h => simp [inferTypeCore] at h
  | .letE n' t' v' b', h => simp [inferTypeCore] at h
  | .lit l', h => simp [inferTypeCore] at h

end Claims

/-- The mutual soundness induction; see the module docstring. -/
theorem check_sound (m : EnvModel V env) :
    ∀ (fuel : Nat), WhnfClaims m φ fuel ∧ DefEqClaims m φ fuel ∧ InferClaims m φ fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ihAll =>
    match fuel with
    | 0 =>
      refine ⟨?_, ?_, ?_⟩
      · intro d e e' ρ h
        exact nomatch h
      · intro d a b ρ h
        exact nomatch h
      · intro d e t ρ h
        exact nomatch h
    | fuel + 1 =>
      obtain ⟨ihw, ihd, ihi⟩ := ihAll fuel (by omega)
      exact ⟨whnf_claims m ihw ihd ihi (fun f hf => ihAll f (by omega)),
        defeq_claims m ihw ihd ihi (fun f hf => ihAll f (by omega)),
        infer_claims m ihw ihd ihi⟩

/-! ## Fuel-generic core soundness lemmas -/

/-- Reduction preserves the interpretation and annotation truthfulness
(explicit fuel). -/
theorem whnfCore_facts (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e e' : Expr} {ρ : Nat → V}
    (h : whnfCore env fuel d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m fuel).1 h hw hb hLb hok ha

/-- Definitional equality identifies interpretations (explicit fuel). -/
theorem isDefEqCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {a b : Expr} {ρ : Nat → V}
    (h : isDefEqCore env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  (check_sound m fuel).2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab
    hva hvb

/-- Successful inference is sound (explicit fuel). -/
theorem inferTypeCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e t : Expr} {ρ : Nat → V}
    (h : inferTypeCore env fuel d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m fuel).2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf fuel h hw, this.2⟩

/-- A successful `ensureSortCore` identifies the interpretation of the
type with a universe (explicit fuel). -/
theorem ensureSortCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {t : Expr} {u : Level}
    (h : ensureSortCore env fuel d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSortCore at h
  cases hwh : whnfCore env fuel d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnfCore_facts m fuel hwh hw hb hLb hok ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure,
      interpExpr]

/-! ## Fuel-instantiated wrappers -/

/-- Reduction preserves the interpretation and annotation truthfulness. -/
theorem whnf_facts (m : EnvModel V env) {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : whnf env d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m checkFuel).1 h hw hb hLb hok ha

/-- A positive definitional-equality verdict means the interpretations
agree, whenever both are defined. -/
theorem isDefEq_sound (m : EnvModel V env) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  (check_sound m checkFuel).2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab hva hvb

/-- Successful inference is sound (bundled with syntactic
well-scopedness of the output). -/
theorem inferType_sound (m : EnvModel V env) {d : Nat} {e t : Expr} {ρ : Nat → V}
    (h : inferType env d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m checkFuel).2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf checkFuel h hw, this.2⟩

/-- A successful `ensureSort` identifies the interpretation of the type
with a universe. -/
theorem ensureSort_sound (m : EnvModel V env) {d : Nat} {t : Expr} {u : Level}
    (h : ensureSort env d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSort at h
  cases hwh : whnf env d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnf_facts m hwh hw hb hLb hok ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure, interpExpr]

end Setlec
