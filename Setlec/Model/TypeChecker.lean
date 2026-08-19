import Setlec.Kernel.TypeChecker
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves

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
      obtain ⟨us, cv, rfl, hfind⟩ := isUnitLikeTy_inv hux
      rw [hTxi] at hiw
      simp only [interpExpr, hfind] at hiw
      by_cases hlen : us.length =
          (ConstantInfo.indInfo cv).toConstantVal.levelParams.length
      · rw [if_pos hlen] at hiw
        have hTx : Tx = m.val punitName
            (Level.substFn φ (ConstantInfo.indInfo cv).toConstantVal.levelParams us) :=
          (Option.some.inj hiw).symm
        rw [hxi]
        have hpt := m.ind_ok.right.right cv hfind
          (Level.substFn φ (ConstantInfo.indInfo cv).toConstantVal.levelParams us)
          vx (hTx ▸ hmemx)
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
  obtain ⟨us, pα, pβ, s₁, s₂, cvm, nP, nF, tb, us', A, B, cvi,
    rfl, hfindM, htb, hwtb, hfindI, hlev, hd1, hd2⟩ := pairEtaCert_inv h
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
  obtain ⟨hlpI, htyf⟩ := m.ind_ok.1 cvi hfindI
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
  obtain ⟨hnP2, hnF2, hlpM, hmkfAll⟩ := m.ind_ok.right.left cvm nP nF hfindM
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
          obtain ⟨-, -, -, -, hval⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
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
      | indInfo cv => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
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
    rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, hcert⟩ | rfl
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
        obtain ⟨htc, -, -, -, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
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
    obtain ⟨te, us, A, B, cv, hte, hwt, hfind, hcase⟩ := inferTypeCore_proj_inv h
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
    have hfacts := ((m.ind_ok.1 cv hfind).2 ψ')
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
