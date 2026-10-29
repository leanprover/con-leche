module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.Denote.Closed
import ConLeche.Semantics.LitStep

public section

/-!
# The soundness of the reduction rules (task #305)

One lemma per constructor of `Red`: the motives of its derivation
premises (the induction hypotheses) and its side conditions give the
motive of its conclusion.  The master induction (`Sound.lean`) is the
only place that mentions derivations; these lemmas are pure semantics.
`iota` and the three rescues are in `IotaSound.lean`.

Each rule is proved at the conditional motive `RedSem` (task #342, L9).
Where a rule reads no reduction or comparison claim, the conditional
lemma is an unconditional one (`…_soundU`, `RedSemU`) weakened.  β reads
no premise (`Red.beta_sound`).  The
two literal accelerations at the conditional motive (task #342, L12)
recover the argument's membership in `Nat` from the head's graph
(`arg_mem_of_head`) and equate it with its literal inside the type `Nat`
(`IsTy.eq_of_ne_pt`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-! ## Refl, trans, and the two congruences -/

theorem Red.refl_soundU {d : Nat} {e : Expr} : RedSemU m φ d e e := by
  intro hf Δa ea _ hea
  exact ⟨hf, fun _ hl => hl, ea, hea, fun _ _ _ hg => ⟨hg, rfl⟩⟩

theorem Red.refl_sound {d : Nat} {e : Expr} : RedSem m φ d e e :=
  Red.refl_soundU.cond

theorem Red.trans_sound {d : Nat} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ d e₁ e₂) (h₂ : RedSem m φ d e₂ e₃) :
    RedSem m φ d e₁ e₃ := by
  intro hf Δa ea hC hea
  obtain ⟨hf₂, hsub₂, ea₂, hea₂, hs₂⟩ := h₁ hf hC hea
  obtain ⟨hf₃, hsub₃, ea₃, hea₃, hs₃⟩ := h₂ hf₂ (hC.of_subset hsub₂) hea₂
  refine ⟨hf₃, fun l hl => hsub₂ l (hsub₃ l hl), ea₃, hea₃,
    fun ρ hρ hL hg hne => ?_⟩
  obtain ⟨hg₂, heq₂⟩ := hs₂ ρ hρ hL hg hne
  obtain ⟨hg₃, heq₃⟩ := hs₃ ρ hρ (hL.of_subset hsub₂) hg₂ (heq₂ ▸ hne)
  exact ⟨hg₃, heq₂.trans heq₃⟩

/-- The syntactic side of head reduction under an application. -/
theorem appFn_syntax {d : Nat} {f f' a : Expr}
    (hws : Expr.WScoped d (.app f a)) (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a)) (hff : Frame d f')
    (hsubf : LeavesSub f' f) :
    Frame d (.app f' a) ∧ LeavesSub (.app f' a) (.app f a) := by
  obtain ⟨hwf', hbf', hLf'⟩ := hff
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨⟨by simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩, by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf', hb.2⟩, fun l hl => ?_⟩, fun l hl => ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hLf' l hl
    · exact hLb l (by simp [Expr.fvarLeaves, hl])
  · simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (hsubf l hl)
    · exact Or.inr hl

/-- The app slot rides an equal-valued, graded head. -/
theorem wellDenoted_app_fn_congr {ρ : Nat → V} {fa fa' aa : Term}
    (heq : interp V ρ fa = interp V ρ fa') (hgf' : WellDenoted V ρ fa')
    (hg : WellDenoted V ρ (.app fa aa)) : WellDenoted V ρ (.app fa' aa) := by
  have hx1 := hg
  rw [WellDenoted_app] at hx1 ⊢
  obtain ⟨-, hoka1, v', A, B, h1, h2, h3⟩ := hx1
  exact ⟨hgf', hoka1, v', A, B, heq ▸ h1, h2, h3⟩

/-- Head reduction under an application: the argument rides along.
"Not pt" source (2): the application is not the point, so its head is
not (`app_pt`). -/
theorem Red.appFn_sound {d : Nat} {f f' a : Expr}
    (hf : RedSem m φ d f f') : RedSem m φ d (.app f a) (.app f' a) := by
  intro hfr Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  have hws' := hws
  have hb' := hb
  simp only [Expr.WScoped] at hws'
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb'
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hea
  obtain ⟨hff', hsubf, fa', hfa', hsf⟩ := hf ⟨hws'.1, hb'.1, hLf⟩ hC.app_fn hfa
  obtain ⟨hfr', hsub'⟩ := appFn_syntax hws hb hLb hff' hsubf
  refine ⟨hfr', hsub', .app fa' aa, by rw [denote_app, hfa', haa]; rfl,
    fun ρ hρ hL hg hne => ?_⟩
  have hnf : interp V ρ fa ≠ pt := by
    intro h; apply hne; rw [interp_app, h, app_pt]
  obtain ⟨hgf', heqf⟩ := hsf ρ hρ hL.app_fn hg.app_fn hnf
  exact ⟨wellDenoted_app_fn_congr heqf hgf' hg,
    by rw [interp_app, interp_app, heqf]⟩

/-- The `.proj` clause's scrutinee reduction (`ProjAV.congrV`).
"Not pt" source (2): a projection of the point is the point
(`projS_pt`, `sfst_pt`, `ssnd_pt`), so a projection that is not the
point has a scrutinee that is not. -/
theorem Red.projArg_sound {d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr} (he : RedSem m φ d e e') :
    RedSem m φ d (.proj sn i e) (.proj sn i e') := by
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hsube : ∀ l ∈ e.fvarLeaves, l ∈ (Expr.proj sn i e).fvarLeaves :=
    fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hLe : Expr.LeavesBounded e := fun l hl => hLb l (hsube l hl)
  have hCe : CtxOkS m φ d Δa e := hC.of_subset hsube
  obtain ⟨vp, entry, hvp, hfe, rfl⟩ := denote_proj_inv hea
  obtain ⟨⟨hw', hb', hL'⟩, hsub, vp', hvp', hs⟩ := he ⟨hws, hb, hLe⟩ hCe hvp
  refine ⟨⟨by simp only [Expr.WScoped]; exact hw',
      by simp only [Expr.looseBVarsBounded]; exact hb',
      fun l hl => hL' l (by simpa [Expr.fvarLeaves] using hl)⟩,
    fun l hl => hsube l (hsub l (by simpa [Expr.fvarLeaves] using hl)), ?_⟩
  refine ⟨projNV (i + 1) vp', ?_, fun σ hσ hL hg hne => ?_⟩
  · rw [denote, hvp', hfe]; rfl
  have hnv : interp V σ vp ≠ pt := by
    intro h; apply hne; rw [projNV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
  obtain ⟨hg', heq⟩ := hs σ hσ (hL.of_subset hsube) (ProjAV.hoistV hg) hnv
  exact ⟨ProjAV.congrV heq hg' hg, ProjAV.interp_congr heq⟩

/-! ## β -/

/-- The β redex's syntactic side: the reduct's frame, its leaf inclusion
and its reading. -/
theorem beta_syntax {d : Nat} {ty body a : Expr}
    {ba aa : Term}
    (hws : Expr.WScoped d (.app (.lam ty body) a))
    (hb : (Expr.app (.lam ty body) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.lam ty body) a))
    (hbb : denote m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some ba)
    (haa : denote m.acval env φ d a = some aa) :
    Frame d (body.instantiate1 a) ∧
      LeavesSub (body.instantiate1 a) (.app (.lam ty body) a) ∧
      denote m.acval env φ d (body.instantiate1 a) = some (ba.inst aa) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hsubred : LeavesSub (body.instantiate1 a) (.app (.lam ty body) a) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  refine ⟨⟨ConLeche.Expr.WScoped.instantiate1_gen hws.2 0 hws.1.2,
      ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.2 hb.1.2,
      fun l hl => hLb l (hsubred l hl)⟩, hsubred, ?_⟩
  rw [denote_beta m.acval_closed (acval_inst_self m)
    (ty := ty) hws.1.2.fvarsBelow hws.2 hb.2 haa 0, hbb]
  rfl

/-- **β, with no certificate** (task #342, L9; L14a).  A redex that is
not the point has a λ that is not the point ("not pt" source (2): the
point applied is the point), so the λ is a graph whose domain the
application slot fixes, and β is `app_lamV` at a graded argument
(`betaV`). -/
theorem Red.beta_sound {d : Nat} {ty body a : Expr} :
    RedSem m φ d (.app (.lam ty body) a) (body.instantiate1 a) := by
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hea
  obtain ⟨tya, ba, htya, hbb, rfl⟩ := denote_lam_inv hfa
  obtain ⟨hfr, hsub, hred⟩ := beta_syntax hws hb hLb hbb haa
  refine ⟨hfr, hsub, ba.inst aa, hred, fun ρ _ _ hg hne => ?_⟩
  obtain ⟨h1, h2⟩ := betaV hg hne
  exact ⟨h2, h1⟩

/-! ## ζ, δ and the literal expansions: no claim read -/

/-- **ζ**: a `let` and its reduct interpret alike at every valuation
(`interp_zeta`), and with the value graded (a part of the `let`'s
grading) the reduct is graded (`WellDenoted_zeta _`). -/
theorem Red.zeta_soundU {d : Nat} {ty v body : Expr} :
    RedSemU m φ d (.letE ty v body) (body.instantiate1 v) := by
  intro hf Δa ea hC hea
  obtain ⟨-, va, ba, -, hva, hba, rfl⟩ := denote_letE_inv hea
  obtain ⟨hfr, hsub, hred⟩ := zeta_syntax hf hva hba
  exact ⟨hfr, hsub, ba.inst va, hred,
    fun ρ _ _ hg => ⟨(WellDenoted_zeta _ hg.letE_val).mp hg, interp_zeta V va ba ρ⟩⟩

theorem Red.zeta_sound {d : Nat} {ty v body : Expr} :
    RedSem m φ d (.letE ty v body) (body.instantiate1 v) :=
  Red.zeta_soundU.cond

/-- The δ identity (the unfolding reads and interprets as the subject,
`denote_unfoldDefinition`) + `unfoldDefinition_WScoped`. -/
theorem Red.delta_soundU (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : ConLeche.unfoldDefinition env e = some e') : RedSemU m φ d e e' := by
  intro hf Δa ea _ hea
  refine ⟨⟨ConLeche.unfoldDefinition_WScoped m.wf h hf.1,
      ConLeche.unfoldDefinition_looseBVars m.wf h hf.2.1,
      fun l hl => hf.2.2 l (ConLeche.unfoldDefinition_fvarLeaves m.wf h l hl)⟩,
    fun l hl => ConLeche.unfoldDefinition_fvarLeaves m.wf h l hl,
    (denote_unfoldDefinition hin.defn h hea).imp fun _ h' =>
      ⟨h'.1, fun ρ _ _ hg => h'.2 ρ hg⟩⟩

theorem Red.delta_sound (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : ConLeche.unfoldDefinition env e = some e') : RedSem m φ d e e' :=
  (Red.delta_soundU hin h).cond

/-- `denote_natLitToConstructor`: the expansion has the literal's reading. -/
theorem Red.natLit_soundU {d n : Nat} (h : ConLeche.natLitSupported env = true) :
    RedSemU m φ d (.lit (.natVal n)) (natLitToConstructor n) := by
  intro _ Δa ea _ hea
  refine ⟨⟨ConLeche.natLitToConstructor_WScoped n,
      ConLeche.natLitToConstructor_looseBVars n, ?_⟩, ?_, ea, ?_,
    fun _ _ _ hg => ⟨hg, rfl⟩⟩
  · intro l hl
    rw [ConLeche.natLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · intro l hl
    rw [ConLeche.natLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · rw [denote_natLitToConstructor h]; exact hea

theorem Red.natLit_sound {d n : Nat} (h : ConLeche.natLitSupported env = true) :
    RedSem m φ d (.lit (.natVal n)) (natLitToConstructor n) :=
  (Red.natLit_soundU h).cond

/-- `denote_strLitToConstructor`: the expansion has the literal's reading. -/
theorem Red.strLit_soundU {d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    RedSemU m φ d (.lit (.strVal s)) (strLitToConstructor s) := by
  intro _ Δa ea _ hea
  refine ⟨⟨ConLeche.strLitToConstructor_WScoped s d,
      ConLeche.strLitToConstructor_looseBVars s 0, ?_⟩, ?_, ea, ?_,
    fun _ _ _ hg => ⟨hg, rfl⟩⟩
  · intro l hl
    rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · intro l hl
    rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · rw [denote_strLitToConstructor h]; exact hea

theorem Red.strLit_sound {d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    RedSem m φ d (.lit (.strVal s)) (strLitToConstructor s) :=
  (Red.strLit_soundU h).cond

/-! ## The literal accelerations at the conditional motive (task #342, L12)

The argument's claim is conditional: it equates the argument with its
literal only where the argument is not the point.  The argument lies in
`Nat`: the redex is not the point, so neither is the head ("not pt"
source (2), `app_pt`), and the head's graph fixes its domain to `Nat`
(`piR_dom_unique` against `NatHeads`' `Nat.succ` or `NatOpHead`).  The
literal lies in `Nat` too, and `Nat` is a type, so the two are equal even
where the argument is the point (`IsTy.eq_of_ne_pt`). -/

/-- **The argument of an application that is not the point lies in its
head's domain**: the head is not the point (`app_pt`), so it is read at a
positive kind (`eq_pt_of_mem_piR_zero`), where its graph fixes its domain
(`piR_dom_unique`). -/
theorem arg_mem_of_head {σ : Nat → V} {f a : Term} {b : Nat} {N : V}
    {Y : V → V} (hg : WellDenoted V σ (.app f a))
    (hne : interp V σ (.app f a) ≠ pt) (hf : interp V σ f ∈ˢ piR b N Y) :
    interp V σ a ∈ˢ N := by
  have hw := hg
  rw [WellDenoted_app] at hw
  obtain ⟨-, -, v, A, B, hfv, ha, -, -⟩ := hw
  have hfne : interp V σ f ≠ pt := fun h => hne (by rw [interp_app, h, app_pt])
  have hv : v ≠ 0 := fun h => hfne (eq_pt_of_mem_piR_zero (h ▸ hfv))
  have hb : b ≠ 0 := fun h => hfne (eq_pt_of_mem_piR_zero (h ▸ hf))
  rw [piR_dom_unique hv hb hfv hf] at ha
  exact ha

/-- **A literal reading** (`rawNatLit?`'s two shapes) is graded and lies in
the `Nat` leaf, at every valuation (`NatHeads`). -/
theorem rawNatLit_facts (hin : RulesInputs V m φ)
    (hsup : ConLeche.natLitSupported env = true) {d : Nat} {w : Expr} {n : Nat}
    (hn : ConLeche.rawNatLit? w = some n) {wa : Term}
    (hwa : denote m.acval env φ d w = some wa) (σ : Nat → V) :
    WellDenoted V σ wa ∧
      interp V σ wa ∈ˢ interp V σ (m.acval natName (Level.substFn φ [] [])) := by
  have hlit : denote m.acval env φ d (.lit (.natVal n)) = some wa := by
    match w, hn with
    | .lit (.natVal k), hn =>
      obtain rfl : k = n := Option.some.inj hn
      exact hwa
    | .const c [], hn =>
      simp only [ConLeche.rawNatLit?] at hn
      split at hn
      · next hc =>
        subst hc
        obtain rfl : (0 : Nat) = n := Option.some.inj hn
        rw [← denote_natLitToConstructor hsup d 0]
        exact hwa
      · exact nomatch hn
  rw [denote, ite_eq_left hsup] at hlit
  obtain rfl := (Option.some.inj hlit).symm
  have hf := natLit_factsAV (m.acval_wellDenoted _ _ σ) (m.acval_wellDenoted _ _ σ)
    (hin.nat_heads hsup σ).1 (hin.nat_heads hsup σ).2.1 (hin.nat_heads hsup σ).2.2 n
  exact ⟨hf.1, hf.2⟩

/-- The successor row at the reduced argument, at the conditional motive. -/
theorem Red.natSucc_sound (hin : RulesInputs V m φ) {d : Nat} {a w : Expr}
    {n : Nat} (hsup : ConLeche.natLitSupported env = true)
    (hw : RedSem m φ d a w) (hn : ConLeche.rawNatLit? w = some n) :
    RedSem m φ d (.app (.const natSuccName []) a) (.lit (.natVal (n + 1))) := by
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hea
  rw [denoteNatSuccConst hsup] at hfa
  obtain rfl := Option.some.inj hfa
  obtain ⟨-, -, wa, hwa, hsw'⟩ := hw ⟨hws.2, hb.2, hLa⟩ hC.app_arg haa
  have hsw : denote m.acval env φ d (.app (.const ConLeche.natSuccName []) w)
      = some (.app (m.acval natSuccName (Level.substFn φ [] [])) wa) := by
    rw [denote_app, denoteNatSuccConst hsup, hwa]; rfl
  obtain ⟨ra, hra, hrow⟩ := hin.nat_succ hsup hn hsw
  obtain ⟨hfr, hsubr⟩ := frame_atom (d := d) (e := .lit (.natVal (n + 1)))
    (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
    (by simp [Expr.looseBVarsBounded])
  refine ⟨hfr, hsubr _, ra, hra, fun σ hσ hL hg hne => ?_⟩
  obtain ⟨hgw, hwN⟩ := rawNatLit_facts hin hsup hn hwa σ
  -- the argument lies in `Nat`: "not pt" source (2), through the head's graph
  have haN := arg_mem_of_head hg hne (hin.nat_heads hsup σ).2.1
  -- the argument is the literal: two members of the type `Nat`
  have heqw : interp V σ aa = interp V σ wa :=
    (hin.nat_heads hsup σ).2.2.eq_of_ne_pt haN hwN fun hane _ =>
      (hsw' σ hσ hL.app_arg hg.app_arg hane).2
  obtain ⟨hgra, heqra⟩ := hrow σ (appCongrV rfl heqw hg.app_fn hgw hg)
  refine ⟨hgra, ?_⟩
  rw [interp_app, heqw, ← interp_app]
  exact heqra

/-- The binary row at the reduced arguments, at the conditional motive. -/
theorem Red.natOp_sound (hin : RulesInputs V m φ) {d : Nat} {c : Name}
    {a wa b wb r : Expr} {n₁ n₂ : Nat}
    (hc : c ∈ natBinOpNames) (hst : ConLeche.natOpStored env c = true)
    (hwa : RedSem m φ d a wa) (hn₁ : ConLeche.rawNatLit? wa = some n₁)
    (hwb : RedSem m φ d b wb) (hn₂ : ConLeche.rawNatLit? wb = some n₂)
    (hr : ConLeche.natOpResult c n₁ n₂ = some r) :
    RedSem m φ d (.app (.app (.const c []) a) b) r := by
  intro hf Δa ea hC hea
  obtain ⟨hsup, hhead⟩ := hin.nat_op_head hc hst
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbb : Expr.LeavesBounded b := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨ga, ba, hga, hba, rfl⟩ := denote_app_inv hea
  obtain ⟨ca, aa, hca, haa, rfl⟩ := denote_app_inv hga
  obtain ⟨-, -, waA, hwaA, hsa⟩ :=
    hwa ⟨hws.1.2, hb.1.2, hLa⟩ hC.app_fn.app_arg haa
  obtain ⟨-, -, wbA, hwbA, hsb⟩ :=
    hwb ⟨hws.2, hb.2, hLbb⟩ hC.app_arg hba
  have hsw : denote m.acval env φ d (.app (.app (.const c []) wa) wb)
      = some (.app (.app ca waA) wbA) := by
    rw [denote_app, denote_app, hca, hwaA, hwbA]; rfl
  obtain ⟨ra, hra, hrow⟩ := hin.nat_op hc hst hn₁ hn₂ hr hsw
  obtain ⟨hfr, hsubr⟩ : Frame d r ∧ ∀ (x : Expr), LeavesSub r x := by
    rcases ConLeche.natOpResult_shape hr with ⟨k, rfl⟩ | ⟨bn, rfl⟩
    · exact frame_atom (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
        (by simp [Expr.looseBVarsBounded])
    · exact frame_atom (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
        (by simp [Expr.looseBVarsBounded])
  refine ⟨hfr, hsubr _, ra, hra, fun σ hσ hL hg hne => ?_⟩
  obtain ⟨hgwaA, hwaN⟩ := rawNatLit_facts hin hsup hn₁ hwaA σ
  obtain ⟨hgwbA, hwbN⟩ := rawNatLit_facts hin hsup hn₂ hwbA σ
  have hNty := (hin.nat_heads hsup σ).2.2
  obtain ⟨b₁, b₂, X, hmem⟩ := hhead hca σ
  -- the partial application is not the point: "not pt" source (2)
  have hne₁ : interp V σ (.app ca aa) ≠ pt := fun h =>
    hne (by rw [interp_app, h, app_pt])
  have hcne : interp V σ ca ≠ pt := fun h => hne₁ (by rw [interp_app, h, app_pt])
  have hb₁ : b₁ ≠ 0 := fun h => hcne (eq_pt_of_mem_piR_zero (h ▸ hmem))
  -- both arguments lie in `Nat`, through the head's graph
  have haN := arg_mem_of_head hg.app_fn hne₁ hmem
  have hmem₂ : interp V σ (.app ca aa) ∈ˢ
      piR b₂ (interp V σ (m.acval natName (Level.substFn φ [] []))) (fun _ => X) := by
    rw [interp_app]
    exact app_mem_piR_pos hb₁ hmem haN
  have hbN := arg_mem_of_head hg hne hmem₂
  -- each is its literal: two members of the type `Nat`
  have heqa : interp V σ aa = interp V σ waA :=
    hNty.eq_of_ne_pt haN hwaN fun hane _ =>
      (hsa σ hσ hL.app_fn.app_arg hg.app_fn.app_arg hane).2
  have heqb : interp V σ ba = interp V σ wbA :=
    hNty.eq_of_ne_pt hbN hwbN fun hbne _ =>
      (hsb σ hσ hL.app_arg hg.app_arg hbne).2
  have hgsw : WellDenoted V σ (.app (.app ca waA) wbA) :=
    appCongrV (by rw [interp_app, interp_app, heqa]) heqb
      (appCongrV rfl heqa hg.app_fn.app_fn hgwaA hg.app_fn)
      hgwbA hg
  obtain ⟨hgra, heqra⟩ := hrow σ hgsw
  refine ⟨hgra, ?_⟩
  rw [interp_app, interp_app, heqa, heqb, ← interp_app, ← interp_app]
  exact heqra

/-- The tower law's iota clause at the arity-checked spine
(`teleFit_of_teleFitPA`): conditional on the point — a projection that
is not the point has a scrutinee that is not (`projS_pt`), whose spine
the arity-checked walk then fits ("not pt" source (2)). -/
theorem Red.proj_sound (hin : RulesInputs V m φ) {d : Nat} {sn : Name} {i : Nat}
    {e : Expr} {entry : ProjEntry} {us : List Level} {cvC : ConstantVal}
    {nP nF : Nat}
    (hent : env.findProj? sn i = some entry)
    (hhead : e.getAppFn = .const entry.ctor us)
    (hi : i < entry.numFields)
    (hlen : e.getAppArgs.length = entry.numParams + entry.numFields)
    (hus : us.length = entry.levelParams.length)
    (hfire : entry.fireOk us = true)
    (hctor : env.find? entry.ctor = some (.ctorInfo cvC nP nF))
    (hcerts : TeleAritySem m φ d
      (cvC.type.instantiateLevelParams cvC.levelParams us) e.getAppArgs) :
    RedSem m φ d (.proj sn i e)
      (e.getAppArgs.getD (entry.numParams + i) (.bvar 0)) := by
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hsube : ∀ l ∈ e.fvarLeaves, l ∈ (Expr.proj sn i e).fvarLeaves :=
    fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hLe : Expr.LeavesBounded e := fun l hl => hLb l (hsube l hl)
  have hCe : CtxOkS m φ d Δa e := hC.of_subset hsube
  obtain ⟨vp, -, hvp, -, rfl⟩ := denote_proj_inv hea
  -- the tower entry's laws
  obtain ⟨-, -, -, -, hO5, cvC₀, hfC, hlpsC, hlaw, -⟩ := hin.tower_ok sn i entry hent
  obtain rfl : cvC₀ = cvC := by
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hctor))
    rfl
  obtain ⟨-, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
  -- the constructor spine, read at the constructor's leaf
  have he₃ : e = Expr.mkAppN (.const entry.ctor us) e.getAppArgs := by
    rw [← hhead]; exact (ConLeche.Expr.mkAppN_getApp e).symm
  have hvp' := hvp
  rw [he₃] at hvp'
  obtain ⟨vf, vs, hvf, hspa, hveq⟩ := denote_mkAppN_inv hvp'
  have hlenC : us.length = (ConstantInfo.ctorInfo cvC₀ entry.numParams
      entry.numFields).toConstantVal.levelParams.length := by
    show us.length = cvC₀.levelParams.length
    rw [hlpsC]; exact hus
  rw [denote_const hfC hlenC] at hvf
  obtain rfl : vf = m.acval entry.ctor (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsC]; exact (Option.some.inj hvf).symm
  -- the selected argument's frame and reading
  have hidx : entry.numParams + i < e.getAppArgs.length := by rw [hlen]; omega
  have hmemArg : e.getAppArgs.getD (entry.numParams + i) (.bvar 0)
      ∈ e.getAppArgs := ConLeche.getD_mem hidx
  obtain ⟨hfF, -⟩ := frame_spine ⟨hws, hb, hLe⟩ hCe _ hmemArg
  have hlenVs : vs.length = entry.numParams + entry.numFields := by
    rw [← hspa.length]; exact hlen
  have hfvd : denote m.acval env φ d
      (e.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = some (vs.getD (entry.numParams + i) default) := hspa.getD_read hidx
  -- the constructor type's frame and reading
  have hwfC := m.wf.consts _ (ConLeche.Env.find?_mem hfC)
  have hnfC : (cvC₀.type.instantiateLevelParams cvC₀.levelParams us).hasFvar
      = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have hbdC : (cvC₀.type.instantiateLevelParams cvC₀.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfC.2.2.2.1
  have hTCd : denote m.acval env φ d
      (cvC₀.type.instantiateLevelParams cvC₀.levelParams us) = some TCa :=
    denote_depth_of_closed m.acval_closed hnfC
      (fun k => denote_liftN_eq_self m.cval_closed hnfC hbdC hTCa 1 k)
      hTCa d
  have hTC : CtxOkS m φ d Δa
      (cvC₀.type.instantiateLevelParams cvC₀.levelParams us) :=
    ⟨hC.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfC] at hl
      exact nomatch hl⟩
  obtain ⟨TCa', hTCa', hokTCa, hmemC0⟩ := hin.const_ty 0 entry.ctor _ us hfC
    (by show us.length = cvC₀.levelParams.length; rw [hlpsC]; exact hus)
  obtain rfl : TCa = TCa' := Option.some.inj (hTCa.symm.trans hTCa')
  -- the ∀-chain, off the head data's arity pin
  obtain ⟨cvC'', hfC'', -, hstrip⟩ := (m.proj_ok.towerHead hent).2.2.2.2.2
  obtain ⟨rfl, -, -⟩ :=
    ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC''))
  have hpc : PiChain e.getAppArgs.length TCa := by
    rw [hlen]
    exact piChain_of_stripPis (entry.numParams + entry.numFields)
      (ConLeche.Expr.stripPis_instantiateLevelParams_isSome cvC₀.levelParams us _
        hstrip) hTCd
  -- the arity-checked walk, read outside the valuation
  obtain ⟨resta, hfitA⟩ :=
    hcerts (fa := m.acval entry.ctor (Level.substFn φ entry.levelParams us))
      ⟨ConLeche.Expr.WScoped.of_not_hasFvar hnfC, hbdC,
        ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfC⟩
      hTC hTCd (frame_spine ⟨hws, hb, hLe⟩ hCe) hspa
  refine ⟨hfF, fun l hl => hsube l (ConLeche.fvarLeaves_getAppArgs hmemArg l hl),
    vs.getD (entry.numParams + i) default, hfvd, fun σ hσ hL hg hne => ?_⟩
  have hgvp : WellDenoted V σ (Term.mkAppN
      (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) vs) := by
    rw [← hveq]
    exact ProjAV.hoistV hg
  obtain ⟨-, hoA⟩ := hoist_spineV vs hgvp
  have hokArg : WellDenoted V σ (vs.getD (entry.numParams + i) default) :=
    hoA _ (ConLeche.getD_mem (by rw [hlenVs]; omega))
  have hmemC : interp V σ (m.acval entry.ctor (Level.substFn φ entry.levelParams us))
        ∈ˢ interp V σ TCa := by
    rw [← hlpsC]
    exact hmemC0 σ
  have hLeσ : LeavesGr m φ d e σ := hL.of_subset hsube
  obtain ⟨hfitσ, -⟩ := hfitA σ hσ (LeavesGr.of_fvarLeaves_nil
      (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfC))
    (leavesGr_spine hLeσ) (hokTCa σ).1 hoA ⟨hgvp, hmemC, by
      rw [← hveq]; intro h0
      exact hne (by rw [projNV_interp, h0, ConLeche.SetTheory.Tower.projS_pt])⟩
  refine ⟨hokArg, ?_⟩
  have hfit : TeleFit V σ TCa (vs.map (interp V σ)) (interp V σ resta) :=
    teleFit_of_teleFitPA (by rw [← hspa.length]; exact hpc) hfitσ
  rw [hveq, hB (towerGuardAt_of_fireOk hO5 hfire) σ vs _ hlenVs hgvp hfit]

end ConLeche.Model.Rules
