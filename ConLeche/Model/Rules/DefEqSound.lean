module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.Rules.ProofFastSound
import ConLeche.Model.Rules.EtaSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.DefEqStep
import ConLeche.Semantics.LitStep
import ConLeche.Verify.Denote.Depth

public section

/-!
# The soundness of the definitional-equality rules (task #305)

One lemma per constructor of `DefEq`: the structural rules, the
recursive-structure rule, η, the two proof-irrelevance arms, and the
capability rules `structEta`, `structUnit`.

The rules are proved at the conditional motive `DefEqSem` (task #342,
L9, L11).  A few leaf rules read no claim and are proved unconditionally
(`…_soundU`, `DefEqSemU`) and weakened.  Structure η reads the η
constructor's telescope coherence (task #342 L11b, `EtaSoundKit`).
λ-congruence (`DefEqLams`) and η are the last section
(task #342 S4).
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

theorem DefEq.refl_soundU {d : Nat} {a : Expr} : DefEqSemU m φ d a a := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [haa] at hba
  cases hba
  rfl

/-- Equivalent levels, equal sorts. -/
theorem DefEq.sort_soundU {d : Nat} {u v : Level}
    (h : Level.isEquiv u v = some true) :
    DefEqSemU m φ d (.sort u) (.sort v) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [denote_sort] at haa hba
  obtain rfl : aa = Term.sort (u.eval φ) := (Option.some.inj haa).symm
  obtain rfl : ba = Term.sort (v.eval φ) := (Option.some.inj hba).symm
  rw [Level.isEquiv_sound h φ]

/-- The `fvar` arm: the reading ignores the annotation. -/
theorem DefEq.fvar_soundU {d i : Nat} {ty₁ ty₂ : Expr} :
    DefEqSemU m φ d (.fvar i ty₁) (.fvar i ty₂) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [denote_fvar] at haa hba
  obtain rfl : aa = Term.bvar (d - 1 - i) := (Option.some.inj haa).symm
  obtain rfl : ba = Term.bvar (d - 1 - i) := (Option.some.inj hba).symm
  rfl

/-- `acval_const_congr`, on the `acval_params` field. -/
theorem DefEq.const_soundU {d : Nat} {n : Name} {us us' : List Level}
    (h : Level.isEquivList us us' = some true) :
    DefEqSemU m φ d (.const n us) (.const n us') := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  obtain rfl : aa = ba := acval_const_congr h haa hba
  rfl

/-- `denoteNatZeroConst`: the literal `0` reads as `Nat.zero`. -/
theorem DefEq.natZero_soundU {d : Nat} :
    DefEqSemU m φ d (.lit (.natVal 0)) (.const natZeroName []) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  obtain ⟨hg, rfl⟩ := denote_natLit_inv haa
  rw [denoteNatZeroConst hg] at hba
  obtain rfl : ba = m.acval ConLeche.natZeroName (Level.substFn φ [] []) :=
    (Option.some.inj hba).symm
  rfl

/-! ## The conditional rules (task #342, L11)

The rules at the conditional motive `DefEqSem`: two graded sides are
equal at a valuation where neither is the point.  Every step that uses
"not the point" names its source (`_tmp/port/COMMON.md`'s proof rule):
(1) the subject is a type; (2) the hypothesis of the conditional claim
(a head, a projected subject of a non-point is not the point, since the
point applied or projected is the point); (3) membership in a type
whose members are all the point or none of them (`IsTy.eq_of_ne_pt`).

λ-congruence and η compare the two bodies at every value of the bound
variable, and a body may be the point at one value while the other is
not; their rules carry the body-type check (task #342 S4, the last
section).  Structure η compares the constructor side's parameters and
fields with the stuck side's projections, and nothing at the rules tier
places both spines in one telescope of types (the DESIGN record of task
#342 L11): the η constructor's telescope coherence does (L11b). -/

/-- The slot of a graded application whose head is not the point: the
graph regime, and a domain that is a type. -/
theorem appSlot_of_ne_pt {ρ : Nat → V} {f x : Term}
    (hw : WellDenoted V ρ (.app f x)) (hn : interp V ρ f ≠ pt) :
    ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧
      interp V ρ f ∈ˢ piR v A B ∧ interp V ρ x ∈ˢ A ∧ IsTy A := by
  have h := hw
  rw [WellDenoted_app] at h
  obtain ⟨-, -, v, A, B, hf, hx, -, hT⟩ := h
  have hv : v ≠ 0 := by
    rintro rfl; exact hn (eq_pt_of_mem_piR_zero hf)
  exact ⟨v, A, B, hv, hf, hx, hT hv⟩

theorem DefEq.refl_sound {d : Nat} {a : Expr} : DefEqSem m φ d a a :=
  DefEq.refl_soundU.cond

theorem DefEq.symm_sound {d : Nat} {a b : Expr} (h : DefEqSem m φ d a b) :
    DefEqSem m φ d b a := by
  intro hfb hfa Δa ba aa hCb hCa hba haa ρ hρ hLb hLa hwb hwa hnb hna
  exact (h hfa hfb hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb).symm

/-- The recursive-structure rule: the reduct is graded and equal to the
subject where the subject is not the point ("not pt" source (2)), so it
is not the point there either and the continuation's claim applies. -/
theorem DefEq.redL_sound {d : Nat} {a a' b : Expr}
    (ha : RedSem m φ d a a') (hb : DefEqSem m φ d a' b) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨hfa', hsub, aa', haa', hs⟩ := ha hfa hCa haa
  obtain ⟨hwaa', heq⟩ := hs ρ hρ hLa hwa hna
  rw [heq] at hna ⊢
  exact hb hfa' hfb (hCa.of_subset hsub) hCb haa' hba ρ hρ
    (hLa.of_subset hsub) hLb hwaa' hwb hna hnb

theorem DefEq.sort_sound {d : Nat} {u v : Level}
    (h : Level.isEquiv u v = some true) :
    DefEqSem m φ d (.sort u) (.sort v) :=
  (DefEq.sort_soundU h).cond

theorem DefEq.fvar_sound {d i : Nat} {ty₁ ty₂ : Expr} :
    DefEqSem m φ d (.fvar i ty₁) (.fvar i ty₂) :=
  DefEq.fvar_soundU.cond

theorem DefEq.const_sound {d : Nat} {n : Name} {us us' : List Level}
    (h : Level.isEquivList us us' = some true) :
    DefEqSem m φ d (.const n us) (.const n us') :=
  (DefEq.const_soundU h).cond

theorem DefEq.natZero_sound {d : Nat} :
    DefEqSem m φ d (.lit (.natVal 0)) (.const natZeroName []) :=
  DefEq.natZero_soundU.cond

/-- The packed successor: the two arguments are members of `Nat`, a
type ("not pt" source (3)).  The literal's membership is
`natLit_factsAV`; the other argument's comes from its slot, whose head
is the successor, a member of a graph-regime Π-type and so never the
point, so its domain is `Nat` (`piR_dom_unique`). -/
theorem DefEq.natSucc_sound (hin : RulesInputs V m φ) {d : Nat} {k : Nat} {x : Expr}
    (h : DefEqSem m φ d (.lit (.natVal k)) x) :
    DefEqSem m φ d (.lit (.natVal (k + 1))) (.app (.const natSuccName []) x) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _
  obtain ⟨hg, rfl⟩ := denote_natLit_inv haa
  obtain ⟨fa, xa, hfa', hxa, rfl⟩ := denote_app_inv hba
  rw [denoteNatSuccConst hg] at hfa'
  obtain rfl : fa = m.acval ConLeche.natSuccName (Level.substFn φ [] []) :=
    (Option.some.inj hfa').symm
  obtain ⟨hz, hs, hT⟩ := hin.nat_heads hg ρ
  have hmk := (natLit_factsAV (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ)
    hz hs hT k).2
  have hw := hwb
  rw [WellDenoted_app] at hw
  obtain ⟨-, -, v, A, B, hfm, hxm, -, -⟩ := hw
  have hv : v ≠ 0 := by
    rintro rfl
    exact (mem_piR_pos Nat.one_ne_zero hs).2.2.2 (eq_pt_of_mem_piR_zero hfm)
  have hA := piR_dom_unique Nat.one_ne_zero hv hs hfm
  rw [← hA] at hxm
  have hwk : WellDenoted V ρ (natLitT (m.acval natZeroName (Level.substFn φ [] []))
      (m.acval natSuccName (Level.substFn φ [] [])) k) := by
    simp only [natLitT] at hwa
    exact hwa.app_arg
  refine deqStep_appCong rfl (hT.eq_of_ne_pt hmk hxm fun hn₁ hn₂ =>
    h (Frame.of_not_hasFvar rfl rfl) hfb.app_arg
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
      hCb.app_arg (denote_natLit hg) hxa ρ hρ
      (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves]))
      hLb.app_arg hwk hwb.app_arg hn₁ hn₂)

/-- Π-congruence.  Both sides are types: the domains and every fibre are
types, never the point ("not pt" source (1)), so the premises' claims
apply with no condition. -/
theorem DefEq.forallE_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
   
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂))) :
    DefEqSem m φ d (.forallE ty₁ body₁) (.forallE ty₂ body₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denote_forallE_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denote_forallE_inv hba
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.forallE_ty hfb.forallE_ty hCa.forallE_ty hCb.forallE_ty hta₁ hta₂
      ρ hρ hLa.forallE_ty hLb.forallE_ty hwa.pi_dom.1 hwb.pi_dom.1
      hwa.pi_dom.ne_pt hwb.pi_dom.ne_pt
  refine deqStep_piCong hdom (fun x hx => ?_)
  have hx₂ : x ∈ˢ interp V ρ ta₂ := hdom ▸ hx
  exact hbody (hfa.forallE_open hfb.forallE_ty) (hfb.forallE_open hfb.forallE_ty)
    (CtxOkS.openS hCb.forallE_ty hCa.forallE_body hta₂)
    (CtxOkS.openS hCb.forallE_ty hCb.forallE_body hta₂)
    (denote_open_rename hva₁) hva₂
    (cons x ρ) (Sat_cons V hρ hx₂)
    (LeavesGr.open hCb.forallE_ty hCa.forallE_body hLb.forallE_ty hLa.forallE_body
      hta₂ hwb.pi_dom)
    (LeavesGr.open hCb.forallE_ty hCb.forallE_body hLb.forallE_ty hLb.forallE_body
      hta₂ hwb.pi_dom)
    (hwa.pi_body x hx) (hwb.pi_body x hx₂)
    (hwa.pi_fib x hx).ne_pt (hwb.pi_fib x hx₂).ne_pt

/-- Application congruence.  The heads of two applications that are not
the point are not the point ("not pt" source (2)), so they are equal;
their slots are in the graph regime, so the two domains are the one
domain of the equal heads (`piR_dom_unique`), a type: the arguments are
both the point or neither is ("not pt" source (3)). -/
theorem DefEq.app_sound {d : Nat} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ d f₁ f₂) (ha : DefEqSem m φ d a₁ a₂) :
    DefEqSem m φ d (.app f₁ a₁) (.app f₂ a₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨fa₁, xa₁, hf₁, hx₁, rfl⟩ := denote_app_inv haa
  obtain ⟨fa₂, xa₂, hf₂, hx₂, rfl⟩ := denote_app_inv hba
  have hn₁ : interp V ρ fa₁ ≠ pt := by
    intro h; apply hna; rw [interp_app, h, app_pt]
  have hn₂ : interp V ρ fa₂ ≠ pt := by
    intro h; apply hnb; rw [interp_app, h, app_pt]
  have heF := hf hfa.app_fn hfb.app_fn hCa.app_fn hCb.app_fn hf₁ hf₂ ρ hρ
    hLa.app_fn hLb.app_fn hwa.app_fn hwb.app_fn hn₁ hn₂
  obtain ⟨v₁, A₁, B₁, hv₁, hs₁, hm₁, hT₁⟩ := appSlot_of_ne_pt hwa hn₁
  obtain ⟨v₂, A₂, B₂, hv₂, hs₂, hm₂, -⟩ := appSlot_of_ne_pt hwb hn₂
  rw [← heF] at hs₂
  have hA : A₁ = A₂ := piR_dom_unique hv₁ hv₂ hs₁ hs₂
  rw [← hA] at hm₂
  exact deqStep_appCong heF (hT₁.eq_of_ne_pt hm₁ hm₂ fun h₁ h₂ =>
    ha hfa.app_arg hfb.app_arg hCa.app_arg hCb.app_arg hx₁ hx₂ ρ hρ
      hLa.app_arg hLb.app_arg hwa.app_arg hwb.app_arg h₁ h₂)

/-- Congruence under a projection: a projection of the point is the
point (`projS_pt`), so the projected subjects of
two projections that are not the point are not the point ("not pt"
source (2)). -/
theorem DefEq.proj_sound {d : Nat} {s : Name} {i : Nat} {e₁ e₂ : Expr}
    (h : DefEqSem m φ d e₁ e₂) :
    DefEqSem m φ d (.proj s i e₁) (.proj s i e₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨ia₁, entry, he₁, hfe, rfl⟩ := denote_proj_inv haa
  obtain ⟨ia₂, entry', he₂, hfe', rfl⟩ := denote_proj_inv hba
  obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
  have hn₁ : interp V ρ ia₁ ≠ pt := by
    intro h; apply hna; rw [projNV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
  have hn₂ : interp V ρ ia₂ ≠ pt := by
    intro h; apply hnb; rw [projNV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
  exact ProjAV.interp_congr (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
    hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
    (ProjAV.hoistV hwa) (ProjAV.hoistV hwb) hn₁ hn₂)

/-- Both sides are the point (`prf_of_isProofFast`): vacuous at the
conditional motive. -/
theorem DefEq.proofFast_sound (hin : RulesInputs V m φ) {d : Nat} {a b : Expr}
    (ha : ConLeche.isProofFast env.find? env.findTable? a = true)
    (_hb : ConLeche.isProofFast env.find? env.findTable? b = true) :
    DefEqSem m φ d a b := by
  intro hfa _ Δa aa ba hCa hCb haa _ ρ hρ hLa _ hwa _ hna _
  exact absurd (prf_of_isProofFast hin ha hfa hCa haa ρ hρ hLa hwa) hna

/-- **Proof irrelevance at the io grade**: the left side's io claim at its
io-inferred type, whose io-inferred sort reduces to `Prop` (`PropPt`,
`Sound.lean`'s `prop_pt_io`), makes it the point: vacuous at the
conditional motive.  The right side's premises are the checker's
symmetric run, not consumed. -/
theorem DefEq.proofIrrel_sound {d : Nat} {a ta b : Expr}
    (hta : InferSemIO m φ d a ta) (hpt : PropPt m φ d ta) :
    DefEqSem m φ d a b := by
  intro hfa _ Δa aa ba hCa _ haa _ ρ hρ hLa _ hwa _ hna _
  obtain ⟨hfta, hsub, taa, htaa, hrow⟩ := hta hfa hCa haa
  exact absurd (hpt hfta (hCa.of_subset hsub) htaa ρ _ hρ (hLa.of_subset hsub)
    (hrow ρ hρ hLa hwa).1) hna

/-- Unit-like structure: the two inferred types and their reducts are
types ("not pt" source (1)), so their reductions and the certificate's
comparison are equations; the stored unit law then equates any two
members, the point or not. -/
theorem DefEq.structUnit_sound (hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb wtb : Expr} {T : Name} {us' : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hwtar : Red env d ta wta)
    (hthead : wta.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (htlen : wta.getAppArgs.length = caps.unitParams)
    (hlv : us'.length = cvT.levelParams.length)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hwtbr : Red env d tb wtb) (hwtbF : wtb.isForallE = false)
    (hd : DefEqSem m φ d wta wtb) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB hna hnb
  -- the two sides' inferred types, reduced, with their readings
  obtain ⟨hfta, hsuba, taa, htaa, hXA⟩ := hta hfa hCa hda
  -- neither side is the point, and their types reduce to non-∀s
  -- (`Red.rigid`): the io claims are memberships
  obtain ⟨hokTa, hmemA⟩ := (IORel.mem_of_red (hXA ρ hρ hLa hokA).1 hna hwtar
    (not_forallE_of_getAppFn hthead)).of_reading htaa
  have hCta : CtxOkS m φ d Δa ta := hCa.of_subset hsuba
  have hLtaρ : LeavesGr m φ d ta ρ := hLa.of_subset hsuba
  obtain ⟨hfWA, hsubWA, wtaa, hwtaa, hYA⟩ := hwta hfta hCta htaa
  obtain ⟨hokWA, heqWA⟩ := hYA ρ hρ hLtaρ hokTa.1 hokTa.ne_pt
  have hCwa : CtxOkS m φ d Δa wta := hCta.of_subset hsubWA
  have hLwaρ : LeavesGr m φ d wta ρ := hLtaρ.of_subset hsubWA
  obtain ⟨hftb, hsubb, tba, htba, hXB⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB⟩ := (IORel.mem_of_red (hXB ρ hρ hLb hokB).1 hnb hwtbr
    (fun ty body h => by rw [h] at hwtbF; exact nomatch hwtbF)).of_reading htba
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubb
  obtain ⟨hfWB, hsubWB, wtba, hwtba, hYB⟩ := hwtb hftb hCtb htba
  obtain ⟨hokWB, heqWB⟩ := hYB ρ hρ hLtbρ hokTb.1 hokTb.ne_pt
  have hCwb : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubWB
  have hLwbρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubWB
  have hmemAW : interp V ρ aa ∈ˢ interp V ρ wtaa := by rw [← heqWA]; exact hmemA
  have hmemBW : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqWB]; exact hmemB
  -- the certificate's defeq identifies the two family instances: types
  have hEq : interp V ρ wtaa = interp V ρ wtba :=
    hd hfWA hfWB hCwa hCwb hwtaa hwtba ρ hρ hLwaρ hLwbρ hokWA hokWB
      (heqWA ▸ hokTa.ne_pt) (heqWB ▸ hokTb.ne_pt)
  -- side a's reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wta).symm, hthead] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denote_mkAppN_inv hwtaa
  rw [denote, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  have hstrip : (cvT.type.stripPis caps.unitParams).isSome = true :=
    (m.wf.indCaps hind).1 hunit
  obtain ⟨TVa, hTVa, -, hlaw⟩ :=
    hin.caps_ok.2 T cvT caps hind hunit hresT φ us' hlv
  -- the parameter spine fits the former's telescope: the reduct is a
  -- type, not the point ("not pt" source (1))
  obtain ⟨resta, hfitT⟩ := formerFit hin hind hlv hstrip htlen hspt hTVa ρ hokWA
    (by rw [← heqWA]; exact hokTa.2.ne_pt)
  have hfold : ∀ (l : List Term) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp V ρ aa
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hmemAW
    rwa [interp_mkAppN, hfold] at h
  have hmy : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hEq ▸ hmemBW
    rwa [interp_mkAppN, hfold] at h
  have hlenTs : (tsa.map (interp V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, htlen]
  exact hlaw ρ (tsa.map (interp V ρ)) resta (interp V ρ aa)
    (interp V ρ ba) hlenTs hfitT hmx hmy

/-! ## λ-congruence and η at the value reading (task #342 S4)

`DefEqLams` (task #349) concludes the UNCONDITIONAL `DefEqLamsSem`: the
innermost level's full-grade body types put the two bodies in one type,
whose members are all the point or none, so the bodies' conditional claim
is an equation there; an equation of the bodies at every value of the
variable is an equation of the λs, so `outer` needs no type.  η's typed
premise does the same for the λ's body and `b` applied.  The proofs are
the fragment's (`whitepaper/Fragment/Sound.lean`: `DefEqLams.inner_sound`,
`outer_sound`, `DefEq.eta_sound`) at the value reading; η's other side is
atom-headed (`Expr.ioNeutral`), so its io claim is a membership where it
is not the point (`IORelN`). -/

/-- Syntactically equal λs are equal outright. -/
theorem DefEqLams.refl_sound {d : Nat} {a : Expr} : DefEqLamsSem m φ d a a :=
  DefEq.refl_soundU

/-- **The innermost level** (the fragment's `DefEqLams.inner_sound`): the
two opened bodies lie in one type at every value of the variable — their
full-grade types are types ("not pt" source (1)), compared equal — so
they are both the point or neither, and where neither is the bodies'
conditional claim makes them equal (`IsTy.eq_of_ne_pt`).  The claim is
unconditional: no side need be off the point. -/
theorem DefEqLams.inner_sound {d : Nat} {ty₁ body₁ ty₂ body₂ t₁ t₂ : Expr}
   
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (ht₁ : InferSemFull m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂)) t₁)
    (ht₂ : InferSemFull m φ (d + 1) (body₂.instantiate1 (.fvar d ty₂)) t₂)
    (ht : DefEqSem m φ (d + 1) t₁ t₂) :
    DefEqLamsSem m φ d (.lam ty₁ body₁) (.lam ty₂ body₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denote_lam_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denote_lam_inv hba
  -- "not pt" source (1): the two domains are types
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.lam_ty hfb.lam_ty hCa.lam_ty hCb.lam_ty hta₁ hta₂
      ρ hρ hLa.lam_ty hLb.lam_ty hwa.lam_dom.1 hwb.lam_dom.1
      hwa.lam_dom.ne_pt hwb.lam_dom.ne_pt
  simp only [interp_lam]
  rw [hdom]
  refine lamV_congr fun x hx => ?_
  have hx₁ : x ∈ˢ interp V ρ ta₁ := hdom ▸ hx
  have hf₁ := hfa.lam_open hfb.lam_ty
  have hf₂ := hfb.lam_open hfb.lam_ty
  have hC₁ := CtxOkS.openS hCb.lam_ty hCa.lam_body hta₂
  have hC₂ := CtxOkS.openS hCb.lam_ty hCb.lam_body hta₂
  have hv₁ := denote_open_rename (ty' := ty₂) hva₁
  have hρ' := Sat_cons V hρ hx
  have hL₁ := LeavesGr.open (x := x) hCb.lam_ty hCa.lam_body hLb.lam_ty
    hLa.lam_body hta₂ hwb.lam_dom
  have hL₂ := LeavesGr.open (x := x) hCb.lam_ty hCb.lam_body hLb.lam_ty
    hLb.lam_body hta₂ hwb.lam_dom
  obtain ⟨hft₁, hsub₁, t₁a, ht₁a, hrow₁⟩ := ht₁ hf₁ hC₁ hv₁
  obtain ⟨hft₂, hsub₂, t₂a, ht₂a, hrow₂⟩ := ht₂ hf₂ hC₂ hva₂
  obtain ⟨hw₁, hT₁, hm₁⟩ := hrow₁ _ hρ' hL₁
  obtain ⟨hw₂, hT₂, hm₂⟩ := hrow₂ _ hρ' hL₂
  -- "not pt" source (1): the two bodies' inferred types are types
  have heT := ht hft₁ hft₂ (hC₁.of_subset hsub₁) (hC₂.of_subset hsub₂) ht₁a ht₂a
    _ hρ' (hL₁.of_subset hsub₁) (hL₂.of_subset hsub₂) hT₁.1 hT₂.1 hT₁.ne_pt hT₂.ne_pt
  rw [heT] at hm₁
  exact IsTy.eq_of_ne_pt hT₂.2 hm₁ hm₂ fun hn₁ hn₂ =>
    hbody hf₁ hf₂ hC₁ hC₂ hv₁ hva₂ _ hρ' hL₁ hL₂ hw₁ hw₂ hn₁ hn₂

/-- **An outer level needs no type** (the fragment's
`DefEqLams.outer_sound`): the bodies are equal at every value of the
variable, unconditionally, so the λs are; the domains are types ("not
pt" source (1)), so their conditional claim applies. -/
theorem DefEqLams.outer_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
   
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqLamsSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂))) :
    DefEqLamsSem m φ d (.lam ty₁ body₁) (.lam ty₂ body₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denote_lam_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denote_lam_inv hba
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.lam_ty hfb.lam_ty hCa.lam_ty hCb.lam_ty hta₁ hta₂
      ρ hρ hLa.lam_ty hLb.lam_ty hwa.lam_dom.1 hwb.lam_dom.1
      hwa.lam_dom.ne_pt hwb.lam_dom.ne_pt
  simp only [interp_lam]
  rw [hdom]
  refine lamV_congr fun x hx => ?_
  have hx₁ : x ∈ˢ interp V ρ ta₁ := hdom ▸ hx
  exact hbody (hfa.lam_open hfb.lam_ty) (hfb.lam_open hfb.lam_ty)
    (CtxOkS.openS hCb.lam_ty hCa.lam_body hta₂)
    (CtxOkS.openS hCb.lam_ty hCb.lam_body hta₂)
    (denote_open_rename hva₁) hva₂ _ (Sat_cons V hρ hx)
    (LeavesGr.open hCb.lam_ty hCa.lam_body hLb.lam_ty hLa.lam_body hta₂ hwb.lam_dom)
    (LeavesGr.open hCb.lam_ty hCb.lam_body hLb.lam_ty hLb.lam_body hta₂ hwb.lam_dom)
    (hwa.lam_body x hx₁) (hwb.lam_body x hx)

/-- λ-congruence: the telescopes' unconditional claim, weakened. -/
theorem DefEq.lams_sound {d : Nat} {a b : Expr} (h : DefEqLamsSem m φ d a b) :
    DefEqSem m φ d a b :=
  h.cond

/-- **η, typed, from `b`'s membership where it is not the point** (the
fragment's `DefEq.eta_sound`).  At every value of the variable the λ's
opened body and `b` applied lie in one type — the body's full-grade
type is the ∀'s fibre, a type ("not pt" source (1)) — so they are both
the point or neither, and where neither is the body's conditional claim
makes them equal; a member of a function space whose fibres are types
is the abstraction of its applications (`lamV_eta`).  `hmb` is the
claim of `b`'s type: where `b` is not the point it is a member of it,
which the type's io claim gives for an atom-headed `b`. -/
theorem DefEq.eta_core {d : Nat}
    {ty₁ body₁ b tb ty₂ B t₁ : Expr}
    (htb : Frame d b → ∀ {Δa : List Term} {ea : Term},
      CtxOkS m φ d Δa b → denote m.acval env φ d b = some ea →
      Frame d tb ∧ LeavesSub tb b ∧
        ∃ ta, denote m.acval env φ d tb = some ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d b ρ →
            WellDenoted V ρ ea → interp V ρ ea ≠ pt →
            WellDenotedTy V ρ ta ∧ interp V ρ ea ∈ˢ interp V ρ ta)
    (hwtb : RedSem m φ d tb (.forallE ty₂ B))
    (hty : DefEqSem m φ d ty₂ ty₁)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)))
    (ht₁ : InferSemFull m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁)) t₁)
    (htB : DefEqSem m φ (d + 1) t₁ (B.instantiate1 (.fvar d ty₁))) :
    DefEqSem m φ d (.lam ty₁ body₁) b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB _ hnb
  obtain ⟨hwF1, hbF1, hLF1⟩ := hfa
  obtain ⟨hwF2, hbF2, hLF2⟩ := hfb
  simp only [Expr.WScoped] at hwF1
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbF1
  have hLty : Expr.LeavesBounded ty₁ := fun l hl =>
    hLF1 l (by simp [Expr.fvarLeaves, hl])
  have hLbd : Expr.LeavesBounded body₁ := fun l hl =>
    hLF1 l (by simp [Expr.fvarLeaves, hl])
  have hfty : Frame d ty₁ := ⟨hwF1.1, hbF1.1, hLty⟩
  have hCty : CtxOkS m φ d Δa ty₁ := hCa.lam_ty
  have hCbd : CtxOkS m φ d Δa body₁ := hCa.lam_body
  have hLtyρ : LeavesGr m φ d ty₁ ρ := hLa.lam_ty
  have hLbdρ : LeavesGr m φ d body₁ ρ := hLa.lam_body
  -- the λ's own reading, and its grading at ρ
  obtain ⟨ta, bda, hta, hbda, rfl⟩ := denote_lam_inv hda
  have hokTa : WellDenotedTy V ρ ta := hokA.lam_dom
  -- `b`'s type, its reduct, and both readings; `b` is not the point, so
  -- it is a member
  obtain ⟨hftb, hsubtb, tba, htba, hX⟩ := htb ⟨hwF2, hbF2, hLF2⟩ hCb hdb
  obtain ⟨hokTb, hmemB⟩ := hX ρ hρ hLb hokB hnb
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubtb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hY⟩ := hwtb hftb hCtb htba
  -- "not pt" source (1): `b`'s type is a type
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLtbρ hokTb.1 hokTb.ne_pt
  have hCwr : CtxOkS m φ d Δa (Expr.forallE ty₂ B) := hCtb.of_subset hsubW
  have hLwρ : LeavesGr m φ d (Expr.forallE ty₂ B) ρ := hLtbρ.of_subset hsubW
  obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denote_forallE_inv hwtba
  have hokTa₂ : WellDenotedTy V ρ ta₂ := hokW.pi_dom
  -- the two domains agree ("not pt" source (1): two types)
  have hdom : interp V ρ ta₂ = interp V ρ ta :=
    hty hfW.forallE_ty hfty hCwr.forallE_ty hCty hta₂ hta ρ hρ
      hLwρ.forallE_ty hLtyρ hokTa₂.1 hokTa.1 hokTa₂.ne_pt hokTa.ne_pt
  have hmem : interp V ρ ba ∈ˢ piV (interp V ρ ta₂)
      (fun x => interp V (cons x ρ) ba₂) := by
    have h := hmemB
    rw [heqW, interp_pi] at h
    exact h
  -- the λ's fibre is `app ⟦b⟧`
  have hdbUp : denote m.acval env φ (d + 1) b = some ba.lift := by
    rw [denote_weaken_top m.acval_closed hwF2, hdb]; rfl
  have hdapp : denote m.acval env φ (d + 1) (.app b (.fvar d ty₁))
      = some (.app ba.lift (.bvar 0)) := by
    rw [denote, hdbUp, denote_fvar]
    simp
  have hCfvar : CtxOkS m φ (d + 1) (ta :: Δa) (.fvar d ty₁) := by
    have := CtxOkS.openS (body := Expr.bvar 0) hCty
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves])) hta
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOkS m φ (d + 1) (ta :: Δa) (.app b (.fvar d ty₁)) :=
    CtxOkS.app (CtxOkS.weakenTop hCb) hCfvar
  have hlift : ∀ x, interp V (cons x ρ) ba.lift = interp V ρ ba := fun x =>
    interp_lift_cons V ba x ρ
  have hokApp : ∀ x, x ∈ˢ interp V ρ ta →
      WellDenoted V (cons x ρ) (.app ba.lift (.bvar 0)) := by
    intro x hx
    have hok0 : WellDenoted V (cons x ρ) ba.lift :=
      (WellDenoted_liftN V 1 ba 0 (cons x ρ)).mpr (by rw [shiftE_zero]; exact hokB)
    rw [WellDenoted_app]
    refine ⟨hok0, by simp, _, interp V ρ ta₂, (fun y => interp V (cons y ρ) ba₂),
      ?_, ?_, propN_eq_zero.mp, fun _ => hokTa₂.2⟩
    · rw [hlift]; exact hmem
    · show x ∈ˢ _
      rw [hdom]; exact hx
  have hfopen : Frame (d + 1) (body₁.instantiate1 (.fvar d ty₁)) :=
    Frame.open_body hfty hwF1.2 hbF1.2 hLbd
  have hfapp : Frame (d + 1) (.app b (.fvar d ty₁)) := by
    refine ⟨?_, by simp [Expr.looseBVarsBounded, hbF2], fun l hl => ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨Expr.WScoped.mono (by omega) hwF2, by omega,
        Expr.WScoped.mono (by omega) hwF1.1⟩
    · rw [ConLeche.Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h2 | h2
      · exact hLF2 l h2
      · rw [ConLeche.Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hbF1.1
        · exact hLty l h3
  have hCopen : CtxOkS m φ (d + 1) (ta :: Δa) (body₁.instantiate1 (.fvar d ty₁)) :=
    CtxOkS.openS hCty hCbd hta
  have hLopenBody : ∀ x : V, LeavesGr m φ (d + 1)
      (body₁.instantiate1 (.fvar d ty₁)) (cons x ρ) := fun _ =>
    LeavesGr.open hCty hCbd hLtyρ hLbdρ hta hokTa
  have hLfvar : ∀ x : V, LeavesGr m φ (d + 1) (.fvar d ty₁) (cons x ρ) := by
    intro x
    have := LeavesGr.open (body := Expr.bvar 0) (x := x) hCty
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
      hLtyρ (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves])) hta hokTa
    simpa [Expr.instantiate1] using this
  have hLapp : ∀ x : V, LeavesGr m φ (d + 1) (.app b (.fvar d ty₁)) (cons x ρ) :=
    fun x => LeavesGr.app (LeavesGr.weakenTop (ρ := cons x ρ) hCb hLb) (hLfvar x)
  -- the ∀'s body opened at the λ's domain: the fibre
  have hfB : Frame (d + 1) (B.instantiate1 (.fvar d ty₁)) := hfW.forallE_open hfty
  have hCB : CtxOkS m φ (d + 1) (ta :: Δa) (B.instantiate1 (.fvar d ty₁)) :=
    CtxOkS.openS hCty hCwr.forallE_body hta
  have hdB : denote m.acval env φ (d + 1) (B.instantiate1 (.fvar d ty₁))
      = some ba₂ := denote_open_rename hba₂
  have hLB : ∀ x : V, LeavesGr m φ (d + 1) (B.instantiate1 (.fvar d ty₁)) (cons x ρ) :=
    fun _ => LeavesGr.open hCty hCwr.forallE_body hLtyρ hLwρ.forallE_body hta hokTa
  -- at every value: the body and `b` applied are in one type
  have hpt : ∀ x, x ∈ˢ interp V ρ ta →
      interp V (cons x ρ) bda = SetTheory.app (interp V ρ ba) x := by
    intro x hx
    have hx₂ : x ∈ˢ interp V ρ ta₂ := by rw [hdom]; exact hx
    have hρ' := Sat_cons V hρ hx
    obtain ⟨hft₁, hsub₁, t₁a, ht₁a, hrow₁⟩ := ht₁ hfopen hCopen hbda
    obtain ⟨hw₁, hT₁, hm₁⟩ := hrow₁ _ hρ' (hLopenBody x)
    have hokB₂ : WellDenoted V (cons x ρ) ba₂ := hokW.pi_body x hx₂
    have hTB₂ : IsTy (interp V (cons x ρ) ba₂) := hokW.pi_fib x hx₂
    -- "not pt" source (1): the body's type and the fibre are types
    have heT := htB hft₁ hfB (hCopen.of_subset hsub₁) hCB ht₁a hdB _ hρ'
      ((hLopenBody x).of_subset hsub₁) (hLB x) hT₁.1 hokB₂ hT₁.ne_pt hTB₂.ne_pt
    rw [heT] at hm₁
    have hm₂ : interp V (cons x ρ) (.app ba.lift (.bvar 0))
        ∈ˢ interp V (cons x ρ) ba₂ := by
      rw [interp_app, hlift, interp_bvar]
      exact app_mem_piV hmem hx₂
    rw [IsTy.eq_of_ne_pt hTB₂ hm₁ hm₂ fun hn₁ hn₂ =>
      hbody hfopen hfapp hCopen hCapp hbda hdapp (cons x ρ) hρ'
        (hLopenBody x) (hLapp x) hw₁ (hokApp x hx) hn₁ hn₂,
      interp_app, hlift, interp_bvar]
    rfl
  rw [interp_lam, lamV_congr hpt, ← hdom]
  exact lamV_eta hmem fun x hx => hokW.pi_fib x hx

/-- **η, typed**, with `b`'s io-inferred type: where `b` is not the point,
its io claim is a membership — for an atom-headed `b` (the fragment's
`etaIO_sound`). -/
theorem DefEq.eta_sound {d : Nat}
    {ty₁ body₁ b tb ty₂ B t₁ : Expr}
    (hneu : b.ioNeutral = true)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb (.forallE ty₂ B))
    (hty : DefEqSem m φ d ty₂ ty₁)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)))
    (ht₁ : InferSemFull m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁)) t₁)
    (htB : DefEqSem m φ (d + 1) t₁ (B.instantiate1 (.fvar d ty₁))) :
    DefEqSem m φ d (.lam ty₁ body₁) b := by
  refine DefEq.eta_core (fun hf Δa ea hC hea => ?_) hwtb hty hbody ht₁ htB
  obtain ⟨hft, hsub, ta, hta, hrow⟩ := htb hf hC hea
  refine ⟨hft, hsub, ta, hta, fun ρ hρ hL hw hn => ?_⟩
  -- `b`'s head is no λ and no `let`: its io claim is not hereditary
  rcases (hrow ρ hρ hL hw).2 hneu with h | h
  · exact absurd h hn
  · exact h.of_reading hta

set_option maxHeartbeats 800000 in
/-- **Structure η at the conditional motive** (task #342 L11b).  Neither
side is the point.  The stuck side's type is a type ("not pt" source
(1)), so its reduct is graded and equal, and `etaSide` gives the η law
and the coherence law: `tsa ++ ps` fits the η constructor's telescope.
The constructor side is graded and not the point, so its spine fits the
same telescope ("not pt" source (2), `teleFitPA_of_graded_ne_pt`).  The
telescope's domains are types, so the two comparisons, conditional on
the point, make the spines equal (`teleFit_eq_of_cond`, L11's finding
2).  The type application's certificate is not read. -/
theorem DefEq.structEta_sound (hin : RulesInputs V m φ) {d : Nat}
    {a b tb wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us' : List Level} {cvT : ConstantVal}
    {caps : IndCaps}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hwtbr : Red env d tb wtb)
    (hhead : a.getAppFn = .const c us)
    (hctor : env.find? c = some (.ctorInfo cvc cnP cnF))
    (_hlen : a.getAppArgs.length = cnP + cnF)
    (hthead : wtb.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (heta : ConLeche.capsEta cvT caps = true) (hetaCtor : caps.etaCtor = c)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresc : ConLeche.reservedBasisNames.contains c = false)
    (htlen : wtb.getAppArgs.length = caps.etaParams)
    (hlv : us'.length = cvT.levelParams.length)
    (hlps : cvc.levelParams = cvT.levelParams)
    (htow : ConLeche.towerSlotsAll env T caps.etaFields = true)
    (hus : Level.isEquivList us us' = some true)
    (hparams : DefEqListSem m φ d (a.getAppArgs.take caps.etaParams)
      wtb.getAppArgs)
    (hfields : DefEqListSem m φ d (a.getAppArgs.drop caps.etaParams)
      (ConLeche.etaProjs T b caps.etaFields)) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB hneA hneB
  -- the stuck side's inferred type, reduced: a type; the stuck side is
  -- not the point and its type reduces to a family's application, so
  -- its io claim is a membership (`Red.rigid`)
  obtain ⟨hftb, hsubtb, tba, htba, hX⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB0⟩ := (IORel.mem_of_red (hX ρ hρ hLb hokB).1 hneB hwtbr
    (not_forallE_of_getAppFn hthead)).of_reading htba
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubtb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hY⟩ := hwtb hftb hCtb htba
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLtbρ hokTb.1 hokTb.ne_pt
  have hCr : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubW
  have hLrρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubW
  have hmemB : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqW]; exact hmemB0
  have hneW : interp V ρ wtba ≠ pt := by rw [← heqW]; exact hokTb.ne_pt
  -- the reduced type is the family applied to its parameters
  rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wtb).symm, hthead] at hwtba
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denote_mkAppN_inv hwtba
  rw [denote, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the constructor side is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp a).symm, hhead] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denote_mkAppN_inv hda
  rw [denote, hctor] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  have hψc : Level.substFn φ cvc.levelParams us
      = Level.substFn φ cvT.levelParams us' := by
    rw [hlps]
    exact ConLeche.Level.substFn_congr
      (ConLeche.Level.isEquivList_sound hus φ)
  -- the stuck side: the η law and the coherence law
  obtain ⟨ps, hsps, hfps, TCa, hTCa, hside⟩ := etaSide hin hind heta hresT
    (by rw [hetaCtor]; exact hresc) (by rw [hetaCtor]; exact hctor) hlv htlen htow
    hfb hCb hdb hspt
  obtain ⟨hLps, hokps, hb, restC, hfitC⟩ :=
    hside ρ hρ hLb (leavesGr_spine hLrρ) hokW hneW hokB hmemB
  obtain ⟨-, hoA⟩ := hoist_spineV asa hokA
  obtain ⟨-, hoT⟩ := hoist_spineV tsa hokW
  -- the constructor side fits the same telescope: its head inhabits
  -- the constructor's type reading, and it is not the point
  have hlvc : us'.length = cvc.levelParams.length := by rw [hlps]; exact hlv
  obtain ⟨tc, htc, hoktc, hmemC, -, -⟩ :=
    constTy_pkg hin.const_ty hctor (show us'.length = _ from hlvc)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at htc hmemC
  obtain rfl : TCa = tc := Option.some.inj (hTCa.symm.trans (htc 0))
  have hlenA : asa.length = (tsa ++ ps).length := by
    have h1 := hparams.1
    have h2 := hfields.1
    rw [List.length_take, htlen] at h1
    rw [List.length_drop, hsps.length] at h2
    rw [List.length_append, ← hspt.length, ← hspa.length, htlen]
    omega
  have hpcA : PiChain asa.length TCa := by
    have := piChain_of_teleFit hfitC
    rwa [List.length_map, ← hlenA] at this
  have hmemC' : interp V ρ (m.acval c (Level.substFn φ cvc.levelParams us))
      ∈ˢ interp V ρ TCa := by
    rw [hψc, ← hlps]; exact hmemC ρ
  obtain ⟨restA, hfitA⟩ := teleFitPA_of_graded_ne_pt asa hpcA (hoktc ρ) hmemC' hokA hneA
  have hfitA' := teleFit_of_teleFitPA hpcA hfitA
  -- the two comparisons, conditional on the point
  have htk := hparams.2
    (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_take hx))
    (frame_spine hfW hCr) (hspa.take caps.etaParams) hspt ρ hρ
    (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_take hx))
    (leavesGr_spine hLrρ)
    (fun x hx => hoA x (List.mem_of_mem_take hx)) hoT
  have hdr := hfields.2
    (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_drop hx))
    (fun x hx => ⟨(hfps x hx).1, (hfps x hx).2.1⟩) (hspa.drop caps.etaParams) hsps ρ hρ
    (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_drop hx))
    hLps (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokps
  have htkLen : ((asa.take caps.etaParams).map (interp V ρ)).length
      = (tsa.map (interp V ρ)).length := by
    rw [List.length_map, List.length_map, List.length_take, ← hspt.length, htlen]
    have := hlenA
    rw [List.length_append, ← hspt.length, htlen] at this
    omega
  have hspine : asa.map (interp V ρ) = (tsa ++ ps).map (interp V ρ) := by
    refine teleFit_eq_of_cond (hoktc ρ) hfitA' hfitC
      (by rw [List.length_map, List.length_map, hlenA]) fun p hp => ?_
    rw [← List.take_append_drop caps.etaParams asa, List.map_append, List.map_append,
      List.zip_append htkLen] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact htk p hp'
    · exact hdr p hp'
  have hfold : ∀ (l : List Term) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  rw [hb, interp_mkAppN, hfold, hspine, hψc, ← hetaCtor]

end ConLeche.Model.Rules
