module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSound
import ConLeche.Model.Rules.IotaSound
import ConLeche.Model.Rules.KRecSound
import ConLeche.Model.Rules.DefEqSound
import ConLeche.Model.Rules.InferSound
import ConLeche.Model.Rules.CertsSound
import ConLeche.Model.Rules.BVUnsatSound
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of derivations (task #305)

**Derivation ⇒ P currency**, by one mutual structural recursion over
the eight relations.  Every case is one per-rule lemma applied to the
recursive calls — nothing semantic happens here, which is the whole
point: the per-rule lemmas are the proof lanes' deliverables, this
file is fixed, and it is what the recomposition consumes.

**The claims are conditional on the point** (task #342, L9;
`Motive.lean`): a reduction claims nothing of a subject that is the point,
a definitional equality nothing where a side is.  ι and the K and `And`
rescues (L10) conclude the unconditional `RedSemU` from conditional
premises, and the λ-telescope congruence the unconditional
`DefEqLamsSem` (task #349), both weakened here (`.cond`).  Binders carry no
datum, so β has no premise and no side induction is needed.
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

/-! ## The conditional induction -/

mutual

theorem red_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {e e' : Expr}, Red env d e e' → RedSem m φ d e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ =>
    Red.trans_sound (red_sound hin h₁) (red_sound hin h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound hin h)
  | _, _, _, .projArg h => Red.projArg_sound (red_sound hin h)
  | _, _, _, .beta => Red.beta_sound
  | _, _, _, .zeta => Red.zeta_sound
  | _, _, _, .delta h => Red.delta_sound hin h
  | _, _, _, .natLit h => Red.natLit_sound h
  | _, _, _, .strLit h => Red.strLit_sound h
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    Red.proj_sound hin hent hhead hi hlen hus hfire hctor (teleArity_sound hcerts)
  | _, _, _, .natSucc hsup hw hn => Red.natSucc_sound hin hsup (red_sound hin hw) hn
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr =>
    Red.natOp_sound hin hc hst (red_sound hin hwa) hn₁ (red_sound hin hwb) hn₂ hr
  -- ι and the K/`And` rescues (task #342 L10): one lemma each, from the
  -- conditional claims of their premises
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hlv
      hparams hcertR hcertC hres hidx =>
    Red.iota_sound hin hhead hrec hlen hus (red_sound hin hmajor) hmhead hctor
      hrule hmlen hlv (fun hc => defEqList_sound hin (hparams hc))
      (teleArity_sound hcertR) (fun h3 => certsF_sound hin (hcertC h3)) hres
      (fun h3 hne => defEqList_sound hin (hidx h3 hne))
  | _, _, _, .rescueK hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws
      hb hlv' _ _ htp http hv hv0 =>
    Red.rescueK_sound hin hrec hk hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlv hnP hfab hws hb hlv' (infer_sound hin htp)
      (prop_pt_io hin http rfl (infer_sound hin http) hv (red_sound hin hv)
        (ConLeche.Level.isEquiv_sound hv0 φ))
  | _, _, _, .rescueAnd hrec hctor hres hind htm htmaj hthead hlen hlv hslots
      hfab hws hb hlv' _ _ htp http hv hv0 =>
    Red.rescueAnd_sound hin hrec hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlen hlv hslots hfab hws hb hlv'
      (infer_sound hin htp)
      (prop_pt_io hin http rfl (infer_sound hin http) hv (red_sound hin hv)
        (ConLeche.Level.isEquiv_sound hv0 φ))
  | _, _, _, .rescueEta hrec heta hctor hres hind htm htmaj hthead hlen hlv hnz
      hfab hws hb hlv' hresT hresC htow =>
    Red.rescueEta_sound hin hrec heta hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) htmaj hthead hlen hlv hnz hfab hws hb hlv' hresT hresC
      htow
  | _, _, _, .kRec h1 h2 h3 h4 h5 h6 h7 =>
    Red.kRec_sound hin h1 h2 h3 h4 h5 h6 (teleArity_sound h7)

theorem defeq_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {a b : Expr}, DefEq env d a b → DefEqSem m φ d a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound hin h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hin hr) (defeq_sound hin h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .fvar => DefEq.fvar_sound
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .natZero => DefEq.natZero_sound
  | _, _, _, .natSucc h => DefEq.natSucc_sound hin (defeq_sound hin h)
  | _, _, _, .forallE hty hbody =>
    DefEq.forallE_sound (defeq_sound hin hty) (defeq_sound hin hbody)
  | _, _, _, .lams h => DefEq.lams_sound (defEqLams_sound hin h)
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hin hf) (defeq_sound hin ha)
  | _, _, _, .proj h => DefEq.proj_sound (defeq_sound hin h)
  | _, _, _, .proofFast ha hb => DefEq.proofFast_sound hin ha hb
  | _, _, _, .proofIrrel hta htta hu hu0 _ _ _ _ =>
    DefEq.proofIrrel_sound (infer_sound hin hta)
      (prop_pt_io hin htta rfl (infer_sound hin htta) hu (red_sound hin hu)
        (ConLeche.Level.isEquiv_sound hu0 φ))
  | _, _, _, .structUnit hta hwta hthead hind hunit hresT htlen hlv htb hwtb hwtbF hd =>
    DefEq.structUnit_sound hin (infer_sound hin hta) (red_sound hin hwta) hwta hthead
      hind hunit hresT htlen hlv (infer_sound hin htb) (red_sound hin hwtb) hwtb hwtbF
      (defeq_sound hin hd)
  | _, _, _, .eta hneu htb hwtb hty hbody ht₁ htB =>
    DefEq.eta_sound hneu (infer_sound hin htb) (red_sound hin hwtb)
      (defeq_sound hin hty) (defeq_sound hin hbody) (infer_sound hin ht₁)
      (defeq_sound hin htB)
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT
      hresc htlen hlv hlps hslots hus hparams hfields =>
    DefEq.structEta_sound hin (infer_sound hin htb) (red_sound hin hwtb) hwtb hhead
      hctor hlen hthead hind heta hetaCtor hresT hresc htlen hlv hlps hslots hus
      (defEqList_sound hin hparams) (defEqList_sound hin hfields)

theorem defEqLams_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {a b : Expr}, DefEqLams env d a b → DefEqLamsSem m φ d a b
  | _, _, _, .refl => DefEqLams.refl_sound
  | _, _, _, .inner hty hbody ht₁ ht₂ ht =>
    DefEqLams.inner_sound (defeq_sound hin hty) (defeq_sound hin hbody)
      (infer_sound hin ht₁) (infer_sound hin ht₂) (defeq_sound hin ht)
  | _, _, _, .outer hty hbody =>
    DefEqLams.outer_sound (defeq_sound hin hty) (defEqLams_sound hin hbody)

theorem infer_sound (hin : RulesInputs V m φ) :
    ∀ {g : Grade} {d : Nat} {e t : Expr}, Infer env g d e t → InferSem m φ g d e t
  | _, _, _, _, .sort => Infer.sort_sound
  | _, _, _, _, .fvar h => Infer.fvar_sound h
  | _, _, _, _, .const hf hus => Infer.const_sound hin hf hus
  | _, _, _, _, .natLit h => Infer.natLit_sound hin h
  | _, _, _, _, .strLit h => Infer.strLit_sound hin h
  | _, _, _, _, .forallE hs hu hbs hv =>
    Infer.forallE_sound (infer_sound hin hs) (red_sound hin hu) (fun _ => hu)
      (infer_sound hin hbs) (red_sound hin hv) (fun _ => hv)
  | _, _, _, _, .lam hs hu hbt =>
    Infer.lam_sound (fun hg => infer_sound hin (hs hg))
      (fun hg => red_sound hin (hu hg)) (infer_sound hin hbt)
  | _, _, _, _, .letE _ _ htv _ hb =>
    Infer.letE_sound (fun hg => infer_sound hin (htv hg)) (infer_sound hin hb)
  | _, _, _, _, .app htf hw hta hd =>
    Infer.app_sound (infer_sound hin htf) (red_sound hin hw) (fun _ => hw)
      (fun hg => infer_sound hin (hta hg)) (fun hg => defeq_sound hin (hd hg))
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    Infer.proj_sound hin (infer_sound hin htpe) (red_sound hin hte) (fun _ => hte) hhead hent
      hlen hus hprop
  | _, _, _, _, .bvUnsat hf _ hskip hE hd hC hred hpow =>
    Infer.bvUnsat_soundSkip hin (infer_sound hin hf) (infer_sound hin hE) (defeq_sound hin hd)
      (infer_sound hin hC) hskip (fun x => red_sound hin (hred x)) (fun k => red_sound hin (hpow k))

/-- **Proof irrelevance at the io grade** (task #342 L18): a type whose
io-inferred sort reduces to a sort evaluating to zero holds only the
point in its io claim — by recursion over the type's own io inference,
whose ∀ case recurses into the ∀'s body (`propPt_forallE`). -/
theorem prop_pt_io (hin : RulesInputs V m φ) :
    ∀ {g : Grade} {d : Nat} {T tt : Expr}, Infer env g d T tt → g = .io →
      InferSem m φ g d T tt →
      ∀ {w : Level}, Red env d tt (.sort w) → RedSem m φ d tt (.sort w) →
        w.eval φ = 0 → PropPt m φ d T
  | _, _, _, _, .forallE _ _ hbs hv, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_forallE hsem hrs hr hw0
      (prop_pt_io hin hbs rfl (infer_sound hin hbs) hv (red_sound hin hv)
        (eval_zero_of_red_imax hr hw0))
  | _, _, _, _, .sort, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .fvar _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .const _ _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .natLit _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .strLit _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .lam _ _ _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .letE _ _ _ _ _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .app _ _ _ _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .proj _ _ _ _ _ _ _, rfl, hsem, _, hr, hrs, hw0 =>
    propPt_of_not_forallE hsem hrs hr hw0 (fun _ _ h => nomatch h)
  | _, _, _, _, .bvUnsat _ _ _ _ _ _ _ _, h, _, _, _, _, _ => nomatch h

theorem certsF_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {ty : Expr} {args : List Expr},
      CertsF env d ty args → CertsFSem m φ d ty args
  | _, _, _, .nil => CertsF.nil_sound
  | _, _, _, .cert hta hd hrest =>
    CertsF.cert_sound (infer_sound hin hta) (defeq_sound hin hd)
      (certsF_sound hin hrest)

theorem defEqList_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {as bs : List Expr},
      DefEqList env d as bs → DefEqListSem m φ d as bs
  | _, _, _, .nil => DefEqList.nil_sound
  | _, _, _, .cons h hs =>
    DefEqList.cons_sound (defeq_sound hin h) (defEqList_sound hin hs)

end

/-! ## The global forms the inductive installer's readers consume -/

/-- An establishing inference claim, at every satisfying valuation of a
full context discipline. -/
theorem InferSemFull.global {d : Nat} {e t : Expr} (h : InferSemFull m φ d e t)
    (hf : Frame d e) {Δa : List Term} {ea : Term}
    (hC : CtxOk m φ d Δa e) (hea : denote m.acval env φ d e = some ea) :
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denote m.acval env φ d t = some ta ∧
        Graded V Δa ea ∧ GradedTy V Δa ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨hft, hsub, ta, hta, hs⟩ := h hf hC.toS hea
  exact ⟨hft, hsub, ta, hta, fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).1,
    fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).2.1,
    fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).2.2⟩

/-- **A reduction of a type** (task #342, L12): a subject that is a graded
TYPE at every satisfying valuation reduces to a graded type with the same
interpretation.  The conditional claim applies at every valuation because
a type is never the point ("not pt" source (1): `IsTy.ne_pt`).  The
positivity readers (`Model/Inductives/Pos*`, `NestPosRed`) walk types and
read their whnf steps through it. -/
theorem red_sound_ty (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hf : Frame d e) {Δa : List Term} {ea : Term}
    (hC : CtxOk m φ d Δa e) (hea : denote m.acval env φ d e = some ea)
    (hg : GradedTy V Δa ea) :
    Frame d e' ∧ LeavesSub e' e ∧
      ∃ ea', denote m.acval env φ d e' = some ea' ∧ GradedTy V Δa ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea' := by
  obtain ⟨hf', hsub, ea', hea', hs⟩ := red_sound hin h hf hC.toS hea
  have hs' := fun ρ hρ => hs ρ hρ (hC.leavesGr hρ) (hg ρ hρ).1 (hg ρ hρ).2.ne_pt
  exact ⟨hf', hsub, ea', hea', fun ρ hρ => ⟨(hs' ρ hρ).1, (hs' ρ hρ).2 ▸ (hg ρ hρ).2⟩,
    fun ρ hρ => (hs' ρ hρ).2⟩

end ConLeche.Model.Rules
