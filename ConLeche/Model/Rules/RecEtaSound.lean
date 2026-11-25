module

public import ConLeche.Model.Rules.Motive
import ConLeche.Model.Rules.UnitSound
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Depth
import ConLeche.Verify.Abstract
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Leaves
import ConLeche.Verify.Shift

public section

/-!
# The soundness of recursor η (task #632)

The η-expansion of a partially applied recursor, ι-reduced (official's
`eta_expand_iota_reduce_recursor`, lean4#15374), at the conditional motive.

* **The expansion is the side** (`RecEtaTele`): along a ∀ the result is
  `λ dom. e`, `e` the expansion of the side applied to the fresh variable,
  abstracted back over it; at every value of the variable `e` has the
  application's value, so the abstraction is the abstraction of the side's
  applications, which is the side (`lamV_eta`).  At the full application
  the result is the reduct, a member of a type the comparison makes the
  application's: both are the point or neither, and where neither is, the
  reduction equates them.
* **The rule** (`DefEq.recEta`): a neutral side that is not the point is a
  member of its io-inferred type, so it is its expansion, which is not the
  point either, and the comparison with the other side equates them.
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

/-- The full application: the reduct, typed in the application's type. -/
theorem RecEtaTele.done_sound {d : Nat} {f T e te : Expr}
    (hr : RedSem m φ d f e) (hi : InferSemFull m φ d e te) (hd : DefEqSem m φ d te T) :
    RecEtaTeleSem m φ d f T e := by
  intro hff hfT Δa fa Ta hCf hCT hdf hdT
  obtain ⟨hfe, hsube, ea, hdea, hY⟩ := hr hff hCf hdf
  have hCe : CtxOkS m φ d Δa e := hCf.of_subset hsube
  obtain ⟨hfte, hsubte, tea, hdtea, hZ⟩ := hi hfe hCe hdea
  refine ⟨hfe, fun l hl => Or.inl (hsube l hl), ea, hdea, ?_⟩
  intro ρ hρ hLf hLT hwf hokT hm
  have hLe : LeavesGr m φ d e ρ := hLf.of_subset hsube
  obtain ⟨hwe, hokte, hme⟩ := hZ ρ hρ hLe
  have heq : interp V ρ tea = interp V ρ Ta :=
    hd hfte hfT (hCe.of_subset hsubte) hCT hdtea hdT ρ hρ (hLe.of_subset hsubte) hLT
      hokte.1 hokT.1 hokte.2.ne_pt hokT.2.ne_pt
  refine ⟨hwe, IsTy.eq_of_ne_pt hokT.2 (heq ▸ hme) hm fun _ hnf => ?_⟩
  exact ((hY ρ hρ hLf hwf hnf).2).symm

/-- One binder: the abstraction of the opened expansion, which at every
value of the variable is the side's application. -/
theorem RecEtaTele.step_sound {d : Nat} {f T dom body e : Expr}
    (hr : RedSem m φ d T (.forallE dom body))
    (ih : RecEtaTeleSem m φ (d + 1) (.app f (.fvar d dom))
      (body.instantiate1 (.fvar d dom)) e) :
    RecEtaTeleSem m φ d f T (.lam dom (e.abstract1 d)) := by
  intro hff hfT Δa fa Ta hCf hCT hdf hdT
  obtain ⟨hfW, hsubW, wa, hwa, hY⟩ := hr hfT hCT hdT
  have hCW : CtxOkS m φ d Δa (.forallE dom body) := hCT.of_subset hsubW
  obtain ⟨doma, bda, hdoma, hbda, rfl⟩ := denote_forallE_inv hwa
  have hfd : Frame d dom := hfW.forallE_ty
  have hCd : CtxOkS m φ d Δa dom := hCW.forallE_ty
  -- the opened side and type: context and reading
  have hCfv : CtxOkS m φ (d + 1) (doma :: Δa) (.fvar d dom) := by
    have := CtxOkS.openS (body := Expr.bvar 0) hCd
      (CtxOkS.of_fvarLeaves_nil hCf.length (by simp [Expr.fvarLeaves])) hdoma
    simpa [Expr.instantiate1] using this
  have hCf' : CtxOkS m φ (d + 1) (doma :: Δa) (.app f (.fvar d dom)) :=
    CtxOkS.app (CtxOkS.weakenTop hCf) hCfv
  have hdf' : denote m.acval env φ (d + 1) (.app f (.fvar d dom)) =
      some (.app fa.lift (.bvar 0)) := by
    have hdaUp : denote m.acval env φ (d + 1) f = some fa.lift := by
      rw [denote_weaken_top m.acval_closed hff.1, hdf]; rfl
    rw [denote, hdaUp, denote_fvar]
    simp
  have hCT' : CtxOkS m φ (d + 1) (doma :: Δa) (body.instantiate1 (.fvar d dom)) :=
    CtxOkS.openS hCd hCW.forallE_body hdoma
  obtain ⟨hfe, hsube, ea, hdea, hE⟩ :=
    ih (Frame.app_fvar hff hfd) (hfW.forallE_open hfd) hCf' hCT' hdf' hbda
  -- the leaves of the opened side and type
  have hwsW := hfW.1
  simp only [Expr.WScoped] at hwsW
  have hleafE : ∀ l ∈ e.fvarLeaves, l.1 = d → l.2 = dom := by
    intro l hl hd
    rcases hsube l hl with h2 | h2
    · simp only [Expr.fvarLeaves, List.mem_append, List.mem_cons] at h2
      rcases h2 with h3 | rfl | h3
      · exact absurd hd (by have := Expr.fvarLeaves_lt_of_wscoped hff.1 l h3; omega)
      · rfl
      · exact absurd hd (by have := Expr.fvarLeaves_lt_of_wscoped hwsW.1 l h3; omega)
    · rcases Expr.fvarLeaves_instantiate1 body 0 h2 with h3 | h3
      · exact absurd hd (by have := Expr.fvarLeaves_lt_of_wscoped hwsW.2 l h3; omega)
      · simp only [Expr.fvarLeaves, List.mem_cons] at h3
        rcases h3 with rfl | h4
        · rfl
        · exact absurd hd (by have := Expr.fvarLeaves_lt_of_wscoped hwsW.1 l h4; omega)
  have hcons : Expr.fvarConsistent d dom e := Expr.fvarConsistent_of_leafCond e hleafE
  have hround : (e.abstract1 d).instantiate1 (.fvar d dom) = e :=
    ConLeche.abstract1_instantiate1 e 0 hcons hfe.2.1
  -- every leaf of the result is the side's or its type's
  have hsubL : ∀ l ∈ (Expr.lam dom (e.abstract1 d)).fvarLeaves,
      l ∈ f.fvarLeaves ∨ l ∈ T.fvarLeaves := by
    have hdomT : ∀ l ∈ dom.fvarLeaves, l ∈ T.fvarLeaves := fun l hl =>
      hsubW l (by simp [Expr.fvarLeaves, hl])
    have hbodyT : ∀ l ∈ body.fvarLeaves, l ∈ T.fvarLeaves := fun l hl =>
      hsubW l (by simp [Expr.fvarLeaves, hl])
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with h2 | h2
    · exact Or.inr (hdomT l h2)
    · obtain ⟨hle, hne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne e 0 hfe.1 l h2
      rcases hsube l hle with h3 | h3
      · simp only [Expr.fvarLeaves, List.mem_append, List.mem_cons] at h3
        rcases h3 with h4 | rfl | h4
        · exact Or.inl h4
        · exact absurd rfl hne
        · exact Or.inr (hdomT l h4)
      · rcases Expr.fvarLeaves_instantiate1 body 0 h3 with h4 | h4
        · exact Or.inr (hbodyT l h4)
        · simp only [Expr.fvarLeaves, List.mem_cons] at h4
          rcases h4 with rfl | h5
          · exact absurd rfl hne
          · exact Or.inr (hdomT l h5)
  have hframe : Frame d (.lam dom (e.abstract1 d)) := by
    refine ⟨?_, ?_, fun l hl => ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨hfd.1, ConLeche.WScoped.abstract1 0 hfe.1⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hfd.2.1, ConLeche.looseBVarsBounded_abstract1 e 0 hfe.2.1⟩
    · rcases hsubL l hl with h2 | h2
      · exact hff.2.2 l h2
      · exact hfT.2.2 l h2
  refine ⟨hframe, hsubL, .lam doma ea, by rw [denote, hdoma, hround, hdea]; rfl, ?_⟩
  intro ρ hρ hLf hLT hwf hokT hm
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLT hokT.1 hokT.2.ne_pt
  have hLW : LeavesGr m φ d (.forallE dom body) ρ := hLT.of_subset hsubW
  have hpi := hokW
  rw [WellDenoted_pi] at hpi
  obtain ⟨hwd, htyd, hwB, htyB⟩ := hpi
  have hokd : WellDenotedTy V ρ doma := ⟨hwd, htyd⟩
  rw [heqW, interp_pi] at hm
  have hLd : LeavesGr m φ d dom ρ := hLW.forallE_ty
  obtain ⟨-, -, hLA, hiA, hwA⟩ := open_app hff hCf hCd hdf hdoma hLf hLd hokd
  have hrow : ∀ z, z ∈ˢ interp V ρ doma →
      WellDenoted V (cons z ρ) ea ∧
        interp V (cons z ρ) ea = SetTheory.app (interp V ρ fa) z := by
    intro z hz
    have h := hE (cons z ρ) (Sat_cons V hρ hz) (hLA z)
      (LeavesGr.open hCd hCW.forallE_body hLd hLW.forallE_body hdoma hokd)
      (hwA _ z hwf hm hz) ⟨hwB z hz, htyB z hz⟩ (by rw [hiA]; exact app_mem_piV hm hz)
    rwa [hiA] at h
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hokd.1, hokd.2, fun x hx => (hrow x hx).1⟩
  · rw [interp_lam, lamV_congr (fun x hx => (hrow x hx).2)]
    exact lamV_eta hm htyB

/-- **Recursor η**: a neutral side that is not the point is a member of its
io-inferred type, hence its expansion, which the comparison equates with the
other side. -/
theorem DefEq.recEta_sound {d : Nat} {a b tb lam : Expr}
    (hnb : b.ioNeutral = true) (htb : InferSemIO m φ d b tb)
    (hx : RecEtaTeleSem m φ d b tb lam) (hd : DefEqSem m φ d a lam) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hwa hwb hna hnb'
  obtain ⟨hftb, hsubb, tba, htba, hXB⟩ := htb hfb hCb hdb
  have hmB : WellDenotedTy V ρ tba ∧ interp V ρ ba ∈ˢ interp V ρ tba := by
    rcases (hXB ρ hρ hLb hwb).2 hnb with h | h
    · exact absurd h hnb'
    · exact h.of_reading htba
  obtain ⟨hfl, hsubl, la, hdla, hL⟩ := hx hfb hftb hCb (hCb.of_subset hsubb) hdb htba
  have hsubl' : ∀ l ∈ lam.fvarLeaves, l ∈ b.fvarLeaves := fun l hl =>
    (hsubl l hl).elim id (hsubb l)
  obtain ⟨hwl, heql⟩ := hL ρ hρ hLb (hLb.of_subset hsubb) hwb hmB.1 hmB.2
  rw [hd hfa hfl hCa (hCb.of_subset hsubl') hda hdla ρ hρ hLa (hLb.of_subset hsubl') hwa hwl
    hna (heql ▸ hnb'), heql]

end ConLeche.Model.Rules
