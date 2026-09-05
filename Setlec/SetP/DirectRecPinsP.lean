import Setlec.SetP.DirectRecCompP

/-!
# The recursor's pins at the simple frame (task #175 W4c, P3 module 6, part 11)

The three facts the recursor's own opening supplies directly:

* `recParamIdent` — the recursor's parameter frame and the
  constructor's are identified by the `checkDirectDomsAt` pins
  (`frameIdent` over the defeq claims), and the constructor's residual
  reads at the parameter depth;
* `recMotive` — the motive binder's reading is the Π over the carrier
  into `Sort ℓ` (its domain pinned to the family spine, `famSpineRow`);
* `recMajor` — the major binder's reading is the carrier.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A leaf reachable from a prefix of an opening's variables is one of
them (the annotations are over the earlier variables). -/
theorem leaf_of_prefix {m : EnvS2Core V env} {k : Nat} {e : Expr} {fvs : List Expr}
    {o : Expr} {Γ : List AVExpr} {R : AVExpr}
    (hR : OpenedP m φ k e fvs o Γ R)
    (hidx : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    {n : Nat} {l : Nat × Name × Expr}
    (h : ∃ a ∈ fvs.take n, l ∈ a.fvarLeaves) :
    Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs.take n ∧ l.2.2.looseBVarsBounded 0 = true := by
  obtain ⟨a, ha, hl⟩ := h
  obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
  have hq' : q < n := by
    have := (List.getElem?_eq_some_iff.mp hq).1
    simp at this; omega
  rw [List.getElem?_take_of_lt hq'] at hq
  obtain ⟨nm, ty, rfl⟩ := hidx q a hq
  obtain ⟨-, hw, hb, hL, hleaf⟩ := hR.var q _ hq
  simp only [Expr.fvarTypeD] at hw hb hL hleaf
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact ⟨List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hq']; exact hq), hb⟩
  · have hlt := Expr.fvarLeaves_lt_of_wscoped hw l hl
    have hmem := hleaf l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem hmem
    obtain ⟨nm', ty', hx⟩ := hidx p _ hp
    obtain ⟨h1, -, h3⟩ : l.1 = p ∧ l.2.1 = nm' ∧ l.2.2 = ty' := by
      injection hx with a b c
      exact ⟨a, b, c⟩
    refine ⟨List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (i := p) (j := n) (by omega)]; exact hp), ?_⟩
    obtain ⟨-, -, hb', -, -⟩ := hR.var p _ hp
    rw [hx] at hb'
    rw [h3]
    simpa [Expr.fvarTypeD] using hb'

/-- **The family spine's row** at depth `nP + e` over the recursor's
frame: scoped, bounded, correlated with the context, read, and — at
every satisfying frame — graded with the carrier's value. -/
theorem famSpineRow {m : EnvS2Core V env} {nP k : Nat} {tyR : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + k) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + k)
    {T : Name} {lps : List Name} {ci : ConstantInfo} (hfT : env.find? T = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    {us : List Level} (hus : Level.substFn φ lps us = φ) (hlus : us.length = lps.length)
    {w : Nat} {Fs : List AVExpr} {pps : List (Nat × Nat × AVExpr)}
    (hleafT : m.acval T φ = directTyAV w pps Fs)
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0) (hbelow : DomsBelow 0 pps) (hlen : pps.length = nP)
    (hok : ∀ ρ : Nat → V, ParamsOkT w ρ Fs pps)
    (hval : ∀ ρ : Nat → V, UnderTowerValid ρ (towerBodyAV w Fs) pps)
    (hsatP : ∀ ρ : Nat → V, Sat2 V (Γr.drop k) ρ → Sat2 V ((pps.map (·.2.2)).reverse) ρ)
    (e : Nat) (he : e ≤ k) :
    Expr.WScoped (nP + e) (Expr.mkAppN (.const T us) (fvsR.take nP)) ∧
    (Expr.mkAppN (.const T us) (fvsR.take nP)).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (Expr.mkAppN (.const T us) (fvsR.take nP)) ∧
    CtxOkP m φ (nP + e) (Γr.drop (k - e))
      (Expr.mkAppN (.const T us) (fvsR.take nP)) ∧
    denoteP m.acval env φ (nP + e) (Expr.mkAppN (.const T us) (fvsR.take nP))
      = some (AVExpr.mkAppN (directTyAV w pps Fs) (paramBvarsAt nP (nP + e))) ∧
    ∀ ρ : Nat → V, Sat2 V (Γr.drop (k - e)) ρ →
      AnnotOkP V ρ (AVExpr.mkAppN (directTyAV w pps Fs) (paramBvarsAt nP (nP + e))) ∧
      interp2 V ρ (AVExpr.mkAppN (directTyAV w pps Fs) (paramBvarsAt nP (nP + e)))
        = towerSet w (teleOfFields (fun j => ρ (j + e)) Fs) := by
  have hcl : VExpr.bvarsBelow 0 (directTyAV w pps Fs).erase := by
    have := m.cval_closedL T φ
    rwa [hleafT] at this
  have hidxT : ∀ (k : Nat) (x : Expr), (fvsR.take nP)[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hk] at hx
    exact hidxR k x hx
  have hlenT : (fvsR.take nP).length = nP := by simp [hlenF]
  -- the spine's variables are scoped, bounded and leaf-bounded
  have hvars : ∀ a ∈ fvsR.take nP, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    have hq' : q < nP := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hq'] at hq
    obtain ⟨nm, ty, rfl⟩ := hidxR q a hq
    obtain ⟨-, hw, -, -, -⟩ := hR.var q _ hq
    simp only [Expr.fvarTypeD] at hw
    exact ⟨by simp only [Expr.WScoped]; exact ⟨hq', hw⟩, rfl⟩
  have hws : Expr.WScoped (nP + e) (Expr.mkAppN (.const T us) (fvsR.take nP)) :=
    WScoped_mkAppN (by simp [Expr.WScoped]) fun a ha =>
      Expr.WScoped.mono (by omega) (hvars a ha).1
  have hbd : (Expr.mkAppN (.const T us) (fvsR.take nP)).looseBVarsBounded 0
      = true :=
    Setlec.looseBVarsBounded_mkAppN rfl fun a ha => (hvars a ha).2
  have hleaves : ∀ l ∈ (Expr.mkAppN (.const T us) (fvsR.take nP)).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧ l.2.2.looseBVarsBounded 0 = true := by
    intro l hl
    rcases Setlec.fvarLeaves_mkAppN hl with h | h
    · simp [Expr.fvarLeaves] at h
    · exact leaf_of_prefix hR hidxR h
  refine ⟨hws, hbd, fun l hl => (hleaves l hl).2, ?_, ?_, ?_⟩
  · have := hR.ctx (i := nP + e) (by omega) hws
      (fun l hl => List.mem_of_mem_take (hleaves l hl).1)
    rw [show nP + k - (nP + e) = k - e from by omega] at this
    exact this
  · rw [famSpine_read_at hfT hlps hus hlus hlenT hidxT (nP + e), hleafT]
  · intro ρ hρ
    have hρ3 : Sat2 V (Γr.drop k) (fun j => ρ (j + e)) := by
      have := Sat2_drop hρ e
      rwa [List.drop_drop, show k - e + e = k from by omega] at this
    exact famSpine_val hbits hbelow hlen hok hval hcl (fun j => rfl) (hsatP _ hρ3)

/-! ## The parameter frames, identified -/

/-- **The recursor's parameter frame is the constructor's**, and the
constructor's residual at the recursor's parameters reads to the field
tower at depth `nP`. -/
theorem recParamIdent {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP nF k : Nat} {tyR cty : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + k) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + k)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hlenDs : ds.length = nP + nF)
    (hCread : denoteP m.acval env φ 0 cty = some (mkPisAV ds bodyC))
    (hCok : ∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV ds bodyC))
    (hCcl : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    {cdomsP : List Expr} {crest : Expr}
    (hci : Expr.instPisAt (fvsR.take nP) cty = some (cdomsP, crest))
    (hpins : ∀ i, i < nP → ∃ a b, (fvsR.take nP)[i]? = some a ∧ cdomsP[i]? = some b ∧
      Setlec.isDefEqCore μ env F (0 + i) (Expr.fvarTypeD a) b = .ok true) :
    (∀ i, i ≤ nP → ∀ ρ : Nat → V, Sat2 V (Γr.drop (nP + k - i)) ρ ↔
      Sat2 V ((((ds.take nP).map (·.2.2)).reverse).drop (nP - i)) ρ) ∧
    denoteP m.acval env φ nP crest = some (mkPisAV (ds.drop nP) bodyC) ∧
    Expr.WScoped nP crest ∧ crest.looseBVarsBounded 0 = true ∧
    (∀ l ∈ crest.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧ l.2.2.looseBVarsBounded 0 = true) := by
  have hlenT : (fvsR.take nP).length = nP := by simp [hlenF]
  have hidxT : ∀ (k : Nat) (x : Expr), (fvsR.take nP)[k]? = some x →
      ∃ nm ty, x = Expr.fvar (0 + k) nm ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hk] at hx
    obtain ⟨nm, ty, h⟩ := hidxR k x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  have hspW : ∀ (i : Nat) (a : Expr), (fvsR.take nP)[i]? = some a →
      Expr.WScoped (0 + i + 1) a := by
    intro i a ha
    have hi : i < nP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hi] at ha
    obtain ⟨nm, ty, rfl⟩ := hidxR i a ha
    obtain ⟨-, hw, -, -, -⟩ := hR.var i _ ha
    simp only [Expr.fvarTypeD] at hw
    simp only [Expr.WScoped]
    exact ⟨by omega, hw⟩
  have hnilC : cty.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hCcl
  -- the constructor tower's peels
  have hstC := stripPisAV_mkPisAV ds bodyC
  rw [hlenDs] at hstC
  have hteleC := piTeleP_of_stripPisAV hstC
  have hteleP := piTeleP_of_stripPisAV (stripPisAV_mkPisAV_take nP ds bodyC (by omega))
  obtain ⟨okΓc, -⟩ := piTeleP_graded (V := V) hteleC (Δ₀ := []) (fun ρ _ => hCok ρ)
  simp only [List.append_nil] at okΓc
  -- the run's domains and residual, read
  have hdomsC := instPisAt_openerDomsP (fvsR.take nP) hci hidxT hCread
    (by rw [hlenT]; exact hteleP)
  rw [hlenT] at hdomsC
  have hres := instPisAt_openerResP (fvsR.take nP) hci hidxT hCread
    (by rw [hlenT]; exact hteleP)
  rw [hlenT, Nat.zero_add] at hres
  -- the residual's scoping
  have hwres := instPisAt_res_WScoped (fvsR.take nP) (d := 0) hci
    (Expr.WScoped.of_not_hasFvar hCcl) hspW
  rw [hlenT, Nat.zero_add] at hwres
  obtain ⟨hbdoms, hbres⟩ := instPisAt_bounded (fvsR.take nP) hci hCb
    (fun a ha => by
      obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
      rfl)
  have hleavesRun := instPisAt_leaves (fvsR.take nP) hci
  have hleafC : ∀ l, ((∃ x ∈ cdomsP, l ∈ x.fvarLeaves) ∨ l ∈ crest.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧ l.2.2.looseBVarsBounded 0 = true := by
    intro l hl
    rcases hleavesRun l hl with h | h
    · rw [hnilC] at h; exact absurd h List.not_mem_nil
    · exact leaf_of_prefix hR hidxR h
  refine ⟨?_, hres, hwres, hbres, fun l hl => hleafC l (Or.inr hl)⟩
  -- the identification
  have hΓ1 : (Γr.drop k).length = nP := by rw [List.length_drop, hR.len]; omega
  have hΓ2 : ((((ds.take nP).map (·.2.2)).reverse)).length = nP := by
    simp [hlenDs]
  have hdrop3 : ∀ i, i ≤ nP → (Γr.drop k).drop (nP - i) = Γr.drop (nP + k - i) := by
    intro i hi; rw [List.drop_drop]; congr 1; omega
  have key := frameIdent (V := V) hΓ1 hΓ2 (fun i hi hiff ρ hρ => by
    rw [hdrop3 i (by omega)] at hρ
    obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
    rw [Nat.zero_add] at hdeq
    have ha' : fvsR[i]? = some a := by rw [List.getElem?_take_of_lt hi] at ha; exact ha
    obtain ⟨-, hwa, hba, hLa, hleafa⟩ := hR.var i a ha'
    have hda := hR.doms i a ha'
    have hCa := hR.ctx (i := i) (by omega) hwa hleafa
    -- the constructor domain's side
    have hwb : Expr.WScoped i b := by
      have := instPisAt_index_WScoped (fvsR.take nP) (d := 0) hci
        (Expr.WScoped.of_not_hasFvar hCcl) hspW i b hb
      rwa [Nat.zero_add] at this
    have hbb : b.looseBVarsBounded 0 = true := hbdoms b (List.mem_of_getElem? hb)
    have hleafb : ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take nP ∧
        l.2.2.looseBVarsBounded 0 = true :=
      fun l hl => hleafC l (Or.inl ⟨b, List.mem_of_getElem? hb, hl⟩)
    have hLb : Expr.LeavesBounded b := fun l hl => (hleafb l hl).2
    have hCb' := hR.ctx (i := i) (by omega) hwb
      (fun l hl => List.mem_of_mem_take (hleafb l hl).1)
    have hdb : denoteP m.acval env φ i b
        = some (((((ds.take nP).map (·.2.2)).reverse)).getD (nP - 1 - i) default) := by
      have := hdomsC i hi
      rw [List.getD_eq_getElem?_getD (l := cdomsP), hb, Option.getD_some, Nat.zero_add] at this
      exact this
    -- the gradings, under the recursor's frame
    have hoka : ∀ ρ : Nat → V, Sat2 V (Γr.drop (nP + k - i)) ρ →
        AnnotOkP V ρ (Γr.getD (nP + k - 1 - i) default) := hR.okΓ i (by omega)
    have hokb : ∀ ρ : Nat → V, Sat2 V (Γr.drop (nP + k - i)) ρ →
        AnnotOkP V ρ (((((ds.take nP).map (·.2.2)).reverse)).getD (nP - 1 - i) default) := by
      intro ρ hρ
      have hρ2 := (hiff ρ).mp (by rw [hdrop3 i (by omega)]; exact hρ)
      have := okΓc i (by omega) ρ (by rw [drop_fields_eq hlenDs i (by omega)]; exact hρ2)
      rwa [getD_reverse_take hlenDs hi] at this
    have := hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb' hda hdb hoka hokb ρ hρ
    rw [getD_drop', show k + (nP - 1 - i) = nP + k - 1 - i from by omega]
    exact this)
  intro i hi ρ
  rw [← hdrop3 i hi]
  exact key i hi ρ

/-! ## The motive and the major -/

/-- **The motive binder's reading** is the Π over the carrier into the
elimination sort. -/
theorem recMotive {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP : Nat} {tyR : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + 3)
    {nmM nmm : Name} {mdom : Expr} {elimL : Level} {mbm : BinderMeta}
    (hmfv : fvsR[nP]? = some (.fvar nP nmM (.forallE nmm mdom (.sort elimL) mbm)))
    (hbitM : pwBit φ mbm.pw ≠ 0)
    {T : Name} {lps : List Name} {ci : ConstantInfo} (hfT : env.find? T = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    (hmdeq : Setlec.isDefEqCore μ env F nP mdom
      (Expr.mkAppN (.const T (lps.map .param)) (fvsR.take nP)) = .ok true)
    {w : Nat} {Fs : List AVExpr} {pps : List (Nat × Nat × AVExpr)}
    (hleafT : m.acval T φ = directTyAV w pps Fs)
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0) (hbelow : DomsBelow 0 pps) (hlen : pps.length = nP)
    (hok : ∀ ρ : Nat → V, ParamsOkT w ρ Fs pps)
    (hval : ∀ ρ : Nat → V, UnderTowerValid ρ (towerBodyAV w Fs) pps)
    (hsatP : ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ → Sat2 V ((pps.map (·.2.2)).reverse) ρ) :
    ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ →
      interp2 V ρ (Γr.getD 2 default)
        = piR (elimL.eval φ + 1) (towerSet w (teleOfFields ρ Fs))
            (fun _ => (univ (elimL.eval φ) : V)) := by
  obtain ⟨hws, hbd, hLB, hCb, hread, hrow⟩ :=
    famSpineRow hR hidxR hlenF hfT hlps (Level.substFn_param_self φ lps) (by simp) hleafT
      hbits hbelow hlen hok hval hsatP 0 (by omega)
  simp only [Nat.add_zero, Nat.sub_zero] at hws hbd hLB hCb hread hrow
  -- the motive type's reading
  obtain ⟨-, hwM, hbM, hLM, hleafM⟩ := hR.var nP _ hmfv
  simp only [Expr.fvarTypeD] at hwM hbM hLM hleafM
  have hdM := hR.doms nP _ hmfv
  simp only [Expr.fvarTypeD] at hdM
  rw [show nP + 3 - 1 - nP = 2 from by omega] at hdM
  obtain ⟨A, Bv, hA, hB, hpi⟩ := denoteP_forallE_inv hdM
  rw [Expr.instantiate1_sort, denoteP_sort] at hB
  obtain rfl := Option.some.inj hB
  -- the domain's pieces
  have hwd : Expr.WScoped nP mdom := by
    simp only [Expr.WScoped] at hwM; exact hwM.1
  have hbdd : mdom.looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbM; exact hbM.1
  have hleafd : ∀ l ∈ mdom.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR := fun l hl =>
    hleafM l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl)
  have hLd : Expr.LeavesBounded mdom := fun l hl =>
    hLM l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl)
  have hCd := hR.ctx (i := nP) (by omega) hwd hleafd
  rw [show nP + 3 - nP = 3 from by omega] at hCd
  have hokM : ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ → AnnotOkP V ρ A := by
    intro ρ hρ
    have := hR.okΓ nP (by omega) ρ (by rw [show nP + 3 - nP = 3 from by omega]; exact hρ)
    rw [show nP + 3 - 1 - nP = 2 from by omega, hpi] at this
    obtain ⟨h1, h2⟩ := this
    rw [AnnotOk2_pi] at h1
    rw [AnnotValidV_pi] at h2
    exact ⟨h1.1, h2.1⟩
  have heq := hc.defEqRow hmdeq hwd hbdd hLd hws hbd hLB hCd hCb hA hread hokM
    (fun ρ hρ => (hrow ρ hρ).1)
  intro ρ hρ
  rw [hpi, interp2_pi, heq ρ hρ, (hrow ρ hρ).2,
    piR_congr_bit (v' := elimL.eval φ + 1) (by omega)]
  rfl

/-- **The major binder's reading** is the carrier. -/
theorem recMajor {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP : Nat} {tyR : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + 3)
    {nmJ : Name} {jdom : Expr}
    (hjfv : fvsR[nP + 2]? = some (.fvar (nP + 2) nmJ jdom))
    {T : Name} {lps : List Name} {ci : ConstantInfo} (hfT : env.find? T = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    (hjdeq : Setlec.isDefEqCore μ env F (nP + 2) jdom
      (Expr.mkAppN (.const T (lps.map .param)) (fvsR.take nP)) = .ok true)
    {w : Nat} {Fs : List AVExpr} {pps : List (Nat × Nat × AVExpr)}
    (hleafT : m.acval T φ = directTyAV w pps Fs)
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0) (hbelow : DomsBelow 0 pps) (hlen : pps.length = nP)
    (hok : ∀ ρ : Nat → V, ParamsOkT w ρ Fs pps)
    (hval : ∀ ρ : Nat → V, UnderTowerValid ρ (towerBodyAV w Fs) pps)
    (hsatP : ∀ ρ : Nat → V, Sat2 V (Γr.drop 3) ρ → Sat2 V ((pps.map (·.2.2)).reverse) ρ) :
    ∀ ρ : Nat → V, Sat2 V (Γr.drop 1) ρ →
      interp2 V ρ (Γr.getD 0 default) = towerSet w (teleOfFields (fun j => ρ (j + 2)) Fs) := by
  obtain ⟨hws, hbd, hLB, hCb, hread, hrow⟩ :=
    famSpineRow hR hidxR hlenF hfT hlps (Level.substFn_param_self φ lps) (by simp) hleafT
      hbits hbelow hlen hok hval hsatP 2 (by omega)
  simp only [show 3 - 2 = 1 from rfl] at hCb hrow
  obtain ⟨-, hwJ, hbJ, hLJ, hleafJ⟩ := hR.var (nP + 2) _ hjfv
  simp only [Expr.fvarTypeD] at hwJ hbJ hLJ hleafJ
  have hdJ := hR.doms (nP + 2) _ hjfv
  simp only [Expr.fvarTypeD] at hdJ
  rw [show nP + 3 - 1 - (nP + 2) = 0 from by omega] at hdJ
  have hCJ := hR.ctx (i := nP + 2) (by omega) hwJ hleafJ
  rw [show nP + 3 - (nP + 2) = 1 from by omega] at hCJ
  have hokJ : ∀ ρ : Nat → V, Sat2 V (Γr.drop 1) ρ → AnnotOkP V ρ (Γr.getD 0 default) := by
    intro ρ hρ
    have := hR.okΓ (nP + 2) (by omega) ρ (by rw [show nP + 3 - (nP + 2) = 1 from by omega]; exact hρ)
    rwa [show nP + 3 - 1 - (nP + 2) = 0 from by omega] at this
  have heq := hc.defEqRow hjdeq hwJ hbJ hLJ hws hbd hLB hCJ hCb hdJ hread hokJ
    (fun ρ hρ => (hrow ρ hρ).1)
  intro ρ hρ
  rw [heq ρ hρ, (hrow ρ hρ).2]

end Setlec.SetR.Interp2
