module

import ConLeche.Model.OpenedCtx
import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Model.IndTele
import ConLeche.Model.Env.EnvModelM
public import ConLeche.Kernel.Inductives.StoredRecs
import ConLeche.Model.Env.Laws
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Tiers
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Inductives.StoredRecsInv
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.TypeU

public section

/-!
# The stored recursors' semantics (task #431)

What the stored check (`storedRecsCheck`) says in the model, at the
generated install's carrier:

* **the stored type** (`recTyCheck`): opened `n` binders deep beside
  the generated one, its domains pinned definitionally binder by
  binder and its residue definitionally the generated residue; in the
  model the two readings are towers that agree domain by domain along
  every chain of members and in their residues (`TEqAt`), so they read
  alike and every fit of at most `n` arguments of the stored reading is
  a fit of the generated one (`TEqAt.fit`) — `storedTy_sem`;
* **a stored right-hand side** (`ruleAgree`): both sides inferred,
  their types definitionally equal (so both members of one type: both
  the point or neither), the sides definitionally equal — the stored
  reading is graded and reads as the generated one (`storedRhs_sem`);
* **the ι contract carried over** (`recRuleLaw_stored`): a rule's law
  at the generated type and right-hand side gives the law at the stored
  ones, at any carrier with the same leaves, readings and constructor
  lookups.  The type enters the law only as a fit premise, the
  right-hand side only through its reading's value and grading.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Two towers that agree along their chains -/

/-- **Two readings agree as `k`-binder towers at `ρ`**: both are Π's
whose domains read alike at `ρ`, and whose bodies agree as
`(k-1)`-binder towers at every member of the domain; at `0` binders,
they read alike. -/
@[expose] def TEqAt : Nat → (Nat → V) → Term → Term → Prop
  | 0, ρ, T, T' => interp V ρ T = interp V ρ T'
  | k + 1, ρ, T, T' => ∃ A B A' B', T = .pi A B ∧ T' = .pi A' B' ∧
      interp V ρ A = interp V ρ A' ∧
      ∀ x, x ∈ˢ interp V ρ A → TEqAt k (cons x ρ) B B'

/-- Agreeing towers read alike. -/
theorem TEqAt.interp_eq : ∀ {k : Nat} {ρ : Nat → V} {T T' : Term},
    TEqAt k ρ T T' → interp V ρ T = interp V ρ T'
  | 0, _, _, _, h => h
  | _ + 1, ρ, _, _, h => by
    obtain ⟨A, B, A', B', rfl, rfl, hA, hB⟩ := h
    simp only [interp_pi]
    rw [← hA]
    exact piV_congr fun x hx => (hB x hx).interp_eq

/-- Agreement survives substituting a term for a variable. -/
theorem TEqAt.inst : ∀ {k : Nat} {c : Nat} {ρ : Nat → V} {a T T' : Term},
    TEqAt k (instE c (interp V (shiftE c 0 ρ) a) ρ) T T' →
    TEqAt k ρ (T.inst a c) (T'.inst a c)
  | 0, c, ρ, a, T, T', h => by
    show interp V ρ (T.inst a c) = interp V ρ (T'.inst a c)
    rw [interp_inst, interp_inst]
    exact h
  | k + 1, c, ρ, a, _, _, h => by
    obtain ⟨A, B, A', B', rfl, rfl, hA, hB⟩ := h
    refine ⟨A.inst a c, B.inst a (c + 1), A'.inst a c, B'.inst a (c + 1),
      Term.inst_pi a c A B, Term.inst_pi a c A' B', ?_, fun x hx => ?_⟩
    · rw [interp_inst, interp_inst]; exact hA
    · rw [interp_inst] at hx
      refine TEqAt.inst (c := c + 1) ?_
      rw [shiftE_succ_cons, ← cons_instE]
      exact hB x hx

/-- **A fit of at most `k` arguments moves along agreeing towers.** -/
theorem TEqAt.fit {ρ : Nat → V} : ∀ {T : Term} {xs : List Term} {rest : Term},
    TeleFitPA V ρ T xs rest → ∀ {k : Nat} {T' : Term}, TEqAt k ρ T T' → xs.length ≤ k →
      ∃ rest', TeleFitPA V ρ T' xs rest' := by
  intro T xs rest h
  induction h with
  | nil => intro _ T' _ _; exact ⟨T', TeleFitPA.nil⟩
  | @cons A B rest a as hmem _ ih =>
    intro k T' hk hlen
    match k, hk with
    | k + 1, hk =>
      obtain ⟨A₁, B₁, A', B', he, rfl, hA, hB⟩ := hk
      obtain ⟨rfl, rfl⟩ : A = A₁ ∧ B = B₁ := by injection he with h1 h2; exact ⟨h1, h2⟩
      have hB' : TEqAt k ρ (B.inst a 0) (B'.inst a 0) := by
        refine TEqAt.inst (c := 0) ?_
        rw [shiftE_zero_zero, instE_zero]
        exact hB _ hmem
      obtain ⟨rest', hr⟩ := ih hB' (by simp at hlen; omega)
      exact ⟨rest', TeleFitPA.cons (hA ▸ hmem) hr⟩

/-- **Agreeing towers from their contexts**: two `.pi` telescopes whose
`i`-th domains read alike under every valuation satisfying the second
one's earlier domains (above a frame `Δ₀`), and whose residues read alike
under the second one's whole context, agree at every valuation
satisfying `Δ₀`. -/
theorem tEqAt_of_tele :
    ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
      PiTeleAV k T Γ R → ∀ {T' : Term} {Γ' : List Term} {R' : Term},
      PiTeleAV k T' Γ' R' → ∀ {Δ₀ : List Term},
      (∀ i, i < k → ∀ σ : Nat → V, Sat V (Γ'.drop (k - i) ++ Δ₀) σ →
        interp V σ (Γ.getD (k - 1 - i) default) = interp V σ (Γ'.getD (k - 1 - i) default)) →
      (∀ σ : Nat → V, Sat V (Γ' ++ Δ₀) σ → interp V σ R = interp V σ R') →
      ∀ ρ : Nat → V, Sat V Δ₀ ρ → TEqAt k ρ T T' := by
  intro k T Γ R h
  induction h with
  | nil =>
    intro T' Γ' R' h' Δ₀ _ hres ρ hρ
    cases h'
    exact hres ρ (by simpa using hρ)
  | @cons k A B R Γ₁ h ih =>
    intro T' Γ' R' h' Δ₀ hdom hres ρ hρ
    obtain ⟨A', B', Γ₂, rfl, rfl, h₂⟩ := h'.succ_inv
    have hlen₁ : Γ₁.length = k := h.length
    have hlen₂ : Γ₂.length = k := h₂.length
    -- the head domains: binder `0`, at the frame alone
    have hA : ∀ σ : Nat → V, Sat V Δ₀ σ → interp V σ A = interp V σ A' := by
      intro σ hσ
      have := hdom 0 (by omega) σ (by
        rw [Nat.sub_zero, show k + 1 = (Γ₂ ++ [A']).length by simp [hlen₂],
          List.drop_length, List.nil_append]
        exact hσ)
      rwa [show (Γ₁ ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
          rw [List.getElem?_append_right (by omega), hlen₁, Nat.sub_self]; rfl,
        show (Γ₂ ++ [A']).getD (k + 1 - 1 - 0) default = A' from by
          simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
          rw [List.getElem?_append_right (by omega), hlen₂, Nat.sub_self]; rfl] at this
    refine ⟨A, B, A', B', rfl, rfl, hA ρ hρ, fun x hx => ?_⟩
    refine ih h₂ (Δ₀ := A' :: Δ₀) (fun i hi σ hσ => ?_) (fun σ hσ => ?_) (cons x ρ)
      (Sat_cons V hρ (by rw [← hA ρ hρ]; exact hx))
    · have := hdom (i + 1) (by omega) σ (by
        rw [show k + 1 - (i + 1) = k - i from by omega,
          List.drop_append_of_le_length (by omega), List.append_assoc,
          List.singleton_append]
        exact hσ)
      rwa [show (Γ₁ ++ [A]).getD (k + 1 - 1 - (i + 1)) default
          = Γ₁.getD (k - 1 - i) default from by
          simp only [List.getD]
          rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
            List.getElem?_append_left (by omega)],
        show (Γ₂ ++ [A']).getD (k + 1 - 1 - (i + 1)) default
          = Γ₂.getD (k - 1 - i) default from by
          simp only [List.getD]
          rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
            List.getElem?_append_left (by omega)]] at this
    · exact hres σ (by rw [List.append_assoc, List.singleton_append]; exact hσ)

/-- **A type tower's residue is a type**: under a context satisfying
the telescope, the residue of a graded type is graded and a type. -/
theorem piTeleAV_residue_ty :
    ∀ {k : Nat} {T : Term} {Γ : List Term} {R : Term},
      PiTeleAV k T Γ R → ∀ {Δ₀ : List Term},
      (∀ ρ : Nat → V, Sat V Δ₀ ρ → WellDenotedTy V ρ T) →
      ∀ ρ : Nat → V, Sat V (Γ ++ Δ₀) ρ → WellDenotedTy V ρ R := by
  intro k T Γ R h
  induction h with
  | nil => intro Δ₀ hT ρ hρ; exact hT ρ (by simpa using hρ)
  | @cons k A B R Γ' h ih =>
    intro Δ₀ hT ρ hρ
    refine ih (Δ₀ := A :: Δ₀) (fun σ hσ => ?_) ρ
      (by rw [List.append_assoc, List.singleton_append] at hρ; exact hρ)
    obtain ⟨h0, htl⟩ := Sat_cons_inv hσ
    have hpi := cast (WellDenoted_pi V _ A B) (hT _ htl).1
    have h1 := hpi.2.2.1 _ h0
    have h2 := hpi.2.2.2 _ h0
    rw [cons_eta] at h1 h2
    exact ⟨h1, h2⟩

/-! ## Application spines read through their head -/

/-- A spine reads through its head's value. -/
theorem interp_mkAppN_head_congr {ρ : Nat → V} :
    ∀ (as : List Term) {f f' : Term}, interp V ρ f = interp V ρ f' →
      interp V ρ (Term.mkAppN f as) = interp V ρ (Term.mkAppN f' as)
  | [], _, _, h => h
  | a :: as, f, f', h => by
    simp only [Term.mkAppN]
    exact interp_mkAppN_head_congr as (by simp only [interp_app, h])

/-- A spine's grading reads its head's value and grading only. -/
theorem wellDenoted_mkAppN_head_congr {ρ : Nat → V} :
    ∀ (as : List Term) {f f' : Term}, WellDenoted V ρ f' → interp V ρ f = interp V ρ f' →
      WellDenoted V ρ (Term.mkAppN f as) → WellDenoted V ρ (Term.mkAppN f' as)
  | [], _, _, hw, _, _ => hw
  | a :: as, f, f', hw, he, h => by
    simp only [Term.mkAppN] at h ⊢
    have happ := Rules.mkAppN_head as h
    refine wellDenoted_mkAppN_head_congr as ?_ (by simp only [interp_app, he]) h
    have hc := cast (WellDenoted_app V ρ f a) happ
    exact cast (WellDenoted_app V ρ f' a).symm ⟨hw, hc.2.1, by rw [← he]; exact hc.2.2⟩

/-! ## The stored type -/


/-- **The stored type, in the model** (`recTyCheck` at the generated
install): at every level assignment the stored type reads, its reading
is a graded type, and it agrees with the generated type's reading as an
`n`-binder tower at every valuation. -/
theorem storedTy_sem {env : Env} (mp : EnvModelM V env) {F : Nat}
    {rec : Name} {lps : List Name} {n : Nat} {S G : Expr}
    (hck : ConLeche.recTyCheck (ConLeche.fueledOps .verified F) .plain (ConLeche.mkFEnv env) rec lps n
      S G = .ok ())
    (hGb : G.looseBVarsBounded 0 = true)
    (hGr : ∀ φ : Name → Nat, ∃ TG, denote mp.base2.acval env φ 0 G = some TG)
    (hGw : ∀ (φ : Name → Nat) (TG : Term), denote mp.base2.acval env φ 0 G = some TG →
      ∀ ρ : Nat → V, WellDenotedTy V ρ TG) (φ : Name → Nat) :
    ∃ TS TG, denote mp.base2.acval env φ 0 S = some TS ∧
      denote mp.base2.acval env φ 0 G = some TG ∧
      (∀ ρ : Nat → V, WellDenotedTy V ρ TS) ∧ ∀ ρ : Nat → V, TEqAt n ρ TS TG := by
  obtain ⟨hSb, hSf, hGf, -, -, ⟨st, u, hinf, hens⟩, sfvs, srest, gfvs, grest, hopS, hopG,
    hdoms, hres⟩ := ConLeche.recTyCheck_inv hck
  have hc := claimsAt_of (V := V) mp φ F
  have hwS : Expr.WScoped 0 S := Expr.WScoped.of_not_hasFvar hSf
  have hnlS : S.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hSf
  have hLS : Expr.LeavesBounded S := fun l hl => by
    rw [hnlS] at hl; exact absurd hl List.not_mem_nil
  have hinf' : inferTypeCore .verified false env F 0 S = .ok st := hinf
  have hens' : ConLeche.ensureSortCore .verified false env F 0 st = .ok u := hens
  obtain ⟨TS, hTS⟩ := acceptedReads_of mp.base2 φ hinf' hwS hSb hLS
  have hsr := hc.sortRow hinf' hens' hwS hSb hLS (CtxOk.nil hnlS) hTS
  have hTSw : ∀ ρ : Nat → V, WellDenotedTy V ρ TS := fun ρ =>
    ⟨(hsr ρ (Sat_nil V ρ)).1, IsTy_of_mem_univ (hsr ρ (Sat_nil V ρ)).2⟩
  obtain ⟨TG, hTG⟩ := hGr φ
  have hTGw := hGw φ TG hTG
  obtain ⟨ΓS, RS, htS, OS⟩ := opened_of hopS hSf hSb hTS (fun ρ => (hTSw ρ).1)
  obtain ⟨ΓG, RG, htG, OG⟩ := opened_of hopG hGf hGb hTG (fun ρ => (hTGw ρ).1)
  have PF := paramFrames hc (nP := n) (nF := 0) OG OS (fun i hi => by
    obtain ⟨a, b, ha, hb, hd⟩ := ConLeche.recDomsAt_inv hdoms i (Nat.zero_le _) (by omega)
    exact ⟨a, b, ha, hb, hd⟩)
  simp only [Nat.add_zero] at PF
  have hlS := OS.len
  have hlG := OG.len
  have hsatn : ∀ ρ : Nat → V, Sat V ΓS ρ ↔ Sat V ΓG ρ := by
    intro ρ; have := (PF n (Nat.le_refl _)).1 ρ; simpa using this
  -- the residues, compared at the generated context
  have hCa₀ := OS.ctx (Nat.le_refl n) OS.bodyScoped.1 OS.bodyScoped.2.2.2
  have hCb₀ := OG.ctx (Nat.le_refl n) OG.bodyScoped.1 OG.bodyScoped.2.2.2
  simp only [Nat.sub_self, List.drop_zero] at hCa₀ hCb₀
  have hCa : CtxOk mp.base2 φ n ΓG srest := by
    refine hCa₀.transfer hlG (fun ρ h => (hsatn ρ).mpr h) ?_
    intro p A₁ A₂ hA₁ hA₂ ρ hρ
    have hp : p < n := by
      have := (List.getElem?_eq_some_iff.mp hA₂).1; omega
    have h1 := (PF (n - 1 - p) (by omega)).2 (by omega) (fun j => ρ (j + (p + 1)))
      (by
        rw [show n - (n - 1 - p) = p + 1 by omega]
        exact Sat_drop ((hsatn ρ).mpr hρ) (p + 1))
    rw [show n - 1 - (n - 1 - p) = p by omega, List.getD, List.getD, hA₁, hA₂] at h1
    exact h1
  have hres' := hc.defEqRow hres OS.bodyScoped.1 OS.bodyScoped.2.1 OS.bodyScoped.2.2.1
    OG.bodyScoped.1 OG.bodyScoped.2.1 OG.bodyScoped.2.2.1 hCa hCb₀ OS.body OG.body
    (fun ρ hρ => piTeleAV_residue_ty htS (Δ₀ := []) (fun ρ _ => hTSw ρ) ρ
      (by simpa using (hsatn ρ).mpr hρ))
    (fun ρ hρ => piTeleAV_residue_ty htG (Δ₀ := []) (fun ρ _ => hTGw ρ) ρ (by simpa using hρ))
  refine ⟨TS, TG, hTS, hTG, hTSw, fun ρ => tEqAt_of_tele htS htG (Δ₀ := [])
    (fun i hi σ hσ => ?_) (fun σ hσ => hres' σ (by simpa using hσ)) ρ (Sat_nil V ρ)⟩
  rw [List.append_nil] at hσ
  exact (PF i (by omega)).2 hi σ (((PF i (by omega)).1 σ).mpr hσ)

/-! ## A stored right-hand side -/

/-- **A stored right-hand side, in the model** (`ruleAgree` at the
generated install): at every level assignment where the generated side
reads, the stored side reads, is graded, and reads as the generated
one. -/
theorem storedRhs_sem {env : Env} (mp : EnvModelM V env) {F : Nat}
    {rec ctor : Name} {lps : List Name} {s g : Expr}
    (hck : ConLeche.ruleAgree (ConLeche.fueledOps .verified F) .plain (ConLeche.mkFEnv env) rec ctor lps
      s g = .ok ())
    (hgb : g.looseBVarsBounded 0 = true) (φ : Name → Nat) {Rg : Term}
    (hRg : denote mp.base2.acval env φ 0 g = some Rg) :
    ∃ Rs, denote mp.base2.acval env φ 0 s = some Rs ∧
      ∀ ρ : Nat → V, WellDenoted V ρ Rs ∧ interp V ρ Rs = interp V ρ Rg := by
  obtain ⟨hsb, hsf, hgf, -, -, ts, tg, hts, htg, hdt, hds⟩ := ConLeche.ruleAgree_inv hck
  have hc := claimsAt_of (V := V) mp φ F
  have hws : Expr.WScoped 0 s := Expr.WScoped.of_not_hasFvar hsf
  have hnls : s.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hsf
  have hLs : Expr.LeavesBounded s := fun l hl => by
    rw [hnls] at hl; exact absurd hl List.not_mem_nil
  have hwg : Expr.WScoped 0 g := Expr.WScoped.of_not_hasFvar hgf
  have hnlg : g.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hgf
  have hLg : Expr.LeavesBounded g := fun l hl => by
    rw [hnlg] at hl; exact absurd hl List.not_mem_nil
  have hts' : inferTypeCore .verified false env F 0 s = .ok ts := hts
  have htg' : inferTypeCore .verified false env F 0 g = .ok tg := htg
  obtain ⟨Rs, hRs⟩ := acceptedReads_of mp.base2 φ hts' hws hsb hLs
  obtain ⟨tsa, htsa⟩ := hc.reads hts' hws hsb hLs (CtxOk.nil hnls) hRs
  obtain ⟨tga, htga⟩ := hc.reads htg' hwg hgb hLg (CtxOk.nil hnlg) hRg
  obtain ⟨hRsw, htsw, hRsm⟩ := hc.infer hts' hws hsb hLs (CtxOk.nil hnls) hRs htsa
  obtain ⟨hRgw, htgw, hRgm⟩ := hc.infer htg' hwg hgb hLg (CtxOk.nil hnlg) hRg htga
  -- the two types, and the two sides
  have hwts := inferTypeCore_WScoped mp.base2.wf F hts' hws
  have hbts := inferTypeCore_looseBVars mp.base2.wf F hts' hws hsb hLs
  have hLts : Expr.LeavesBounded ts := fun l hl =>
    hLs l (inferTypeCore_fvarLeaves mp.base2.wf F hts' hws l hl)
  have hwtg := inferTypeCore_WScoped mp.base2.wf F htg' hwg
  have hbtg := inferTypeCore_looseBVars mp.base2.wf F htg' hwg hgb hLg
  have hLtg : Expr.LeavesBounded tg := fun l hl =>
    hLg l (inferTypeCore_fvarLeaves mp.base2.wf F htg' hwg l hl)
  have hnlts : ts.fvarLeaves = [] := by
    cases h : ts.fvarLeaves with
    | nil => rfl
    | cons l _ =>
      have := inferTypeCore_fvarLeaves mp.base2.wf F hts' hws l (by rw [h]; exact List.mem_cons_self)
      rw [hnls] at this; exact absurd this List.not_mem_nil
  have hnltg : tg.fvarLeaves = [] := by
    cases h : tg.fvarLeaves with
    | nil => rfl
    | cons l _ =>
      have := inferTypeCore_fvarLeaves mp.base2.wf F htg' hwg l (by rw [h]; exact List.mem_cons_self)
      rw [hnlg] at this; exact absurd this List.not_mem_nil
  have hty := hc.defEqRow hdt hwts hbts hLts hwtg hbtg hLtg (CtxOk.nil hnlts) (CtxOk.nil hnltg)
    htsa htga (fun ρ hρ => htsw ρ hρ) (fun ρ hρ => htgw ρ hρ)
  have hside := hc.defeq hds hws hsb hLs hwg hgb hLg (CtxOk.nil hnls) (CtxOk.nil hnlg) hRs hRg
    hRsw hRgw
  refine ⟨Rs, hRs, fun ρ => ⟨hRsw ρ (Sat_nil V ρ), ?_⟩⟩
  have hρ := Sat_nil V ρ
  exact IsTy.eq_of_ne_pt (htgw ρ hρ).2 (hty ρ hρ ▸ hRsm ρ hρ) (hRgm ρ hρ) (hside ρ hρ)

/-! ## The ι contract, carried to the stored recursor -/

/-- **The ι contract at the stored type and right-hand side** from the
generated one's, at a carrier with the same leaves (`hac`), the same
readings (`hde`), the same constructor lookups (`hctor`) and the same
`Prop`-family test (`hnp`): the stored type's reading enters the law only
as a fit premise (`hty`: a fit of at most `mI + 1` arguments at the
stored reading is one at the generated), the right-hand side only through
its reading's value and grading (`hrhs`). -/
theorem recRuleLaw_stored {envG envS : Env} {mG : EnvModel V envG} {mS : EnvModel V envS}
    (hac : mS.acval = mG.acval)
    (hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mG.acval envS ψ d e = denote mG.acval envG ψ d e)
    (hctor : ∀ (c : Name) (cvj : ConstantVal) (cnP cnF : Nat),
      envS.find? c = some (.ctorInfo cvj cnP cnF) → envG.find? c = some (.ctorInfo cvj cnP cnF))
    (hnp : ∀ (cvj : ConstantVal) (us : List Level),
      ConLeche.iotaCtorNeverProp envS.find? cvj us = ConLeche.iotaCtorNeverProp envG.find? cvj us)
    {φ : Name → Nat} {n : Name} {cvG : ConstantVal} {T : Expr} {mI rP : Nat} {rlG : RecRule}
    {e : Expr}
    (hty : ∀ us : List Level, us.length = cvG.levelParams.length → ∀ TS : Term,
      denote mG.acval envG φ 0 (T.instantiateLevelParams cvG.levelParams us) = some TS →
      ∃ TG, denote mG.acval envG φ 0 (cvG.type.instantiateLevelParams cvG.levelParams us)
          = some TG ∧
        ∀ (ρ : Nat → V) (xs : List Term) (rest : Term), xs.length ≤ mI + 1 →
          TeleFitPA V ρ TS xs rest → ∃ rest', TeleFitPA V ρ TG xs rest')
    (hrhs : ∀ us : List Level, us.length = cvG.levelParams.length → ∀ RaG : Term,
      denote mG.acval envG φ 0 (rlG.rhs.instantiateLevelParams cvG.levelParams us) = some RaG →
      ∃ RaS, denote mG.acval envG φ 0 (e.instantiateLevelParams cvG.levelParams us) = some RaS ∧
        ∀ ρ : Nat → V, WellDenoted V ρ RaS ∧ interp V ρ RaS = interp V ρ RaG)
    (h : RecRuleLaw mG φ n cvG mI rP rlG) :
    RecRuleLaw mS φ n { cvG with type := T } mI rP { rlG with rhs := e } := by
  unfold RecRuleLaw RecRuleExtra at h ⊢
  simp only [hac, hde, hnp] at ⊢
  obtain ⟨hrPle, hmain, hextra⟩ := h
  -- the stored right-hand side's reading, at given levels
  have hRa : ∀ us : List Level, us.length = cvG.levelParams.length →
      ∃ RaG RaS, denote mG.acval envG φ 0
          (rlG.rhs.instantiateLevelParams cvG.levelParams us) = some RaG ∧
        denote mG.acval envG φ 0 (e.instantiateLevelParams cvG.levelParams us) = some RaS ∧
        ∀ ρ : Nat → V, WellDenoted V ρ RaS ∧ interp V ρ RaS = interp V ρ RaG := by
    intro us hlen
    obtain ⟨RaG, hRaG, -⟩ := hmain us hlen
    obtain ⟨RaS, hRaS, hS⟩ := hrhs us hlen RaG hRaG
    exact ⟨RaG, RaS, hRaG, hRaS, hS⟩
  refine ⟨hrPle, fun us hlen => ?_, fun us hlen TVa hTVa => ?_⟩
  · obtain ⟨RaG, hRaG, -, hpins, hlaw⟩ := hmain us hlen
    obtain ⟨RaS, hRaS, hS⟩ := hrhs us hlen RaG hRaG
    refine ⟨RaS, hRaS, fun ρ => (hS ρ).1, fun lvls pins hfire i hi => ?_, ?_⟩
    · obtain ⟨vpa, hvpa, hok⟩ := hpins lvls pins hfire i hi
      refine ⟨vpa, hvpa, fun ρ zs TVa restR hzl hzw hTVa hfit => ?_⟩
      obtain ⟨TG, hTG, hfitT⟩ := hty us hlen TVa hTVa
      obtain ⟨r', hr'⟩ := hfitT ρ zs restR (by omega) hfit
      exact hok ρ zs TG r' hzl hzw hTG hr'
    · intro cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxl hyl hujl hψ hyw hpin hTVa
        hTVja hfitR hfitC
      obtain ⟨TG, hTG, hfitT⟩ := hty us hlen TVa hTVa
      obtain ⟨r', hr'⟩ := hfitT ρ _ restR (by simp [hxl]) hfitR
      obtain ⟨heq, hwd⟩ := hlaw cvj cnP cnF (hctor _ _ _ _ hfc) usj ρ xs ys TG TVja r' restC
        hxl hyl hujl hψ hyw hpin hTG hTVja hr' hfitC
      exact ⟨heq.trans (interp_mkAppN_head_congr _ (hS ρ).2.symm),
        fun ha hb => wellDenoted_mkAppN_head_congr _ (hS ρ).1 (hS ρ).2.symm (hwd ha hb)⟩
  · obtain ⟨TG, hTG, hfitT⟩ := hty us hlen TVa hTVa
    obtain ⟨hK, hrest⟩ := hextra us hlen TG hTG
    have fitN : ∀ {ρ : Nat → V} {xs : List Term} {a restR : Term}, xs.length = mI →
        TeleFitPA V ρ TVa (xs ++ [a]) restR → ∃ r', TeleFitPA V ρ TG (xs ++ [a]) r' :=
      fun hxl hfit => hfitT _ _ _ (by simp [hxl]) hfit
    refine ⟨fun hk => ?_, fun cvj cnP cnF hfc => ?_⟩
    · obtain ⟨hnf, hKl⟩ := hK hk
      refine ⟨hnf, fun Ra hRaS ρ xs a restR hxl hfit hxw => ?_⟩
      obtain ⟨RaG, RaS, hRaG, hRaS', hS⟩ := hRa us hlen
      obtain rfl : Ra = RaS := Option.some.inj (hRaS.symm.trans hRaS')
      obtain ⟨r', hr'⟩ := fitN hxl hfit
      obtain ⟨heq, hwd⟩ := hKl RaG hRaG ρ xs a r' hxl hr' hxw
      exact ⟨heq.trans (interp_mkAppN_head_congr _ (hS ρ).2.symm),
        fun hw => wellDenoted_mkAppN_head_congr _ (hS ρ).1 (hS ρ).2.symm (hwd hw)⟩
    · obtain ⟨har, hrest2⟩ := hrest cvj cnP cnF (hctor _ _ _ _ hfc)
      refine ⟨har, fun hk => ?_⟩
      obtain ⟨hSc, hTc, hPU⟩ := hrest2 hk
      refine ⟨fun hn ρ xs a restR hxl hfit => ?_, fun hn usj hujl TVja hTVja ρ xs ys restR restC
          hxl hyl hfit => ?_, fun usj hujl hψ TVja hTVja => ?_⟩
      · obtain ⟨r', hr'⟩ := fitN hxl hfit
        exact hSc hn ρ xs a r' hxl hr'
      · obtain ⟨r', hr'⟩ := fitN hxl hfit
        exact hTc hn usj hujl TVja hTVja ρ xs ys r' restC hxl hyl hr'
      · obtain ⟨hP, hU⟩ := hPU usj hujl hψ TVja hTVja
        refine ⟨fun ρ xs a restR hxl hfit => ?_, fun ρ xs ys restR restC hxl hyl hfit => ?_⟩
        · obtain ⟨r', hr'⟩ := fitN hxl hfit
          exact hP ρ xs a r' hxl hr'
        · obtain ⟨r', hr'⟩ := fitN hxl hfit
          exact hU ρ xs ys r' restC hxl hyl hr'

end ConLeche.Model
