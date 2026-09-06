import Setlec.SetP.Direct.DirectRecSpineP

/-!
# The recursor's frame kit, continued (task #175 W4c, P3 module 6, part 9)

Openings at any depth, per-index scoping of an opening's variables and
of an `instPisAt` residual, frame shifts under a consed spine,
application scoping, the identification of two contexts from entry-wise
agreement (`frameIdent`), the minor space as a Π-tower reading
(`interp_minorSp_of_tele`), and list arithmetic.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Openings at any depth -/

theorem stripPis_isSome_of_instantiate1_fvar :
    ∀ (n : Nat) {e : Expr} {i : Nat} {nm : Name} {ty : Expr} {k : Nat},
      (Expr.stripPis n (e.instantiate1 (.fvar i nm ty) k)).isSome = true →
      (Expr.stripPis n e).isSome = true
  | 0, _, _, _, _, _, _ => by simp [Expr.stripPis]
  | n + 1, e, i, nm, ty, k, h => by
    match e, h with
    | .forallE nm' dom body mb, h =>
      simp only [Expr.instantiate1_forallE, Expr.stripPis, Option.isSome_map] at h ⊢
      exact stripPis_isSome_of_instantiate1_fvar n h
    | .bvar j, h =>
      simp only [Expr.instantiate1_bvar] at h
      split at h
      · simp [Expr.stripPis] at h
      · split at h <;> simp [Expr.stripPis] at h
    | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.instantiate1, Expr.stripPis] at h

theorem openPisAtFvars_stripPis_isSome :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → (Expr.stripPis n e).isSome = true
  | 0, _, _, _, _, _ => by simp [Expr.stripPis]
  | n + 1, e, d, fvs, o, h => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' o' h' =>
        have := openPisAtFvars_stripPis_isSome n h'
        simp only [Expr.stripPis, Option.isSome_map]
        exact stripPis_isSome_of_instantiate1_fvar n this
      · exact nomatch h
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

theorem openPisAtFvars_of_stripPis_isSome :
    ∀ (n : Nat) {e : Expr} (d : Nat), (Expr.stripPis n e).isSome = true →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, e, _, _ => ⟨[], e, rfl⟩
  | n + 1, e, d, h => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      obtain ⟨fvs, o, ho⟩ := openPisAtFvars_of_stripPis_isSome n (d + 1)
        (Expr.stripPis_instantiate1_isSome (v := .fvar d nm dom) n 0 h)
      exact ⟨.fvar d nm dom :: fvs, o, by simp only [openPisAtFvars, ho]⟩
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- An opening at one depth exists at every depth. -/
theorem openPisAtFvars_any_depth {n : Nat} {e : Expr} {d : Nat} {fvs : List Expr}
    {o : Expr} (h : openPisAtFvars n e d = some (fvs, o)) (d' : Nat) :
    ∃ fvs' o', openPisAtFvars n e d' = some (fvs', o') :=
  openPisAtFvars_of_stripPis_isSome n d' (openPisAtFvars_stripPis_isSome n h)

/-! ## Per-index scoping -/

/-- Each opened variable's annotation is scoped at its own depth. -/
theorem openPisAtFvars_typeWScoped :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → Expr.WScoped d e →
      ∀ (i : Nat) (x : Expr), fvs[i]? = some x → Expr.WScoped (d + i) (Expr.fvarTypeD x)
  | 0, _, _, _, _, hop, _, i, x, hx => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, e, d, fvs, o, hop, hw, i, x, hx => by
    match e, hop with
    | .forallE nm dom body mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hw' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
          simpa only [Expr.WScoped] using hw
        cases i with
        | zero =>
          obtain rfl : Expr.fvar d nm dom = x := by simpa using hx
          show Expr.WScoped (d + 0) dom
          rw [Nat.add_zero]; exact hw'.1
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          have hb : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d nm dom)) :=
            Expr.WScoped.instantiate1_gen (v := .fvar d nm dom) (d := d + 1)
              (by simp only [Expr.WScoped]; exact ⟨by omega, hw'.1⟩) 0
              (Expr.WScoped.mono (by omega) hw'.2)
          have := openPisAtFvars_typeWScoped n hop' hb i x hx
          rw [show d + (i + 1) = d + 1 + i from by omega]
          exact this
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _ _, hop | .sort _, hop | .const _ _, hop | .app _ _, hop
    | .lam _ _ _ _, hop | .letE _ _ _ _, hop | .lit _, hop | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-- An `instPisAt` residual is scoped at the spine's end. -/
theorem instPisAt_res_WScoped :
    ∀ (sp : List Expr) {d : Nat} {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) → Expr.WScoped d ty →
      (∀ (i : Nat) (a : Expr), sp[i]? = some a → Expr.WScoped (d + i + 1) a) →
      Expr.WScoped (d + sp.length) rs
  | [], d, ty, ds, rs, h, hty, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hty
  | a :: sp, d, ty, ds, rs, h, hty, hsp => by
    match ty, h with
    | .forallE nm dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hty' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
          simpa only [Expr.WScoped] using hty
        have ha : Expr.WScoped (d + 1) a := by
          have := hsp 0 a rfl
          rwa [Nat.add_zero] at this
        have hb : Expr.WScoped (d + 1) (body.instantiate1 a) :=
          Expr.WScoped.instantiate1_gen ha 0 (Expr.WScoped.mono (by omega) hty'.2)
        have := instPisAt_res_WScoped sp h1 hb (fun i a' ha' => by
          have := hsp (i + 1) a' (by simpa using ha')
          rwa [show d + (i + 1) + 1 = d + 1 + i + 1 from by omega] at this)
        simp only [List.length_cons]
        rw [show d + (sp.length + 1) = d + 1 + sp.length from by omega]
        exact this
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.instPisAt] at h

theorem WScoped_mkAppN {d : Nat} :
    ∀ {as : List Expr} {f : Expr}, Expr.WScoped d f → (∀ a ∈ as, Expr.WScoped d a) →
      Expr.WScoped d (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    simp only [Expr.mkAppN]
    exact WScoped_mkAppN (by simp only [Expr.WScoped]; exact ⟨hf, has a List.mem_cons_self⟩)
      (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))

/-! ## Frame shifts under a consed spine -/

omit [SetTheory V] in
theorem shiftE_cons_succ' (n k : Nat) (a : V) (σ : Nat → V) :
    shiftE n (k + 1) (cons a σ) = cons a (shiftE n k σ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ i =>
    simp only [shiftE, cons_succ]
    by_cases h : i < k
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, show i + 1 + n = i + n + 1 from by omega, cons_succ]

omit [SetTheory V] in
theorem shiftE_consList_len' (n : Nat) :
    ∀ (as : List V) (k : Nat) (σ : Nat → V),
      shiftE n (as.length + k) (consList as σ) = consList as (shiftE n k σ)
  | [], _, _ => by simp
  | a :: as, k, σ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show as.length + 1 + k = as.length + (k + 1) from by omega,
      shiftE_consList_len' n as (k + 1) (cons a σ), shiftE_cons_succ']

omit [SetTheory V] in
theorem shiftE_consList_len (n : Nat) (as : List V) (σ : Nat → V) :
    shiftE n as.length (consList as σ) = consList as (shiftE n 0 σ) := by
  have := shiftE_consList_len' n as 0 σ
  rwa [Nat.add_zero] at this

omit [SetTheory V] in
theorem shiftE_cons_cons (a b : V) (σ : Nat → V) :
    shiftE 2 0 (cons a (cons b σ)) = σ := by
  rw [shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
theorem shiftE_one_cons (a : V) (σ : Nat → V) : shiftE 1 0 (cons a σ) = σ := by
  rw [shiftE_succ_cons, shiftE_zero_zero]

/-! ## List arithmetic -/

theorem getD_drop' {α : Type _} [Inhabited α] (l : List α) (k i : Nat) :
    (l.drop k).getD i default = l.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_succ_eq_getD_cons {Γ : List AVExpr} {n i : Nat} (hΓ : Γ.length = n)
    (hi : i < n) :
    Γ.drop (n - (i + 1)) = Γ.getD (n - 1 - i) default :: Γ.drop (n - i) := by
  rw [show n - (i + 1) = n - i - 1 from by omega,
    List.drop_eq_getElem_cons (l := Γ) (i := n - i - 1) (by omega)]
  have hG : Γ[n - i - 1]'(by omega) = Γ.getD (n - 1 - i) default := by
    rw [List.getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1; omega
  rw [hG, show n - i - 1 + 1 = n - i from by omega]

theorem mkPisAV_append :
    ∀ (l₁ l₂ : List (Nat × Nat × AVExpr)) (b : AVExpr),
      mkPisAV (l₁ ++ l₂) b = mkPisAV l₁ (mkPisAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkPisAV, mkPisAV_append l₁ l₂ b]

theorem Sat2_cons_of_tail {Δ : List AVExpr} {A : AVExpr} {ρ : Nat → V}
    (ht : Sat2 V Δ (fun j => ρ (j + 1)))
    (hx : ρ 0 ∈ˢ interp2 V (fun j => ρ (j + 1)) A) : Sat2 V (A :: Δ) ρ := by
  have h := Sat2_cons V ht hx
  have e : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i <;> rfl
  rwa [e] at h

/-! ## Two contexts, identified -/

/-- **Two contexts of one length whose entries interpret alike under
both have the same satisfying valuations**, at every depth. -/
theorem frameIdent {Γ₁ Γ₂ : List AVExpr} {n : Nat} (h1 : Γ₁.length = n)
    (h2 : Γ₂.length = n)
    (hent : ∀ i, i < n →
      (∀ ρ : Nat → V, Sat2 V (Γ₁.drop (n - i)) ρ ↔ Sat2 V (Γ₂.drop (n - i)) ρ) →
      ∀ ρ : Nat → V, Sat2 V (Γ₁.drop (n - i)) ρ →
      interp2 V ρ (Γ₁.getD (n - 1 - i) default) = interp2 V ρ (Γ₂.getD (n - 1 - i) default)) :
    ∀ i, i ≤ n → ∀ ρ : Nat → V, Sat2 V (Γ₁.drop (n - i)) ρ ↔ Sat2 V (Γ₂.drop (n - i)) ρ := by
  intro i
  induction i with
  | zero =>
    intro _ ρ
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  | succ i ih =>
    intro hi ρ
    have hiff := ih (by omega)
    rw [drop_succ_eq_getD_cons h1 (by omega), drop_succ_eq_getD_cons h2 (by omega)]
    constructor
    · intro h
      obtain ⟨hx, ht⟩ := Sat2_cons_inv h
      have ht' := (hiff _).mp ht
      refine Sat2_cons_of_tail ht' ?_
      rw [← hent i (by omega) hiff _ ht]
      exact hx
    · intro h
      obtain ⟨hx, ht⟩ := Sat2_cons_inv h
      have ht' := (hiff _).mpr ht
      refine Sat2_cons_of_tail ht' ?_
      rw [hent i (by omega) hiff _ ht']
      exact hx

/-! ## The minor space as a Π-tower reading -/

/-- **The minor space is the interpreted Π-tower** over field domains
that agree with the chain's, bits zero exactly at a zero elimination
level, whose core is the motive at the accumulated tuple. -/
theorem interp_minorSp_of_tele {ℓ w : Nat} {M : V} :
    ∀ {Fs : List AVExpr} {gds : List (Nat × Nat × AVExpr)} {Rm : AVExpr}
      {σ ρf : Nat → V} {acc : List V},
      gds.length = Fs.length →
      (∀ d ∈ gds, (ℓ = 0 ↔ d.2.1 = 0)) →
      (∀ (j : Nat) (as : List V), j < Fs.length → SpineFit ρf (Fs.take j) as →
        interp2 V (consList as σ) ((gds.getD j default).2.2)
          = interp2 V (consList as ρf) (Fs.getD j default)) →
      (∀ as : List V, SpineFit ρf Fs as →
        interp2 V (consList as σ) Rm
          = SetTheory.app M (if w = 0 then pt else mkTower (acc ++ as))) →
      interp2 V σ (mkPisAV gds Rm) = minorSp ℓ w M Fs ρf acc
  | [], [], Rm, σ, ρf, acc, _, _, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simpa [mkPisAV, minorSp] using this
  | [], _ :: _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _, _ => by simp at hlen
  | F :: Fs, d :: gds, Rm, σ, ρf, acc, hlen, hbits, hdom, hbase => by
    simp only [mkPisAV, interp2_pi, minorSp]
    have hd0 : interp2 V σ d.2.2 = interp2 V ρf F := by
      have := hdom 0 [] (by simp) trivial
      simpa [consList] using this
    rw [hd0, piR_congr_bit (v := d.2.1) (v' := ℓ) (hbits d List.mem_cons_self).symm]
    apply piR_congr
    intro a ha
    refine interp_minorSp_of_tele (by simpa using hlen)
      (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_ ?_
    · intro j as hj hsp
      have := hdom (j + 1) (a :: as) (by simpa using hj)
        (by simp only [List.take_succ_cons, SpineFit]; exact ⟨ha, hsp⟩)
      simpa [consList_cons] using this
    · intro as hsp
      have := hbase (a :: as) ⟨ha, hsp⟩
      rw [consList_cons] at this
      rw [this, List.append_cons]

end Setlec.SetP
