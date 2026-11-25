module

public import ConLeche.Model.Inductives.TargetRecRead

public section

/-!
# The target call's kit

Generic facts the call's typing (`TargetCallCore.lean`) is read with:

* `interp_mkPisAV_congr` — a Π-tower's value reads only the domains of
  its domains.
-/

namespace ConLeche.Model
open ConLeche.Verify (denote denote_const denote_fvar projNV)
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory

open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A Π-tower reads only its domains -/

/-! ## Syntax helpers -/

theorem WellDenoted_mkAppN_head {ρ : Nat → V} :
    ∀ (as : List Term) {g : Term},
      WellDenoted V ρ (Term.mkAppN g as) → WellDenoted V ρ g
  | [], _, h => h
  | a :: as, g, h => by
    have h1 := WellDenoted_mkAppN_head as (g := .app g a) h
    exact (cast (WellDenoted_app V ρ g a) h1).1

/-- A spine headed by the point is the point. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : Term} (hf : interp V ρ f = pt) :
    ∀ (as : List Term), interp V ρ (Term.mkAppN f as) = pt
  | [] => hf
  | a :: as => by
    rw [Term.mkAppN_cons]
    exact interp_mkAppN_pt (by rw [interp_app, hf, app_pt]) as

/-- **A graded application spine that is not the point, of a value of a
Π-tower, fits the tower**: the head is not the point, so it is a graph
(`mem_piSet_of_mem_piV`); each application node's clause puts its
argument in the domain of the graph the head is (`AppliesTo.mem`). -/
theorem spineFit_of_wellDenoted_mkAppN_pi {R : Term} :
    ∀ {pds : List Term} {h : Term} {args : List Term}
      {τ σ : Nat → V},
      interp V τ (Term.mkAppN h args) ≠ pt →
      WellDenoted V τ (Term.mkAppN h args) →
      interp V τ h ∈ˢ interp V σ (mkPisAV pds R) →
      args.length = pds.length →
      SpineFit σ (pds) (args.map (interp V τ))
  | [], _, [], _, _, _, _, _, _ => trivial
  | [], _, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, _, [], _, _, _, _, _, hlen => by simp at hlen
  | d :: pds, h, a :: args, τ, σ, hne, hwd, hmem, hlen => by
    simp only [List.map_cons, SpineFit]
    rw [Term.mkAppN_cons] at hwd hne
    have hwdA := WellDenoted_mkAppN_head args hwd
    have hap := (cast (WellDenoted_app V τ h a) hwdA).2.2
    have hhne : interp V τ h ≠ pt := fun h0 =>
      hne (interp_mkAppN_pt (by rw [interp_app, h0, app_pt]) args)
    have hmem' : interp V τ h ∈ˢ piSet (interp V σ d)
        (fun x => interp V (cons x σ) (mkPisAV pds R))
        (interp_hasSigmaPairs_cons σ (interp V σ d) (mkPisAV pds R)) := by
      have := hmem
      simp only [mkPisAV, interp_pi] at this
      exact mem_piSet_of_mem_piV this hhne
    have hx : interp V τ a ∈ˢ interp V σ d := hap.mem hmem'
    refine ⟨hx, ?_⟩
    refine spineFit_of_wellDenoted_mkAppN_pi (R := R) (h := .app h a) hne hwd ?_
      (by simpa using hlen)
    rw [interp_app]
    exact app_mem_of_mem_piSet hmem' hx

/-! ## Replacing free variables by terms -/

/-! ## The member abstraction, read at the members' own values -/

/-- Two optional readings agree: both absent, or both present and
related. -/
@[expose] def ReadAgree (P : Term → Term → Prop) : Option Term → Option Term → Prop
  | some a2, some a1 => P a2 a1
  | none, none => True
  | _, _ => False

/-- A projection spelling keeps a value and a truthfulness transfer. -/
theorem projNV_agree {ρ : Nat → V} :
    ∀ (n : Nat) {e2 e1 : Term}, interp V ρ e2 = interp V ρ e1 →
      (WellDenoted V ρ e2 → WellDenoted V ρ e1) →
      interp V ρ (projNV n e2) = interp V ρ (projNV n e1) ∧
        (WellDenoted V ρ (projNV n e2) → WellDenoted V ρ (projNV n e1))
  | 0, e2, e1, hv, hw => by
    refine ⟨by simp [projNV, hv], fun h => ?_⟩
    simp only [projNV, WellDenoted_fst] at h ⊢
    obtain ⟨h1, u, v, A, Bf, hS, h2, h3, h4⟩ := h
    exact ⟨hw h1, u, v, A, Bf, hS, hv ▸ h2, h3, h4⟩
  | n + 1, e2, e1, hv, hw => by
    refine projNV_agree n (e2 := .snd e2) (e1 := .snd e1) (by simp [hv]) fun h => ?_
    simp only [WellDenoted_snd] at h ⊢
    obtain ⟨h1, u, v, A, Bf, hS, h2, h3, h4⟩ := h
    exact ⟨hw h1, u, v, A, Bf, hS, hv ▸ h2, h3, h4⟩

section Abs

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}
  {names : List Name} {lvls : List Level} {formerTys : List Expr} {B : Nat} {hvC : Nat → V}

/-- The relation `targetAbs_read` concludes: at every valuation whose
hole slots carry the members' values, the abstract reading has the
concrete one's value, and its truthfulness gives the concrete one's. -/
@[expose] def AbsAgree (V : Type w) [SetTheory V] (k d : Nat) (hvC : Nat → V)
    (a2 a1 : Term) : Prop :=
  ∀ (vals : List V) (τ : Nat → V), vals.length = d → (∀ t, t < k → τ (k - 1 - t) = hvC t) →
    interp V (consList vals τ) a2 = interp V (consList vals τ) a1 ∧
      (WellDenoted V (consList vals τ) a2 → WellDenoted V (consList vals τ) a1)

theorem readAgree_refl {k d : Nat} (o : Option Term) :
    ReadAgree (AbsAgree V k d hvC) o o := by
  cases o with
  | none => trivial
  | some a => exact fun _ _ _ _ => ⟨rfl, id⟩

set_option maxHeartbeats 1600000 in
/-- **The member abstraction read at the members' own values is the
concrete term**: `targetAbs` replaces a member constant (at the block's
levels) by its hole; at a valuation carrying, at every hole's slot,
the member constant's own value, the two readings agree — the same
reading everywhere else. -/
theorem targetAbs_read
    (hnames : ∀ (n : Name) (t : Nat), names.findIdx? (· == n) = some t →
      t < formerTys.length ∧ ∃ ci : ConLeche.ConstantInfo, env.find? n = some ci ∧
        lvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (m.acval n (Level.substFn φ ci.toConstantVal.levelParams lvls))
          = hvC t) :
    ∀ (e : Expr) (d : Nat) (as2 as1 : List Expr),
      LocList (B + formerTys.length) d as2 → LocList (B + formerTys.length) d as1 →
      ReadAgree (AbsAgree V formerTys.length d hvC)
        (denote m.acval env φ (B + formerTys.length + d)
          ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) e).instantiateList
            as2 0))
        (denote m.acval env φ (B + formerTys.length + d) (e.instantiateList as1 0))
  | .bvar j, d, as2, as1, h2, h1 => by
    simp only [ConLeche.targetAbs]
    rcases Nat.lt_or_ge j d with hjd | hjd
    · obtain ⟨ty1, he1⟩ := h1.bvar_lt hjd
      obtain ⟨ty2, he2⟩ := h2.bvar_lt hjd
      rw [he1, he2, denote_fvar, denote_fvar]
      exact readAgree_refl (V := V) _
    · rw [h1.bvar_ge hjd, h2.bvar_ge hjd]
      exact readAgree_refl (V := V) _
  | .fvar i ty, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList, denote_fvar]
    exact readAgree_refl (V := V) _
  | .sort u, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList]
    exact readAgree_refl (V := V) _
  | .lit l, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList]
    exact readAgree_refl (V := V) _
  | .letE ty v b, d, as2, as1, h2, h1 => by
    have iht := targetAbs_read hnames ty d as2 as1 h2 h1
    have ihv := targetAbs_read hnames v d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denote]
    revert iht ihv
    cases hT2 : denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList as2 0)
      <;> cases hT1 : denote m.acval env φ (B + formerTys.length + d) (ty.instantiateList as1 0)
      <;> cases hA2 : denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) v).instantiateList as2 0)
      <;> cases hA1 : denote m.acval env φ (B + formerTys.length + d) (v.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i T2 T1 A2 A1
    intro _ hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
      show B + formerTys.length + d + 1 = B + formerTys.length + (d + 1) from by omega]
    have ihb := targetAbs_read hnames b (d + 1)
      (Expr.fvar (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
          as2 0) :: as2)
      (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1)
      (h2.cons _) (h1.cons _)
    revert ihb
    cases denote m.acval env φ (B + formerTys.length + (d + 1))
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) b).instantiateList
          (Expr.fvar (B + formerTys.length + d)
            ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
              as2 0) :: as2) 0)
      <;> cases denote m.acval env φ (B + formerTys.length + (d + 1))
        (b.instantiateList (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1) 0)
      <;> simp [ReadAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    obtain ⟨hAv, hAw⟩ := hA vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2 = interp V (cons x (consList vals τ)) b1 ∧
        (WellDenoted V (cons x (consList vals τ)) b2 → WellDenoted V (cons x (consList vals τ)) b1) := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    refine ⟨?_, fun hw => ?_⟩
    · rw [interp_letE, interp_letE, hAv]; exact (hbx _).1
    · rw [WellDenoted_letE] at hw ⊢
      obtain ⟨w1, w2⟩ := hw
      refine ⟨hAw w1, ?_⟩
      rw [← hAv]; exact (hbx _).2 w2
  | .const n us, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs]
    split
    · rename_i hus
      split
      · rename_i t ht
        obtain ⟨htk, ci, hfind, hlen, hval⟩ := hnames n t ht
        have hus' : us = lvls := by simpa using hus
        subst hus'
        rw [List.getD_eq_getElem?_getD, ConLeche.targetHoles, List.getElem?_map,
          List.getElem?_range htk, Option.map_some, Option.getD_some]
        simp only [Expr.instantiateList, denote_fvar]
        rw [denote_const hfind hlen]
        intro vals τ hvl hτ
        rw [interp_bvar, show B + formerTys.length + d - 1 - (B + t)
            = (formerTys.length - 1 - t) + vals.length from by omega, consList_apply_add,
          hτ t htk, hval]
        exact ⟨rfl, fun _ => m.acval_wellDenoted _ _ _⟩
      · simp only [Expr.instantiateList]; exact readAgree_refl (V := V) _
    · simp only [Expr.instantiateList]; exact readAgree_refl (V := V) _
  | .app f a, d, as2, as1, h2, h1 => by
    have ihf := targetAbs_read hnames f d as2 as1 h2 h1
    have iha := targetAbs_read hnames a d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denote]
    revert ihf iha
    cases denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) f).instantiateList as2 0)
      <;> cases denote m.acval env φ (B + formerTys.length + d) (f.instantiateList as1 0)
      <;> cases denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) a).instantiateList as2 0)
      <;> cases denote m.acval env φ (B + formerTys.length + d) (a.instantiateList as1 0)
      <;> simp [ReadAgree]
    intro hf ha vals τ hvl hτ
    obtain ⟨hfv, hfw⟩ := hf vals τ hvl hτ
    obtain ⟨hav, haw⟩ := ha vals τ hvl hτ
    refine ⟨by simp [hfv, hav], fun hw => ?_⟩
    rw [WellDenoted_app] at hw ⊢
    obtain ⟨w1, w2, h3⟩ := hw
    exact ⟨hfw w1, haw w2, by rw [hfv, hav] at h3; exact h3⟩
  | .proj sn i e, d, as2, as1, h2, h1 => by
    have ihe := targetAbs_read hnames e d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denote]
    revert ihe
    cases denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) e).instantiateList as2 0)
      <;> cases denote m.acval env φ (B + formerTys.length + d) (e.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? sn i with
    | some entry =>
      intro vals τ hvl hτ
      obtain ⟨hv, hw⟩ := he vals τ hvl hτ
      exact projNV_agree (i + 1) hv hw
    | none => trivial
  | .lam ty b, d, as2, as1, h2, h1 | .forallE ty b, d, as2, as1, h2, h1 => by
    have iht := targetAbs_read hnames ty d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denote]
    revert iht
    cases hA2 : denote m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList as2 0)
      <;> cases hA1 : denote m.acval env φ (B + formerTys.length + d) (ty.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
      show B + formerTys.length + d + 1 = B + formerTys.length + (d + 1) from by omega]
    have ihb := targetAbs_read hnames b (d + 1)
      (Expr.fvar (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
          as2 0) :: as2)
      (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1)
      (h2.cons _) (h1.cons _)
    revert ihb
    cases denote m.acval env φ (B + formerTys.length + (d + 1))
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) b).instantiateList
          (Expr.fvar (B + formerTys.length + d)
            ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
              as2 0) :: as2) 0)
      <;> cases denote m.acval env φ (B + formerTys.length + (d + 1))
        (b.instantiateList (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1) 0)
      <;> simp [ReadAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    obtain ⟨hAv, hAw⟩ := hA vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2 = interp V (cons x (consList vals τ)) b1 ∧
        (WellDenoted V (cons x (consList vals τ)) b2 → WellDenoted V (cons x (consList vals τ)) b1) := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    refine ⟨?_, fun hw => ?_⟩
    · first
      | (rw [interp_lam, interp_lam]; exact lamV_ext hAv _ _ fun x _ => (hbx x).1)
      | (rw [interp_pi, interp_pi]; exact piV_ext hAv _ _ fun x _ => (hbx x).1)
    · first
      | (rw [WellDenoted_lam] at hw ⊢
         obtain ⟨w1, wt, w2⟩ := hw
         exact ⟨hAw w1, hAv ▸ wt, fun x hx => (hbx x).2 (w2 x (hAv ▸ hx))⟩)
      | (rw [WellDenoted_pi] at hw ⊢
         obtain ⟨w1, wt, w2, w3⟩ := hw
         refine ⟨hAw w1, hAv ▸ wt, fun x hx => (hbx x).2 (w2 x (hAv ▸ hx)), fun x hx => ?_⟩
         rw [← (hbx x).1]
         exact w3 x (hAv ▸ hx))

end Abs

end ConLeche.Model
