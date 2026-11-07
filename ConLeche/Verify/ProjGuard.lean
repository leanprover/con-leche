module

public import ConLeche.Kernel.CoreDefs
public import ConLeche.Verify.Shift
import ConLeche.Verify.Subst
import ConLeche.Verify.InstLevels
import ConLeche.Verify.LooseBVar
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The rows of a projection's guard (task #480)

`projGuardRows` opens the constructor's parameters and steps its fields
(`projGuardRowsGo`), the field loop of the official `infer_proj`.  What it
hands the checker is scoped: each row's term at its own depth.  And it is
complete: the projected field's domain and that of every earlier field the
rest of the telescope uses (`structUsedLater`, the occurrence the model
states the guard's law in) are rows, at the telescope opened in full.
-/

namespace ConLeche

open Expr

/-- A row list whose terms are scoped at their own depths. -/
@[expose] def GuardRowsWS (rows : List (Nat × Expr)) : Prop :=
  ∀ p ∈ rows, Expr.WScoped p.1 p.2

theorem GuardRowsWS.nil : GuardRowsWS [] := fun _ h => nomatch h

theorem GuardRowsWS.head {d : Nat} {dom : Expr} {rest : List (Nat × Expr)}
    (h : GuardRowsWS ((d, dom) :: rest)) : Expr.WScoped d dom :=
  h (d, dom) List.mem_cons_self

theorem GuardRowsWS.tail {p : Nat × Expr} {rest : List (Nat × Expr)}
    (h : GuardRowsWS (p :: rest)) : GuardRowsWS rest :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The field loop hands back rows scoped at their depths. -/
theorem projGuardRowsGo_ws :
    ∀ (k : Nat) {d : Nat} {r : Expr} {rows : List (Nat × Expr)},
      Expr.WScoped d r → projGuardRowsGo k d r = some rows → GuardRowsWS rows
  | 0, d, .forallE dom body, rows, hw, h => by
    simp only [projGuardRowsGo, Option.some.injEq] at h
    subst h
    simp only [Expr.WScoped] at hw
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact hw.1
  | k + 1, d, .forallE dom body, rows, hw, h => by
    simp only [Expr.WScoped] at hw
    simp only [projGuardRowsGo] at h
    split at h
    · revert h
      cases hrec : projGuardRowsGo k (d + 1) (body.instantiate1 (.fvar d dom)) with
      | none => intro h; exact nomatch h
      | some rows' =>
        intro h
        simp only [Option.some.injEq] at h
        subst h
        have hrest := projGuardRowsGo_ws k (Expr.WScoped.instantiate1 hw.1 0 hw.2) hrec
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hw.1
        · exact hrest p hp
    · exact projGuardRowsGo_ws k (Expr.WScoped.mono (by omega) hw.2) h
  | 0, _, .bvar _, _, _, h | 0, _, .fvar .., _, _, h | 0, _, .sort _, _, _, h
  | 0, _, .const .., _, _, h | 0, _, .app .., _, _, h | 0, _, .lam .., _, _, h
  | 0, _, .letE .., _, _, h | 0, _, .lit _, _, _, h | 0, _, .proj .., _, _, h
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar .., _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h | _ + 1, _, .lam .., _, _, h
  | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h | _ + 1, _, .proj .., _, _, h => by
    simp [projGuardRowsGo] at h

/-- The guard's rows over a stored constructor without free variables
are scoped at their depths. -/
theorem projGuardRows_ws {find? : Name → Option ConstantInfo} {entry : ProjEntry}
    {us : List Level} {rows : List (Nat × Expr)}
    (hcl : ∀ ci, find? entry.ctor = some ci → ci.toConstantVal.type.hasFvar = false)
    (h : projGuardRows find? entry us = some rows) : GuardRowsWS rows := by
  unfold projGuardRows at h
  split at h
  · rename_i ci hc
    dsimp only at h
    split at h
    · rename_i fvsP r hp
      have hwT : Expr.WScoped 0
          (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) :=
        Expr.WScoped.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]; exact hcl ci hc)
      have hwr : Expr.WScoped entry.numParams r := by
        simpa using (openPisAtFvars_WScoped _ _ 0 hp hwT).2
      exact projGuardRowsGo_ws _ hwr h
    · exact nomatch h
  · exact nomatch h

/-! ### The occurrence predicate through an opening -/

/-- `structUsedLater` counts its binders from the telescope's front: a
field `j + 1` after `m` binders is a field `j` after `m + 1`. -/
theorem structUsedLater_succ (e : Expr) (m j : Nat) :
    structUsedLater e m (j + 1) = structUsedLater e (m + 1) j := by
  unfold structUsedLater
  rw [show m + (j + 1) + 1 = m + 1 + j + 1 by omega]

/-- **Through one opened binder**: the binder's variable is a closed term
substituted at an index above the remainder's own, which leaves the
remainder's occurrence of its own variable as it was. -/
theorem structUsedLater_open_step {dom body : Expr} {i m j : Nat} :
    structUsedLater (.forallE dom body) (m + 1) j
      = structUsedLater (body.instantiate1 (.fvar i dom)) m j := by
  have hv : (Expr.fvar i dom).looseBVarsBounded 0 = true := rfl
  unfold structUsedLater
  rw [show m + 1 + j + 1 = (m + j + 1) + 1 by omega]
  simp only [Expr.stripPis]
  cases hb : body.stripPis (m + j + 1) with
  | none =>
    cases h' : (body.instantiate1 (.fvar i dom)).stripPis (m + j + 1) with
    | none => rfl
    | some _ =>
      have := Verify.stripPis_instantiate1_fvar_isSome_rev (m + j + 1) 0 (by rw [h']; rfl)
      rw [hb] at this
      exact absurd this (by simp)
  | some p =>
    obtain ⟨bs, rest⟩ := p
    have hs : ((body.instantiate1 (.fvar i dom)).stripPis (m + j + 1)).isSome :=
      Expr.stripPis_instantiate1_isSome (m + j + 1) 0 (by rw [hb]; rfl)
    obtain ⟨⟨bs', rest'⟩, h'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hrest, -⟩ := Expr.stripPis_instantiate1_eq (m + j + 1) 0 hb h'
    rw [h', hrest]
    simp only [Option.map_some]
    rw [Expr.hasLooseBVarB_eq, Expr.hasLooseBVarB_eq,
      Expr.hasLooseBVar_instantiate1_lt hv _ (by omega)]

/-- **Through an opening of `m` binders**: field `j` after `m` binders of
`e` is field `j` of what the opening leaves. -/
theorem structUsedLater_openPis :
    ∀ (m : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {r : Expr} (j : Nat),
      openPisAtFvars m e d = some (fvs, r) → structUsedLater e m j = structUsedLater r 0 j
  | 0, e, d, fvs, r, j, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | m + 1, .forallE dom body, d, fvs, r, j, h => by
    simp only [openPisAtFvars] at h
    revert h
    cases hrec : openPisAtFvars m (body.instantiate1 (.fvar d dom)) (d + 1) with
    | none => intro h; exact nomatch h
    | some p =>
      obtain ⟨fvs', r'⟩ := p
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [structUsedLater_open_step (i := d)]
      exact structUsedLater_openPis m j hrec
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar .., _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const .., _, _, _, _, h
  | _ + 1, .app .., _, _, _, _, h | _ + 1, .lam .., _, _, _, _, h
  | _ + 1, .letE .., _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj .., _, _, _, _, h => by simp [openPisAtFvars] at h

/-- Level instantiation leaves the occurrence predicate as it was. -/
theorem structUsedLater_instantiateLevelParams (ks : List Name) (us : List Level)
    (e : Expr) (m j : Nat) :
    structUsedLater (e.instantiateLevelParams ks us) m j = structUsedLater e m j := by
  unfold structUsedLater
  rw [Expr.stripPis_instantiateLevelParams]
  cases e.stripPis (m + j + 1) with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [Expr.hasLooseBVarB_eq, Expr.hasLooseBVarB_eq, Expr.hasLooseBVar_instantiateLevelParams]

/-- Opening `a` binders and then `b` more opens `a + b`. -/
theorem openPisAtFvars_append :
    ∀ (a : Nat) {b : Nat} {e : Expr} {d : Nat} {f₁ f₂ : List Expr} {r o : Expr},
      openPisAtFvars a e d = some (f₁, r) → openPisAtFvars b r (d + a) = some (f₂, o) →
      openPisAtFvars (a + b) e d = some (f₁ ++ f₂, o)
  | 0, b, e, d, f₁, f₂, r, o, h₁, h₂ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simpa using h₂
  | a + 1, b, .forallE dom body, d, f₁, f₂, r, o, h₁, h₂ => by
    simp only [openPisAtFvars] at h₁
    revert h₁
    cases hrec : openPisAtFvars a (body.instantiate1 (.fvar d dom)) (d + 1) with
    | none => intro h; exact nomatch h
    | some p =>
      obtain ⟨f₁', r'⟩ := p
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h₂' : openPisAtFvars b r' (d + 1 + a) = some (f₂, o) := by
        rw [show d + 1 + a = d + (a + 1) by omega]; exact h₂
      have := openPisAtFvars_append a hrec h₂'
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [openPisAtFvars, this, List.cons_append]
  | _ + 1, _, .bvar _, _, _, _, _, _, h, _ | _ + 1, _, .fvar .., _, _, _, _, _, h, _
  | _ + 1, _, .sort _, _, _, _, _, _, h, _ | _ + 1, _, .const .., _, _, _, _, _, h, _
  | _ + 1, _, .app .., _, _, _, _, _, h, _ | _ + 1, _, .lam .., _, _, _, _, _, h, _
  | _ + 1, _, .letE .., _, _, _, _, _, h, _ | _ + 1, _, .lit _, _, _, _, _, _, h, _
  | _ + 1, _, .proj .., _, _, _, _, _, h, _ => by simp [openPisAtFvars] at h

/-- **The field loop is complete**: over a closed telescope, the loop's
success opens `k + 1` fields in full, and the projected field and every
earlier field the rest uses are rows, at their domains in that opening.
An unused field is stepped over without being opened; over a closed
telescope that is the same term, so the loop runs along the full
opening. -/
theorem projGuardRowsGo_complete :
    ∀ (k : Nat) {d : Nat} {r : Expr} {rows : List (Nat × Expr)},
      r.looseBVarsBounded 0 = true → projGuardRowsGo k d r = some rows →
      ∃ fvs o, openPisAtFvars (k + 1) r d = some (fvs, o) ∧
        ∀ j, j ≤ k → (j = k ∨ structUsedLater r 0 j = true) →
          ∃ x, fvs[j]? = some x ∧ (d + j, x.fvarTypeD) ∈ rows
  | 0, d, .forallE dom body, rows, _, h => by
    simp only [projGuardRowsGo, Option.some.injEq] at h
    subst h
    refine ⟨[.fvar d dom], body.instantiate1 (.fvar d dom), by simp [openPisAtFvars], ?_⟩
    intro j hj _
    obtain rfl : j = 0 := by omega
    exact ⟨.fvar d dom, rfl, by simp [Expr.fvarTypeD]⟩
  | k + 1, d, .forallE dom body, rows, hb, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hv : (Expr.fvar d dom).looseBVarsBounded 0 = true := rfl
    simp only [projGuardRowsGo] at h
    split at h
    · rename_i hused
      revert h
      cases hrec : projGuardRowsGo k (d + 1) (body.instantiate1 (.fvar d dom)) with
      | none => intro h; exact nomatch h
      | some rows' =>
        intro h
        simp only [Option.some.injEq] at h
        subst h
        have hbI : (body.instantiate1 (.fvar d dom)).looseBVarsBounded 0 = true :=
          Expr.looseBVarsBounded_instantiate1_gen hv hb.2
        obtain ⟨fvs', o, hop, hmem⟩ := projGuardRowsGo_complete k hbI hrec
        refine ⟨.fvar d dom :: fvs', o, by simp [openPisAtFvars, hop], ?_⟩
        intro j hj hrow
        cases j with
        | zero => exact ⟨.fvar d dom, rfl, by simp [Expr.fvarTypeD]⟩
        | succ j =>
          have hrow' : j = k ∨ structUsedLater (body.instantiate1 (.fvar d dom)) 0 j = true := by
            rcases hrow with h | h
            · exact .inl (by omega)
            · rw [structUsedLater_succ, structUsedLater_open_step (i := d)] at h
              exact .inr h
          obtain ⟨x, hx, hxm⟩ := hmem j (by omega) hrow'
          refine ⟨x, by simpa using hx, ?_⟩
          rw [show d + (j + 1) = d + 1 + j by omega]
          exact List.mem_cons_of_mem _ hxm
    · rename_i hunused
      have hn : body.hasLooseBVar 0 = false := by
        rw [← Expr.hasLooseBVarB_eq]; simpa using hunused
      have hb0 : body.looseBVarsBounded 0 = true :=
        Expr.looseBVarsBounded_of_not_hasLooseBVar body hb.2 hn
      have hinst : body.instantiate1 (.fvar d dom) = body := Expr.instantiate1_eq_self hb0
      obtain ⟨fvs', o, hop, hmem⟩ := projGuardRowsGo_complete k hb0 h
      refine ⟨.fvar d dom :: fvs', o, by simp [openPisAtFvars, hinst, hop], ?_⟩
      intro j hj hrow
      cases j with
      | zero =>
        exfalso
        rcases hrow with h0 | h0
        · omega
        · simp [structUsedLater, Expr.stripPis, Expr.hasLooseBVarB_eq, hn] at h0
      | succ j =>
        have hrow' : j = k ∨ structUsedLater body 0 j = true := by
          rcases hrow with h0 | h0
          · exact .inl (by omega)
          · rw [structUsedLater_succ, structUsedLater_open_step (i := d), hinst] at h0
            exact .inr h0
        obtain ⟨x, hx, hxm⟩ := hmem j (by omega) hrow'
        refine ⟨x, by simpa using hx, ?_⟩
        rw [show d + (j + 1) = d + 1 + j by omega]
        exact hxm
  | 0, _, .bvar _, _, _, h | 0, _, .fvar .., _, _, h | 0, _, .sort _, _, _, h
  | 0, _, .const .., _, _, h | 0, _, .app .., _, _, h | 0, _, .lam .., _, _, h
  | 0, _, .letE .., _, _, h | 0, _, .lit _, _, _, h | 0, _, .proj .., _, _, h
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar .., _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h | _ + 1, _, .lam .., _, _, h
  | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h | _ + 1, _, .proj .., _, _, h => by
    simp [projGuardRowsGo] at h

/-- **The rows are complete** (`projGuardRows`): over the constructor's
closed type at the use's levels, the guard's success opens the telescope
through the projected field, and the projected field and every earlier
field a later one uses (read on the stored type) are rows, at their
domains in that opening. -/
theorem projGuardRows_complete {cty : Expr} {ps : List Name} {us : List Level} {nP idx : Nat}
    {r : Expr} {fvsP : List Expr} {rows : List (Nat × Expr)}
    (hcl : (cty.instantiateLevelParams ps us).looseBVarsBounded 0 = true)
    (hp : openPisAtFvars nP (cty.instantiateLevelParams ps us) 0 = some (fvsP, r))
    (hg : projGuardRowsGo idx nP r = some rows) :
    ∃ fvs o, openPisAtFvars (nP + idx + 1) (cty.instantiateLevelParams ps us) 0 = some (fvs, o) ∧
      ∀ j, j ≤ idx → (j = idx ∨ structUsedLater cty nP j = true) →
        ∃ x, fvs[nP + j]? = some x ∧ (nP + j, x.fvarTypeD) ∈ rows := by
  have hrb : r.looseBVarsBounded 0 = true := (Verify.openPisAtFvars_bounded nP hp hcl).1
  obtain ⟨fvsF, o, hopF, hmem⟩ := projGuardRowsGo_complete idx hrb hg
  have hlenP : fvsP.length = nP := Verify.openPisAtFvars_length _ hp
  refine ⟨fvsP ++ fvsF, o, ?_, ?_⟩
  · have := openPisAtFvars_append nP hp (by simpa using hopF)
    simpa [Nat.add_assoc] using this
  · intro j hj hrow
    have hrow' : j = idx ∨ structUsedLater r 0 j = true := by
      rcases hrow with h | h
      · exact .inl h
      · rw [← structUsedLater_instantiateLevelParams ps us, structUsedLater_openPis nP j hp] at h
        exact .inr h
    obtain ⟨x, hx, hxm⟩ := hmem j hj hrow'
    refine ⟨x, ?_, hxm⟩
    rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
    exact hx

end ConLeche
