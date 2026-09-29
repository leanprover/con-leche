module

public import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.Leaves

public section

/-!
# The opened-statement frame: towers, spines, and the cross-frame walk

The `Expr`-level facts about the checker's telescope openers
(`openPisAtFvars`, `instPisAt`, `instLamsAt`) that the iota bottoms'
frame machinery consumes: `ctxInstAt`, leaf closure
(`openPisAtFvars_leaves`, `instPisAt_leaves`, `instLamsAt_leaves`),
loose-bvar bounds and scoping, lengths, and composition.  All V-free.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- Indexing a list by its own `range` is mapping it. -/
theorem map_range_getD {α β : Type} [Inhabited α] (xs : List α)
    (g : α → β) :
    (List.range xs.length).map (fun l => g (xs.getD l default)) = xs.map g := by
  refine List.ext_getElem? ?_
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem?_range h, List.getElem?_eq_getElem h]
    simp [List.getD, List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
    rfl

/-- A context's entries, instantiated after a variable *below* all of
them is substituted: the entry `i` places above the substituted slot is
instantiated at cut `j + i` (`j` counts binders below the substituted
slot that remain).  The entry adjacent to the slot — the list's last —
gets cut `j`. -/
@[expose] def ctxInstAt (v : Term) (j : Nat) : List Term → List Term
  | [] => []
  | B :: Γ => B.inst v (j + Γ.length) :: ctxInstAt v j Γ

@[simp] theorem ctxInstAt_nil (v : Term) (j : Nat) :
    ctxInstAt v j [] = [] := rfl

/-- Every free-variable leaf reachable from an opened telescope — from
the opened body or from any opener's own annotation — is either a leaf
of the unopened expression or exactly one of the openers.  With the
subject closed, the openers are a *leaf-closed* set: annotations
mention only earlier openers, which are openers again. -/
theorem openPisAtFvars_leaves :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
        l ∈ e.fvarLeaves ∨ Expr.fvar l.1 l.2 ∈ fvs := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h l hl
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with hl | ⟨x, hx, -⟩
    · exact Or.inl hl
    · exact nomatch hx
  | succ k ih =>
    intro e d fvs body h l hl
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        -- a leaf of the head opener resolves directly
        have head : l ∈ (Expr.fvar d dom).fvarLeaves →
            l ∈ (Expr.forallE dom bodyE mb).fvarLeaves ∨
              Expr.fvar l.1 l.2 ∈
                Expr.fvar d dom :: p.1 := by
          intro hl'
          rw [Expr.fvarLeaves] at hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact Or.inr (List.mem_cons_self ..)
          · refine Or.inl ?_
            rw [Expr.fvarLeaves]
            exact List.mem_append_left _ hl'
        rcases hl with hl | ⟨x, hx, hlx⟩
        · rcases ih hop l (Or.inl hl) with hl' | hl'
          · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
            · refine Or.inl ?_
              rw [Expr.fvarLeaves]
              exact List.mem_append_right _ h1
            · exact head h1
          · exact Or.inr (List.mem_cons_of_mem _ hl')
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact head hlx
          · rcases ih hop l (Or.inr ⟨x, hx', hlx⟩) with hl' | hl'
            · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
              · refine Or.inl ?_
                rw [Expr.fvarLeaves]
                exact List.mem_append_right _ h1
              · exact head h1
            · exact Or.inr (List.mem_cons_of_mem _ hl')

/-- Opening keeps everything at loose-bvar level zero: the body and
each opener's annotation. -/
theorem openPisAtFvars_bounded :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      e.looseBVarsBounded 0 = true →
      body.looseBVarsBounded 0 = true ∧
        ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h hb
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hb, fun x hx => nomatch hx⟩
  | succ k ih =>
    intro e d fvs body h hb
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb' : dom.looseBVarsBounded 0 = true ∧
            bodyE.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        obtain ⟨hbody, hanns⟩ := ih hop
          (looseBVarsBounded_instantiate1 bodyE 0 hb'.2)
        refine ⟨hbody, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hanns x hx'

/-- `instPisAt` keeps everything at loose-bvar level zero. -/
theorem instPisAt_bounded :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ty.looseBVarsBounded 0 = true →
      (∀ a ∈ sp, a.looseBVarsBounded 0 = true) →
      (∀ x ∈ ds, x.looseBVarsBounded 0 = true) ∧
        rs.looseBVarsBounded 0 = true := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h hb _
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hb⟩
  | cons a sp ih =>
    intro ty ds rs h hb hsp
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb' : dom.looseBVarsBounded 0 = true ∧
            body.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        obtain ⟨hds, hrs⟩ := ih h1
          (Expr.looseBVarsBounded_instantiate1_gen
            (hsp a List.mem_cons_self) hb'.2)
          (fun b hb2 => hsp b (List.mem_cons_of_mem _ hb2))
        refine ⟨?_, hrs⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hds x hx'

/-- The opener returns one variable per binder. -/
theorem openPisAtFvars_length :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) → fvs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e d fvs body h
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases h1 : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih h1]



end ConLeche.Verify
