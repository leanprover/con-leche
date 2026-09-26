module

public import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.Leaves

public section

/-!
# The opened-statement frame: towers, spines, and the cross-frame walk

Relocated verbatim from `ConLeche/TTVerify/IndBottom.lean` (task #148,
T5): the pure denote/`Term` tier of the modeled-iota bottoms' frame
machinery — `PiTele` (a `.pi` tower's domains as a de Bruijn context),
`ctxInstAt`, the opened-telescope walks (`openPisAtFvars_leaves`,
`openPisAtFvars_denoteTele`), the `instSeq`/`instRevChain` algebra,
the cross-frame instantiation (`instPisAt_denote_cross` — the
load-bearing "instantiate-then-denote = denote-then-instantiate"
identity) and the spine-reading lemmas.  All V-free and
`Deq`- and judgment-free; both verification lanes' bottoms consume them.
The namespace stays `ConLeche.Verify` so no call site moves.
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

/-- The checker's opener, read as an `instPisAt` at its own variables:
the returned domains are the opened annotations. -/
theorem openPisAtFvars_instPisAt :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      Expr.instPisAt fvs e = some (fvs.map Expr.fvarTypeD, body) := by
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
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show (Expr.instPisAt p.1 (bodyE.instantiate1
          (Expr.fvar d dom))).map _ = _
        rw [ih hop]
        rfl

/-- `instPisAt` outputs at `RenEqT`-related inputs are `RenEqT`-related,
pointwise on the domains and on the residual. -/
theorem instPisAt_renEq {f : Name → Name} :
    ∀ (as as' : List Expr) {ty ty' : Expr} {ds ds' : List Expr}
      {rs rs' : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt as' ty' = some (ds', rs') →
      RenEqT f ty ty' →
      (∀ (i : Nat) (a a' : Expr), as[i]? = some a → as'[i]? = some a' →
        RenEqT f a a') →
      as.length = as'.length →
      (∀ (i : Nat) (x x' : Expr), ds[i]? = some x → ds'[i]? = some x' →
        RenEqT f x x') ∧ RenEqT f rs rs' := by
  intro as
  induction as with
  | nil =>
    intro as' ty ty' ds ds' rs rs' h h' hty _ hlen
    obtain rfl : as' = [] := by
      cases as' with
      | nil => rfl
      | cons _ _ => exact nomatch hlen
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨(fun i x x' hx _ => nomatch hx), hty⟩
  | cons a as ih =>
    intro as' ty ty' ds ds' rs rs' h h' hty hargs hlen
    cases as' with
    | nil => exact nomatch hlen
    | cons a' as'' => ?_
    match ty, h with
    | .forallE d₁ b₁ m₁, h => ?_
    match ty', h' with
    | .forallE d₂ b₂ m₂, h' => ?_
    have hty' : (m₁ = m₂ ∧ Expr.ErasedEq (d₁.renameConsts f) d₂ ∧
        Expr.ErasedEq (b₁.renameConsts f) b₂) := by
      have h0 : Expr.ErasedEq
          (Expr.forallE (d₁.renameConsts f) (b₁.renameConsts f) m₁)
          (.forallE d₂ b₂ m₂) := hty
      simpa [Expr.ErasedEq] using h0
    obtain ⟨-, hdom, hbody⟩ := hty'
    simp only [Expr.instPisAt] at h h'
    cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    cases h2 : Expr.instPisAt as'' (b₂.instantiate1 a') with
    | none => rw [h2] at h'; exact nomatch h'
    | some p2 => ?_
    rw [h1] at h
    rw [h2] at h'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    have hrec : RenEqT f (b₁.instantiate1 a) (b₂.instantiate1 a') :=
      RenEqT.instantiate1 hbody (hargs 0 a a' rfl rfl)
    obtain ⟨hds, hrs⟩ := ih as'' h1 h2 hrec
      (fun i x x' hx hx' => hargs (i + 1) x x' (by simpa using hx)
        (by simpa using hx'))
      (by simpa using hlen)
    refine ⟨?_, hrs⟩
    intro i x x' hx hx'
    cases i with
    | zero =>
      obtain rfl : d₁ = x := by simpa using hx
      obtain rfl : d₂ = x' := by simpa using hx'
      exact hdom
    | succ i =>
      exact hds i x x' (by simpa using hx) (by simpa using hx')

/-- Every leaf reachable from an `instPisAt` run — from any returned
domain or from the residual — is a leaf of the subject or of a spine
entry. -/
theorem instPisAt_leaves :
    ∀ (as : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      ∀ l, ((∃ x ∈ ds, l ∈ x.fvarLeaves) ∨ l ∈ rs.fvarLeaves) →
        l ∈ ty.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil =>
    intro ty ds rs h l hl
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with ⟨x, hx, -⟩ | hl
    · exact nomatch hx
    · exact Or.inl hl
  | cons a as ih =>
    intro ty ds rs h l hl
    match ty, h with
    | .forallE d₁ b₁ m₁, h => ?_
    simp only [Expr.instPisAt] at h
    cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    rw [h1] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have step : l ∈ (b₁.instantiate1 a).fvarLeaves ∨
        (l ∈ (Expr.forallE d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves) → _ := fun h => h
    have push : l ∈ (b₁.instantiate1 a).fvarLeaves →
        l ∈ (Expr.forallE d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves := by
      intro hb
      rcases Expr.fvarLeaves_instantiate1 b₁ 0 hb with hb' | hb'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_right _ hb'
      · exact Or.inr ⟨a, List.mem_cons_self .., hb'⟩
    rcases hl with ⟨x, hx, hlx⟩ | hl
    · rcases List.mem_cons.mp hx with rfl | hx'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_left _ hlx
      · rcases ih h1 l (Or.inl ⟨x, hx', hlx⟩) with h2 | ⟨b, hb, hlb⟩
        · exact push h2
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩
    · rcases ih h1 l (Or.inr hl) with h2 | ⟨b, hb, hlb⟩
      · exact push h2
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩

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

/-- **`instLamsAt` preserves `looseBVarsBounded 0`** — the λ-side
mirror of `instPisAt_bounded`, which the λ-row's domain package
needs and which no lane had yet. -/
theorem instLamsAt_bounded :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instLamsAt sp ty = some (ds, rs) →
      ty.looseBVarsBounded 0 = true →
      (∀ a ∈ sp, a.looseBVarsBounded 0 = true) →
      (∀ x ∈ ds, x.looseBVarsBounded 0 = true) ∧
        rs.looseBVarsBounded 0 = true := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h hb _
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hb⟩
  | cons a sp ih =>
    intro ty ds rs h hb hsp
    match ty, h with
    | .lam dom body mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
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

/-- **`instLamsAt`'s domains are scoped at their own index** — the
λ-side mirror of `instPisAt_index_WScoped`.  Domain `i` has only the
spine's first `i` entries substituted into it, so it is scoped at
`d + i` and not merely at the telescope's full height; that grading is
what lets each domain's denotation be *lifted* to a common walk depth
(task #148 T6, `IotaWalksR`'s λ-row). -/
theorem instLamsAt_index_WScoped :
    ∀ (sp : List Expr) {d : Nat} {ty : Expr} {ds : List Expr}
      {rs : Expr},
      Expr.instLamsAt sp ty = some (ds, rs) → Expr.WScoped d ty →
      (∀ (i : Nat) (a : Expr), sp[i]? = some a →
        Expr.WScoped (d + i + 1) a) →
      ∀ (i : Nat) (x : Expr), ds[i]? = some x → Expr.WScoped (d + i) x
  | [], d, ty, ds, rs, h, _, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i x hx
    exact nomatch hx
  | a :: as, d, ty, ds, rs, h, hty, hsp => by
    cases ty with
    | lam dom body mb =>
      simp only [Expr.instLamsAt, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      have hty' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
        simpa [Expr.WScoped] using hty
      have haw : Expr.WScoped (d + 1) a := by
        have h0 := hsp 0 a rfl
        rwa [Nat.add_zero] at h0
      intro i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, Nat.add_zero]
        exact hty'.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have hrec := instLamsAt_index_WScoped as (d := d + 1) hq
          (Expr.WScoped.instantiate1_gen haw 0
            (hty'.2.mono (Nat.le_succ d)))
          (fun k b hb => by
            have h0 := hsp (k + 1) b (by simpa using hb)
            rw [show d + (k + 1) + 1 = d + 1 + k + 1 from by omega]
              at h0
            exact h0) i x hx
        rw [show d + (i + 1) = d + 1 + i from by omega]
        exact hrec
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | forallE _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h


/-! ## The stored levels' arity (the nested bottom's `hlvlsLen`)

The checker never compares `lvls.length` against the constructor's
level arity — the fact is forced *semantically*: the checked
statement's major applies `f ctor` at `lvls`, the statement denotes
(it is a stored, checked theorem), and `denote`'s `.const` clause is
guarded on the stored arity.  Sealed per the house rule: the walk
rewrites under `denote` terms.

Relocated verbatim from `ConLeche/TTVerify/DeclIndRecs.lean` (task #148,
T5 stage 3b): the statement is about `denote` and a `TConstVal`, so
both verified lanes' nested bottoms read it. -/

/-- `instLamsAt` returns one domain per argument. -/
theorem instLamsAt_length :
    ∀ (sp : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instLamsAt sp e = some (ds, rest) → ds.length = sp.length := by
  intro sp
  induction sp with
  | nil =>
    intro e ds rest h
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a sp ih =>
    intro e ds rest h
    match e, h with
    | .lam dom body mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih h1]

/-- Composition of two `instPisAt` runs: walking `as ++ bs` is walking
`as`, then `bs` on the residual. -/
theorem Expr.instPisAt_append :
    ∀ (as : List Expr) {bs : List Expr} {ty : Expr} {ds ds2 : List Expr}
      {rs rs2 : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt bs rs = some (ds2, rs2) →
      Expr.instPisAt (as ++ bs) ty = some (ds ++ ds2, rs2) := by
  intro as
  induction as with
  | nil =>
    intro bs ty ds ds2 rs rs2 h h2
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h2
  | cons a as ih =>
    intro bs ty ds ds2 rs rs2 h h2
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt as (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show (Expr.instPisAt (as ++ bs) (body.instantiate1 a)).map _ = _
        rw [ih h1 h2]
        rfl


/-- Leaves of an `instLamsAt` run come from the telescope or the
spine (the λ mirror of `instPisAt_leaves`). -/
theorem instLamsAt_leaves :
    ∀ (as : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instLamsAt as ty = some (ds, rs) →
      ∀ l, ((∃ x ∈ ds, l ∈ x.fvarLeaves) ∨ l ∈ rs.fvarLeaves) →
        l ∈ ty.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil =>
    intro ty ds rs h l hl
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with ⟨x, hx, -⟩ | hl
    · exact nomatch hx
    · exact Or.inl hl
  | cons a as ih =>
    intro ty ds rs h l hl
    match ty, h with
    | .lam d₁ b₁ m₁, h => ?_
    simp only [Expr.instLamsAt] at h
    cases h1 : Expr.instLamsAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    rw [h1] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have push : l ∈ (b₁.instantiate1 a).fvarLeaves →
        l ∈ (Expr.lam d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves := by
      intro hb
      rcases Expr.fvarLeaves_instantiate1 b₁ 0 hb with hb' | hb'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_right _ hb'
      · exact Or.inr ⟨a, List.mem_cons_self .., hb'⟩
    rcases hl with ⟨x, hx, hlx⟩ | hl
    · rcases List.mem_cons.mp hx with rfl | hx'
      · refine Or.inl ?_
        rw [Expr.fvarLeaves]
        exact List.mem_append_left _ hlx
      · rcases ih h1 l (Or.inl ⟨x, hx', hlx⟩) with h2 | ⟨b, hb, hlb⟩
        · exact push h2
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩
    · rcases ih h1 l (Or.inr hl) with h2 | ⟨b, hb, hlb⟩
      · exact push h2
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩


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
