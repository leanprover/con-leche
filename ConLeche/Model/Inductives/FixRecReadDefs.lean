module

import ConLeche.Model.Inductives.SumRecRead
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The generated recursive recursor's readings: the targets (task #188)

The binder data the generated recursor type `structRecTyR`
(`ConLeche/Kernel/Inductives/NativeParts.lean`) reads to, and the rules' λ-data
and cores — the indexed sum route's (`SumRecReadP.lean`) with the
**inductive-hypothesis binders** in the minors (`ihPisAV`: for each
recursive field `i`, at ih position `l`, `motive e⃗_i f_i` with the
field's index readings moved to the binder's frame, `ihIdxAt`) and
the ih applications in the rules (`ihAppAV`: the recursor's leaf at
the block's variables, the field's index readings and the field).  The
reading theorems (`FixRecReadP.lean`) prove the kernel's generators
read to exactly these.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The ih binders -/

/-- A recursive constructor datum: name, field count, field data,
index readings, recursive positions, per-field index-expression
readings, per-field telescopes (empty at a finitary field; task
#202). -/
abbrev CtorDatumR :=
  Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm × List Nat × List (List AnnotTerm) ×
    List (List (Nat × Nat × AnnotTerm))

/-! ## The telescope toolkit (task #202)

The kernel spells a reflexive field's own telescope with
`Expr.piBinders` (`structFieldTeleOf`); the readings need its
elementary laws — the round trip, its stability under the frame's
instantiation (whose arguments are free variables), and the openers'
count. -/

@[simp] theorem Expr.piBinders_forallE (ty b : Expr) (mt : BinderMeta) :
    (Expr.forallE ty b mt).piBinders = ((ty, mt) :: (b.piBinders).1, (b.piBinders).2) := rfl

/-- **A Π-tower is its own binders over its own body.** -/
theorem Expr.mkPisOf_piBinders : ∀ e : Expr, Expr.mkPisOf (e.piBinders).1 (e.piBinders).2 = e
  | .forallE ty b mt => by
    rw [Expr.piBinders_forallE]
    show Expr.forallE ty (Expr.mkPisOf (b.piBinders).1 (b.piBinders).2) mt = _
    rw [Expr.mkPisOf_piBinders b]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- Substituting a free variable moves a Π-tower's body but not its
binder count. -/
theorem Expr.piBinders_instantiate1_fvar {i : Nat} {tya : Expr} (e : Expr) :
    ∀ k : Nat,
      ((e.instantiate1 (.fvar i tya) k).piBinders).1.length = (e.piBinders).1.length ∧
      ((e.instantiate1 (.fvar i tya) k).piBinders).2
        = ((e.piBinders).2).instantiate1 (.fvar i tya) (k + (e.piBinders).1.length) := by
  induction e with
  | forallE ty b mt _ ihb =>
    intro k
    obtain ⟨hl, hb⟩ := ihb (k + 1)
    show (((Expr.forallE (ty.instantiate1 _ k) (b.instantiate1 _ (k + 1)) mt)).piBinders).1.length
        = _ ∧ _
    rw [Expr.piBinders_forallE, Expr.piBinders_forallE]
    refine ⟨by simp only [List.length_cons, hl], ?_⟩
    show ((b.instantiate1 (.fvar i tya) (k + 1)).piBinders).2 = _
    rw [hb]
    congr 1
    simp only [List.length_cons]
    omega
  | bvar j =>
    intro k
    show (((Expr.bvar j).instantiate1 (.fvar i tya) k).piBinders).1.length = ([] : List _).length ∧
      (((Expr.bvar j).instantiate1 (.fvar i tya) k).piBinders).2
        = (Expr.bvar j).instantiate1 (.fvar i tya) (k + ([] : List _).length)
    simp only [List.length_nil, Nat.add_zero, Expr.instantiate1]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  | _ => intro k; exact ⟨rfl, rfl⟩

/-- The frame's instantiation moves a Π-tower's body but not its
binder count (the frame's entries are free variables). -/
theorem Expr.piBinders_instSeq :
    ∀ (L : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ L, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty) →
      L.length ≤ t + 1 →
      ((Expr.instSeq L t e).piBinders).1.length = (e.piBinders).1.length ∧
      ((Expr.instSeq L t e).piBinders).2
        = Expr.instSeq L (t + (e.piBinders).1.length) ((e.piBinders).2)
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | a :: L, t, e, hfv, hlen => by
    obtain ⟨i, tya, rfl⟩ := hfv a List.mem_cons_self
    obtain ⟨hl1, hb1⟩ := Expr.piBinders_instantiate1_fvar (i := i) (tya := tya) e t
    have hfv' : ∀ x ∈ L, ∃ (i : Nat) (ty : Expr), x = Expr.fvar i ty :=
      fun x hx => hfv x (List.mem_cons_of_mem _ hx)
    have hlen' : L.length ≤ t - 1 + 1 := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hl2, hb2⟩ := Expr.piBinders_instSeq L (t - 1) (e.instantiate1 (.fvar i tya) t)
      hfv' hlen'
    have hstep : Expr.instSeq (Expr.fvar i tya :: L) t e
        = Expr.instSeq L (t - 1) (e.instantiate1 (Expr.fvar i tya) t) := rfl
    have hstep2 : Expr.instSeq (Expr.fvar i tya :: L) (t + (e.piBinders).1.length)
          ((e.piBinders).2)
        = Expr.instSeq L (t + (e.piBinders).1.length - 1)
            (((e.piBinders).2).instantiate1 (Expr.fvar i tya)
              (t + (e.piBinders).1.length)) := rfl
    refine ⟨by rw [hstep, hl2, hl1], ?_⟩
    rw [hstep, hstep2, hb2, hb1, hl1]
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · have : L = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst this
      rfl
    · rw [show t - 1 + (e.piBinders).1.length = t + (e.piBinders).1.length - 1 from by omega]

/-- A Π-tower strips exactly its own binders. -/
theorem Expr.stripPis_piBinders : ∀ e : Expr, e.stripPis (e.piBinders).1.length = some e.piBinders
  | .forallE ty b mt => by
    rw [Expr.piBinders_forallE]
    simp only [List.length_cons, Expr.stripPis]
    rw [Expr.stripPis_piBinders b]
    rfl
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- A binder-free Π-tower is its own body. -/
theorem Expr.piBinders_nil_body : ∀ {e : Expr}, (e.piBinders).1 = [] → (e.piBinders).2 = e
  | .forallE _ _ _, h => by rw [Expr.piBinders_forallE] at h; exact nomatch h
  | .bvar _, _ | .fvar .., _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _
  | .letE .., _ | .lit _, _ | .proj .., _ => rfl

/-- An application spine has no leading `∀`. -/
theorem Expr.piBinders_nil_of_getAppFn_const {e : Expr} {c : Name} {us : List Level}
    (h : e.getAppFn = .const c us) : (e.piBinders).1 = [] := by
  match e with
  | .forallE _ _ _ => exact nomatch h
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- **An opened variable's type is its binder's domain instantiated at
the earlier variables.** -/
theorem openPisAtFvars_fvarTypeD :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
      {bs : List (Expr × BinderMeta)} {body : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      e.stripPis n = some (bs, body) →
      ∀ (i : Nat) (b : Expr × BinderMeta) (x : Expr),
        bs[i]? = some b → fvs[i]? = some x →
        x.fvarTypeD = Expr.instSeq (fvs.take i) (i - 1) b.1
  | 0, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    rw [← hst.1] at hb
    exact nomatch hb
  | n + 1, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, hx => by
    match e, hop, hst with
    | .forallE dom bd mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hx
          subst hb; subst hx
          rfl
        | succ i =>
          simp only [List.getElem?_cons_succ] at hb hx
          obtain ⟨bs'', hst'', hdoms⟩ :=
            ConLeche.stripPis_instantiate1_full (v := .fvar d dom) n 0 hst'
          have hb'' := hdoms i b hb
          rw [Nat.zero_add] at hb''
          have ih := openPisAtFvars_fvarTypeD n h₁ hst'' i _ x hb'' hx
          rw [ih, List.take_succ_cons]
          rfl
      · exact nomatch hop

end ConLeche.Model
