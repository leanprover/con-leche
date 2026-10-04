module

public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Verify.ExceptBind
public import ConLeche.Verify.Subst
import ConLeche.Verify.Level

public section

/-!
# The class match (`targetClassMatch`), inverted

The recursor check matches a recursor class against an instantiation the
positivity check recorded PER COMPONENT (ruling 2026-09-27): levels by
`Level.isEquivList`, every parameter by the kernel's defeq with the
members abstracted, both sides moved to the class's recursor-prefix
openers (`targetCanonParams`).  This file inverts the run and states the
two syntactic facts the model reads it with:

* `targetClassMatch_true` / `targetParamsDefEq_true` — the run, per
  component: both sides closed over the openers, and either their
  abstractions coincide or both were inferred and found defeq;
* `targetClassMatch_congr` — the match reads the recorded side only up to
  the free variables' annotations (`ErasedEq`): the canonical move
  replaces every free variable whole, and the guard's ranges ignore
  annotations;
* `targetMajorNfs_mem` — an entry of one of the class's constructors that
  the class matches is among its recorded normal forms.
-/

namespace ConLeche

/-! ## Erasure-equal terms: one range, one canonical form -/

theorem Expr.ErasedEq.ranges : ∀ {a b : Expr}, Expr.ErasedEq a b →
    a.fvarRange = b.fvarRange ∧ a.bvarBound = b.bvarBound := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarRange, Expr.bvarBound]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarRange, Expr.bvarBound]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarRange, Expr.bvarBound]
  | const n us => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarRange, Expr.bvarBound]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarRange, Expr.bvarBound]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e1, e2⟩ := ihf h1
    obtain ⟨e3, e4⟩ := iha h2
    simp [Expr.fvarRange, Expr.bvarBound, e1, e2, e3, e4]
  | lam t b' m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨-, h1, h2⟩ := h
    obtain ⟨e1, e2⟩ := iht h1
    obtain ⟨e3, e4⟩ := ihb h2
    simp [Expr.fvarRange, Expr.bvarBound, e1, e2, e3, e4]
  | forallE t b' m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨-, h1, h2⟩ := h
    obtain ⟨e1, e2⟩ := iht h1
    obtain ⟨e3, e4⟩ := ihb h2
    simp [Expr.fvarRange, Expr.bvarBound, e1, e2, e3, e4]
  | letE t v b' iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨e1, e2⟩ := iht h1
    obtain ⟨e3, e4⟩ := ihv h2
    obtain ⟨e5, e6⟩ := ihb h3
    simp [Expr.fvarRange, Expr.bvarBound, e1, e2, e3, e4, e5, e6]
  | proj s i e ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨-, -, h1⟩ := h
    obtain ⟨e1, e2⟩ := ih h1
    simp [Expr.fvarRange, Expr.bvarBound, e1, e2]

/-- **The canonical move forgets annotations**: erasure-equal terms whose
free variables are all mapped move to one term. -/
theorem replaceFVars_eq_of_erasedEq {g : Nat → Option Expr} {d : Nat}
    (hg : ∀ i, i < d → (g i).isSome = true) :
    ∀ {a b : Expr}, Expr.ErasedEq a b → a.fvarsBelow d →
      a.replaceFVars g = b.replaceFVars g := by
  intro a
  induction a with
  | bvar i => intro b h _; cases b <;> simp_all [Expr.ErasedEq]
  | fvar i ty =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    subst h
    simp only [Expr.fvarsBelow] at ha
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hg _ ha)
    simp [Expr.replaceFVars, hx]
  | sort u => intro b h _; cases b <;> simp_all [Expr.ErasedEq]
  | const n us => intro b h _; cases b <;> simp_all [Expr.ErasedEq]
  | lit l => intro b h _; cases b <;> simp_all [Expr.ErasedEq]
  | app f a ihf iha =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.fvarsBelow] at ha
    simp only [Expr.replaceFVars, ihf h.1 ha.1, iha h.2 ha.2]
  | lam t b' m iht ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨rfl, h1, h2⟩ := h
    simp only [Expr.fvarsBelow] at ha
    simp only [Expr.replaceFVars, iht h1 ha.1, ihb h2 ha.2]
  | forallE t b' m iht ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨rfl, h1, h2⟩ := h
    simp only [Expr.fvarsBelow] at ha
    simp only [Expr.replaceFVars, iht h1 ha.1, ihb h2 ha.2]
  | letE t v b' iht ihv ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Expr.fvarsBelow] at ha
    simp only [Expr.replaceFVars, iht h1 ha.1, ihv h2 ha.2.1, ihb h3 ha.2.2]
  | proj s i e ih =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    obtain ⟨rfl, rfl, h1⟩ := h
    simp only [Expr.fvarsBelow] at ha
    simp only [Expr.replaceFVars, ih h1 ha]

theorem targetCanonParams_eq_of_erasedEq {pfvs : List Expr} {a b : Expr}
    (h : Expr.ErasedEq a b) (ha : a.fvarB ≤ pfvs.length) :
    targetCanonParams pfvs a = targetCanonParams pfvs b :=
  replaceFVars_eq_of_erasedEq (d := pfvs.length) (fun i hi => by simp [hi]) h
    (Expr.fvarsBelow_iff.mpr (Expr.fvarB_eq a ▸ ha))

/-! ## The run, inverted -/

variable {ops : CheckerOps CheckM} {env : Env}

/-- One matched parameter pair (`targetParamsDefEq`'s passing branch). -/
@[expose] def ParamMatch (ops : CheckerOps CheckM) (env : Env) (d : Nat) (absM : Expr → Expr)
    (pfvs : List Expr) (a b : Expr) : Prop :=
  a.bvarB = 0 ∧ b.bvarB = 0 ∧ a.fvarB ≤ pfvs.length ∧ b.fvarB ≤ pfvs.length ∧
    (absM (targetCanonParams pfvs a) = absM (targetCanonParams pfvs b) ∨
      ((∃ ta, ops.inferType env d (absM (targetCanonParams pfvs a)) = .ok ta) ∧
       (∃ tb, ops.inferType env d (absM (targetCanonParams pfvs b)) = .ok tb) ∧
       ops.isDefEq env d (absM (targetCanonParams pfvs a)) (absM (targetCanonParams pfvs b))
         = .ok true))

theorem targetParamsDefEq_true {d : Nat} {absM : Expr → Expr} {pfvs : List Expr} :
    ∀ {as bs : List Expr}, targetParamsDefEq ops env d absM pfvs as bs = .ok true →
      as.length = bs.length ∧ ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        ParamMatch ops env d absM pfvs a b
  | [], [], _ => ⟨rfl, fun i a b h _ => by simp at h⟩
  | [], _ :: _, h => by simp [targetParamsDefEq, pure, Except.pure] at h
  | _ :: _, [], h => by simp [targetParamsDefEq, pure, Except.pure] at h
  | a :: as, b :: bs, h => by
    unfold targetParamsDefEq at h
    split at h
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      obtain ⟨⟨⟨ha0, hb0⟩, haf⟩, hbf⟩ := hg
      dsimp only at h
      have hrest : ∀ (P : Prop), P → targetParamsDefEq ops env d absM pfvs as bs = .ok true →
          (a :: as).length = (b :: bs).length ∧ ∀ (i : Nat) (a' b' : Expr), (a :: as)[i]? = some a' →
            (b :: bs)[i]? = some b' → (i = 0 → ParamMatch ops env d absM pfvs a' b') →
            ParamMatch ops env d absM pfvs a' b' := by
        intro _ _ h'
        obtain ⟨hl, hall⟩ := targetParamsDefEq_true h'
        refine ⟨by simp [hl], fun i a' b' h1 h2 h0 => ?_⟩
        cases i with
        | zero => exact h0 rfl
        | succ i => exact hall i a' b' (by simpa using h1) (by simpa using h2)
      split at h
      · rename_i heq
        obtain ⟨hl, hall⟩ := hrest True trivial h
        refine ⟨hl, fun i a' b' h1 h2 => hall i a' b' h1 h2 fun hi => ?_⟩
        subst hi
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        exact ⟨ha0, hb0, haf, hbf, Or.inl (by simpa using heq)⟩
      · obtain ⟨ta, hta, h⟩ := exceptBind_ok h
        obtain ⟨tb, htb, h⟩ := exceptBind_ok h
        obtain ⟨c, hc, h⟩ := exceptBind_ok h
        cases c
        · simp [pure, Except.pure] at h
        · obtain ⟨hl, hall⟩ := hrest True trivial h
          refine ⟨hl, fun i a' b' h1 h2 => hall i a' b' h1 h2 fun hi => ?_⟩
          subst hi
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
          subst h1 h2
          exact ⟨ha0, hb0, haf, hbf, Or.inr ⟨⟨ta, hta⟩, ⟨tb, htb⟩, hc⟩⟩
    · simp [pure, Except.pure] at h

/-- **The class match, inverted**: the levels are `isEquivList`-equal and
the parameters matched pairwise over the prefix with the holes on top. -/
theorem targetClassMatch_true {p : BlockShape} {formerTys pfvs : List Expr}
    {us lvls : List Level} {ds eds : List Expr}
    (h : targetClassMatch ops env p formerTys pfvs us ds lvls eds = .ok true) :
    Level.isEquivList us lvls = some true ∧
      targetParamsDefEq ops env (pfvs.length + formerTys.length)
        (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys pfvs.length)) pfvs
        ds eds = .ok true := by
  unfold targetClassMatch at h
  split at h
  · rename_i hl
    exact ⟨by simpa using hl, h⟩
  · simp [pure, Except.pure] at h

/-! ## The recorded side up to annotations -/

/-- Two lists of terms, pairwise erasure-equal. -/
@[expose] def ErasedEqs : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => Expr.ErasedEq a b ∧ ErasedEqs as bs
  | _, _ => False

theorem targetParamsDefEq_congr {d : Nat} {absM : Expr → Expr} {pfvs : List Expr} :
    ∀ (as : List Expr) {bs bs' : List Expr}, ErasedEqs bs bs' →
      targetParamsDefEq ops env d absM pfvs as bs = targetParamsDefEq ops env d absM pfvs as bs'
  | [], [], [], _ => rfl
  | _ :: _, [], [], _ => rfl
  | [], _ :: _, _ :: _, _ => rfl
  | a :: as, b :: bs, b' :: bs', ⟨hb, hbs⟩ => by
    obtain ⟨hf, hbb⟩ := Expr.ErasedEq.ranges hb
    have hf' : b.fvarB = b'.fvarB := by rw [Expr.fvarB_eq, Expr.fvarB_eq, hf]
    have hb' : b.bvarB = b'.bvarB := by rw [Expr.bvarB_eq, Expr.bvarB_eq, hbb]
    unfold targetParamsDefEq
    rw [← hf', ← hb']
    split
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      rw [targetCanonParams_eq_of_erasedEq hb hg.2, targetParamsDefEq_congr as hbs]
    · rfl

/-- **The class match reads its recorded side up to annotations.** -/
theorem targetClassMatch_congr {p : BlockShape} {formerTys pfvs : List Expr}
    {us lvls : List Level} {ds eds eds' : List Expr} (h : ErasedEqs eds eds') :
    targetClassMatch ops env p formerTys pfvs us ds lvls eds
      = targetClassMatch ops env p formerTys pfvs us ds lvls eds' := by
  unfold targetClassMatch
  rw [targetParamsDefEq_congr ds h]

/-! ## The recorded normal forms -/

/-- **A matched entry of the class's constructors is recorded** among
its normal forms. -/
theorem targetMajorNfs_mem {p : BlockShape} {formerTys pfvs : List Expr} {us : List Level}
    {ds : List Expr} {ctors : List (ConstantVal × Nat)} :
    ∀ {es nfs : List NestCtorNf},
      targetMajorNfs ops env p formerTys pfvs us ds ctors es = .ok nfs →
      ∀ e ∈ es, ctors.any (·.1.name == e.ctor) = true →
        targetClassMatch ops env p formerTys pfvs us ds e.lvls e.ds = .ok true → e ∈ nfs
  | [], _, _, e, he, _, _ => nomatch he
  | e0 :: es, nfs, h, e, he, hc, hm => by
    unfold targetMajorNfs at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    have ih := targetMajorNfs_mem hrest
    rcases List.mem_cons.mp he with rfl | he
    · rw [ite_eq_left hc] at h
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      rw [hm] at hb
      cases hb
      simp only [ite_true, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hin := ih e he hc hm
      split at h
      · obtain ⟨b, -, h⟩ := exceptBind_ok h
        cases b
        · simp only [Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at h
          subst h; exact hin
        · simp only [ite_true, pure, Except.pure, Except.ok.injEq] at h
          subst h; exact List.mem_cons_of_mem _ hin
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact hin

end ConLeche

namespace ConLeche

/-! ## A class matches its own instantiation -/

theorem isEquivList_self : ∀ (us : List Level), Level.isEquivList us us = some true
  | [] => rfl
  | u :: us => by
    have h : Level.isEquiv u u = some true := Level.isEquiv_of_beq (by simp)
    simp [Level.isEquivList, h, isEquivList_self us]

theorem targetParamsDefEq_self {ops : CheckerOps CheckM} {env : Env} {d : Nat}
    {absM : Expr → Expr} {pfvs : List Expr} :
    ∀ (as : List Expr), (∀ a ∈ as, a.bvarB = 0 ∧ a.fvarB ≤ pfvs.length) →
      targetParamsDefEq ops env d absM pfvs as as = .ok true
  | [], _ => rfl
  | a :: as, h => by
    obtain ⟨h0, hf⟩ := h a List.mem_cons_self
    unfold targetParamsDefEq
    rw [ite_eq_left (by simp [h0, hf]), ite_eq_left (by simp)]
    exact targetParamsDefEq_self as fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem ErasedEqs.symm : ∀ {as bs : List Expr}, ErasedEqs as bs → ErasedEqs bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨Expr.ErasedEq.symm h1, ErasedEqs.symm h2⟩

/-- **A class matches an instantiation erasure-equal to its own** (same
levels, parameters up to the free variables' annotations): the canonical
moves coincide, so every pair passes syntactically. -/
theorem targetClassMatch_self {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys pfvs : List Expr} {us : List Level} {ds eds : List Expr}
    (hds : ∀ a ∈ ds, a.bvarB = 0 ∧ a.fvarB ≤ pfvs.length) (he : ErasedEqs ds eds) :
    targetClassMatch ops env p formerTys pfvs us ds us eds = .ok true := by
  rw [targetClassMatch_congr (eds := eds) (eds' := ds) (ErasedEqs.symm he)]
  unfold targetClassMatch
  rw [ite_eq_left (by simp [isEquivList_self])]
  exact targetParamsDefEq_self ds hds

end ConLeche
