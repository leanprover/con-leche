module

public import ConLeche.Verify.Subst
public import ConLeche.Verify.Abstract
import ConLeche.Verify.AbstractRange
public import ConLeche.Verify.Denote.OpenVars

public section

/-!
# Erasing `fvar` type annotations (task #315)

`Expr.fvar idx ty` carries a type ANNOTATION.  The readings never look
at it — `denoteMeta` (`ConLeche/Model/Annot/Bit.lean`) answers
`.bvar (d - 1 - idx)` at every `fvar` leaf — but the syntactic
operations do not agree on it: `Expr.abstractRange` DROPS the
annotation when it closes a variable, and `openPisAtFvars` re-creates
the variable with the *opener's* domain as annotation.  A term that
goes through abstract-then-open therefore comes back equal only **up to
annotations**.

`Expr.eraseAnnots` is that currency as a function: it rewrites every
`fvar` annotation to `.sort .zero` and is otherwise the identity.  It
is the functional form of `Expr.ErasedEq` (`erasedEq_iff_eraseAnnots`),
commutes with every substitution operation the checker runs, and turns
the open/close roundtrip into an equation with no `fvarConsistent` side
condition (`eraseAnnots_openAbstract`) — which is the point: under
erasure the annotations that the two sides disagree about are gone.
-/

namespace ConLeche.Expr

/-- Rewrite every `fvar` type annotation to `.sort .zero`.  No descent
into the annotation is needed — it is replaced wholesale. -/
@[expose] def eraseAnnots : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx _ => .fvar idx (.sort .zero)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.eraseAnnots a.eraseAnnots
  | .lam ty b m => .lam ty.eraseAnnots b.eraseAnnots m
  | .forallE ty b m => .forallE ty.eraseAnnots b.eraseAnnots m
  | .letE ty v b => .letE ty.eraseAnnots v.eraseAnnots b.eraseAnnots
  | .lit l => .lit l
  | .proj s i e => .proj s i e.eraseAnnots

/-- Erasure is idempotent. -/
theorem eraseAnnots_idem (e : Expr) : e.eraseAnnots.eraseAnnots = e.eraseAnnots := by
  induction e <;> simp_all [eraseAnnots]

/-- `ErasedEq` is erasure equality. -/
theorem erasedEq_iff_eraseAnnots : ∀ {a b : Expr},
    ErasedEq a b ↔ a.eraseAnnots = b.eraseAnnots := by
  intro a
  induction a with
  | bvar i =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots]
  | fvar idx ty =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots]
  | sort u =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots]
  | const n us =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots]
  | lit l =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots]
  | app f a ihf iha =>
    intro b; cases b <;> simp [ErasedEq, eraseAnnots, ihf, iha]
  | lam ty bd m ihty ihb =>
    intro b
    cases b <;> simp [ErasedEq, eraseAnnots, ihty, ihb, and_comm, and_left_comm]
  | forallE ty bd m ihty ihb =>
    intro b
    cases b <;> simp [ErasedEq, eraseAnnots, ihty, ihb, and_comm, and_left_comm]
  | letE ty v bd ihty ihv ihb =>
    intro b
    cases b <;> simp [ErasedEq, eraseAnnots, ihty, ihv, ihb]
  | proj s i pe ih =>
    intro b
    cases b <;> simp [ErasedEq, eraseAnnots, ih, and_left_comm]

/-! ## Inversion: erasure does not move the head constructor -/

theorem eraseAnnots_eq_bvar {e : Expr} {i : Nat} (h : e.eraseAnnots = .bvar i) :
    e = .bvar i := by
  cases e <;> simp only [eraseAnnots] at h <;> first | exact Expr.noConfusion h | exact h

theorem eraseAnnots_eq_sort {e : Expr} {u : Level} (h : e.eraseAnnots = .sort u) :
    e = .sort u := by
  cases e <;> simp only [eraseAnnots] at h <;> first | exact Expr.noConfusion h | exact h

theorem eraseAnnots_eq_const {e : Expr} {n : Name} {us : List Level}
    (h : e.eraseAnnots = .const n us) : e = .const n us := by
  cases e <;> simp only [eraseAnnots] at h <;> first | exact Expr.noConfusion h | exact h

theorem eraseAnnots_eq_lit {e : Expr} {l : Literal} (h : e.eraseAnnots = .lit l) :
    e = .lit l := by
  cases e <;> simp only [eraseAnnots] at h <;> first | exact Expr.noConfusion h | exact h

theorem eraseAnnots_eq_fvar {e : Expr} {idx : Nat} {ty : Expr}
    (h : e.eraseAnnots = .fvar idx ty) : ∃ ty', e = .fvar idx ty' := by
  cases e <;> simp only [eraseAnnots, Expr.fvar.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, by rw [h.1]⟩

theorem eraseAnnots_eq_app {e f a : Expr} (h : e.eraseAnnots = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f'.eraseAnnots = f ∧ a'.eraseAnnots = a := by
  cases e <;> simp only [eraseAnnots, Expr.app.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, _, rfl, h.1, h.2⟩

theorem eraseAnnots_eq_lam {e ty b : Expr} {m : BinderMeta}
    (h : e.eraseAnnots = .lam ty b m) :
    ∃ ty' b', e = .lam ty' b' m ∧ ty'.eraseAnnots = ty ∧ b'.eraseAnnots = b := by
  cases e <;> simp only [eraseAnnots, Expr.lam.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, _, by rw [h.2.2], h.1, h.2.1⟩

theorem eraseAnnots_eq_forallE {e ty b : Expr} {m : BinderMeta}
    (h : e.eraseAnnots = .forallE ty b m) :
    ∃ ty' b', e = .forallE ty' b' m ∧ ty'.eraseAnnots = ty ∧ b'.eraseAnnots = b := by
  cases e <;> simp only [eraseAnnots, Expr.forallE.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, _, by rw [h.2.2], h.1, h.2.1⟩

theorem eraseAnnots_eq_letE {e ty v b : Expr} (h : e.eraseAnnots = .letE ty v b) :
    ∃ ty' v' b', e = .letE ty' v' b' ∧ ty'.eraseAnnots = ty ∧ v'.eraseAnnots = v ∧
      b'.eraseAnnots = b := by
  cases e <;> simp only [eraseAnnots, Expr.letE.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, _, _, rfl, h.1, h.2.1, h.2.2⟩

theorem eraseAnnots_eq_proj {e pe : Expr} {s : Name} {i : Nat}
    (h : e.eraseAnnots = .proj s i pe) :
    ∃ pe', e = .proj s i pe' ∧ pe'.eraseAnnots = pe := by
  cases e <;> simp only [eraseAnnots, Expr.proj.injEq] at h <;>
    first | exact Expr.noConfusion h | exact ⟨_, by rw [h.1, h.2.1], h.2.2⟩

/-! ## The spine -/


/-- Erasure distributes over an application spine. -/
theorem eraseAnnots_mkAppN : ∀ (f : Expr) (as : List Expr),
    (Expr.mkAppN f as).eraseAnnots = Expr.mkAppN f.eraseAnnots (as.map eraseAnnots)
  | _, [] => rfl
  | f, a :: as => by
    show (Expr.mkAppN (.app f a) as).eraseAnnots = _
    rw [eraseAnnots_mkAppN (.app f a) as]
    rfl

/-- Erasure commutes with the spine head. -/
theorem getAppFn_eraseAnnots (e : Expr) : e.eraseAnnots.getAppFn = e.getAppFn.eraseAnnots := by
  induction e with
  | app f a ihf _ => simpa only [eraseAnnots, getAppFn] using ihf
  | _ => rfl

/-- Erasure commutes with the spine arguments. -/
theorem getAppArgs_eraseAnnots (e : Expr) :
    e.eraseAnnots.getAppArgs = e.getAppArgs.map eraseAnnots := by
  induction e with
  | app f a ihf _ =>
    simp only [eraseAnnots, getAppArgs, ihf, List.map_append, List.map_cons, List.map_nil]
  | _ => rfl

/-! ## The substitution operations -/

/-- Erasure commutes with lifting. -/
theorem eraseAnnots_liftLooseBVars : ∀ (e : Expr) (d k : Nat),
    (e.liftLooseBVars d k).eraseAnnots = e.eraseAnnots.liftLooseBVars d k := by
  intro e
  induction e <;> intro d k <;> simp_all [eraseAnnots, liftLooseBVars]
  case bvar i => split <;> rfl

/-- Erasure commutes with opening a binder (the replacement erased
too). -/
theorem eraseAnnots_instantiate1 : ∀ (e v : Expr) (k : Nat),
    (e.instantiate1 v k).eraseAnnots = e.eraseAnnots.instantiate1 v.eraseAnnots k := by
  intro e
  induction e <;> intro v k <;> simp_all [eraseAnnots, instantiate1]
  case bvar i =>
    split
    · rfl
    · split <;> rfl

/-- Erasure commutes with a whole instantiation sequence. -/
theorem eraseAnnots_instSeq : ∀ (vs : List Expr) (t : Nat) (e : Expr),
    (Expr.instSeq vs t e).eraseAnnots
      = Expr.instSeq (vs.map eraseAnnots) t e.eraseAnnots := by
  intro vs
  induction vs with
  | nil => intro t e; rfl
  | cons v vs ih =>
    intro t e
    show (Expr.instSeq vs (t - 1) (e.instantiate1 v t)).eraseAnnots = _
    rw [ih (t - 1) (e.instantiate1 v t), eraseAnnots_instantiate1]
    rfl

/-- Erasure commutes with closing one binder (`abstract1` drops the
annotation, erasure had already flattened it). -/
theorem eraseAnnots_abstract1 : ∀ (e : Expr) (d k : Nat),
    (e.abstract1 d k).eraseAnnots = e.eraseAnnots.abstract1 d k := by
  intro e
  induction e <;> intro d k <;> simp_all [eraseAnnots, abstract1]
  case fvar idx ty _ => split <;> rfl

/-- Erasure commutes with bulk abstraction. -/
theorem eraseAnnots_abstractRange : ∀ (e : Expr) (d k c : Nat),
    (e.abstractRange d k c).eraseAnnots = e.eraseAnnots.abstractRange d k c := by
  intro e
  induction e <;> intro d k c <;> simp_all [eraseAnnots, abstractRange]
  case fvar idx ty _ => split <;> rfl

/-- Erasure does not move the loose-bvar bound. -/
theorem looseBVarsBounded_eraseAnnots : ∀ (e : Expr) (n : Nat),
    e.eraseAnnots.looseBVarsBounded n = e.looseBVarsBounded n := by
  intro e
  induction e <;> intro n <;> simp_all [eraseAnnots, looseBVarsBounded]

/-- Erasure does not move the reachable-`fvar` bound. -/
theorem fvarsBelow_eraseAnnots : ∀ (e : Expr) (n : Nat),
    e.eraseAnnots.fvarsBelow n ↔ e.fvarsBelow n := by
  intro e
  induction e <;> intro n <;> simp_all [eraseAnnots, fvarsBelow]

/-! ## The open/close roundtrip

Under erasure every annotation is `.sort .zero`, so the roundtrip's
`fvarConsistent` side condition is discharged once and for all. -/

/-- An erased term's annotations are all `.sort .zero`, which is
`fvarConsistent` at every index. -/
theorem fvarConsistent_of_eraseAnnots : ∀ {e : Expr}, e.eraseAnnots = e →
    ∀ d, fvarConsistent d (.sort .zero) e := by
  intro e
  induction e <;> intro he d <;> simp_all [eraseAnnots, fvarConsistent]

/-- The canonical opener list, one variable longer at the end. -/
theorem openFvars_snoc : ∀ (d k : Nat),
    Verify.openFvars d (k + 1)
      = Verify.openFvars d k ++ [Expr.fvar (d + k) (.sort .zero)]
  | d, 0 => by simp [Verify.openFvars]
  | d, k + 1 => by
    rw [Verify.openFvars_succ d (k + 1), openFvars_snoc (d + 1) k,
      Verify.openFvars_succ d k]
    simp only [List.cons_append]
    rw [show d + 1 + k = d + (k + 1) from by omega]

/-- The bulk abstraction of an erased term, re-opened at the canonical
openers, is the term again. -/
theorem instSeq_abstractRange_erased :
    ∀ (k : Nat) {e : Expr} (d c : Nat), e.eraseAnnots = e →
      e.looseBVarsBounded c = true →
      Expr.instSeq (Verify.openFvars d k) (k + c - 1) (e.abstractRange d k c) = e := by
  intro k
  induction k with
  | zero =>
    intro e d c _ _
    rw [ConLeche.abstractRange_zero]
    rfl
  | succ k ih =>
    intro e d c he hb
    rw [ConLeche.abstractRange_succ, openFvars_snoc d k, Expr.instSeq_append]
    have hlen : (Verify.openFvars d k).length = k := Verify.openFvars_length d k
    have hd : k + 1 + c - 1 - (Verify.openFvars d k).length = c := by rw [hlen]; omega
    rw [hd]
    have hb' : (e.abstract1 (d + k) c).looseBVarsBounded (c + 1) = true :=
      ConLeche.looseBVarsBounded_abstract1 e c hb
    have he' : (e.abstract1 (d + k) c).eraseAnnots = e.abstract1 (d + k) c := by
      rw [eraseAnnots_abstract1, he]
    have hih := ih (e := e.abstract1 (d + k) c) d (c + 1) he' hb'
    rw [show k + (c + 1) - 1 = k + 1 + c - 1 from by omega] at hih
    rw [hih]
    show (e.abstract1 (d + k) c).instantiate1 (Expr.fvar (d + k) (.sort .zero)) c = e
    exact ConLeche.abstract1_instantiate1 e c
      (fvarConsistent_of_eraseAnnots he (d + k)) hb

/-- **The roundtrip.**  Closing the leading `nP` free variables and
re-opening them at *any* variables with the same indices — the opener
list `openPisAtFvars` produces, whose annotations are the opener's own
domains — returns the term up to annotations.  No `fvarConsistent`
hypothesis: erasure is what absorbs the annotation mismatch. -/
theorem eraseAnnots_openAbstract {nP : Nat} (e : Expr)
    (hb : e.looseBVarsBounded 0 = true) (fvs : List Expr) (hlen : fvs.length = nP)
    (hidx : ∀ k, k < nP → ∃ ty, fvs[k]? = some (.fvar k ty)) :
    (Expr.instSeq fvs (nP - 1) (e.abstractRange 0 nP 0)).eraseAnnots = e.eraseAnnots := by
  have hmap : fvs.map eraseAnnots = Verify.openFvars 0 nP := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < nP
    · obtain ⟨ty, hty⟩ := hidx k hk
      rw [List.getElem?_map, hty, Verify.openFvars_getElem? hk]
      simp [eraseAnnots]
    · rw [List.getElem?_map, List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [Verify.openFvars_length]; omega)]
      rfl
  rw [eraseAnnots_instSeq, hmap, eraseAnnots_abstractRange]
  have := instSeq_abstractRange_erased nP (e := e.eraseAnnots) 0 0
    (eraseAnnots_idem e) (by rw [looseBVarsBounded_eraseAnnots]; exact hb)
  rw [show nP + 0 - 1 = nP - 1 from by omega] at this
  exact this

end ConLeche.Expr
