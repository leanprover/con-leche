module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.AbstractRange

public section

/-!
# The copy's telescope, syntactically (task #315 L-B, DESIGN §U.23)

`mkCopy` stores a copy's former as `closeTelescope pbs 0 tyI` — the
block's first former's parameter binders closed around the container's
type instantiated at the pin's components.  The reading of such a term
goes through `openPisAtFvars`, whose action on a `∀`-telescope is known
(`openPisAtFvars_mkPisB`: the openers depend on the binders only, the
body is `instSeq` of the openers), and the bulk abstraction's round
trip is known modulo annotations (`eraseAnnots_openAbstract`).  What
this module adds is the bridge: `closeTelescope` over fvar-free binder
domains IS the `∀`-telescope over the body's bulk abstraction
(`closeTelescope_eq_mkPisB`), plus the small facts the reading needs —
`instPis` as an `instPisAt` residual, loose-variable bounds through
`instPis` and out of `mkAppN`, and `WScoped` out of `mkAppN`.
-/

namespace ConLeche

open Expr

/-- `abstract1` on an fvar-free term is the identity. -/
theorem Expr.abstract1_of_not_hasFvar :
    ∀ (e : Expr) (d k : Nat), e.hasFvar = false → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k h <;> simp_all [hasFvar, abstract1]

/-- **The lowest variable last**: the bulk abstraction of `n + 1`
variables from `i` is the abstraction of the `n` variables above `i`,
then `i` at cut `c + n` — `abstractRange_succ` from the other end. -/
theorem Expr.abstractRange_succ_low :
    ∀ (e : Expr) (i n c : Nat),
      e.abstractRange i (n + 1) c = (e.abstractRange (i + 1) n c).abstract1 i (c + n) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro i n c
    simp only [abstractRange]
    by_cases h1 : i ≤ idx ∧ idx < i + (n + 1)
    · rw [if_pos h1]
      by_cases h2 : i + 1 ≤ idx ∧ idx < i + 1 + n
      · rw [if_pos h2]
        simp only [abstract1]
        congr 1
        omega
      · rw [if_neg h2]
        have hidx : idx = i := by omega
        simp only [abstract1, if_pos hidx]
        congr 1
        omega
    · rw [if_neg h1]
      have h2 : ¬ (i + 1 ≤ idx ∧ idx < i + 1 + n) := by omega
      rw [if_neg h2]
      simp only [abstract1]
      rw [if_neg (by omega)]
  | bvar _ => intro i n c; simp [abstractRange, abstract1]
  | sort _ => intro i n c; simp [abstractRange, abstract1]
  | const _ _ => intro i n c; simp [abstractRange, abstract1]
  | lit _ => intro i n c; simp [abstractRange, abstract1]
  | app f a ihf iha =>
    intro i n c
    simp only [abstractRange, abstract1, ihf, iha]
  | lam ty b _ ihty ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | forallE ty b _ ihty ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | letE ty v b ihty ihv ihb =>
    intro i n c
    simp only [abstractRange, abstract1, ihty, ihv, ihb]
    rw [show c + 1 + n = c + n + 1 from by omega]
  | proj _ _ x ih =>
    intro i n c
    simp only [abstractRange, abstract1, ih]

/-- `mkPisB` at the empty binder list. -/
theorem mkPisB_nil (e : Expr) : mkPisB [] e = e := (mkPisB_eq_foldr [] e).symm

/-- `mkPisB` at a cons. -/
theorem mkPisB_cons (b : Expr × BinderMeta) (bs : List (Expr × BinderMeta)) (e : Expr) :
    mkPisB (b :: bs) e = .forallE b.1 (mkPisB bs e) b.2 := by
  rw [← mkPisB_eq_foldr, ← mkPisB_eq_foldr]
  rfl

/-- A `∀`-telescope over fvar-free domains under `abstract1`: the
domains stay, the body is abstracted under the binders. -/
theorem mkPisB_abstract1 :
    ∀ (bs : List (Expr × BinderMeta)) (X : Expr) (d k : Nat),
      (∀ b ∈ bs, b.1.hasFvar = false) →
      (mkPisB bs X).abstract1 d k = mkPisB bs (X.abstract1 d (k + bs.length))
  | [], X, d, k, _ => by
    rw [mkPisB_nil, mkPisB_nil]
    rfl
  | b :: bs, X, d, k, h => by
    rw [mkPisB_cons, mkPisB_cons]
    show Expr.forallE (b.1.abstract1 d k) ((mkPisB bs X).abstract1 d (k + 1)) b.2
      = Expr.forallE b.1 (mkPisB bs (X.abstract1 d (k + (b :: bs).length))) b.2
    rw [Expr.abstract1_of_not_hasFvar _ _ _ (h b List.mem_cons_self),
      mkPisB_abstract1 bs X d (k + 1) (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')),
      List.length_cons, show k + 1 + bs.length = k + (bs.length + 1) from by omega]

/-- **`closeTelescope` is the telescope over the bulk abstraction** when
the binder domains carry no free variables (the first former's binders,
read off a closed type): one `abstract1` per binder, innermost first,
is `abstractRange` of the body under the binders. -/
theorem closeTelescope_eq_mkPisB :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (e : Expr),
      (∀ b ∈ bs, b.1.hasFvar = false) →
      closeTelescope bs i e = mkPisB bs (e.abstractRange i bs.length 0)
  | [], i, e, _ => by
    rw [mkPisB_nil]
    simp [closeTelescope, abstractRange_zero]
  | (dom, bm) :: bs, i, e, h => by
    simp only [closeTelescope]
    rw [closeTelescope_eq_mkPisB bs (i + 1) e (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      mkPisB_abstract1 bs _ i 0 (fun b hb => h b (List.mem_cons_of_mem _ hb)), Nat.zero_add,
      List.length_cons, Expr.abstractRange_succ_low e i bs.length 0, Nat.zero_add, mkPisB_cons]

/-- An fvar-free telescope has fvar-free domains and body. -/
theorem hasFvar_mkPisB :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
      (mkPisB bs body).hasFvar = false →
      (∀ b ∈ bs, b.1.hasFvar = false) ∧ body.hasFvar = false
  | [], body, h => ⟨fun _ hb => absurd hb (by simp), by rwa [mkPisB_nil] at h⟩
  | b :: bs, body, h => by
    rw [mkPisB_cons] at h
    have h' : (b.1.hasFvar || (mkPisB bs body).hasFvar) = false := h
    simp only [Bool.or_eq_false_iff] at h'
    obtain ⟨hall, hb⟩ := hasFvar_mkPisB bs body h'.2
    refine ⟨fun b' hb' => ?_, hb⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact h'.1
    · exact hall b' hb'

/-- `instPis` is the residual of an `instPisAt` run. -/
theorem instPis_instPisAt :
    ∀ (as : List Expr) (e r : Expr), Expr.instPis e as = some r →
      ∃ ds, Expr.instPisAt as e = some (ds, r)
  | [], e, r, h => by
    simp only [Expr.instPis, Option.some.injEq] at h
    exact ⟨[], by simp [Expr.instPisAt, h]⟩
  | a :: as, e, r, h => by
    cases e with
    | forallE ty body bm =>
      simp only [Expr.instPis] at h
      obtain ⟨ds, hds⟩ := instPis_instPisAt as _ r h
      exact ⟨ty :: ds, by simp [Expr.instPisAt, hds]⟩
    | _ => simp [Expr.instPis] at h

/-- Instantiating a bounded telescope at bounded arguments stays
bounded. -/
theorem looseBVarsBounded_instPis :
    ∀ (as : List Expr) (e r : Expr),
      e.looseBVarsBounded 0 = true → (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      Expr.instPis e as = some r → r.looseBVarsBounded 0 = true
  | [], e, r, he, _, h => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    exact he
  | a :: as, e, r, he, has, h => by
    cases e with
    | forallE ty body bm =>
      simp only [Expr.instPis] at h
      have hb : body.looseBVarsBounded 1 = true := by
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
        exact he.2
      exact looseBVarsBounded_instPis as _ r
        (looseBVarsBounded_instantiate1_gen (has a List.mem_cons_self) hb)
        (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) h
    | _ => simp [Expr.instPis] at h

/-- A bounded application chain has a bounded head and bounded
arguments. -/
theorem looseBVarsBounded_of_mkAppN {k : Nat} :
    ∀ {xs : List Expr} {f : Expr}, (Expr.mkAppN f xs).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ x ∈ xs, x.looseBVarsBounded k = true
  | [], f, h => ⟨h, fun _ hx => absurd hx (by simp)⟩
  | x :: xs, f, h => by
    obtain ⟨hf, hxs⟩ := looseBVarsBounded_of_mkAppN (xs := xs) (f := .app f x) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hf
    refine ⟨hf.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf.2
    · exact hxs y hy

/-- A scoped application chain has a scoped head and scoped
arguments. -/
theorem WScoped_of_mkAppN {d : Nat} :
    ∀ {xs : List Expr} {f : Expr}, Expr.WScoped d (Expr.mkAppN f xs) →
      Expr.WScoped d f ∧ ∀ x ∈ xs, Expr.WScoped d x
  | [], f, h => ⟨h, fun _ hx => absurd hx (by simp)⟩
  | x :: xs, f, h => by
    obtain ⟨hf, hxs⟩ := WScoped_of_mkAppN (xs := xs) (f := .app f x) h
    simp only [Expr.WScoped] at hf
    refine ⟨hf.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf.2
    · exact hxs y hy


/-! ## The open/close round trip, up to `ErasedEq` (task #315 L-B, DESIGN §U.38 (c))

A copy's constructor is STORED closed (`closeTelescope`) and READ open
(`openPisAtFvars`, twice — `MutualCtorDataI.opens`), so every identity
about the elimination's output has to travel that round trip.  It is
**not** an identity: `closeTelescope` leaves each binder's domain where
it stands and the re-opening plants `.fvar i (bs.getD i).1`, so every
free variable the body carries comes back with the CLOSING telescope's
annotation — which at a copy's fields is the positivity-NORMALISED
domain, not the one the minted opening planted.  `abstract1_instantiate1`
is exact only under `fvarConsistent`, which is what fails there; the
tolerance the readings consume is `ErasedEq` (`denoteMeta_erasedEq`),
and `ErasedEq` is exactly blind to `fvar` annotations. -/

/-- `abstract1_instantiate1` with its consistency hypothesis dropped:
the round trip changes nothing an interpretation reads. -/
theorem abstract1_instantiate1_erasedEq {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      Expr.ErasedEq ((e.abstract1 d k).instantiate1 (.fvar d ty) k) e := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1, Expr.ErasedEq]
  case bvar i =>
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [h1, h2, Expr.ErasedEq]
  case fvar idx ty' ih =>
    by_cases hidx : idx = d
    · subst hidx
      rw [if_pos rfl]
      show (Expr.instantiate1 (.bvar k) (.fvar idx ty) k).ErasedEq (.fvar idx ty')
      simp only [Expr.instantiate1]
      exact rfl
    · rw [if_neg hidx]
      exact Expr.ErasedEq.rfl _

/-- The checker's opener respects `ErasedEq`: what it does to a term is
determined by the shape the interpretation reads. -/
theorem openPisAtFvars_erasedEq :
    ∀ (k : Nat) {e e' : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      Expr.ErasedEq e e' → openPisAtFvars k e' d = some (fvs, body) →
      ∃ (fvs' : List Expr) (body' : Expr),
        openPisAtFvars k e d = some (fvs', body') ∧ fvs'.length = fvs.length ∧
        Expr.ErasedEq body' body := by
  intro k
  induction k with
  | zero =>
    intro e e' d fvs body he h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl, he⟩
  | succ k ih =>
    intro e e' d fvs body he h
    match e', h with
    | .forallE dom' body' m', h =>
      match e, he with
      | .forallE dom bodyE m, he =>
        obtain ⟨rfl, hdom, hbody⟩ := he
        simp only [openPisAtFvars] at h
        cases hop : openPisAtFvars k (body'.instantiate1 (.fvar d dom') 0) (d + 1) with
        | none => rw [hop] at h; exact nomatch h
        | some q =>
          rw [hop] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨fvs₂, body₂, hop₂, hlen₂, he₂⟩ := ih
            (Expr.ErasedEq.instantiate1 hbody
              (show Expr.ErasedEq (Expr.fvar d dom) (Expr.fvar d dom') from rfl)) hop
          refine ⟨Expr.fvar d dom :: fvs₂, body₂, ?_, by simp [hlen₂], he₂⟩
          show (match openPisAtFvars k (bodyE.instantiate1 (.fvar d dom) 0) (d + 1) with
            | some (fvs, e) => some (Expr.fvar d dom :: fvs, e)
            | none => none) = _
          rw [hop₂]

/-- A closed telescope is bound-variable closed. -/
theorem looseBVarsBounded_closeTelescope :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (r : Expr),
      (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) → r.looseBVarsBounded 0 = true →
      (closeTelescope bs i r).looseBVarsBounded 0 = true
  | [], _, r, _, hr => hr
  | (dom, bm) :: bs, i, r, hbs, hr => by
    show (Expr.looseBVarsBounded 0 dom &&
      Expr.looseBVarsBounded 1 ((closeTelescope bs (i + 1) r).abstract1 i 0)) = true
    rw [hbs (dom, bm) List.mem_cons_self, Bool.true_and]
    exact ConLeche.looseBVarsBounded_abstract1 _ 0
      (looseBVarsBounded_closeTelescope bs (i + 1) r
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) hr)

/-- **THE ROUND TRIP** (task #315 L-B): a telescope closed over
bound-variable-closed binders and re-opened at the same depth gives
back its own binders' domains and a body `ErasedEq` to the one it was
closed around. -/
theorem openPisAtFvars_closeTelescope :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (r : Expr),
      (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) → r.looseBVarsBounded 0 = true →
      ∃ (fvs : List Expr) (r' : Expr),
        openPisAtFvars bs.length (closeTelescope bs i r) i = some (fvs, r') ∧
        fvs.length = bs.length ∧ Expr.ErasedEq r' r
  | [], i, r, _, _ => ⟨[], r, rfl, rfl, Expr.ErasedEq.rfl r⟩
  | (dom, bm) :: bs, i, r, hbs, hr => by
    obtain ⟨fvs, r', hop, hlen, her⟩ :=
      openPisAtFvars_closeTelescope bs (i + 1) r
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) hr
    obtain ⟨fvs₂, body₂, hop₂, hlen₂, he₂⟩ := openPisAtFvars_erasedEq bs.length
      (abstract1_instantiate1_erasedEq (ty := dom) (closeTelescope bs (i + 1) r) 0
        (looseBVarsBounded_closeTelescope bs (i + 1) r
          (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) hr)) hop
    refine ⟨Expr.fvar i dom :: fvs₂, body₂, ?_, by simp [hlen₂, hlen], he₂.trans her⟩
    show (match openPisAtFvars bs.length
        (((closeTelescope bs (i + 1) r).abstract1 i 0).instantiate1 (.fvar i dom) 0) (i + 1) with
      | some (fvs, e) => some (Expr.fvar i dom :: fvs, e)
      | none => none) = _
    rw [hop₂]

/-- **`ErasedEq` at an application spine**: what the interpretation
reads of a spine is its head and its arguments, one by one.  The arms
compare a copy's residual with the container's through two different
openings, and only the ARGUMENTS past the parameters have to agree. -/
theorem ErasedEq.mkAppN_inv :
    ∀ {as bs : List Expr} {f g : Expr},
      Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN g bs) → as.length = bs.length →
      Expr.ErasedEq f g ∧
        ∀ l, l < as.length → Expr.ErasedEq (as.getD l default) (bs.getD l default) := by
  intro as
  induction as with
  | nil =>
    intro bs f g h hlen
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨h, fun l hl => absurd hl (by simp)⟩
  | cons a as ih =>
    intro bs f g h hlen
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      obtain ⟨hfg, hargs⟩ := ih (f := .app f a) (g := .app g b)
        (show Expr.ErasedEq (Expr.mkAppN (.app f a) as) (Expr.mkAppN (.app g b) bs) from h)
        (by simpa using hlen)
      obtain ⟨hf, hab⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := hfg
      refine ⟨hf, fun l hl => ?_⟩
      cases l with
      | zero => exact hab
      | succ l => exact hargs l (by simpa using hl)

end ConLeche
