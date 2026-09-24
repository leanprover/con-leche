module

public import ConLeche.Model.Annot.BitInst
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Semantics.Tower.TowerIntro
public import ConLeche.Semantics.NoBVar
import ConLeche.Model.IndSubst
import ConLeche.Semantics.Kit

public section

/-!
# Filling the holes back in, all at once (lane HOLE2, stage E2a)

The block's walked term has its members abstracted to the hole
variables `p ..< p + k` (`nestAbstract`).  Substituting the members'
constants back, top hole first (`substAll`), gives the concrete term up
to erasure (`substAll_replaceConsts_erasedEq`), and the substitution
lemma (`denoteMeta_substFvarAt`) iterated says the concrete reading is
the abstract one with the holes' bound variables instantiated at the
members' leaves (`instAll`, `denoteMeta_substAll`).  The algebra of
`instAll` — through Π-towers and spines, on variables, against values
(`interp_instAll`: the instantiated term reads, at a frame, what the
abstract one reads with the leaves' values in the hole slots) and as
the inverse of a lift on a hole-free term (`instAll_liftN_of_noBVar`) —
is what turns that into the stored field shape facts.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

/-! ## The operations -/

/-- Substitute `as[m]` for the variable `p + m`, the top one first. -/
@[expose] def substAll : Nat → List Expr → Expr → Expr
  | _, [], e => e
  | p, a :: as, e => Expr.substFvarAt p a (substAll (p + 1) as e)

/-- Instantiate the bound variables `c ..< c + xs.length` at `xs`, the
innermost one (`c`) at the LAST entry. -/
@[expose] def instAll : List AnnotTerm → Nat → AnnotTerm → AnnotTerm
  | [], _, e => e
  | x :: xs, c, e => (instAll xs c e).inst x c

/-! ## `substAll`, syntactically -/

theorem fvarsBelow_substFvarAt {p D : Nat} {a : Expr} (hpD : p ≤ D) (ha : Expr.fvarsBelow D a) :
    ∀ (e : Expr), Expr.fvarsBelow (D + 1) e → Expr.fvarsBelow D (Expr.substFvarAt p a e) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    simp only [Expr.substFvarAt]
    split
    · exact ha
    · split
      · simp only [Expr.fvarsBelow]; omega
      · simp only [Expr.fvarsBelow]; omega
  | bvar _ => intro _; trivial
  | sort _ => intro _; trivial
  | const _ _ => intro _; trivial
  | lit _ => intro _; trivial
  | app f b ihf ihb => intro h; exact ⟨ihf h.1, ihb h.2⟩
  | lam t b _ iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b _ iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb => intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj _ _ e ih => intro h; exact ih h

theorem fvarsBelow_substAll :
    ∀ (as : List Expr) (p D : Nat) (e : Expr), p ≤ D → (∀ a ∈ as, Expr.fvarsBelow 0 a) →
      Expr.fvarsBelow (D + as.length) e → Expr.fvarsBelow D (substAll p as e)
  | [], _, _, _, _, _, h => h
  | a :: as, p, D, e, hpD, ha, h => by
    refine fvarsBelow_substFvarAt hpD
      (Expr.fvarsBelow_mono (Nat.zero_le _) (ha a List.mem_cons_self)) _ ?_
    refine fvarsBelow_substAll as (p + 1) (D + 1) e (by omega)
      (fun b hb => ha b (List.mem_cons_of_mem _ hb)) ?_
    simpa [Nat.add_assoc, Nat.add_comm 1] using h

theorem substAll_app : ∀ (as : List Expr) (p : Nat) (f a : Expr),
    substAll p as (.app f a) = .app (substAll p as f) (substAll p as a)
  | [], _, _, _ => rfl
  | b :: as, p, f, a => by
    simp only [substAll, substAll_app as (p + 1) f a]; rfl

theorem substAll_lam : ∀ (as : List Expr) (p : Nat) (t b : Expr) (bm : ConLeche.BinderMeta),
    substAll p as (.lam t b bm) = .lam (substAll p as t) (substAll p as b) bm
  | [], _, _, _, _ => rfl
  | c :: as, p, t, b, bm => by
    simp only [substAll, substAll_lam as (p + 1) t b bm]; rfl

theorem substAll_forallE : ∀ (as : List Expr) (p : Nat) (t b : Expr) (bm : ConLeche.BinderMeta),
    substAll p as (.forallE t b bm) = .forallE (substAll p as t) (substAll p as b) bm
  | [], _, _, _, _ => rfl
  | c :: as, p, t, b, bm => by
    simp only [substAll, substAll_forallE as (p + 1) t b bm]; rfl

theorem substAll_letE : ∀ (as : List Expr) (p : Nat) (t v b : Expr),
    substAll p as (.letE t v b) = .letE (substAll p as t) (substAll p as v) (substAll p as b)
  | [], _, _, _, _ => rfl
  | c :: as, p, t, v, b => by
    simp only [substAll, substAll_letE as (p + 1) t v b]; rfl

theorem substAll_proj : ∀ (as : List Expr) (p : Nat) (s : Name) (i : Nat) (e : Expr),
    substAll p as (.proj s i e) = .proj s i (substAll p as e)
  | [], _, _, _, _ => rfl
  | c :: as, p, s, i, e => by
    simp only [substAll, substAll_proj as (p + 1) s i e]; rfl

theorem substAll_bvar : ∀ (as : List Expr) (p i : Nat), substAll p as (.bvar i) = .bvar i
  | [], _, _ => rfl
  | c :: as, p, i => by simp only [substAll, substAll_bvar as (p + 1) i]; rfl

theorem substAll_sort : ∀ (as : List Expr) (p : Nat) (u : Level), substAll p as (.sort u) = .sort u
  | [], _, _ => rfl
  | c :: as, p, u => by simp only [substAll, substAll_sort as (p + 1) u]; rfl

theorem substAll_lit : ∀ (as : List Expr) (p : Nat) (l : ConLeche.Literal),
    substAll p as (.lit l) = .lit l
  | [], _, _ => rfl
  | c :: as, p, l => by simp only [substAll, substAll_lit as (p + 1) l]; rfl

theorem substAll_const : ∀ (as : List Expr) (p : Nat) (n : Name) (us : List Level),
    substAll p as (.const n us) = .const n us
  | [], _, _, _ => rfl
  | c :: as, p, n, us => by simp only [substAll, substAll_const as (p + 1) n us]; rfl

theorem substAll_fvar_lt : ∀ (as : List Expr) (p i : Nat) (ty : Expr), i < p →
    substAll p as (.fvar i ty) = .fvar i ty
  | [], _, _, _, _ => rfl
  | c :: as, p, i, ty, h => by
    simp only [substAll, substAll_fvar_lt as (p + 1) i ty (by omega)]
    simp [Expr.substFvarAt, show i ≠ p by omega, show ¬ i > p by omega]

theorem substAll_fvar_hole : ∀ (as : List Expr) (p m : Nat) (ty a : Expr),
    (∀ b ∈ as, ∃ n us, b = .const n us) → as[m]? = some a → substAll p as (.fvar (p + m) ty) = a
  | [], _, _, _, _, _, h => by simp at h
  | c :: as, p, 0, ty, a, hc, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [substAll, Nat.add_zero, substAll_fvar_lt as (p + 1) p ty (by omega)]
    simp [Expr.substFvarAt]
  | c :: as, p, m + 1, ty, a, hc, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [substAll]
    rw [show p + (m + 1) = (p + 1) + m by omega,
      substAll_fvar_hole as (p + 1) m ty a (fun b hb => hc b (List.mem_cons_of_mem _ hb)) h]
    obtain ⟨n, us, rfl⟩ := hc a (List.mem_cons_of_mem _ (List.mem_of_getElem? h))
    rfl

/-- **Substituting the holes back undoes the abstraction**, up to
erasure: a term below `p` whose constants `f` replaced by hole variables
`p + m` gets `as[m]` back where the constant stood. -/
theorem substAll_replaceConsts_erasedEq {p : Nat} {as : List Expr}
    {f : Name → List Level → Option Expr}
    (has : ∀ a ∈ as, ∃ n us, a = .const n us)
    (hf : ∀ c us e, f c us = some e → ∃ m ty, e = .fvar (p + m) ty ∧ as[m]? = some (.const c us)) :
    ∀ (Y : Expr), Expr.fvarsBelow p Y → Expr.ErasedEq (substAll p as (Y.replaceConsts f)) Y := by
  intro Y
  induction Y with
  | bvar i => intro _; rw [Expr.replaceConsts, substAll_bvar]; exact Expr.ErasedEq.rfl _
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    rw [Expr.replaceConsts, substAll_fvar_lt as p i _ h]
    rfl
  | sort u => intro _; rw [Expr.replaceConsts, substAll_sort]; exact Expr.ErasedEq.rfl _
  | lit l => intro _; rw [Expr.replaceConsts, substAll_lit]; exact Expr.ErasedEq.rfl _
  | const c us =>
    intro _
    rw [Expr.replaceConsts]
    cases hfc : f c us with
    | none => rw [Option.getD_none, substAll_const]; exact Expr.ErasedEq.rfl _
    | some e =>
      obtain ⟨m, ty, rfl, hm⟩ := hf c us e hfc
      rw [Option.getD_some, substAll_fvar_hole as p m ty _ has hm]
      exact Expr.ErasedEq.rfl _
  | app a b iha ihb =>
    intro h
    rw [Expr.replaceConsts, substAll_app]
    exact ⟨iha h.1, ihb h.2⟩
  | lam t b bm iht ihb =>
    intro h
    rw [Expr.replaceConsts, substAll_lam]
    exact ⟨rfl, iht h.1, ihb h.2⟩
  | forallE t b bm iht ihb =>
    intro h
    rw [Expr.replaceConsts, substAll_forallE]
    exact ⟨rfl, iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    rw [Expr.replaceConsts, substAll_letE]
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    rw [Expr.replaceConsts, substAll_proj]
    exact ⟨rfl, rfl, ih h⟩

/-! ## `substAll`, read -/

section Read

variable {env : Env} {φ : Name → Nat} {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The substitution lemma, iterated**: substituting closed terms
reading `xs` for the variables `p ..< p + k` reads as the abstract
reading with the corresponding bound variables instantiated. -/
theorem denoteMeta_substAll
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (as : List Expr) (xs : List AnnotTerm), as.length = xs.length →
      (∀ (i : Nat) (a : Expr) (x : AnnotTerm), as[i]? = some a → xs[i]? = some x →
        Expr.WScoped 0 a ∧ a.looseBVarsBounded 0 = true ∧
          ∀ d, denoteMeta acval env φ d a = some x) →
      ∀ (p D : Nat) (e : Expr), p ≤ D → Expr.fvarsBelow (D + as.length) e →
        denoteMeta acval env φ D (substAll p as e)
          = (denoteMeta acval env φ (D + as.length) e).map (instAll xs (D - p))
  | [], [], _, _, p, D, e, _, _ => by
    simp only [substAll, List.length_nil, Nat.add_zero]
    cases denoteMeta acval env φ D e <;> rfl
  | [], _ :: _, hl, _, _, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _, _, _ => by simp at hl
  | a :: as, x :: xs, hl, hax, p, D, e, hpD, hfe => by
    obtain ⟨hw, hb, hr⟩ := hax 0 a x rfl rfl
    have hax' : ∀ (i : Nat) (a : Expr) (x : AnnotTerm), as[i]? = some a → xs[i]? = some x →
        Expr.WScoped 0 a ∧ a.looseBVarsBounded 0 = true ∧
          ∀ d, denoteMeta acval env φ d a = some x :=
      fun i a x ha hx => hax (i + 1) a x ha hx
    have hfe' : Expr.fvarsBelow (D + 1 + as.length) e := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using hfe
    have hall0 : ∀ b ∈ as, Expr.fvarsBelow 0 b := by
      intro b hb
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
      obtain ⟨y, hy⟩ : ∃ y, xs[i]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp at hl; omega)⟩
      exact (hax' i b y hi hy).1.fvarsBelow
    show denoteMeta acval env φ D (Expr.substFvarAt p a (substAll (p + 1) as e)) = _
    rw [denoteMeta_substFvarAt hacl hainst (Expr.WScoped.mono (Nat.zero_le p) hw) hb (hr p) _ D
        hpD (fvarsBelow_substAll as (p + 1) (D + 1) e (by omega) hall0 hfe'),
      denoteMeta_substAll hacl hainst as xs (by simpa using hl) hax' (p + 1) (D + 1) e (by omega)
        hfe',
      Option.map_map, show D + 1 - (p + 1) = D - p by omega,
      show D + 1 + as.length = D + (a :: as).length by simp; omega]
    rfl

end Read

/-! ## `instAll`, structurally -/

open ConLeche.Semantics.AnnotTerm in
theorem instAll_pi : ∀ (xs : List AnnotTerm) (c u v : Nat) (A B : AnnotTerm),
    instAll xs c (.pi u v A B) = .pi u v (instAll xs c A) (instAll xs (c + 1) B)
  | [], _, _, _, _, _ => rfl
  | x :: xs, c, u, v, A, B => by simp only [instAll, instAll_pi xs c u v A B, inst_pi]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_lam : ∀ (xs : List AnnotTerm) (c u : Nat) (A b : AnnotTerm),
    instAll xs c (.lam u A b) = .lam u (instAll xs c A) (instAll xs (c + 1) b)
  | [], _, _, _, _ => rfl
  | x :: xs, c, u, A, b => by simp only [instAll, instAll_lam xs c u A b, inst_lam]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_app : ∀ (xs : List AnnotTerm) (c : Nat) (f a : AnnotTerm),
    instAll xs c (.app f a) = .app (instAll xs c f) (instAll xs c a)
  | [], _, _, _ => rfl
  | x :: xs, c, f, a => by simp only [instAll, instAll_app xs c f a, inst_app]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_eqE : ∀ (xs : List AnnotTerm) (c : Nat) (a b : AnnotTerm),
    instAll xs c (.eqE a b) = .eqE (instAll xs c a) (instAll xs c b)
  | [], _, _, _ => rfl
  | x :: xs, c, a, b => by simp only [instAll, instAll_eqE xs c a b, inst_eqE]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_fst : ∀ (xs : List AnnotTerm) (c : Nat) (e : AnnotTerm),
    instAll xs c (.fst e) = .fst (instAll xs c e)
  | [], _, _ => rfl
  | x :: xs, c, e => by simp only [instAll, instAll_fst xs c e, inst_fst]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_snd : ∀ (xs : List AnnotTerm) (c : Nat) (e : AnnotTerm),
    instAll xs c (.snd e) = .snd (instAll xs c e)
  | [], _, _ => rfl
  | x :: xs, c, e => by simp only [instAll, instAll_snd xs c e, inst_snd]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_sort : ∀ (xs : List AnnotTerm) (c u : Nat), instAll xs c (.sort u) = .sort u
  | [], _, _ => rfl
  | x :: xs, c, u => by simp only [instAll, instAll_sort xs c u, inst_sort]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_const : ∀ (xs : List AnnotTerm) (c : Nat) (k : ConLeche.Term.BConst)
    (us : List Nat), instAll xs c (.const k us) = .const k us
  | [], _, _, _ => rfl
  | x :: xs, c, k, us => by simp only [instAll, instAll_const xs c k us, inst_const]

open ConLeche.Semantics.AnnotTerm in
theorem instAll_prf : ∀ (xs : List AnnotTerm) (c : Nat), instAll xs c .prf = .prf
  | [], _ => rfl
  | x :: xs, c => by simp only [instAll, instAll_prf xs c, inst_prf]

/-- A telescope's entries instantiated, entry `l` of a telescope
starting at cut `c` at the cut `c + l`. -/
@[expose] def instTele (xs : List AnnotTerm) : Nat → List (Nat × Nat × AnnotTerm) →
    List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | c, dd :: tl => (dd.1, dd.2.1, instAll xs c dd.2.2) :: instTele xs (c + 1) tl

theorem instTele_length (xs : List AnnotTerm) :
    ∀ (c : Nat) (tl : List (Nat × Nat × AnnotTerm)), (instTele xs c tl).length = tl.length
  | _, [] => rfl
  | c, _ :: tl => by simp [instTele, instTele_length xs (c + 1) tl]

theorem instTele_getElem? (xs : List AnnotTerm) :
    ∀ (c : Nat) (tl : List (Nat × Nat × AnnotTerm)) (q : Nat),
      (instTele xs c tl)[q]? = (tl[q]?).map fun dd => (dd.1, dd.2.1, instAll xs (c + q) dd.2.2)
  | _, [], _ => rfl
  | c, _ :: tl, 0 => by simp [instTele]
  | c, _ :: tl, q + 1 => by
    simp only [instTele, List.getElem?_cons_succ]
    rw [instTele_getElem? xs (c + 1) tl q, show c + 1 + q = c + (q + 1) by omega]

theorem instAll_mkPisAV (xs : List AnnotTerm) :
    ∀ (c : Nat) (tl : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      instAll xs c (mkPisAV tl B) = mkPisAV (instTele xs c tl) (instAll xs (c + tl.length) B)
  | c, [], B => by simp [mkPisAV, instTele]
  | c, dd :: tl, B => by
    simp only [mkPisAV, instAll_pi, instTele, List.length_cons]
    rw [instAll_mkPisAV xs (c + 1) tl B, show c + 1 + tl.length = c + (tl.length + 1) by omega]

theorem instAll_mkAppN (xs : List AnnotTerm) (c : Nat) :
    ∀ (args : List AnnotTerm) (f : AnnotTerm),
      instAll xs c (AnnotTerm.mkAppN f args) = AnnotTerm.mkAppN (instAll xs c f) (args.map (instAll xs c))
  | [], f => rfl
  | a :: args, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons]
    rw [instAll_mkAppN xs c args (.app f a), instAll_app]

/-! ## `instAll` on variables -/

open ConLeche.Semantics.AnnotTerm in
/-- A term closed in the lifting sense is fixed by every lift. -/
theorem liftN_closed {x : AnnotTerm} (hx : ∀ k, x.liftN 1 k = x) :
    ∀ (n k : Nat), x.liftN n k = x
  | 0, k => liftN_zero x k
  | n + 1, k => by
    rw [show n + 1 = 1 + n by omega, ← liftN_liftN x 1 n k, liftN_closed hx n k, hx k]

theorem instAll_bvar_lt : ∀ (xs : List AnnotTerm) {c i : Nat}, i < c →
    instAll xs c (.bvar i) = .bvar i
  | [], _, _, _ => rfl
  | x :: xs, c, i, h => by
    simp only [instAll, instAll_bvar_lt xs h, AnnotTerm.inst_bvar, if_pos h]

theorem instAll_bvar_ge : ∀ (xs : List AnnotTerm) {c i : Nat}, c + xs.length ≤ i →
    instAll xs c (.bvar i) = .bvar (i - xs.length)
  | [], _, i, _ => rfl
  | x :: xs, c, i, h => by
    simp only [List.length_cons] at h
    simp only [instAll, instAll_bvar_ge xs (c := c) (i := i) (by omega), AnnotTerm.inst_bvar,
      List.length_cons]
    rw [if_neg (by omega), if_neg (by omega)]
    rw [Nat.sub_sub]

/-- The variable `c + j` is the entry `j` places from the END. -/
theorem instAll_bvar_mid : ∀ (xs : List AnnotTerm) {c j : Nat} {x : AnnotTerm},
    (∀ y ∈ xs, ∀ k, y.liftN 1 k = y) → xs[xs.length - 1 - j]? = some x → j < xs.length →
    instAll xs c (.bvar (c + j)) = x
  | [], _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | y :: xs, c, j, x, hcl, hx, hj => by
    simp only [List.length_cons] at hx hj
    by_cases hjn : j < xs.length
    · have hx' : xs[xs.length - 1 - j]? = some x := by
        rw [show xs.length + 1 - 1 - j = (xs.length - 1 - j) + 1 by omega,
          List.getElem?_cons_succ] at hx
        exact hx
      simp only [instAll]
      rw [instAll_bvar_mid xs (fun z hz => hcl z (List.mem_cons_of_mem _ hz)) hx' hjn]
      have hxm : x ∈ xs := List.mem_of_getElem? hx'
      exact AVExprSubst.inst_eq_self_of_closed (hcl x (List.mem_cons_of_mem _ hxm)) y c
    · obtain rfl : j = xs.length := by omega
      rw [show xs.length + 1 - 1 - xs.length = 0 by omega, List.getElem?_cons_zero,
        Option.some.injEq] at hx
      subst hx
      simp only [instAll]
      rw [instAll_bvar_ge xs (by omega), show c + xs.length - xs.length = c by omega,
        AnnotTerm.inst_bvar, if_neg (by omega), if_pos rfl]
      exact liftN_closed (hcl _ List.mem_cons_self) c 0

/-- **A term reading no hole slot is its instantiation lifted back.** -/
theorem instAll_liftN_of_noBVar :
    ∀ (e : AnnotTerm) (xs : List AnnotTerm) (c : Nat),
      NoBVar (fun i => c ≤ i ∧ i < c + xs.length) e → (instAll xs c e).liftN xs.length c = e := by
  intro e
  induction e with
  | bvar i =>
    intro xs c h
    have h' : ¬ (c ≤ i ∧ i < c + xs.length) := h
    by_cases hic : i < c
    · rw [instAll_bvar_lt xs hic, AnnotTerm.liftN_bvar, if_pos hic]
    · rw [instAll_bvar_ge xs (by omega), AnnotTerm.liftN_bvar, if_neg (by omega)]
      congr 1; omega
  | sort u => intro xs c _; rw [instAll_sort]; rfl
  | const k us => intro xs c _; rw [instAll_const]; rfl
  | prf => intro xs c _; rw [instAll_prf]; rfl
  | app f a ihf iha =>
    intro xs c h
    rw [instAll_app, AnnotTerm.liftN_app, ihf xs c h.1, iha xs c h.2]
  | eqE a b iha ihb =>
    intro xs c h
    rw [instAll_eqE, AnnotTerm.liftN_eqE, iha xs c h.1, ihb xs c h.2]
  | fst e ih => intro xs c h; rw [instAll_fst, AnnotTerm.liftN_fst, ih xs c h]
  | snd e ih => intro xs c h; rw [instAll_snd, AnnotTerm.liftN_snd, ih xs c h]
  | lam u A b ihA ihb =>
    intro xs c h
    rw [instAll_lam, AnnotTerm.liftN_lam, ihA xs c h.1, ihb xs (c + 1) (NoBVar.mono ?_ h.2)]
    intro i hi
    cases i with
    | zero => omega
    | succ i => show c ≤ i ∧ i < c + xs.length; omega
  | pi u v A B ihA ihB =>
    intro xs c h
    rw [instAll_pi, AnnotTerm.liftN_pi, ihA xs c h.1, ihB xs (c + 1) (NoBVar.mono ?_ h.2)]
    intro i hi
    cases i with
    | zero => omega
    | succ i => show c ≤ i ∧ i < c + xs.length; omega

/-! ## `instAll`, interpreted -/

section Interp

variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
theorem instE_consList_add (v : V) :
    ∀ (as : List V) (c : Nat) (ρ : Nat → V),
      instE (as.length + c) v (consList as ρ) = consList as (instE c v ρ)
  | [], c, ρ => by simp
  | a :: as, c, ρ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show as.length + 1 + c = as.length + (c + 1) by omega, instE_consList_add v as (c + 1)]
    congr 1
    funext i
    cases i with
    | zero => simp [instE]
    | succ i =>
      simp only [instE, cons_succ]
      by_cases h1 : i < c
      · rw [if_pos (by omega), if_pos h1]
      · rw [if_neg (by omega), if_neg h1]
        by_cases h2 : i = c
        · rw [if_pos (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg h2]
          cases i with
          | zero => omega
          | succ i => simp

omit [SetTheory V] in
theorem instE_consList (v : V) (as : List V) (ρ : Nat → V) :
    instE as.length v (consList as ρ) = consList as (cons v ρ) := by
  have h := instE_consList_add v as 0 ρ
  rw [Nat.add_zero] at h
  rw [h]
  congr 1
  funext i
  cases i <;> simp [instE]

/-- **The instantiated term reads the abstract one with the values in
the hole slots**: at a frame `as` deep, the leaves `xs` (closed, reading
`hs` everywhere) are the values of the slots `as.length ..<
as.length + k`, the LAST leaf innermost. -/
theorem interp_instAll :
    ∀ (xs : List AnnotTerm) (hs : List V), xs.length = hs.length →
      (∀ (i : Nat) (x : AnnotTerm) (h : V), xs[i]? = some x → hs[i]? = some h →
        ∀ σ : Nat → V, interp V σ x = h) →
      ∀ (e : AnnotTerm) (as : List V) (ρ : Nat → V),
        interp V (consList as ρ) (instAll xs as.length e)
          = interp V (consList as (consList hs ρ)) e
  | [], [], _, _, e, as, ρ => rfl
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | x :: xs, h :: hs, hl, hv, e, as, ρ => by
    simp only [instAll]
    rw [interp_inst, hv 0 x h rfl rfl, instE_consList,
      interp_instAll xs hs (by simpa using hl) (fun i y g hy hg => hv (i + 1) y g hy hg) e as
        (cons h ρ)]
    rfl

end Interp

end ConLeche.Model
