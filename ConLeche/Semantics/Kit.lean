import Lech.Semantics.Interp
import Lech.Verify.Denote.VClosed

/-!
# The `interp2` lemma kit (task #151, tier B)

Two halves.

**The substitution stack** — `interp2_liftN` and `interp2_inst`, the
layer's *entire* substitution metatheory, transposed from
`Lech/VExpr/Semantics/Interp.lean` unchanged in shape.  That they
transpose is the point: `interp2` is structural, so removing the
collapse costs nothing here.  (lean4lean needs ~123 syntactic lemmas at
this spot because its metatheory is syntactic; soundness against a
model needs two semantic ones.)

**The regime lemmas** — what the two-regime design is *for*:

* `interp2_mem_pi_pos` — the graph-regime inversion.  A member of
  `⟦(x : A) → B⟧` with the codomain sort nonzero **is** a graph, with
  domain exactly `⟦A⟧`, pointwise-fibred, non-`pt`, and canonical `∅`
  off the domain.  By definition, not by dispatch.
* `interp2_beta_pos` / `interp2_app_graph` — on-domain application
  computes, with no typing premise at all.
* `interp2_pi_zero_subsingleton`, `interp2_proof_irrel` — the squash
  regime is subsingleton-valued.
* `interp2_pi_zero_small` — **impredicativity**: a product landing in
  `Prop` is a truth value, for an arbitrary domain.
* `interp2_not_pt_mem_pi_pos`, `interp2_app_off_dom` — junk-freeness:
  the proof point never inhabits a graph-regime product, and off-domain
  application is the canonical `∅`, never a point a consumer must
  dispatch on.

On `pt`: the only occurrences in this file are in *conclusions about
the squash regime* (`interp2 V ρ .prf = pt` and the `v = 0`
subsingleton facts) and in the *negative* junk-freeness statements.  No
lemma here has a `pt` hypothesis, no proof does a case split on whether
a value is `pt`, and the graph regime never mentions it except to deny
it.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The substitution stack -/

theorem interp2_liftN (n : Nat) :
    ∀ (e : AVExpr) (k : Nat) (ρ : Nat → V),
      interp2 V ρ (e.liftN n k) = interp2 V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AVExpr.liftN_bvar, interp2_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; simp only [AVExpr.liftN_app, interp2_app, ihf, iha]
  | lam v A b ihA ihb =>
    intro k ρ
    simp only [AVExpr.liftN_lam, interp2_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    simp only [AVExpr.liftN_pi, interp2_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]
  | letE T e b ihT ihe ihb =>
    intro k ρ
    simp only [AVExpr.liftN_letE, interp2_letE, ihe, ihb, cons_shiftE]
  | eqE T a b ihT iha ihb =>
    intro k ρ; simp only [AVExpr.liftN_eqE, interp2_eqE, iha, ihb]
  | proj i e ihe =>
    intro k ρ; simp only [AVExpr.liftN_proj, interp2_proj, ihe]
  | prf => intro k ρ; rfl

theorem interp2_lift (e : AVExpr) (ρ : Nat → V) :
    interp2 V ρ e.lift = interp2 V (fun i => ρ (i + 1)) e := by
  rw [AVExpr.lift, interp2_liftN, shiftE_zero]

theorem interp2_lift_cons (e : AVExpr) (x : V) (ρ : Nat → V) :
    interp2 V (cons x ρ) e.lift = interp2 V ρ e := by
  rw [interp2_lift]; rfl

theorem interp2_inst :
    ∀ (e a : AVExpr) (k : Nat) (ρ : Nat → V),
      interp2 V ρ (e.inst a k) =
        interp2 V (instE k (interp2 V (shiftE k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    show interp2 V ρ
        (if i < k then .bvar i
         else if i = k then AVExpr.liftN k a else .bvar (i - 1)) =
      instE k (interp2 V (shiftE k 0 ρ) a) ρ i
    by_cases h : i < k
    · simp only [if_pos h, instE]; rfl
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, instE]
        exact interp2_liftN V k a 0 ρ
      · simp only [if_neg h, if_neg h2, instE]; rfl
  | sort u => intro a k ρ; rfl
  | const c us => intro a k ρ; rfl
  | app f b ihf ihb =>
    intro a k ρ; simp only [AVExpr.inst_app, interp2_app, ihf, ihb]
  | lam v A b ihA ihb =>
    intro a k ρ
    simp only [AVExpr.inst_lam, interp2_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ
    simp only [AVExpr.inst_pi, interp2_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]
  | letE T e b ihT ihe ihb =>
    intro a k ρ
    simp only [AVExpr.inst_letE, interp2_letE, ihe, ihb, shiftE_succ_cons,
      cons_instE]
  | eqE T b c ihT ihb ihc =>
    intro a k ρ; simp only [AVExpr.inst_eqE, interp2_eqE, ihb, ihc]
  | proj i e ihe =>
    intro a k ρ; simp only [AVExpr.inst_proj, interp2_proj, ihe]
  | prf => intro a k ρ; rfl

/-! ### Interpretation invariance below a bound

`interp_congr_below`/`interp_closed`'s analogue
(`Lech/SetR/AnnotOkV.lean`): a closed term's interpretation does not
read the environment.  Stated through the **erasure's** bound rather
than a fresh `AVExpr.bvarsBelow`: `erase` maps `bvar i` to `bvar i` and
preserves every former's shape, so `VExpr.bvarsBelow k e.erase` says
exactly "`e`'s indices are below `k`", and no new predicate is needed.

Needed by the literal clauses of any `Claims2` discharge: the `Nat`/
`String` blocks of `Sound/{Lit,NatOps,NatOpsWf}.lean` touch the
interpretation only through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed`, and this was the one of the five with
no `interp2` analogue. -/

theorem interp2_congr_below :
    ∀ (e : AVExpr) (k : Nat) (ρ ρ' : Nat → V),
      Lech.VExpr.VExpr.bvarsBelow k e.erase →
      (∀ i, i < k → ρ i = ρ' i) →
      interp2 V ρ e = interp2 V ρ' e := by
  intro e
  induction e with
  | bvar i => intro k ρ ρ' hb hag; exact hag i hb
  | sort u => intros; rfl
  | const c us => intros; rfl
  | prf => intros; rfl
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    simp only [interp2_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    simp only [interp2_lam, ihA k ρ ρ' hb.1 hag]
    refine lamR_congr fun x _ => ihb (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    simp only [interp2_pi, ihA k ρ ρ' hb.1 hag]
    refine piR_congr fun x _ => ihB (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | letE T v b ihT ihv ihb =>
    intro k ρ ρ' hb hag
    rw [interp2_letE, interp2_letE, ihv k ρ ρ' hb.2.1 hag]
    refine ihb (k + 1) _ _ hb.2.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | eqE T a b ihT iha ihb =>
    intro k ρ ρ' hb hag
    simp only [interp2_eqE, iha k ρ ρ' hb.2.1 hag,
      ihb k ρ ρ' hb.2.2 hag]
  | proj i e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp2_proj, ihe k ρ ρ' hb hag]

/-- A closed term interprets the same under every environment. -/
theorem interp2_closed {e : AVExpr}
    (he : Lech.VExpr.VExpr.bvarsBelow 0 e.erase) (ρ ρ' : Nat → V) :
    interp2 V ρ e = interp2 V ρ' e :=
  interp2_congr_below V e 0 ρ ρ' he
    (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- Substitution at the outermost binder — the form every rule uses. -/
theorem interp2_inst0 (e a : AVExpr) (ρ : Nat → V) :
    interp2 V ρ (e.inst a) = interp2 V (cons (interp2 V ρ a) ρ) e := by
  rw [interp2_inst, shiftE_zero_zero, instE_zero]

theorem interp2_mkAppN (ρ : Nat → V) :
    ∀ (as : List AVExpr) (f : AVExpr),
      interp2 V ρ (AVExpr.mkAppN f as) =
        as.foldl (fun r a => SetTheory.app r (interp2 V ρ a)) (interp2 V ρ f)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AVExpr.mkAppN_cons, List.foldl_cons]
    rw [interp2_mkAppN ρ as (.app f a)]
    rfl

/-! ## The graph regime

Everything below is stated at the interpretation, where the annotation
is visible on the term.  Nothing inspects a value. -/

/-- **The graph-regime inversion** — the prized one.  If the codomain
annotation of a product is nonzero, every member of its interpretation
is a genuine function graph: it *is* the graph of its own application
over `⟦A⟧` (so its domain is exactly `⟦A⟧`), its applications land in
the fibres pointwise, it applies to the canonical junk `∅` off the
domain, and it is not the proof point.

All four clauses hold **by definition** of the positive regime — no
case split, no `mem_piC_cases`, and in particular nothing about what
the fibres `⟦B⟧` are: `interp2_univ_cod_inversion`
(`Interp2/Univ.lean`) is this lemma at universe-valued fibres. -/
theorem interp2_mem_pi_pos {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AVExpr} {f : V} (hf : f ∈ˢ interp2 V ρ (.pi u v A B)) :
    graph (fun x => SetTheory.app f x) (interp2 V ρ A) = f ∧
    (∀ x, x ∈ˢ interp2 V ρ A →
      SetTheory.app f x ∈ˢ interp2 V (cons x ρ) B) ∧
    (∀ a, ¬ a ∈ˢ interp2 V ρ A → SetTheory.app f a = empty) ∧
    f ≠ pt :=
  mem_piR_pos hv hf

/-- The domain of a graph-regime product member is exactly the
interpretation of the binder's domain: it is recoverable from the value
alone, and two products containing the same member have the same
domain.  No `≠ pt` side condition — that is the collapse's tax, and it
is gone. -/
theorem interp2_pi_dom_unique {v v' : Nat} (hv : v ≠ 0) (hv' : v' ≠ 0)
    {u u' : Nat} {ρ ρ' : Nat → V} {A B A' B' : AVExpr} {f : V}
    (h1 : f ∈ˢ interp2 V ρ (.pi u v A B))
    (h2 : f ∈ˢ interp2 V ρ' (.pi u' v' A' B')) :
    interp2 V ρ A = interp2 V ρ' A' :=
  piR_dom_unique hv hv' h1 h2

/-- **Application is graph application.**  On the domain, the value
`app f a` is literally the second component of the pair that `f`, as a
set, contains at `a` — there is no tag, no fallback and no dispatch in
the graph regime. -/
theorem interp2_app_graph {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AVExpr} {f a : V} (hf : f ∈ˢ interp2 V ρ (.pi u v A B))
    (ha : a ∈ˢ interp2 V ρ A) :
    kpair a (SetTheory.app f a) ∈ˢ f := by
  have hg := (interp2_mem_pi_pos V hv hf).1
  have h1 : kpair a (SetTheory.app f a) ∈ˢ
      graph (fun x => SetTheory.app f x) (interp2 V ρ A) :=
    mem_graph.mpr ⟨a, ha, rfl⟩
  rwa [hg] at h1

/-- **β in the graph regime**, with *no* typing premise beyond the
argument inhabiting the domain.  Under the collapse this needs the
kernel's annotation gates; here it is `app_graph`. -/
theorem interp2_beta_pos {v : Nat} (hv : v ≠ 0) (ρ : Nat → V)
    (A b a : AVExpr) (ha : interp2 V ρ a ∈ˢ interp2 V ρ A) :
    interp2 V ρ (.app (.lam v A b) a) = interp2 V ρ (b.inst a) := by
  rw [interp2_app, interp2_lam, interp2_inst0, app_lamR_pos hv ha]

/-- β in the squash regime: both sides are the canonical proof as soon
as the body's fibres are truth values — the premise a `Prop`-valued
codomain supplies. -/
theorem interp2_beta_zero (ρ : Nat → V) (A b a : AVExpr) {B : V → V}
    (ha : interp2 V ρ a ∈ˢ interp2 V ρ A)
    (hbody : ∀ x, x ∈ˢ interp2 V ρ A → interp2 V (cons x ρ) b ∈ˢ B x)
    (hB : ∀ x, x ∈ˢ interp2 V ρ A → B x ∈ˢ (univZero : V)) :
    interp2 V ρ (.app (.lam 0 A b) a) = interp2 V ρ (b.inst a) := by
  rw [interp2_app, interp2_lam, interp2_inst0]
  exact app_lamR ha hbody (fun _ => hB)

/-- η in the graph regime: a product member is the abstraction of its
applications. -/
theorem interp2_eta {v u : Nat} {ρ : Nat → V} {A B : AVExpr} {f : V}
    (hf : f ∈ˢ interp2 V ρ (.pi u v A B)) :
    lamR v (interp2 V ρ A) (fun x => SetTheory.app f x) = f :=
  lamR_eta hf

/-! ## Junk-freeness: there is no proof point in the graph regime -/

/-- **The proof point never inhabits a graph-regime product.**
Unconditional in the domain and in the fibres — in particular at
universe-valued codomains, where the collapse's
`pt ∈ˢ piC A (fun _ => univ 0)` was the wall that the eta-law
derivation had to dodge (`docs/SetR-DESIGN.md`, T5 c5). -/
theorem interp2_not_pt_mem_pi_pos {v : Nat} (hv : v ≠ 0) {u : Nat}
    {ρ : Nat → V} {A B : AVExpr} :
    ¬ (pt : V) ∈ˢ interp2 V ρ (.pi u v A B) :=
  not_pt_mem_piR_pos hv

/-- Off-domain application of a graph-regime member is the canonical
junk `∅`, never a point: no junk-point is needed, and off-domain
behaviour is *canonical*, so on-domain agreement is total agreement
(`interp2_pi_ext`). -/
theorem interp2_app_off_dom {v : Nat} (hv : v ≠ 0) {u : Nat} {ρ : Nat → V}
    {A B : AVExpr} {f a : V} (hf : f ∈ˢ interp2 V ρ (.pi u v A B))
    (ha : ¬ a ∈ˢ interp2 V ρ A) : SetTheory.app f a = empty :=
  app_off_dom_piR_pos hv hf ha

/-- Function extensionality at a product: on-domain agreement is
equality.  (Holds in both regimes — at `v = 0` both sides are the
canonical proof.) -/
theorem interp2_pi_ext {v u : Nat} {ρ : Nat → V} {A B B' : AVExpr} {f g : V}
    (hf : f ∈ˢ interp2 V ρ (.pi u v A B))
    (hg : g ∈ˢ interp2 V ρ (.pi u v A B'))
    (h : ∀ x, x ∈ˢ interp2 V ρ A →
      SetTheory.app f x = SetTheory.app g x) : f = g :=
  eq_of_mem_piR_app_eq hf hg h

/-- An empty domain does **not** collapse an abstraction: with a
nonzero codomain annotation the value is the empty graph, and the
`Type`-level facts the #100 countermodel needed (`app` computing, the
value not being `pt`) survive. -/
theorem interp2_lam_empty_dom {v : Nat} (hv : v ≠ 0) (ρ : Nat → V)
    (A b : AVExpr) (hA : interp2 V ρ A = empty) :
    interp2 V ρ (.lam v A b) = empty := by
  rw [interp2_lam, hA, lamR_pos_empty hv]

/-! ## The squash regime -/

/-- **Impredicativity.**  A product whose codomain annotation is `0` is
a truth value — whatever its domain is, and with no premise on the
fibres.  This is the whole content of `Prop`'s impredicativity in the
model, and here it is one branch of a numeral test. -/
theorem interp2_pi_zero_small {u : Nat} (ρ : Nat → V) (A B : AVExpr) :
    interp2 V ρ (.pi u 0 A B) ∈ˢ (univ 0 : V) := by
  rw [interp2_pi, univ_zero]
  exact piR_zero_mem_univZero

/-- Proof irrelevance at a `Prop`-valued product: any two inhabitants
are equal. -/
theorem interp2_pi_zero_subsingleton {u : Nat} {ρ : Nat → V} {A B : AVExpr}
    {x y : V} (hx : x ∈ˢ interp2 V ρ (.pi u 0 A B))
    (hy : y ∈ˢ interp2 V ρ (.pi u 0 A B)) : x = y :=
  piR_zero_subsingleton hx hy

/-- Proof irrelevance, in the form consumers use it: members of a
proposition — anything the interpretation places in `univ 0` — are all
equal, and all equal to the canonical proof `⟦prf⟧`. -/
theorem interp2_proof_irrel {ρ : Nat → V} {T : AVExpr} {x y : V}
    (hT : interp2 V ρ T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ interp2 V ρ T)
    (hy : y ∈ˢ interp2 V ρ T) : x = y :=
  subsingleton_of_mem_univZero (univ_zero (V := V) ▸ hT) hx hy

theorem interp2_eq_prf {ρ : Nat → V} {T : AVExpr} {x : V}
    (hT : interp2 V ρ T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ interp2 V ρ T) :
    x = interp2 V ρ .prf :=
  eq_pt_of_mem_univZero (univ_zero (V := V) ▸ hT) hx

/-- Equality reflection: an inhabited `eqE` *is* the equation.  As in
the collapse layer, the type slot is never read. -/
theorem interp2_eqE_reflect {ρ : Nat → V} {T a b : AVExpr} {x : V}
    (hx : x ∈ˢ interp2 V ρ (.eqE T a b)) : interp2 V ρ a = interp2 V ρ b :=
  mem_eqv hx

end Lech.Semantics
