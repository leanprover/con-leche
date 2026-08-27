import Setlec.TTVerify.DeclInd
import Setlec.TTVerify.Certs
import Setlec.TTVerify.ReducePin

/-!
# The bottoms' context machinery: open equations, fired

`IndBottomPlainTT` (`DESIGN.md` §16.1) consumes the kernel kit of a
checked `iota_j` theorem, whose definitional-equality facts ran at the
**install** environment on *opened* expressions — at depth `k = rP +
cnF`, over the statement telescope's free variables.  The claims
(`DefEqClaimsTT`) turn each of those runs into a `Deq` in a context of
length exactly `k` (that length is `CtxOk`'s first conjunct, so it is
not negotiable).  The fired law lives in the use site's context `Δ`.
This module is the bridge between the two: **instantiate an open `Deq`
along a typed spine**, the way `identity_of_cert`
(`Setlec/TTVerify/ReducePin.lean`) does for one binder, generalized to
a telescope.

Three pieces:

* `PiTele` — a `.pi` tower's first `k` domains *as a de Bruijn
  context* (innermost binder first, so the outermost domain is the
  list's **last** entry), with the body after `k` binders.  The shape
  `HasType.instN`'s `InstCtx` walks.
* `CtxSpine` — a spine consuming such a context from its outermost
  entry inward, each value typed at its entry with the values so far
  substituted.  `VTeleTyped` read on the context rather than on the
  tower; the two meet at `VTeleTyped.toCtxSpine`.
* `Deq.instCtx` — the payoff: an open `Deq` over `Γ ++ Δ`, instantiated
  along a `CtxSpine`, is a `Deq` over `Δ` between the `instSeq`s.

## The padding trick, because it is this module's one non-obvious move

A domain fact at *position `n`* of the telescope mentions only the
first `n` opened variables, but the checker ran it at depth `k` — so
its `Deq` arrives in a length-`k` context whose first `k - n` entries
(the *innermost* ones) are unconstrained: `CtxOk` restricts only the
entries at indices its subject's leaves reach.  Those free slots are
chosen as `.sort 0`, and instantiated with the closed inhabitant
`dummyPropT = ∀ p : Prop, p` (`CtxSpine.pad`) — so a partially-fitted
spine instantiates a full-depth `Deq` without a strengthening lemma,
which this layer does not have and does not want.  The set model never
meets this: `interpExpr` reads a *valuation*, and restricting a
valuation is free.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The tower's context -/

/-- The first `k` domains of a `.pi` tower, as a de Bruijn context —
innermost binder first, so the *outermost* domain is the last entry —
with the body after `k` binders.  Each entry is as written in the
tower, its dependencies pointing at the entries after it, which is
exactly how `HasType.bvar` reads a context. -/
inductive PiTele : Nat → VExpr → List VExpr → VExpr → Prop
  | nil {T : VExpr} : PiTele 0 T [] T
  | cons {k : Nat} {A B R : VExpr} {Γ : List VExpr} :
      PiTele k B Γ R → PiTele (k + 1) (.pi A B) (Γ ++ [A]) R

theorem PiTele.length : ∀ {k : Nat} {T : VExpr} {Γ : List VExpr}
    {R : VExpr}, PiTele k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A context's entries, instantiated after a variable *below* all of
them is substituted: the entry `i` places above the substituted slot is
instantiated at cut `j + i` (`j` counts binders below the substituted
slot that remain).  The entry adjacent to the slot — the list's last —
gets cut `j`. -/
def ctxInstAt (v : VExpr) (j : Nat) : List VExpr → List VExpr
  | [] => []
  | B :: Γ => B.inst v (j + Γ.length) :: ctxInstAt v j Γ

@[simp] theorem ctxInstAt_nil (v : VExpr) (j : Nat) :
    ctxInstAt v j [] = [] := rfl

theorem ctxInstAt_cons (v : VExpr) (j : Nat) (B : VExpr) (Γ : List VExpr) :
    ctxInstAt v j (B :: Γ) = B.inst v (j + Γ.length) :: ctxInstAt v j Γ := rfl

@[simp] theorem ctxInstAt_length (v : VExpr) (j : Nat) :
    ∀ (Γ : List VExpr), (ctxInstAt v j Γ).length = Γ.length
  | [] => rfl
  | B :: Γ => by simp [ctxInstAt_cons, ctxInstAt_length v j Γ]

/-- `ctxInstAt` over an append: the left block's cuts shift by the
right block's length. -/
theorem ctxInstAt_append (v : VExpr) (j : Nat) :
    ∀ (Γ₁ Γ₂ : List VExpr),
      ctxInstAt v j (Γ₁ ++ Γ₂) =
        ctxInstAt v (j + Γ₂.length) Γ₁ ++ ctxInstAt v j Γ₂
  | [], Γ₂ => rfl
  | B :: Γ₁, Γ₂ => by
    simp only [List.cons_append, ctxInstAt_cons, ctxInstAt_append v j Γ₁ Γ₂,
      List.length_append, List.cons.injEq]
    exact ⟨by congr 1; omega, trivial⟩

/-- The snoc form `PiTele.cons` and `CtxSpine.cons` decompose along. -/
theorem ctxInstAt_snoc (v : VExpr) (j : Nat) (Γ : List VExpr) (A : VExpr) :
    ctxInstAt v j (Γ ++ [A]) = ctxInstAt v (j + 1) Γ ++ [A.inst v j] := by
  rw [ctxInstAt_append]
  rfl

/-- Closed entries are untouched. -/
theorem ctxInstAt_closed (v : VExpr) (j : Nat) :
    ∀ {Γ : List VExpr}, (∀ B ∈ Γ, VExpr.Closed B) → ctxInstAt v j Γ = Γ := by
  intro Γ
  induction Γ with
  | nil => intro _; rfl
  | cons B Γ ih =>
    intro h
    rw [ctxInstAt_cons,
      VExpr.inst_eq_self_of_closed (h B List.mem_cons_self) _ _,
      ih fun C hC => h C (List.mem_cons_of_mem _ hC)]

/-- A substituted tower is a tower over the substituted context — the
`PiTele` transcription of `PiTower.inst`. -/
theorem PiTele.inst : ∀ {k : Nat} {T : VExpr} {Γ : List VExpr} {R : VExpr},
    PiTele k T Γ R → ∀ (v : VExpr) (j : Nat),
      PiTele k (T.inst v j) (ctxInstAt v j Γ) (R.inst v (j + k)) := by
  intro k T Γ R h
  induction h with
  | nil => intro v j; simpa using PiTele.nil
  | @cons k A B R Γ _ ih =>
    intro v j
    rw [VExpr.inst_pi, ctxInstAt_snoc]
    have h1 := ih v (j + 1)
    rw [show j + 1 + k = j + (k + 1) from by omega] at h1
    exact PiTele.cons h1

/-! ## The context spine -/

/-- A spine consuming a de Bruijn context from its **outermost** entry
(the list's last) inward: each value is typed over `Δ` at its entry,
and the remaining entries are instantiated with it.  This is
`VTeleTyped` read on the context rather than on the `.pi` tower, and
each `cons` is exactly one `HasType.instN` step. -/
inductive CtxSpine (Δ : List VExpr) : List VExpr → List VExpr → Prop
  | nil : CtxSpine Δ [] []
  | cons {Γ : List VExpr} {A w : VExpr} {ws : List VExpr} :
      HasType Δ w A → CtxSpine Δ (ctxInstAt w 0 Γ) ws →
      CtxSpine Δ (Γ ++ [A]) (w :: ws)

theorem CtxSpine.length {Δ : List VExpr} :
    ∀ {Γ : List VExpr} {ws : List VExpr}, CtxSpine Δ Γ ws →
      Γ.length = ws.length := by
  intro Γ ws h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp_all

/-- A fitted spine consumes the tower's context.  The connection
between the two readings of the same walk: `VTeleTyped` peels the
tower's outermost `.pi`, `CtxSpine` peels the context's last entry, and
`PiTele.inst` keeps the two in step. -/
theorem VTeleTyped.toCtxSpine {Δ : List VExpr} :
    ∀ {T : VExpr} {ws : List VExpr} {rest : VExpr},
      VTeleTyped Δ T ws rest →
      ∀ {Γ : List VExpr} {R : VExpr}, PiTele ws.length T Γ R →
      CtxSpine Δ Γ ws := by
  intro T ws rest h
  induction h with
  | nil =>
    intro Γ R hp
    cases hp
    exact .nil
  | @cons A B x xs rest hx _ ih =>
    intro Γ R hp
    cases hp with
    | @cons _ _ _ _ Γ' hp' =>
      exact CtxSpine.cons hx (ih (hp'.inst x 0))

/-! ## Instantiating an open equation -/

/-- One substitution step on a derivable equation: `HasType.instN`
through the `Deq` package (`.prf` and `.eqE` both commute with
`inst`). -/
theorem Deq.instN {Γ₀ : List VExpr} {v A₀ : VExpr} (hv : HasType Γ₀ v A₀)
    {Γ : List VExpr} {a b : VExpr} (h : Deq Γ a b) {k : Nat}
    {Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') :
    Deq Γ' (a.inst v k) (b.inst v k) := by
  obtain ⟨T, hT⟩ := h
  have h1 := hv.instN hT H
  rw [VExpr.inst_prf, VExpr.inst_eqE] at h1
  exact ⟨T.inst v k, h1⟩

/-- The `InstCtx` chain a `CtxSpine.cons` step needs: substituting for
the entry below a prefix `Γp` instantiates exactly that prefix. -/
theorem InstCtx.ofPrefix (Γ₀ : List VExpr) (v A : VExpr) :
    ∀ (Γp : List VExpr),
      InstCtx Γ₀ v A Γp.length (Γp ++ A :: Γ₀) (ctxInstAt v 0 Γp ++ Γ₀) := by
  intro Γp
  induction Γp with
  | nil => exact .zero
  | cons B Γ ih =>
    have h := InstCtx.succ (Γ₀ := Γ₀) (v := v) (A₀ := A) B ih
    simpa [ctxInstAt_cons] using h

/-- **Instantiating an open equation along a context spine.**  The
n-ary `identity_of_cert`: a `Deq` over `Γ ++ Δ` becomes a `Deq` over
`Δ` between the spine-instantiated sides, outermost argument first at
descending cuts — which is `VExpr.instSeq`'s recursion, on the nose. -/
theorem Deq.instCtx {Δ : List VExpr} :
    ∀ {Γ : List VExpr} {ws : List VExpr}, CtxSpine Δ Γ ws →
      ∀ {a b : VExpr}, Deq (Γ ++ Δ) a b →
      Deq Δ (VExpr.instSeq ws (ws.length - 1) a)
        (VExpr.instSeq ws (ws.length - 1) b) := by
  intro Γ ws h
  induction h with
  | nil =>
    intro a b h
    simpa using h
  | @cons Γ A w ws hw hsp ih =>
    intro a b h
    rw [List.append_assoc] at h
    have hlen : Γ.length = ws.length := by
      have h1 := hsp.length
      simpa using h1
    have h1 := Deq.instN hw h (InstCtx.ofPrefix Δ w A Γ)
    rw [hlen] at h1
    have h2 := ih h1
    simpa [VExpr.instSeq_cons, List.length_cons, Nat.add_sub_cancel] using h2

/-! ## The padding

A domain fact at position `n` arrives in a length-`k` context whose
innermost `k - n` entries nothing constrains.  They are chosen as
`.sort 0` and consumed by the closed inhabitant below, so a
partially-fitted spine can instantiate a full-depth equation. -/

/-- A closed inhabitant of... nothing — a closed **term of type
`Prop`**: `∀ p : Prop, p`.  (`False`, in fact, which is fine: only its
*typing* is consumed.) -/
def dummyPropT : VExpr := .pi (.sort 0) (.bvar 0)

theorem dummyPropT_typed (Γ : List VExpr) :
    HasType Γ dummyPropT (.sort 0) := by
  have h2 : HasType ((VExpr.sort 0) :: Γ) (.bvar 0) (.sort 0) := by
    have h1 := HasType.bvar (Γ := (VExpr.sort 0) :: Γ) (i := 0)
      (A := .sort 0) rfl
    exact h1
  have h : HasType Γ (.pi (.sort 0) (.bvar 0)) (.sort (imax 1 0)) :=
    HasType.pi HasType.sort h2
  rw [dummyPropT]
  simpa using h

/-- The all-padding spine: `.sort 0` entries consumed by
`dummyPropT`. -/
theorem CtxSpine.dummy {Δ : List VExpr} :
    ∀ m : Nat, CtxSpine Δ (List.replicate m (.sort 0))
      (List.replicate m dummyPropT) := by
  intro m
  induction m with
  | zero => exact .nil
  | succ m ih =>
    rw [List.replicate_succ' (n := m), List.replicate_succ (n := m)]
    refine CtxSpine.cons (dummyPropT_typed Δ) ?_
    rw [ctxInstAt_closed _ _ (fun B hB => by
      rw [List.eq_of_mem_replicate hB]; trivial)]
    exact ih

/-- **Padding a spine**: the entries above a consumed context prefix
are unconstrained slots, fillable as `.sort 0`.  This is what lets a
fact about the telescope's first `n` variables — checked at the full
depth `k` — be instantiated with only `n` real arguments in hand. -/
theorem CtxSpine.pad {Δ : List VExpr} :
    ∀ {Γ : List VExpr} {ws : List VExpr}, CtxSpine Δ Γ ws →
      ∀ m : Nat, CtxSpine Δ (List.replicate m (.sort 0) ++ Γ)
        (ws ++ List.replicate m dummyPropT) := by
  intro Γ ws h
  induction h with
  | nil =>
    intro m
    simpa using CtxSpine.dummy m
  | @cons Γ A w ws hw hsp ih =>
    intro m
    rw [show List.replicate m (VExpr.sort 0) ++ (Γ ++ [A]) =
      (List.replicate m (.sort 0) ++ Γ) ++ [A] from by
        rw [List.append_assoc], List.cons_append]
    refine CtxSpine.cons hw ?_
    rw [ctxInstAt_append,
      ctxInstAt_closed _ _ (fun B hB => by
        rw [List.eq_of_mem_replicate hB]; trivial)]
    exact ih m
