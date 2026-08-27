import Setlec.TTVerify.DeclInd
import Setlec.TTVerify.Certs
import Setlec.TTVerify.ReducePin
import Setlec.Verify.BridgeWfImp

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

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

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

/-! ## Opening the statement's telescope

The kit's expressions all live in one frame: the checked theorem's
telescope opened at free variables (`openPisAtFvars` at depth `0`).
This section is the walk that turns that frame into the claims' inputs:
the denoted tower (`PiTele`), each opener's annotation denoted at its
own depth, and the `CtxOk` any kit expression needs — its leaves are
all openers (`openPisAtFvars_leaves`), each of which the walk has
covered. -/

/-- Every free-variable leaf reachable from an opened telescope — from
the opened body or from any opener's own annotation — is either a leaf
of the unopened expression or exactly one of the openers.  With the
subject closed, the openers are a *leaf-closed* set: annotations
mention only earlier openers, which are openers again. -/
theorem openPisAtFvars_leaves :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
        l ∈ e.fvarLeaves ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
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
    | .forallE nm dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d nm dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        -- a leaf of the head opener resolves directly
        have head : l ∈ (Expr.fvar d nm dom).fvarLeaves →
            l ∈ (Expr.forallE nm dom bodyE mb).fvarLeaves ∨
              Expr.fvar l.1 l.2.1 l.2.2 ∈
                Expr.fvar d nm dom :: p.1 := by
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

/-- **The opening walk, denoted.**  Opening a telescope whose denote
succeeds yields the `.pi` tower's context, the denoted opened body, and
each opener's annotation denoted *at its own depth* to its tower
entry.  (Consumers lift with `denote_lift`; the entry `Γ.getD (k-1-i)`
is the `i`-th binder's domain as written, which is where `HasType.bvar`
wants it.) -/
theorem openPisAtFvars_denoteTele {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} :
    ∀ (k : Nat) {e : Expr} {j : Nat} {fvs : List Expr} {body : Expr}
      {T : VExpr},
      openPisAtFvars k e j = some (fvs, body) →
      denote cval env ψ j e = some T →
      ∃ (Γ : List VExpr) (R : VExpr),
        PiTele k T Γ R ∧
        denote cval env ψ (j + k) body = some R ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          denote cval env ψ (j + i) (Expr.fvarTypeD x) =
            some (Γ.getD (k - 1 - i) default) := by
  intro k
  induction k with
  | zero =>
    intro e j fvs body T h hT
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], T, .nil, hT, fun i x hx => nomatch hx⟩
  | succ k ih =>
    intro e j fvs body T h hT
    match e, h with
    | .forallE nm dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar j nm dom))
          (j + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [denote_forallE] at hT
        cases hA : denote cval env ψ j dom with
        | none => rw [hA] at hT; exact nomatch hT
        | some A => ?_
        rw [hA] at hT
        cases hB : denote cval env ψ (j + 1)
            (bodyE.instantiate1 (.fvar j nm dom)) with
        | none => rw [hB] at hT; exact nomatch hT
        | some B => ?_
        rw [hB] at hT
        obtain rfl : T = .pi A B := (Option.some.inj hT).symm
        obtain ⟨Γ', R, htele, hbody, hdoms⟩ := ih hop hB
        have hΓlen : Γ'.length = k := htele.length
        refine ⟨Γ' ++ [A], R, .cons htele, ?_, ?_⟩
        · rw [show j + (k + 1) = j + 1 + k from by omega]
          exact hbody
        · intro i x hx
          cases i with
          | zero =>
            obtain rfl : Expr.fvar j nm dom = x := by
              simpa using hx
            show denote cval env ψ (j + 0) dom = _
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
              simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
              rw [List.getElem?_append_right (by omega), hΓlen,
                Nat.sub_self]
              rfl]
            exact hA
          | succ i =>
            rw [List.getElem?_cons_succ] at hx
            have h1 := hdoms i x hx
            have hik : i < k := by
              rcases Nat.lt_or_ge i k with h' | h'
              · exact h'
              · exfalso
                rw [List.getElem?_eq_none (by
                  have := openPisAtFvars_stripPis k hop
                  obtain ⟨-, -, -, hlen, -, -⟩ := this
                  omega)] at hx
                exact nomatch hx
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default =
                Γ'.getD (k - 1 - i) default from by
              simp only [List.getD]
              rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
                List.getElem?_append_left (by omega)]]
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h1

/-- **`CtxOk` for a kit expression**, at any context whose entries at
the touched indices are the tower's domains.  The expression's leaves
are all openers below `n` (openers by `openPisAtFvars_leaves`, below
`n` by its own `WScoped`), so entries at indices `< k - n` — the
padding — are never consulted. -/
theorem ctxOk_of_openers {cval : TConstVal} {env : Env} {ψ : Name → Nat}
    (hcl : ∀ n ψ', VExpr.Closed (cval n ψ'))
    {k : Nat} {fvs : List Expr} {As : Nat → VExpr} {Δ' : List VExpr}
    (hΔlen : Δ'.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ i (Expr.fvarTypeD x) = some (As i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hwsE : Expr.WScoped n e)
    (hent : ∀ i, i < n → Δ'[k - 1 - i]? = some (As i)) :
    CtxOk cval env ψ k Δ' e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨nm, ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2, h3⟩ : l.1 = pos ∧ l.2.1 = nm ∧ l.2.2 = ty := by
    injection hx with a b c
    exact ⟨a, b, c⟩
  subst h1 h2 h3
  -- the leaf's index is below `n`
  have hlt : l.1 < n := Expr.fvarLeaves_lt_of_wscoped hwsE l hl
  -- the annotation is scoped below its own variable
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2.2 := by
    simpa [Expr.WScoped] using hw
  have hfb : Expr.fvarsBelow l.1 l.2.2 := hwty.2.fvarsBelow
  refine ⟨by omega, hfb, (As l.1).liftN (k - l.1), ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hpos
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2.1 l.2.2) = l.2.2 from rfl]
      at hd1
    have hd2 := denote_lift (cval := cval) (env := env) (φ := ψ) hcl
      (p := l.1) (e := l.2.2) hfb k (by omega)
    rw [hd2, hd1]
    rfl
  · have h4 := HasType.bvar (Γ := Δ') (i := k - 1 - l.1)
      (hent l.1 hlt)
    rw [show k - 1 - l.1 + 1 = k - l.1 from by omega] at h4
    exact h4

/-- **A lifted term under a padded spine.**  A depth-`k` denote of an
expression over the first `n` openers is the depth-`n` denote lifted by
the padding's width; instantiating the padded spine on the lift is
instantiating the real prefix on the original — every padding cut
passes under the lift, one unit each.  Unconditional in `A`: bvars
beyond the real prefix shift identically on both sides. -/
theorem instSeq_append_absorb :
    ∀ (ws pads : List VExpr) (A : VExpr),
      VExpr.instSeq (ws ++ pads) (ws.length + pads.length - 1)
        (VExpr.liftN pads.length A 0) =
      VExpr.instSeq ws (ws.length - 1) A := by
  intro ws
  induction ws with
  | nil =>
    intro pads A
    rcases Nat.eq_zero_or_pos pads.length with h0 | h0
    · rw [List.eq_nil_of_length_eq_zero h0]
      simp [VExpr.liftN_zero]
    · rw [List.nil_append, VExpr.instSeq_nil]
      have h := VExpr.instSeq_liftN pads (pads.length - 1) A
        (by omega)
      rw [show pads.length - 1 + 1 = pads.length from by omega] at h
      simpa [Nat.sub_self, VExpr.liftN_zero] using h
  | cons w ws ih =>
    intro pads A
    have e1 : (w :: ws).length + pads.length - 1 =
        ws.length + pads.length := by
      simp only [List.length_cons]
      omega
    have e2 : (w :: ws).length - 1 = ws.length := by
      simp only [List.length_cons, Nat.add_sub_cancel]
    rw [e1, e2, List.cons_append, VExpr.instSeq_cons, VExpr.instSeq_cons]
    rw [VExpr.inst_liftN_comm A (by omega) w,
      show ws.length + pads.length - pads.length = ws.length from by omega]
    exact ih pads (A.inst w ws.length)

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

/-! ## Reading a context entry, instantiated -/

/-- `ctxInstAt`, per entry: the entry at index `i` is instantiated at
its own residual depth. -/
theorem ctxInstAt_getD (v : VExpr) (j : Nat) :
    ∀ (Γ : List VExpr) (i : Nat), i < Γ.length →
      (ctxInstAt v j Γ).getD i default =
        (Γ.getD i default).inst v (j + Γ.length - 1 - i)
  | [], i, h => absurd h (by simp)
  | B :: Γ, 0, _ => by
    simp only [ctxInstAt_cons, List.getD_cons_zero, List.length_cons,
      Nat.sub_zero]
    congr 1
  | B :: Γ, i + 1, h => by
    simp only [ctxInstAt_cons, List.getD_cons_succ, List.length_cons]
    rw [ctxInstAt_getD v j Γ i (by simpa using h)]
    congr 1
    omega

/-- `HasType`, instantiated along a context spine — `Deq.instCtx`'s
sibling, for the sort premise and the sides' typings. -/
theorem HasType.instCtx {Δ : List VExpr} :
    ∀ {Γ : List VExpr} {ws : List VExpr}, CtxSpine Δ Γ ws →
      ∀ {e T : VExpr}, HasType (Γ ++ Δ) e T →
      HasType Δ (VExpr.instSeq ws (ws.length - 1) e)
        (VExpr.instSeq ws (ws.length - 1) T) := by
  intro Γ ws h
  induction h with
  | nil =>
    intro e T h
    simpa using h
  | @cons Γ A w ws hw hsp ih =>
    intro e T h
    rw [List.append_assoc] at h
    have hlen : Γ.length = ws.length := by
      have h1 := hsp.length
      simpa using h1
    have h1 := hw.instN h (InstCtx.ofPrefix Δ w A Γ)
    rw [hlen] at h1
    have h2 := ih h1
    simpa [VExpr.instSeq_cons, List.length_cons, Nat.add_sub_cancel] using h2

/-! ## The tower, peeled at a spine

`VTeleTyped.ofPiTele` builds a fitting from per-position typings at the
progressively instantiated context entries — the *zipper* the bottoms
use to fit the fired spine into the checked statement's telescope.
`VTeleTyped.steps` is its inverse (reading the per-position typings off
a fitting the fire site already holds), and `rest_of_piTele` identifies
the fitting's residual with the tower body's `instSeq`. -/

/-- A fitting's residual is the tower body, spine-instantiated. -/
theorem VTeleTyped.rest_of_piTele {Δ : List VExpr} :
    ∀ {T : VExpr} {ws : List VExpr} {rest : VExpr},
      VTeleTyped Δ T ws rest →
      ∀ {Γ : List VExpr} {R : VExpr}, PiTele ws.length T Γ R →
      rest = VExpr.instSeq ws (ws.length - 1) R := by
  intro T ws rest h
  induction h with
  | nil =>
    intro Γ R hp
    cases hp
    rfl
  | @cons A B x xs rest hx _ ih =>
    intro Γ R hp
    cases hp with
    | @cons _ _ _ _ Γ' hp' =>
      have h1 := ih (hp'.inst x 0)
      rw [Nat.zero_add] at h1
      simpa [VExpr.instSeq_cons, List.length_cons, Nat.add_sub_cancel]
        using h1

/-- Per-position typings, read off a fitting: the `n`-th spine entry is
typed at the `n`-th context entry with the prefix substituted. -/
theorem VTeleTyped.steps {Δ : List VExpr} :
    ∀ {T : VExpr} {ws : List VExpr} {rest : VExpr},
      VTeleTyped Δ T ws rest →
      ∀ {Γ : List VExpr} {R : VExpr}, PiTele ws.length T Γ R →
      ∀ n, n < ws.length →
        HasType Δ (ws.getD n default)
          (VExpr.instSeq (ws.take n) (n - 1)
            (Γ.getD (ws.length - 1 - n) default)) := by
  intro T ws rest h
  induction h with
  | nil =>
    intro Γ R hp n hn
    exact absurd hn (by simp)
  | @cons A B x xs rest hx _ ih =>
    intro Γ R hp n hn
    cases hp with
    | @cons _ _ _ _ Γ' hp' =>
      have hΓlen : Γ'.length = xs.length := hp'.length
      cases n with
      | zero =>
        simp only [List.getD_cons_zero, List.take_zero, VExpr.instSeq_nil]
        rw [show (x :: xs).length - 1 - 0 = xs.length from by simp,
          show (Γ' ++ [A]).getD xs.length default = A from by
            simp only [List.getD]
            rw [List.getElem?_append_right (by omega), hΓlen,
              Nat.sub_self]
            rfl]
        exact hx
      | succ n =>
        have hn' : n < xs.length := by simpa using hn
        have h1 := ih (hp'.inst x 0) n hn'
        rw [ctxInstAt_getD x 0 Γ' (xs.length - 1 - n) (by omega),
          show 0 + Γ'.length - 1 - (xs.length - 1 - n) = n from by omega]
          at h1
        have h2 : VExpr.instSeq (xs.take n) (n - 1)
            ((Γ'.getD (xs.length - 1 - n) default).inst x n) =
            VExpr.instSeq ((x :: xs).take (n + 1)) (n + 1 - 1)
              (Γ'.getD (xs.length - 1 - n) default) := by
          rw [List.take_succ_cons, VExpr.instSeq_cons, Nat.add_sub_cancel]
        rw [h2] at h1
        rw [show (x :: xs).length - 1 - (n + 1) = xs.length - 1 - n from
            by simp only [List.length_cons]; omega,
          show (Γ' ++ [A]).getD (xs.length - 1 - n) default =
            Γ'.getD (xs.length - 1 - n) default from by
            simp only [List.getD]
            rw [List.getElem?_append_left (by omega)]]
        simpa using h1

/-- **The zipper.**  A spine typed per position at the progressively
instantiated context entries fits the tower, and lands at the
instantiated body.  This is how a fired spine is fitted into the
checked statement's telescope, whose domains only the per-position
facts reach — and each position's obligation receives the *prefix
fit already built*, which is what lets a step instantiate an open
install fact along the values before it (the sequential structure the
padding trick needs). -/
theorem VTeleTyped.ofPiTele {Δ : List VExpr} :
    ∀ {zs : List VExpr} {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele zs.length T Γ R →
      (∀ n, n < zs.length →
        (∃ mid, VTeleTyped Δ T (zs.take n) mid) →
        HasType Δ (zs.getD n default)
          (VExpr.instSeq (zs.take n) (n - 1)
            (Γ.getD (zs.length - 1 - n) default))) →
      VTeleTyped Δ T zs (VExpr.instSeq zs (zs.length - 1) R) := by
  intro zs
  induction zs with
  | nil =>
    intro T Γ R hp _
    cases hp
    exact .nil
  | cons z zs ih =>
    intro T Γ R hp hstep
    cases hp with
    | @cons _ A B _ Γ' hp' =>
      have hΓlen : Γ'.length = zs.length := hp'.length
      have hz : HasType Δ z A := by
        have h0 := hstep 0 (by simp) ⟨_, VTeleTyped.nil⟩
        simp only [List.take_zero, VExpr.instSeq_nil, List.getD_cons_zero,
          List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at h0
        rwa [show (Γ' ++ [A]).getD zs.length default = A from by
          simp only [List.getD]
          rw [List.getElem?_append_right (by omega), hΓlen, Nat.sub_self]
          rfl] at h0
      have hrec := ih (hp'.inst z 0) ?_
      · refine VTeleTyped.cons hz ?_
        rw [Nat.zero_add] at hrec
        have h2 : VExpr.instSeq (z :: zs) ((z :: zs).length - 1) R =
            VExpr.instSeq zs (zs.length - 1) (R.inst z zs.length) := by
          rw [VExpr.instSeq_cons]
          simp
        rw [h2]
        exact hrec
      · intro n hn hpref
        obtain ⟨mid, hmid⟩ := hpref
        have h1 := hstep (n + 1) (by simpa using hn)
          ⟨mid, VTeleTyped.cons hz hmid⟩
        rw [show (z :: zs).getD (n + 1) default = zs.getD n default from rfl,
          show (z :: zs).length - 1 - (n + 1) = zs.length - 1 - n from by
            simp only [List.length_cons]; omega,
          show (Γ' ++ [A]).getD (zs.length - 1 - n) default =
            Γ'.getD (zs.length - 1 - n) default from by
            simp only [List.getD]
            rw [List.getElem?_append_left (by omega)],
          List.take_succ_cons, show n + 1 - 1 = n from rfl,
          VExpr.instSeq_cons] at h1
        rw [ctxInstAt_getD z 0 Γ' (zs.length - 1 - n) (by omega),
          show 0 + Γ'.length - 1 - (zs.length - 1 - n) = n from by omega]
        exact h1

/-- The tower, truncated: the first `n` binders with the inner tower as
their body. -/
theorem PiTele.prefix :
    ∀ {k : Nat} {T : VExpr} {Γ : List VExpr} {R : VExpr},
      PiTele k T Γ R → ∀ n, n ≤ k →
      ∃ mid, PiTele n T (Γ.drop (k - n)) mid ∧
        PiTele (k - n) mid (Γ.take (k - n)) R := by
  intro k T Γ R h
  induction h with
  | nil =>
    intro n hn
    obtain rfl : n = 0 := by omega
    exact ⟨_, .nil, .nil⟩
  | @cons k A B R Γ hp ih =>
    intro n hn
    cases n with
    | zero =>
      refine ⟨.pi A B, ?_, ?_⟩
      · rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp [hp.length])]
        exact .nil
      · rw [Nat.sub_zero, List.take_of_length_le (by simp [hp.length])]
        exact .cons hp
    | succ n =>
      obtain ⟨mid, h1, h2⟩ := ih n (by omega)
      have he : k + 1 - (n + 1) = k - n := by omega
      refine ⟨mid, ?_, ?_⟩
      · rw [he, List.drop_append_of_le_length (by rw [hp.length]; omega)]
        exact .cons h1
      · rw [he, List.take_append_of_le_length (by rw [hp.length]; omega)]
        exact h2

/-- A fitting, truncated at any prefix. -/
theorem VTeleTyped.take {Δ : List VExpr} :
    ∀ {T : VExpr} {ws : List VExpr} {rest : VExpr},
      VTeleTyped Δ T ws rest → ∀ n,
      ∃ mid, VTeleTyped Δ T (ws.take n) mid ∧
        VTeleTyped Δ mid (ws.drop n) rest := by
  intro T ws rest h
  induction h with
  | nil => intro n; exact ⟨_, by simpa using VTeleTyped.nil, by simpa using VTeleTyped.nil⟩
  | @cons A B x xs rest hx hfit ih =>
    intro n
    cases n with
    | zero => exact ⟨.pi A B, .nil, .cons hx hfit⟩
    | succ n =>
      obtain ⟨mid, h1, h2⟩ := ih n
      exact ⟨mid, .cons hx h1, h2⟩

/-! ## Substitution congruence, through the λ-tower

Two spines consuming the same context yield `Deq`-equal
instantiations of any subject — the fired form of "the iota equation
only speaks about the canonical tuple".  The typing-free half is
`Deq.mkAppN` (application congruence carries no premises); the typed
half is `HasType.beta` once per binder, packaged as a `BetaSpine` over
the context's λ-tower.  Both spines must be *fitted* (`CtxSpine`) —
that is `beta`'s own premise, not a convenience. -/

/-- The context's λ-tower over a subject: the outermost binder is the
context's last entry, matching `CtxSpine`'s peel. -/
def lamCtx (Γ : List VExpr) (C : VExpr) : VExpr :=
  Γ.foldl (fun acc A => .lam A acc) C

theorem lamCtx_cons (B : VExpr) (Γ : List VExpr) (C : VExpr) :
    lamCtx (B :: Γ) C = lamCtx Γ (.lam B C) := rfl

theorem lamCtx_snoc (Γ : List VExpr) (A C : VExpr) :
    lamCtx (Γ ++ [A]) C = .lam A (lamCtx Γ C) := by
  unfold lamCtx
  rw [List.foldl_append]
  rfl

theorem lamCtx_inst : ∀ (Γ : List VExpr) (C v : VExpr) (j : Nat),
    (lamCtx Γ C).inst v j =
      lamCtx (ctxInstAt v j Γ) (C.inst v (j + Γ.length))
  | [], C, v, j => by simp [lamCtx, ctxInstAt]
  | B :: Γ, C, v, j => by
    rw [lamCtx_cons, lamCtx_inst Γ (.lam B C) v j, ctxInstAt_cons,
      lamCtx_cons, VExpr.inst_lam]
    congr 2

/-- A fitted spine β-reduces the context's λ-tower to the subject's
`instSeq` — the `BetaSpine` whose typings the `CtxSpine` carries. -/
theorem CtxSpine.betaSpine {Δ : List VExpr} :
    ∀ {Γ : List VExpr} {ws : List VExpr}, CtxSpine Δ Γ ws →
      ∀ (C : VExpr),
        BetaSpine Δ (lamCtx Γ C) ws
          (VExpr.instSeq ws (ws.length - 1) C) := by
  intro Γ ws h
  induction h with
  | nil => intro C; exact .nil
  | @cons Γ A w ws hw hsp ih =>
    intro C
    have hlen : Γ.length = ws.length := by
      have h1 := hsp.length
      simpa using h1
    rw [lamCtx_snoc]
    refine BetaSpine.cons hw ?_
    show BetaSpine Δ ((lamCtx Γ C).inst w) ws _
    rw [show (lamCtx Γ C).inst w = (lamCtx Γ C).inst w 0 from rfl,
      lamCtx_inst Γ C w 0, Nat.zero_add, hlen]
    have h2 := ih (C.inst w ws.length)
    rw [show VExpr.instSeq (w :: ws) ((w :: ws).length - 1) C =
      VExpr.instSeq ws (ws.length - 1) (C.inst w ws.length) from by
        rw [VExpr.instSeq_cons]
        simp]
    exact h2

/-- **Substitution congruence.**  Two fitted spines, pointwise `Deq`,
instantiate any subject to `Deq`-equal results. -/
theorem CtxSpine.instSeq_congr {Δ : List VExpr} {Γ ws ws' : List VExpr}
    (h : CtxSpine Δ Γ ws) (h' : CtxSpine Δ Γ ws')
    (hpt : ∀ i : Fin ws.length, Deq Δ ws[i] (ws'.getD i default))
    (C : VExpr) :
    Deq Δ (VExpr.instSeq ws (ws.length - 1) C)
      (VExpr.instSeq ws' (ws'.length - 1) C) := by
  have hlen : ws.length = ws'.length := by
    rw [← h.length, ← h'.length]
  refine Deq.trans (Deq.symm (Deq.ofBetaSpine (h.betaSpine C)))
    (Deq.trans ?_ (Deq.ofBetaSpine (h'.betaSpine C)))
  exact Deq.mkAppN Deq.refl hlen hpt

/-! ## The two openers' instantiations agree

The kit's `instPisAt` runs are at the statement's opened variables;
the tower walk (`openPisAtFvars_denoteTele`) is at another opening's.
`denote` reads neither an opener's name nor its annotation, so the two
runs' outputs are `RenEqT`-related whenever the subjects are — which
also absorbs the public↔model renaming in the same pass. -/

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
    | .forallE nm dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d nm dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show (Expr.instPisAt p.1 (bodyE.instantiate1
          (Expr.fvar d nm dom))).map _ = _
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
    | .forallE n₁ d₁ b₁ m₁, h => ?_
    match ty', h' with
    | .forallE n₂ d₂ b₂ m₂, h' => ?_
    have hty' : (m₁ = m₂ ∧ Expr.ErasedEq (d₁.renameConsts f) d₂ ∧
        Expr.ErasedEq (b₁.renameConsts f) b₂) := by
      have h0 : Expr.ErasedEq
          (Expr.forallE n₁ (d₁.renameConsts f) (b₁.renameConsts f) m₁)
          (.forallE n₂ d₂ b₂ m₂) := hty
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
    | .forallE n₁ d₁ b₁ m₁, h => ?_
    simp only [Expr.instPisAt] at h
    cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
    | none => rw [h1] at h; exact nomatch h
    | some p1 => ?_
    rw [h1] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have step : l ∈ (b₁.instantiate1 a).fvarLeaves ∨
        (l ∈ (Expr.forallE n₁ d₁ b₁ m₁).fvarLeaves ∨
          ∃ x ∈ a :: as, l ∈ x.fvarLeaves) → _ := fun h => h
    have push : l ∈ (b₁.instantiate1 a).fvarLeaves →
        l ∈ (Expr.forallE n₁ d₁ b₁ m₁).fvarLeaves ∨
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

/-! ## The slot-sort premise (supplied since task #146)

`DESIGN.md` §16.1 named it in advance and task #146 landed the
supplier: `checkIotaSidesTy` now additionally infers the equation
type slot's type and `isDefEq`s it against `.sort ℓA` at the
statement's own equation level, and this definition's ∃-shape arrives
verbatim as the last conjunct of `PlainChecked`, `NestedChecked` and
`checkProjIota_inv`.  The bottoms keep it as one named hypothesis
(`hslot`); the assembly discharges it by `exact` from the
inversions. -/

/-- The iota statement's equation type slot inhabits the sort its
`Eq.{ℓA}` names, checked at the opened statement frame. -/
def IotaSlotSorted (F : Nat) (env₀ : Env) (k : Nat) (αS : Expr)
    (ℓA : Level) : Prop :=
  ∃ tα, inferTypeCore mode env₀ F k αS = .ok tα ∧
    isDefEqCore mode env₀ F k tα (Expr.sort ℓA) = .ok true

/-! ## More opener bookkeeping -/

/-- A telescope that strips opens — the checker's opener succeeds
whenever `stripPis` does, because opening substitutes variables and
variables preserve the `∀`-structure (`stripPis_instantiate1_isSome`,
forward direction). -/
theorem openPisAtFvars_isSome_of_stripPis :
    ∀ (k : Nat) {e : Expr}, (e.stripPis k).isSome = true →
      ∀ (d : Nat), (openPisAtFvars k e d).isSome = true := by
  intro k
  induction k with
  | zero => intro e _ d; rfl
  | succ k ih =>
    intro e hs d
    match e, hs with
    | .forallE nm dom body mb, hs =>
      have hs' : (body.stripPis k).isSome = true := by
        simp only [Expr.stripPis, Option.isSome_map] at hs
        exact hs
      have h1 : ((body.instantiate1
          (.fvar d nm dom)).stripPis k).isSome = true :=
        Expr.stripPis_instantiate1_isSome k 0 hs'
      have h2 := ih h1 (d + 1)
      simp only [openPisAtFvars]
      revert h2
      cases openPisAtFvars k (body.instantiate1 (.fvar d nm dom))
          (d + 1) with
      | none => intro h; exact nomatch h
      | some p => intro _; rfl

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
    | .forallE nm dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d nm dom))
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

/-- `instPisAt`, truncated at a spine prefix: the first `n` domains and
the telescope that remains. -/
theorem instPisAt_take :
    ∀ (sp : List Expr) (n : Nat) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∃ mid, Expr.instPisAt (sp.take n) ty = some (ds.take n, mid) ∧
        Expr.instPisAt (sp.drop n) mid = some (ds.drop n, rs) := by
  intro sp
  induction sp with
  | nil =>
    intro n ty ds rs h
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ty, by simp [Expr.instPisAt], by simp [Expr.instPisAt]⟩
  | cons a sp ih =>
    intro n ty ds rs h
    match ty, h with
    | .forallE nm dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p =>
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases n with
        | zero =>
          refine ⟨.forallE nm dom body mb, by simp [Expr.instPisAt], ?_⟩
          simp only [List.drop_zero, Expr.instPisAt, h1]
          rfl
        | succ n =>
          obtain ⟨mid, h2, h3⟩ := ih n h1
          refine ⟨mid, ?_, by simpa using h3⟩
          simp only [List.take_succ_cons, Expr.instPisAt, h2]
          rfl

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
    | .forallE nm dom body mb, h =>
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

/-! ## The cross-frame instantiation

The kit's `instPisAt` runs open the constructor's telescope at
*scattered* statement-frame variables (parameters at `0..cnP-1`, fields
at `rP..`), while the fire site walks the same telescope's *denoted
tower* at its own values.  The two meet here: instantiating the run's
residual (denoted at the frame) along the frame's value spine is
walking the denoted tower at the values the openers map to.

The whole content is one commutation (`instSeq_inst0`): substitution at
the innermost binder passes under a value spine, transforming exactly
as its `bvar` argument does — which is how a scattered opener's `bvar`
becomes the right spine value. -/

/-- Instantiation at cut `0` commutes with a value spine. -/
theorem VExpr.instSeq_inst0 :
    ∀ (as : List VExpr) (t : Nat) (X b : VExpr), as.length ≤ t + 1 →
      VExpr.instSeq as t (X.inst b 0) =
        (VExpr.instSeq as (t + 1) X).inst (VExpr.instSeq as t b) 0 := by
  intro as
  induction as with
  | nil => intro t X b _; rfl
  | cons w as ih =>
    intro t X b hlen
    simp only [List.length_cons] at hlen
    rw [VExpr.instSeq_cons (e := X.inst b 0),
      VExpr.inst_inst_comm X (Nat.zero_le t) w b, Nat.sub_zero]
    cases as with
    | nil => simp only [VExpr.instSeq_nil, VExpr.instSeq_cons]
    | cons y ys =>
      have hlen' : (y :: ys).length ≤ t - 1 + 1 := by
        simp only [List.length_cons] at hlen ⊢
        omega
      have ht : 1 ≤ t := by
        simp only [List.length_cons] at hlen
        omega
      have h2 := ih (t - 1) (X.inst w (t + 1)) (b.inst w t) hlen'
      rw [show t - 1 + 1 = t from by omega] at h2
      rw [h2, VExpr.instSeq_cons (e := X), VExpr.instSeq_cons (e := b),
        show t + 1 - 1 = t from by omega]

/-- `instSeq` moves under an outer lift at cut `0`: the cut shifts by
the lift (task #119, the nested arc's chain algebra). -/
theorem VExpr.instSeq_liftN0 :
    ∀ (vs : List VExpr) (t m : Nat) (Y : VExpr), vs.length ≤ t + 1 →
      VExpr.instSeq vs (t + m) (Y.liftN m)
        = (VExpr.instSeq vs t Y).liftN m
  | [], _, _, _, _ => rfl
  | a :: vs, t, m, Y, h => by
    show VExpr.instSeq vs (t + m - 1) ((VExpr.liftN m Y).inst a (t + m))
      = _
    rw [VExpr.inst_liftN_comm Y (by omega) a, Nat.add_sub_cancel]
    cases t with
    | zero =>
      obtain rfl : vs = [] := by
        simp only [List.length_cons] at h
        exact List.eq_nil_of_length_eq_zero (by omega)
      rfl
    | succ t' =>
      rw [show t' + 1 + m - 1 = t' + m from by omega]
      exact VExpr.instSeq_liftN0 vs t' m (Y.inst a (t' + 1))
        (by simpa using Nat.le_of_succ_le_succ (by simpa using h))

/-- A subject with only low bound variables passes through `instSeq`
untouched: every cut is above its range. -/
theorem VExpr.instSeq_eq_self_of_bvarsBelow :
    ∀ (vs : List VExpr) (t : Nat) {X : VExpr} {m : Nat},
      VExpr.bvarsBelow m X → m + vs.length ≤ t + 1 →
      VExpr.instSeq vs t X = X
  | [], _, _, _, _, _ => rfl
  | a :: vs, t, X, m, hb, h => by
    show VExpr.instSeq vs (t - 1) (X.inst a t) = _
    rw [VExpr.inst_eq_self (VExpr.bvarsBelow.mono (by
      simp only [List.length_cons] at h
      omega) hb)]
    cases t with
    | zero =>
      obtain rfl : vs = [] := by
        simp only [List.length_cons] at h
        exact List.eq_nil_of_length_eq_zero (by omega)
      rfl
    | succ t' =>
      exact VExpr.instSeq_eq_self_of_bvarsBelow vs t' hb (by
        simp only [List.length_cons] at h
        omega)

/-- **`instSeq` through a reverse-instantiation chain**, with no side
conditions: the chain's elements move to the ambient cut, the subject
to the cut shifted past the chain (task #119, the nested bottom's
statement-side pins under the fired spine). -/
theorem VExpr.instSeq_instRevChain :
    ∀ (bs : List VExpr) (X : VExpr) (vs : List VExpr) (t : Nat),
      vs.length ≤ t + 1 →
      VExpr.instSeq vs t (VExpr.instRevChain bs X)
        = VExpr.instRevChain (bs.map (VExpr.instSeq vs t))
            (VExpr.instSeq vs (t + bs.length) X)
  | [], X, vs, t, _ => rfl
  | b :: bs, X, vs, t, h => by
    show VExpr.instSeq vs t (VExpr.instRevChain bs
        (X.inst (b.liftN bs.length) 0)) = _
    rw [VExpr.instSeq_instRevChain bs _ vs t h,
      VExpr.instSeq_inst0 vs (t + bs.length) X _ (by omega),
      VExpr.instSeq_liftN0 vs t bs.length b h]
    show VExpr.instRevChain (List.map _ bs) _ = _
    rw [show (b :: bs).map (VExpr.instSeq vs t)
        = VExpr.instSeq vs t b :: bs.map (VExpr.instSeq vs t) from rfl]
    show _ = VExpr.instRevChain (bs.map (VExpr.instSeq vs t)) _
    rw [show (bs.map (VExpr.instSeq vs t)).length = bs.length from by
        simp]
    simp only [List.length_cons]
    rfl

/-- **The cross-frame instantiation.**  An `instPisAt` run at scattered
frame variables, denoted at the frame and instantiated along the
frame's full value spine, is the walk of the (spine-instantiated)
denoted tower at the values the openers map to.  The openers may sit at
*any* indices below the frame — which is exactly how the kit's
constructor runs mix parameter and field variables — and the subject
may itself be open over the frame. -/
theorem instPisAt_denote_cross {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} (hcl : ∀ n ψ', VExpr.Closed (cval n ψ')) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat} {vals : List VExpr}, vals.length = D →
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : VExpr}, denote cval env ψ D ty = some T →
      ∀ {vRs : VExpr}, denote cval env ψ D rs = some vRs →
      ∀ {ws : List VExpr}, ws.length = sp.length →
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        ∃ w0, denote cval env ψ D x = some w0 ∧
          ws[j]? = some (VExpr.instSeq vals (D - 1) w0)) →
      ∀ {Γ : List VExpr} {R : VExpr},
        PiTele sp.length (VExpr.instSeq vals (D - 1) T) Γ R →
        VExpr.instSeq vals (D - 1) vRs =
          VExpr.instSeq ws (ws.length - 1) R := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D vals hvlen hsp hfb hb T hT vRs hRs ws hwlen hws Γ R hp
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl : T = vRs := by rw [hT] at hRs; exact Option.some.inj hRs
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hwlen
    cases hp
    rfl
  | cons a sp ih =>
    intro ty ds rs h D vals hvlen hsp hfb hb T hT vRs hRs ws hwlen hws Γ R hp
    obtain ⟨hwsa, hba⟩ := hsp 0 a rfl
    obtain ⟨w0, hw0den, hw0⟩ := hws 0 a rfl
    match ty, h with
    | .forallE nmT dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp
          (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- the frame facts of the head
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      -- the head, denoted
      rw [denote_forallE] at hT
      cases hA : denote cval env ψ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denote cval env ψ (D + 1)
          (body.instantiate1 (.fvar D nmT dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      rw [hB] at hT
      obtain rfl : T = .pi A B := (Option.some.inj hT).symm
      -- the instantiated body, denoted through the top value
      have hbeta := denote_beta (n := nmT) (ty := dom) hcl hfb'.2 hwsa hba
        hw0den 0
      -- the spine and its values
      match ws, hwlen with
      | w :: ws', hwlen => ?_
      have hw : w = VExpr.instSeq vals (D - 1) w0 := by
        simpa using hw0
      -- the tower, peeled
      rw [show VExpr.instSeq vals (D - 1) (VExpr.pi A B) =
          .pi (VExpr.instSeq vals (D - 1) A)
            (VExpr.instSeq vals D B) from by
        rw [VExpr.instSeq_pi _ _ _ _ (by omega)]
        congr 1
        rcases Nat.eq_zero_or_pos D with h0 | h0
        · obtain rfl : vals = [] := by
            rw [h0] at hvlen
            exact List.eq_nil_of_length_eq_zero hvlen
          rfl
        · rw [show D - 1 + 1 = D from by omega]] at hp
      cases hp with
      | @cons _ _ _ _ Γ' hp' => ?_
      -- the recursive frame
      have hfbI : Expr.fvarsBelow D (body.instantiate1 a) :=
        Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2
      have hbI : (body.instantiate1 a).looseBVarsBounded 0 = true :=
        Expr.looseBVarsBounded_instantiate1_gen hba hb'.2
      have hTI : denote cval env ψ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [hbeta, hB]
        rfl
      -- the instantiated tower for the recursion
      have hp2 := hp'.inst w 0
      rw [Nat.zero_add] at hp2
      have hrec := ih h1 hvlen
        (fun j x hx => hsp (j + 1) x (by simpa using hx))
        hfbI hbI hTI hRs (by simpa using hwlen)
        (fun j x hj => by
          obtain ⟨w1, hd1, hg1⟩ := hws (j + 1) x (by simpa using hj)
          exact ⟨w1, hd1, by simpa using hg1⟩)
        (Γ := ctxInstAt w 0 Γ') (R := R.inst w sp.length) ?_
      · have hlen' : ws'.length = sp.length := by simpa using hwlen
        rw [hrec, show (w :: ws').length - 1 = ws'.length from by simp,
          VExpr.instSeq_cons, hlen']
      · have hID : VExpr.instSeq vals (D - 1)
            (B.inst w0 0) = (VExpr.instSeq vals D B).inst w 0 := by
          rcases Nat.eq_zero_or_pos D with h0 | h0
          · obtain rfl : vals = [] := by
              rw [h0] at hvlen
              exact List.eq_nil_of_length_eq_zero hvlen
            simp only [VExpr.instSeq] at hw ⊢
            rw [hw]
          · rw [VExpr.instSeq_inst0 vals (D - 1) B w0
              (by omega), show D - 1 + 1 = D from by omega, ← hw]
        rw [hID]
        exact hp2

/-! ## Reading equal spines apart

`Deq` has no application injectivity — semantically it must not — so a
componentwise fact can only come from a *syntactic* spine equality at a
*known* arity.  The arity is what `IotaIndexPin`'s length disjunct
pins, and what the opener-invariance lemmas below compute for the kit's
runs: opening at variables never changes an application's arity, so
every reading of the constructor's residual has the raw telescope's. -/

/-- Equal applications of equal arity have equal heads and spines. -/
theorem VExpr.mkAppN_inj :
    ∀ {as bs : List VExpr} {f g : VExpr},
      VExpr.mkAppN f as = VExpr.mkAppN g bs → as.length = bs.length →
      f = g ∧ as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs f g h hlen
    obtain rfl : bs = [] :=
      List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨h, rfl⟩
  | cons a as ih =>
    intro bs f g h hlen
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      rw [VExpr.mkAppN_cons, VExpr.mkAppN_cons] at h
      obtain ⟨h1, rfl⟩ := ih h (by simpa using hlen)
      injection h1 with h2 h3
      exact ⟨h2, by rw [h3]⟩

/-- Substituting a *variable* never changes an application's arity: the
inserted value is atomic, so no application node is created or
absorbed. -/
theorem Expr.getAppArgs_length_instantiate1_fvar {i : Nat} {nm : Name}
    {t : Expr} :
    ∀ (e : Expr) (k : Nat),
      ((e.instantiate1 (.fvar i nm t) k).getAppArgs).length =
        e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    simp only [Expr.instantiate1, Expr.getAppArgs, List.length_append]
    rw [ihg k]
    rfl
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; first | rfl | (simp only [Expr.instantiate1]; rfl)

/-- Renaming constants never changes an application's arity. -/
theorem Expr.getAppArgs_length_renameConsts (f : Name → Name) :
    ∀ (e : Expr),
      ((e.renameConsts f).getAppArgs).length = e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.renameConsts, Expr.getAppArgs, List.length_append]
    rw [ihg]
    rfl
  | _ => first | rfl | (simp only [Expr.renameConsts]; rfl)

/-- An `instPisAt` run at variables lands at the raw telescope
residual's arity. -/
theorem instPisAt_fvar_residual_arity :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      (∀ x ∈ sp, ∃ i nm t, x = Expr.fvar i nm t) →
      ∀ {bs : List (Name × Expr × BinderMeta)} {body : Expr},
        ty.stripPis sp.length = some (bs, body) →
        rs.getAppArgs.length = body.getAppArgs.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h _ bs body hstrip
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip' : (some ([], ty) :
        Option (List (Name × Expr × BinderMeta) × Expr)) = some (bs, body) :=
      hstrip
    simp only [Option.some.injEq, Prod.mk.injEq] at hstrip'
    rw [hstrip'.2]
  | cons a sp ih =>
    intro ty ds rs h hsp bs body hstrip
    obtain ⟨i, nm, t, rfl⟩ := hsp a List.mem_cons_self
    match ty, h with
    | .forallE nmT dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1 (.fvar i nm t)) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons, Expr.stripPis] at hstrip
      cases h2 : bodyE.stripPis sp.length with
      | none => rw [h2] at hstrip; exact nomatch hstrip
      | some q => ?_
      rw [h2] at hstrip
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨-, rfl⟩ := hstrip
      -- the instantiated body strips to the instantiated residual
      have h3 : ((bodyE.instantiate1
          (.fvar i nm t)).stripPis sp.length).isSome = true :=
        Expr.stripPis_instantiate1_isSome sp.length 0 (by rw [h2]; rfl)
      obtain ⟨⟨bs', body'⟩, h4⟩ := Option.isSome_iff_exists.mp h3
      obtain ⟨hbody', -⟩ := Expr.stripPis_instantiate1_eq sp.length 0 h2 h4
      have h5 := ih h1 (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) h4
      rw [h5, hbody', Nat.zero_add,
        Expr.getAppArgs_length_instantiate1_fvar]

/-- Substituting under a constant-headed application never changes its
arity (the head cannot be hit, so no application node is created or
absorbed). -/
theorem Expr.getAppArgs_length_instantiate1_const {c : Name}
    {cus : List Level} {v : Expr} :
    ∀ (e : Expr) (k : Nat), e.getAppFn = .const c cus →
      ((e.instantiate1 v k).getAppArgs).length = e.getAppArgs.length ∧
      (e.instantiate1 v k).getAppFn = .const c cus := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k hh
    have hgh : g.getAppFn = .const c cus := by
      simpa [Expr.getAppFn] using hh
    obtain ⟨h1, h2⟩ := ihg k hgh
    simp only [Expr.instantiate1, Expr.getAppArgs, List.length_append]
    refine ⟨by rw [h1]; rfl, ?_⟩
    simpa [Expr.getAppFn] using h2
  | const n us =>
    intro k hh
    exact ⟨rfl, hh⟩
  | bvar j =>
    intro k hh
    exact nomatch hh
  | _ =>
    intro k hh
    first
    | exact nomatch hh
    | exact ⟨rfl, hh⟩

/-- Level instantiation never changes an application's arity. -/
theorem Expr.getAppArgs_length_instantiateLevelParams
    (ks : List Name) (us : List Level) :
    ∀ (e : Expr),
      ((e.instantiateLevelParams ks us).getAppArgs).length =
        e.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs,
      List.length_append]
    rw [ihg]
    rfl
  | _ => first | rfl | (simp only [Expr.instantiateLevelParams]; rfl)

/-- An `instPisAt` run over any spine lands at the raw telescope
residual's arity, provided the residual is constant-headed (the
nested runs' spines hold pin instantiations, not variables). -/
theorem instPisAt_residual_arity_const {c : Name} {cus : List Level} :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {bs : List (Name × Expr × BinderMeta)} {body : Expr},
        ty.stripPis sp.length = some (bs, body) →
        body.getAppFn = .const c cus →
        rs.getAppArgs.length = body.getAppArgs.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h bs body hstrip hhead
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip' : (some ([], ty) :
        Option (List (Name × Expr × BinderMeta) × Expr)) = some (bs, body) :=
      hstrip
    simp only [Option.some.injEq, Prod.mk.injEq] at hstrip'
    rw [hstrip'.2]
  | cons a sp ih =>
    intro ty ds rs h bs body hstrip hhead
    match ty, h with
    | .forallE nmT dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons, Expr.stripPis] at hstrip
      cases h2 : bodyE.stripPis sp.length with
      | none => rw [h2] at hstrip; exact nomatch hstrip
      | some q => ?_
      rw [h2] at hstrip
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨-, rfl⟩ := hstrip
      have h3 : ((bodyE.instantiate1 a).stripPis sp.length).isSome
          = true :=
        Expr.stripPis_instantiate1_isSome sp.length 0 (by rw [h2]; rfl)
      obtain ⟨⟨bs', body'⟩, h4⟩ := Option.isSome_iff_exists.mp h3
      obtain ⟨hbody', -⟩ := Expr.stripPis_instantiate1_eq sp.length 0 h2 h4
      have hhead' : body'.getAppFn = .const c cus := by
        rw [hbody', Nat.zero_add]
        exact (Expr.getAppArgs_length_instantiate1_const _ _ hhead).2
      have h5 := ih h1 h4 hhead'
      rw [h5, hbody', Nat.zero_add,
        (Expr.getAppArgs_length_instantiate1_const _ _ hhead).1]

/-- The application head under constant renaming. -/
theorem Expr.getAppFn_renameConsts (f : Name → Name) :
    ∀ (e : Expr),
      (e.renameConsts f).getAppFn = (e.getAppFn).renameConsts f := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.renameConsts, Expr.getAppFn]
    exact ihg
  | _ => rfl

/-- The application head under level instantiation. -/
theorem Expr.getAppFn_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr),
      (e.instantiateLevelParams ks us).getAppFn =
        (e.getAppFn).instantiateLevelParams ks us := by
  intro e
  induction e with
  | app g a ihg iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppFn]
    exact ihg
  | _ => rfl

/-- Renaming constants never changes loose-bvar levels. -/
theorem Expr.looseBVarsBounded_renameConsts (f : Name → Name) :
    ∀ (e : Expr) (k : Nat),
      Expr.looseBVarsBounded k (e.renameConsts f) =
        Expr.looseBVarsBounded k e := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.renameConsts, Expr.looseBVarsBounded]

/-- One domain per argument. -/
theorem instPisAt_length :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) → ds.length = sp.length := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | cons a sp ih =>
    intro ty ds rs h
    match ty, h with
    | .forallE nm dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ih h1]

/-- An `instPisAt` run at frame variables of a denoting subject has a
denoting residual — the definedness half of
`instPisAt_denote_cross`. -/
theorem instPisAt_fvar_denote_defined {cval : TConstVal} {env : Env}
    {ψ : Name → Nat} (hcl : ∀ n ψ', VExpr.Closed (cval n ψ')) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat},
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        (∃ w, denote cval env ψ D x = some w) ∧ Expr.WScoped D x ∧
          x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : VExpr}, denote cval env ψ D ty = some T →
      ∃ vRs, denote cval env ψ D rs = some vRs := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D _ _ _ T hT
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨T, hT⟩
  | cons a sp ih =>
    intro ty ds rs h D hsp hfb hb T hT
    obtain ⟨⟨w0, hw0⟩, hwsa, hba⟩ := hsp 0 a rfl
    match ty, h with
    | .forallE nmT dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp
          (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denote_forallE] at hT
      cases hA : denote cval env ψ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denote cval env ψ (D + 1)
          (body.instantiate1 (.fvar D nmT dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      have hTI : denote cval env ψ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [denote_beta (n := nmT) (ty := dom) hcl hfb'.2 hwsa hba
          hw0 0, hB]
        rfl
      exact ih h1
        (fun j x hx => hsp (j + 1) x (by simpa using hx))
        (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
        (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2) hTI

/-- A nonempty tower's head domain is its context's outermost entry. -/
theorem PiTele.head : ∀ {k : Nat} {T : VExpr} {Γ : List VExpr} {R : VExpr},
    PiTele (k + 1) T Γ R →
    ∃ B, T = .pi (Γ.getD k default) B ∧ PiTele k B (Γ.take k) R := by
  intro k T Γ R h
  cases h with
  | @cons _ A B _ Γ' hp =>
    have hlen : Γ'.length = k := hp.length
    refine ⟨B, ?_, ?_⟩
    · have hget : (Γ' ++ [A]).getD k default = A := by
        simp only [List.getD]
        rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        rfl
      rw [hget]
    · rw [List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      exact hp

/-- A denoted spine, built pointwise. -/
theorem DenoteSpine.of_getElem {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List VExpr}, as.length = vs.length →
      (∀ (q : Nat), q < as.length →
        denote cval env φ d (as.getD q default) =
          some (vs.getD q default)) →
      DenoteSpine cval env φ d as vs := by
  intro as
  induction as with
  | nil =>
    intro vs hlen _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | cons a as ih =>
    intro vs hlen hget
    cases vs with
    | nil => exact nomatch hlen
    | cons v vs =>
      refine DenoteSpine.cons ?_ (ih (by simpa using hlen) ?_)
      · have h0 := hget 0 (by simp)
        simpa using h0
      · intro q hq
        have h1 := hget (q + 1) (by simpa using hq)
        simpa using h1
