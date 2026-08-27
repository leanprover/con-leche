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
    {k : Nat} {fvs : List Expr} {Γ Δ' : List VExpr}
    (hΔlen : Δ'.length = k) (hfvslen : fvs.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote cval env ψ i (Expr.fvarTypeD x) =
        some (Γ.getD (k - 1 - i) default))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hwsE : Expr.WScoped n e)
    (hent : ∀ i, i < n → Δ'[k - 1 - i]? =
      some (Γ.getD (k - 1 - i) default)) :
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
  refine ⟨by omega, hfb,
    (Γ.getD (k - 1 - l.1) default).liftN (k - l.1), ?_, ?_⟩
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
