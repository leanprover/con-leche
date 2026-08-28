import Setlec.TTVerify.DeclInd
import Setlec.TTVerify.Certs
import Setlec.TTVerify.ReducePin
import Setlec.Verify.BridgeWfImp
import Setlec.Verify.Denote.IndFrame

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

@[simp] theorem ctxInstAt_length (v : VExpr) (j : Nat) :
    ∀ (Γ : List VExpr), (ctxInstAt v j Γ).length = Γ.length
  | [] => rfl
  | B :: Γ => by simp [ctxInstAt_cons, ctxInstAt_length v j Γ]

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

/-! ## The padding

A domain fact at position `n` arrives in a length-`k` context whose
innermost `k - n` entries nothing constrains.  They are chosen as
`.sort 0` and consumed by the closed inhabitant below, so a
partially-fitted spine can instantiate a full-depth equation. -/

/- `dummyPropT` relocated to `Setlec/Verify/Denote/IndFrame.lean`. -/

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

/-! ## Reading equal spines apart

`Deq` has no application injectivity — semantically it must not — so a
componentwise fact can only come from a *syntactic* spine equality at a
*known* arity.  The arity is what `IotaIndexPin`'s length disjunct
pins, and what the opener-invariance lemmas below compute for the kit's
runs: opening at variables never changes an application's arity, so
every reading of the constructor's residual has the raw telescope's. -/
