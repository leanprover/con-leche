import Setlec.TT.Judgment
import Setlec.TT.Deq
import Setlec.TTVerify.VClosed
import Setlec.TTVerify.SubstAlgebra
import Setlec.TTVerify.HasTypeSubst

/-!
# Context weakening

`HasType Γ e A → HasType (Γ ++ Δ) e A`.

**On the critical path, and it was missing.**  `EnvTT.has_type` gives
each constant a derivation in the *empty* context, while the fuel
induction consumes constants at depth `d > 0`, i.e. in a context of
length `d`.  Nothing in `Setlec/TT/*` or `Setlec/TTVerify/*` bridged
the two, so the first `.const` clause of `CheckStepTT` could not have
been written.

It is **lift-free**, which is what makes it cheap: appending to the
*tail* of the context leaves every de Bruijn index pointing where it
did, so the `bvar` rule's `Γ[i]? = some A` only gains successes and
nothing is shifted.  Every other rule is a straight congruence, and the
binder rules work because `(A :: Γ) ++ Δ` is `A :: (Γ ++ Δ)`
definitionally.

The same fact could equally be had by `∀ Δ`-quantifying `EnvTT`'s
`has_type` field and pushing the obligation to the install side.  It is
the same lemma either way; proving it once here keeps the invariant
stated at the empty context, which is where the corollary wants it.

**Gotcha for anyone writing a `HasType` induction here.**  Do not
reach for `induction h <;> constructor <;> assumption`: `conv`'s
conclusion is `HasType Γ t B` with both `t` and `B` metavariables, so
it unifies with *every* goal and `constructor` picks it in all 32
cases.  The cases have to name their own constructor.  (Also note that
`solve_by_elim`, `apply_assumption` and `by_contra` are Mathlib, not
core, so they are unavailable in this project.)

Like `Setlec/TTVerify/Inversion.lean` and
`Setlec/TTVerify/VClosed.lean`, this lives on the bridge side so that
it stays marked as a bridge need rather than becoming layer
metatheory — see `Setlec/TT/DESIGN.md` §3.1 for the accounting of how
much of that the bridge has taken on.
-/

namespace Setlec.TT

/-- Appending to the tail of the context preserves every derivation. -/
theorem HasType.weakenTail (Δ : List VExpr) : ∀ {Γ : List VExpr}
    {e A : VExpr}, HasType Γ e A → HasType (Γ ++ Δ) e A := by
  intro Γ e A h
  induction h with
  | @bvar Γ' i A' hi =>
    refine .bvar ?_
    have hlt : i < Γ'.length := by
      rcases Nat.lt_or_ge i Γ'.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hi
        exact nomatch hi
    rw [List.getElem?_append_left hlt]
    exact hi
  -- every other rule is a straight congruence; the binder cases work
  -- because `(A :: Γ) ++ Δ` is `A :: (Γ ++ Δ)` definitionally
  | sort => exact .sort
  | const => exact .const
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2
  | lam _ ih => exact .lam ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | eqType => exact .eqType
  | conv _ _ ih1 ih2 => exact .conv ih1 ih2
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | congrApp _ _ ih1 ih2 => exact .congrApp ih1 ih2
  | congrLam _ _ ih1 ih2 => exact .congrLam ih1 ih2
  | congrPi _ _ ih1 ih2 => exact .congrPi ih1 ih2
  | congrProj _ ih => exact .congrProj ih
  | congrEq _ _ ih1 ih2 => exact .congrEq ih1 ih2
  | beta _ ih => exact .beta ih
  | zeta => exact .zeta
  | eta _ ih => exact .eta ih
  | funext _ _ _ ih1 ih2 ih3 => exact .funext ih1 ih2 ih3
  | proofIrrel _ _ _ _ ih1 ih2 ih3 ih4 => exact .proofIrrel ih1 ih2 ih3 ih4
  | natRecZero _ _ _ ih1 ih2 ih3 => exact .natRecZero ih1 ih2 ih3
  | natRecSucc _ _ _ _ ih1 ih2 ih3 ih4 => exact .natRecSucc ih1 ih2 ih3 ih4
  | punitRecUnit _ _ ih1 ih2 => exact .punitRecUnit ih1 ih2
  | punitEta _ _ ih1 ih2 => exact .punitEta ih1 ih2
  | projFst _ _ _ ih1 ih2 ih3 => exact .projFst ih1 ih2 ih3
  | projSnd _ _ _ ih1 ih2 ih3 => exact .projSnd ih1 ih2 ih3
  | projFstMk _ _ _ _ ih1 ih2 ih3 ih4 => exact .projFstMk ih1 ih2 ih3 ih4
  | projSndMk _ _ _ _ ih1 ih2 ih3 ih4 => exact .projSndMk ih1 ih2 ih3 ih4
  | psigmaEta _ _ _ ih1 ih2 ih3 => exact .psigmaEta ih1 ih2 ih3
  | quotLiftMk _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    exact .quotLiftMk ih1 ih2 ih3 ih4 ih5 ih6

/-- The form the bridge uses: a closed derivation holds in any context.
`EnvTT.has_type` produces exactly this shape. -/
theorem HasType.weakenNil {e A : VExpr} (h : HasType [] e A)
    (Δ : List VExpr) : HasType Δ e A := by
  simpa using HasType.weakenTail Δ h

/-! ## Closing an open equation at arguments

`Setlec/TTVerify/DESIGN.md` §5's recipe, mechanized once.  An
environment law stated over free variables — `NatOpsTT`'s recurrences
are the case in hand, at depth 2 in context `[Nat, Nat]` — has to be
used at *closed* instances, and the temptation is to reach for a
substitution lemma about `HasType`.

**Do not.**  The theory internalizes its own substitution:

1. `lam` twice.  The rule carries **no domain premise**, so this is
   free; it turns the open equation into a closed λ-λ-equation.
2. `app` twice, at the arguments.  The rule's own `B.inst a` performs
   the instantiation *object-level, in the type*.
3. `Deq.intro` re-slots the result, the proof term being irrelevant.

Nothing about `Nat` enters, which is why this is stated for an
arbitrary domain: whenever a `Deq` has to move from an open context to
a closed instance, this is the route. -/

/-- **Closing a two-variable equation.**  A `Deq` in context `[A, A]`
holds at any two terms of `A`, in any context. -/
theorem Deq.close2 {A T L R : VExpr} (hA : VExpr.Closed A)
    (h : HasType [A, A] .prf (.eqE T L R)) {Γ : List VExpr} {a b : VExpr}
    (ha : HasType Γ a A) (hb : HasType Γ b A) :
    Deq Γ ((L.inst a 1).inst b) ((R.inst a 1).inst b) := by
  have h1 : HasType Γ (.lam A (.lam A .prf)) (.pi A (.pi A (.eqE T L R))) :=
    HasType.weakenNil (HasType.lam (HasType.lam h)) Γ
  have h2 := HasType.app h1 ha
  rw [VExpr.inst_pi, VExpr.inst_eq_self_of_closed hA] at h2
  have h3 := HasType.app h2 hb
  rw [VExpr.inst_eqE] at h3
  exact Deq.intro h3

/-- **Closing a two-variable typing.**  The one place the object-level
route does *not* reach: `lam`/`app` would move the equation's
**subject** to a redex, which no rule concludes (F1).  So a typing over
the frame's two variables is instantiated with `HasType.instN` — the
residue that file is for. -/
theorem HasType.close2 {A T e : VExpr} (hA : VExpr.Closed A)
    (hT : VExpr.Closed T) (h : HasType [A, A] e T)
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x A) (hy : HasType Γ y A) :
    HasType Γ ((e.inst x 1).inst y) T := by
  have h1 := hx.instN (h.weakenTail Γ) (.succ A .zero)
  rw [VExpr.inst_eq_self_of_closed hA, VExpr.inst_eq_self_of_closed hT] at h1
  have h2 := hy.instN h1 .zero
  rwa [VExpr.inst_eq_self_of_closed hT] at h2

/-- **Closing a two-variable equation under proof binders.**  The
div/mod certificate frame: two `Nat` variables and one binder per
`ble`-guard hypothesis, the guards being propositions the equation
itself never mentions.

The two extra binders cost nothing.  Each hypothesis type and the
equation are *lifted* over the binders below them, so every
instantiation the `app` rule performs at a proof binder meets a lift
and is absorbed — `inst_liftN_comm` / `inst_liftN_absorb` do the whole
of it, and the conclusion is `close2`'s, unchanged.  Which is the
point: **a certificate checked under extra hypotheses closes at the
same instantiation as one checked without them.**

There is deliberately no three-binder variant.  The checker runs every
certificate at depth `4` whatever its hypothesis count, and `CtxOk`
fixes the context length to the depth — so a one-hypothesis frame is
still a four-entry context with one entry no leaf mentions.  Give that
entry the type of the hypothesis that *is* used and inhabit it with the
same proof: the unused binder costs a duplicated argument, not a
lemma.

The reason is recorded rather than the absence: a missing lemma with a
reason is documentation, a missing lemma without one is a gap someone
will fill. -/
theorem Deq.close4 {A H1 H2 T L R : VExpr} (hA : VExpr.Closed A)
    (h : HasType [VExpr.liftN 1 H2 0, H1, A, A] .prf
      (VExpr.liftN 2 (.eqE T L R) 0))
    {Γ : List VExpr} {a b : VExpr}
    (ha : HasType Γ a A) (hb : HasType Γ b A)
    (hp1 : HasType Γ .prf ((H1.inst a 1).inst b))
    (hp2 : HasType Γ .prf ((H2.inst a 1).inst b)) :
    Deq Γ ((L.inst a 1).inst b) ((R.inst a 1).inst b) := by
  have hab : ∀ e : VExpr, ∀ n : Nat,
      ((VExpr.liftN n e 0).inst a (n + 1)).inst b n
        = VExpr.liftN n ((e.inst a 1).inst b) 0 := by
    intro e n
    rw [VExpr.inst_liftN_comm e (show 0 + n ≤ n + 1 by omega) a,
      show n + 1 - n = 1 by omega,
      VExpr.inst_liftN_comm (e.inst a 1) (show 0 + n ≤ n by omega) b,
      Nat.sub_self]
  have h1 : HasType Γ
      (.lam A (.lam A (.lam H1 (.lam (VExpr.liftN 1 H2 0) .prf))))
      (.pi A (.pi A (.pi H1 (.pi (VExpr.liftN 1 H2 0)
        (VExpr.liftN 2 (.eqE T L R) 0))))) :=
    HasType.weakenNil (HasType.lam (HasType.lam (HasType.lam
      (HasType.lam h)))) Γ
  have h3 : HasType Γ
      (.app (.app (.lam A (.lam A (.lam H1 (.lam (VExpr.liftN 1 H2 0) .prf))))
        a) b)
      (.pi ((H1.inst a 1).inst b)
        (.pi (VExpr.liftN 1 ((H2.inst a 1).inst b) 0)
          (VExpr.liftN 2 (((VExpr.eqE T L R).inst a 1).inst b) 0))) := by
    have h2 := HasType.app h1 ha
    rw [VExpr.inst_pi, VExpr.inst_pi, VExpr.inst_pi,
      VExpr.inst_eq_self_of_closed hA] at h2
    have h3 := HasType.app h2 hb
    rw [VExpr.inst_pi, VExpr.inst_pi] at h3
    rw [hab H2 1, hab (.eqE T L R) 2] at h3
    exact h3
  have h4 := HasType.app h3 hp1
  rw [VExpr.inst_pi,
    VExpr.inst_liftN_absorb ((H2.inst a 1).inst b) (Nat.zero_le _)
      (Nat.le_refl 0) VExpr.prf,
    VExpr.liftN_zero,
    VExpr.inst_liftN_absorb (((VExpr.eqE T L R).inst a 1).inst b)
      (Nat.zero_le _) (show 1 ≤ 0 + 1 by omega) VExpr.prf] at h4
  have h5 := HasType.app h4 hp2
  rw [VExpr.inst_liftN_absorb (((VExpr.eqE T L R).inst a 1).inst b)
      (Nat.zero_le _) (Nat.le_refl 0) VExpr.prf, VExpr.liftN_zero,
    VExpr.inst_eqE, VExpr.inst_eqE] at h5
  exact Deq.intro h5

/-- **Closing a one-variable equation.**  The `Nat.pred` shape.

Note it needs **no** closedness hypothesis on `A`, where `close2` does:
`close2`'s second `app` meets the domain after one instantiation has
already run over it, and only closedness makes that instantiation
invisible.  With one binder there is no such instantiation.  The
asymmetry is real, not an oversight — and it was the linter that
pointed it out, which is the one variety of §8.2's defect something
else catches for you. -/
theorem Deq.close1 {A T L R : VExpr}
    (h : HasType [A] .prf (.eqE T L R)) {Γ : List VExpr} {a : VExpr}
    (ha : HasType Γ a A) : Deq Γ (L.inst a) (R.inst a) := by
  have h1 : HasType Γ (.lam A .prf) (.pi A (.eqE T L R)) :=
    HasType.weakenNil (HasType.lam h) Γ
  have h2 := HasType.app h1 ha
  rw [VExpr.inst_eqE] at h2
  exact Deq.intro h2

end Setlec.TT
