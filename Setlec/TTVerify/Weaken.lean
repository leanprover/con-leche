import Setlec.TT.Judgment

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
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
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

end Setlec.TT
