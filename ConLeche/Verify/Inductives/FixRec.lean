module

public import ConLeche.Verify.Inductives.SumRec
import ConLeche.Kernel.Inductives.FieldTele

public section

/-!
# The generated recursive recursor, unfolded (task #188)

`ConLeche/Verify/Inductives/SumRec.lean`'s syntactic kit with the inductive
hypotheses threaded: the unfoldings of the recursive generators
(`structMinorTyR`, `structMinorsPisR`/`structMinorsLamsR`,
`structRecTyR`, `structRecRhsR`), and the closed spellings the
readings need.

The one genuinely new piece is `instSeq_structIdxAt`: a recursive
field's index expression is spelled at the field's own frame (the
parameters and the `i` earlier fields) and moved to the recursor's
frame `p⃗ x⃗ f⃗ ih⃗` by `structIdxAt`'s two lifts; instantiating there at
the frame's own variables undoes both lifts and leaves the expression
instantiated at the parameters and the `i` earlier field variables
alone — twice `instSeq_liftLooseBVars_mid`.

`Expr.shiftFromN` (`Expr.shiftFrom`, iterated) is here too: the
reading of those index expressions moves from the constructor's own
opening to the recursor's frame by inserting the `o` extra slots just
after the parameters, which is exactly that shift (its `denoteMeta` side
is `ConLeche/Model/Inductives/FixRecRead.lean`).
-/

namespace ConLeche

open Expr

/-! ## The index expression at the recursor's frame -/

/-! ## Iterated variable shifts -/

/-- `Expr.shiftFrom p`, iterated `n` times: insert `n` fresh variable
slots at index `p`. -/
@[expose] def Expr.shiftFromN (p : Nat) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.shiftFrom p (Expr.shiftFromN p n e)

/-- A shift bumps a free variable at or above the cut by one. -/
theorem Expr.shiftFromN_fvar (p : Nat) :
    ∀ (n idx : Nat) (ty : Expr),
      ∃ (ty' : Expr),
        Expr.shiftFromN p n (Expr.fvar idx ty)
          = Expr.fvar (if idx < p then idx else idx + n) ty'
  | 0, idx, ty => ⟨ty, by
      show Expr.fvar idx ty = _
      by_cases h : idx < p
      · rw [if_pos h]
      · rw [if_neg h, Nat.add_zero]⟩
  | n + 1, idx, ty => by
    obtain ⟨ty', hn⟩ := Expr.shiftFromN_fvar p n idx ty
    by_cases h : idx < p
    · refine ⟨ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_pos h, if_pos h]
      simp only [Expr.shiftFrom, if_neg (show ¬ idx ≥ p from by omega)]
    · refine ⟨Expr.shiftFrom p ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_neg h, if_neg h,
        show idx + (n + 1) = idx + n + 1 from by omega]
      simp only [Expr.shiftFrom, if_pos (show idx + n ≥ p from by omega)]


/-- Well-scopedness survives an instantiation sequence at well-scoped
arguments. -/
theorem Expr.instSeq_WScoped {d : Nat} :
    ∀ (sp : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ sp, Expr.WScoped d a) → Expr.WScoped d e → Expr.WScoped d (instSeq sp t e)
  | [], _, _, _, he => he
  | a :: sp, t, _e, hsp, he =>
    Expr.instSeq_WScoped sp (t - 1) (fun x hx => hsp x (List.mem_cons_of_mem _ hx))
      (Expr.WScoped.instantiate1_gen (hsp a List.mem_cons_self) t he)

end ConLeche
