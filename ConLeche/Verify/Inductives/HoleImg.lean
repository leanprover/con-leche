module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift

public section

/-!
# The holes read back

`nestHoleImg ctx prog` (`Kernel/Inductives/Positivity.lean`) reads every
hole under the frames `prog` back as the WHOLE application it stands for:
member `m`'s hole `nP + m` as `T_m.{lps}` applied to the canonical
parameters, a frame's hole as its container applied to the frame's
parameters, themselves read back.  Below the holes and above them it is
`none`; a longer stack reads the holes of a shorter one alike
(`nestHoleImg_suffix`).
-/

namespace ConLeche

variable {ctx : NestCtx}

theorem nestHoleImg_root_lt_nP {v : Nat} (hv : v < ctx.nP) : nestHoleImg ctx [] v = none := by
  simp only [nestHoleImg]
  rw [if_neg (by omega)]

theorem nestHoleImg_lt_nP : ∀ {prog : List NestHole} {v : Nat}, v < ctx.nP →
    nestHoleImg ctx prog v = none
  | [], v, hv => nestHoleImg_root_lt_nP hv
  | h :: prog, v, hv => by
    simp only [nestHoleImg]
    rw [if_neg (by simp [NestCtx.hiAt]; omega)]
    exact nestHoleImg_lt_nP hv

theorem nestHoleImg_ge : ∀ {prog : List NestHole} {v : Nat}, ctx.hiAt prog.length ≤ v →
    nestHoleImg ctx prog v = none
  | [], v, hv => by
    simp only [nestHoleImg]
    simp only [NestCtx.hiAt] at hv
    rw [if_neg (by simp only [NestCtx.hiAt]; omega)]
  | h :: prog, v, hv => by
    simp only [nestHoleImg]
    rw [if_neg (by simp [NestCtx.hiAt] at hv ⊢; omega)]
    exact nestHoleImg_ge (by simp [NestCtx.hiAt] at hv ⊢; omega)

/-- **A longer stack reads the holes of a shorter one alike.** -/
theorem nestHoleImg_suffix (X anc : List NestHole) {v : Nat} (hv : v < ctx.hiAt anc.length) :
    nestHoleImg ctx (X ++ anc) v = nestHoleImg ctx anc v := by
  induction X with
  | nil => rfl
  | cons h X ih =>
    simp only [List.cons_append, nestHoleImg]
    rw [if_neg (by simp [NestCtx.hiAt, List.length_append] at hv ⊢; omega)]
    exact ih

/-- Every hole reads back. -/
theorem nestHoleImg_hole : ∀ {prog : List NestHole} {v : Nat}, ctx.nP ≤ v →
    v < ctx.hiAt prog.length → ∃ e, nestHoleImg ctx prog v = some e
  | [], v, h1, h2 => by
    simp only [nestHoleImg]
    rw [if_pos ⟨h1, by simpa using h2⟩]
    exact ⟨_, rfl⟩
  | h :: prog, v, h1, h2 => by
    simp only [nestHoleImg]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      simp only [NestCtx.hiAt, List.length_cons] at h2 hne ⊢
      exact nestHoleImg_hole h1 (by simp only [NestCtx.hiAt]; omega)

end ConLeche

namespace ConLeche

/-- A read-back hole is a constant's spine. -/
theorem nestHoleImg_spine {ctx : NestCtx} : ∀ {prog : List NestHole} {v : Nat} {e : Expr},
    nestHoleImg ctx prog v = some e → ∃ c us args, e = Expr.mkAppN (.const c us) args
  | [], v, e, h => by
    simp only [nestHoleImg] at h
    split at h
    · exact ⟨_, _, _, (Option.some.inj h).symm⟩
    · exact nomatch h
  | hh :: prog, v, e, h => by
    simp only [nestHoleImg] at h
    split at h
    · exact ⟨_, _, _, (Option.some.inj h).symm⟩
    · exact nestHoleImg_spine h

end ConLeche

namespace ConLeche

/-- A spine over a head that is no `∀` is no `∀`. -/
theorem Expr.mkAppN_ne_forallE : ∀ (args : List Expr) {f : Expr},
    (∀ a b bm, f ≠ .forallE a b bm) → ∀ a b bm, Expr.mkAppN f args ≠ .forallE a b bm
  | [], _, hf => hf
  | x :: xs, f, _ => Expr.mkAppN_ne_forallE xs (f := .app f x) (fun _ _ _ h => nomatch h)

end ConLeche
