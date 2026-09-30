module

public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# Official's uniform check, inverted

The install runs official's `check_uniform_ind_occs` BEFORE the
positivity check (`nestUniform`, `Kernel/Inductives/Positivity.lean`):
at every stored constructor, the parameters' domains name no member, and
its root crest (`nestRootCrest`: every whole application `T_m.{lps} p⃗`
replaced by the member's hole) names no member constant.  `nestUniform_inv`
reads the check off the run; the syntactic lemmas below move the
"no member constant" fact through instantiation.
-/

namespace ConLeche

/-! ## The uniform check, inverted -/

/-- `nestUniform` passed: the check at every stored constructor. -/
theorem nestUniform_inv {ctx : NestCtx}
    {ctorss : List (List (ConstantVal × Nat))}
    (h : nestUniform (m := CheckM) ctx ctorss = .ok ()) :
    ∀ cs ∈ ctorss, ∀ c ∈ cs, nestUniformOk ctx c.1 = true := by
  unfold nestUniform at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hn
    intro cs hcs c hc
    rw [List.findSome?_eq_none_iff] at hn
    have := List.find?_eq_none.mp (hn cs hcs) c hc
    simpa using this

/-- Instantiating a bound variable by a free one changes no member constant. -/
theorem nestOcc_zero_instantiate1 {names : List Name} {i : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar i ty) k).nestOcc names 0 0 =
      e.nestOcc names 0 0 := by
  intro e
  induction e with
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · simp [Expr.nestOcc]
    · split <;> rfl
  | app f a ihf iha => intro k; simp [Expr.instantiate1, Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp [Expr.instantiate1, Expr.nestOcc, iht, ihv, ihb]
  | proj s j e ih => intro k; simp [Expr.instantiate1, Expr.nestOcc, ih]
  | _ => intro k; rfl

/-- No member or hole is in particular no member constant. -/
theorem nestOcc_zero_of {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr), e.nestOcc names lo hi = false → e.nestOcc names 0 0 = false := by
  intro e
  induction e with
  | fvar i ty _ => intro _; simp [Expr.nestOcc]
  | app f a ihf iha =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam t b mm iht ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b mm iht ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s j e ih => intro h; simp only [Expr.nestOcc] at h ⊢; exact ih h
  | _ => intro h; exact h

/-- No member or hole in the parameters' domains is in particular no member
constant there. -/
theorem piDomsOcc_zero_of {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr), e.piDomsOcc names lo hi n = false → e.piDomsOcc names 0 0 n = false
  | 0, _, _ => rfl
  | n + 1, .forallE d b bm, h => by
    simp only [Expr.piDomsOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨nestOcc_zero_of _ h.1, piDomsOcc_zero_of n b h.2⟩
  | _ + 1, .bvar _, _ | _ + 1, .fvar .., _ | _ + 1, .sort _, _ | _ + 1, .const .., _
  | _ + 1, .app .., _ | _ + 1, .lam .., _ | _ + 1, .letE .., _ | _ + 1, .lit _, _
  | _ + 1, .proj .., _ => rfl

/-- The parameters' domains name the same member constants after
instantiating a bound variable by a free one. -/
theorem piDomsOcc_zero_instantiate1 {names : List Name} {x : Nat} {t : Expr} :
    ∀ (n : Nat) (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar x t) k).piDomsOcc names 0 0 n = e.piDomsOcc names 0 0 n
  | 0, _, _ => rfl
  | n + 1, .forallE d b bm, k => by
    simp only [Expr.instantiate1, Expr.piDomsOcc, nestOcc_zero_instantiate1,
      piDomsOcc_zero_instantiate1 n b (k + 1)]
  | _ + 1, .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ + 1, .fvar .., _ | _ + 1, .sort _, _ | _ + 1, .const .., _
  | _ + 1, .app .., _ | _ + 1, .lam .., _ | _ + 1, .letE .., _ | _ + 1, .lit _, _
  | _ + 1, .proj .., _ => rfl

/-- A telescope whose parameters' domains name no member constant and
whose body at the (free-variable) parameters names none names none. -/
theorem nestOcc_zero_of_instPisWith {names : List Name} :
    ∀ (ps : List Expr) (e crest : Expr), (∀ p ∈ ps, ∃ i ty, p = .fvar i ty) →
      instPisWith ps e = some crest → e.piDomsOcc names 0 0 ps.length = false →
      crest.nestOcc names 0 0 = false → e.nestOcc names 0 0 = false
  | [], e, crest, _, hi', _, hc => by
    simp only [instPisWith, Option.some.injEq] at hi'
    subst hi'; exact hc
  | p :: ps, .forallE d b bm, crest, hp, hi', hd, hc => by
    obtain ⟨i, ty, rfl⟩ := hp _ List.mem_cons_self
    simp only [instPisWith] at hi'
    simp only [List.length_cons, Expr.piDomsOcc, Bool.or_eq_false_iff] at hd
    have hb := nestOcc_zero_of_instPisWith ps _ crest
      (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hi'
      (by rw [piDomsOcc_zero_instantiate1]; exact hd.2) hc
    rw [nestOcc_zero_instantiate1] at hb
    simp [Expr.nestOcc, hd.1, hb]
  | _ :: _, .bvar _, _, _, h, _, _ | _ :: _, .fvar .., _, _, h, _, _
  | _ :: _, .sort _, _, _, h, _, _ | _ :: _, .const .., _, _, h, _, _
  | _ :: _, .app .., _, _, h, _, _ | _ :: _, .lam .., _, _, h, _, _
  | _ :: _, .letE .., _, _, h, _, _ | _ :: _, .lit _, _, _, h, _, _
  | _ :: _, .proj .., _, _, h, _, _ => by simp [instPisWith] at h

/-- **The canonical crest of a constructor that passed the check names no
member constant.** -/
theorem nestRootCanon_nestOcc_zero {ctx : NestCtx} {cv : ConstantVal}
    (hu : nestUniformOk ctx cv = true) :
    ∃ A, nestRootCanon ctx cv = some A ∧ A.nestOcc ctx.names 0 0 = false := by
  simp only [nestUniformOk, Bool.and_eq_true, Bool.not_eq_true'] at hu
  obtain ⟨-, hb⟩ := hu
  split at hb
  case h_2 => exact nomatch hb
  rename_i A hcr
  exact ⟨A, hcr, by simpa using hb⟩

/-- The parameters' domains of a constructor that passed the check name no
member constant. -/
theorem nestUniformOk_piDoms {ctx : NestCtx} {cv : ConstantVal}
    (hu : nestUniformOk ctx cv = true) :
    cv.type.piDomsOcc ctx.names 0 0 ctx.nP = false := by
  simp only [nestUniformOk, Bool.and_eq_true, Bool.not_eq_true'] at hu
  exact piDomsOcc_zero_of _ _ hu.1

end ConLeche
