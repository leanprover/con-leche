module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas

public section

/-!
# The closed spine under an opened telescope (task #315)

The reading side of a nested block sees a constructor's residual
*opened*: `openPisAtFvars L x d` returns one fresh variable per binder
and the residual with those variables substituted.  What the pins and
the restore table describe is the *unopened* residual — `stripPis`'
body, still carrying `L` loose `bvar`s.  When the opened residual is a
constant spine whose first arguments are variables of the ambient
prefix (indices `< d`, so *below* every opener), the two descriptions
line up argument by argument:

* the head constant and the prefix arguments are already there before
  the opening, unchanged;
* the remaining arguments are the unopened ones with the openers
  substituted.

The reason the prefix survives verbatim is one clause of
`Expr.instantiate1`: it maps `.fvar idx ty` to itself (it never
descends into the annotation, and never rewrites a variable).  So an
opener — itself an `fvar` — can only *produce* a variable of its own
index, and an argument that comes out as a variable *below* `d` must
have been that variable all along (`os_instSeq_eq_fvar_inv`).
-/

namespace ConLeche

/-- **The substitution cannot manufacture a foreign variable.**  If a
sequence of `fvar` arguments, none of them the variable `k`, turns `e`
into `.fvar k ty`, then `e` was `.fvar k ty` already. -/
theorem os_instSeq_eq_fvar_inv :
    ∀ (vs : List Expr) (t : Nat) {e : Expr} {k : Nat} {ty : Expr},
      (∀ v ∈ vs, ∃ j tj, v = Expr.fvar j tj ∧ j ≠ k) →
      Expr.instSeq vs t e = .fvar k ty → e = .fvar k ty := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ h; exact h
  | cons v vs ih =>
    intro t e k ty hall h
    obtain ⟨j, tj, hv, hjk⟩ := hall v List.mem_cons_self
    subst hv
    have hstep : e.instantiate1 (.fvar j tj) t = .fvar k ty :=
      ih (t - 1) (fun x hx => hall x (List.mem_cons_of_mem _ hx)) h
    cases e with
    | bvar i =>
      rw [show (Expr.bvar i).instantiate1 (.fvar j tj) t =
          (if i = t then .fvar j tj else if i > t then .bvar (i - 1) else .bvar i) from rfl]
        at hstep
      split at hstep
      · injection hstep with hjeq _
        exact absurd hjeq hjk
      · split at hstep <;> exact absurd hstep (by simp)
    | fvar idx ty' => exact hstep
    | _ => exact absurd hstep (by simp [Expr.instantiate1])

/-- **A prefix of ambient variables is read off unchanged.**  Every
substituted argument is a variable at or above `d`, every expected one
a variable below `d`, so the substitution was the identity on the
prefix and the two lists are equal. -/
theorem os_map_instSeq_fvars_eq (vs : List Expr) (t d : Nat)
    (hvs : ∀ v ∈ vs, ∃ j tj, v = Expr.fvar j tj ∧ d ≤ j) :
    ∀ (A P : List Expr), (∀ p ∈ P, ∃ k ty, p = Expr.fvar k ty ∧ k < d) →
      A.map (Expr.instSeq vs t ·) = P → A = P := by
  intro A
  induction A with
  | nil => intro _ _ h; exact h
  | cons a A ih =>
    intro P hP h
    cases P with
    | nil => simp at h
    | cons p P =>
      rw [List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨k, ty, hpk, hkd⟩ := hP p List.mem_cons_self
      subst hpk
      have ha : a = Expr.fvar k ty := by
        refine os_instSeq_eq_fvar_inv vs t (fun w hw => ?_) h1
        obtain ⟨j, tj, hw', hdj⟩ := hvs w hw
        exact ⟨j, tj, hw', by omega⟩
      rw [ha, ih P (fun q hq => hP q (List.mem_cons_of_mem _ hq)) h2]

/-- `instSeq_getAppFn_const_inv` with the opener hypothesis spelled
out: `AllFvarsL` is sealed outside its own module, so the `∀`-form is
what a caller can actually build. -/
theorem os_instSeq_getAppFn_const_inv : ∀ (vs : List Expr),
    (∀ v ∈ vs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty) →
    ∀ (t : Nat) (e : Expr) {n : Name} {us : List Level},
      (Expr.instSeq vs t e).getAppFn = .const n us → e.getAppFn = .const n us := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ h; exact h
  | cons v vs ih =>
    intro hall t e n us h
    obtain ⟨idx, ty, hv⟩ := hall v List.mem_cons_self
    subst hv
    exact Expr.getAppFn_const_of_instantiate1
      (ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _ h)

/-- `instSeq_getAppArgs` with the opener hypothesis spelled out. -/
theorem os_instSeq_getAppArgs : ∀ (vs : List Expr),
    (∀ v ∈ vs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty) →
    ∀ (t : Nat) (e : Expr),
      (Expr.instSeq vs t e).getAppArgs = e.getAppArgs.map (Expr.instSeq vs t ·) := by
  intro vs
  induction vs with
  | nil => intro _ t e; simp [Expr.instSeq]
  | cons v vs ih =>
    intro hall t e
    obtain ⟨idx, ty, hv⟩ := hall v List.mem_cons_self
    subst hv
    show (Expr.instSeq vs (t - 1) (e.instantiate1 _ t)).getAppArgs = _
    rw [ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _,
      Expr.getAppArgs_instantiate1_var, List.map_map]
    rfl

/-- **The goal.**  An opened residual that is a constant spine with an
ambient-variable prefix comes from an unopened residual with the SAME
head, the SAME prefix, and the remaining arguments substituted. -/
theorem os_openPisAtFvars_constSpine_stripPis {L d : Nat} {x : Expr} {afvs : List Expr}
    {n : Name} {us : List Level} {fvsP is : List Expr}
    (hop : openPisAtFvars L x d = some (afvs, Expr.mkAppN (.const n us) (fvsP ++ is)))
    (hP : ∀ v ∈ fvsP, ∃ (k : Nat) (ty : Expr), v = .fvar k ty ∧ k < d) :
    ∃ (tbs : List (Expr × BinderMeta)) (is₀ : List Expr),
      x.stripPis L = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is₀)) ∧
      is = is₀.map (Expr.instSeq afvs (L - 1)) := by
  obtain ⟨bs, body₀, hstrip, hlen, hIdx, -⟩ := Verify.openPisAtFvars_stripPis L hop
  have hfv : ∀ v ∈ afvs, ∃ j tj, v = Expr.fvar j tj ∧ d ≤ j := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
    have hiL : i < L := by rw [← hlen]; exact hi
    obtain ⟨ty, hj⟩ := hIdx i hiL
    rw [List.getElem?_eq_getElem hi] at hj
    exact ⟨d + i, ty, by rw [← hvi]; exact Option.some.inj hj, Nat.le_add_right d i⟩
  have hall : ∀ v ∈ afvs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    intro v hv
    obtain ⟨j, tj, hv', -⟩ := hfv v hv
    exact ⟨j, tj, hv'⟩
  have hbody := Verify.openPisAtFvars_instSeq L hop hstrip
  have hfn : body₀.getAppFn = .const n us := by
    refine os_instSeq_getAppFn_const_inv afvs hall (L - 1) body₀ ?_
    rw [← hbody, Expr.getAppFn_mkAppN]
    rfl
  have hargs : body₀.getAppArgs.map (Expr.instSeq afvs (L - 1) ·) = fvsP ++ is := by
    rw [← os_instSeq_getAppArgs afvs hall (L - 1) body₀, ← hbody, Expr.getAppArgs_mkAppN]
    rfl
  obtain ⟨A, B, hAB, hA, hB⟩ := List.map_eq_append_iff.mp hargs
  have hAeq : A = fvsP := os_map_instSeq_fvars_eq afvs (L - 1) d hfv A fvsP hP hA
  have hb0 : body₀ = Expr.mkAppN (.const n us) (fvsP ++ B) := by
    rw [← hAeq, ← hAB, ← hfn, Expr.mkAppN_getApp]
  rw [hb0] at hstrip
  exact ⟨bs, B, hstrip, hB.symm⟩

end ConLeche
