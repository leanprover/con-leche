module

public import ConLeche.Kernel.Inductives.NestedElim
import ConLeche.Verify.InstLevels
import ConLeche.Verify.ExceptBind

public section

/-!
# The nested copy ends in the container's sort (task #279)

`mkCopy` (`ConLeche/Kernel/Inductives/NestedElim.lean`) builds the
auxiliary type of one container member `J` at the pins: the member's
stored type has its level parameters instantiated at `lvls`, its own
parameter telescope instantiated at the pin arguments `Ds`, and the
block's parameter telescope `pbs` closed back around the residual.
None of those three steps touches the telescope's LEAF: the copy is
still a `∀`-telescope ending in `J`'s sort, only with `J`'s level
parameters substituted — and its arity is `pbs.length + nIdx` where
`nIdx` is what `J` had left after its own parameters.

That is `mkCopy_stripPis_sort`, and the three steps are proved
separately because each is consumed on its own elsewhere:

* `Expr.stripPis_abstract1_sort` / `stripPis_closeTelescope` — closing
  a telescope back (`abstract1` per binder) adds binders in front and
  leaves a `sort` leaf alone;
* `Expr.stripPis_instantiate1_sort` / `Expr.instPis_stripPis_sort` —
  instantiating the leading binders consumes exactly as many binders as
  arguments and leaves a `sort` leaf alone;
* `Expr.stripPis_instantiateLevelParams_sort` — level instantiation
  keeps the arity and substitutes into the leaf's level
  (`ConLeche/Verify/InstLevels.lean`'s `…_isSome`/`…_eq` pair, read at a
  `sort` body).
-/

namespace ConLeche

namespace Expr

/-- Abstracting a free variable keeps a `sort`-ended `∀`-telescope's
arity and its leaf: `abstract1` descends into binder domains and
bodies, and rewrites neither a `forallE`'s shape nor a `sort`. -/
theorem stripPis_abstract1_sort {d : Nat} {s : Level} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} (j : Nat),
      e.stripPis k = some (bs, .sort s) →
      ∃ bs', (e.abstract1 d j).stripPis k = some (bs', .sort s) := by
  intro k
  induction k with
  | zero =>
    intro e bs j h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [abstract1, stripPis]⟩
  | succ k ih =>
    intro e bs j h
    match e, h with
    | .forallE ty b m, h =>
      simp only [stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        obtain ⟨pbs, pbody⟩ := p
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', hbs'⟩ := ih (j + 1) hs
        exact ⟨(ty.abstract1 d j, m) :: bs', by
          simp only [abstract1, stripPis, hbs', Option.map_some]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [stripPis] at h

/-- Instantiating a binder keeps a `sort`-ended `∀`-telescope's arity
and its leaf (the `sort` reading of `stripPis_instantiate1_isSome` and
`stripPis_instantiate1_eq`). -/
theorem stripPis_instantiate1_sort {v : Expr} {s : Level} {k j : Nat} {e : Expr}
    {bs : List (Expr × BinderMeta)}
    (h : e.stripPis k = some (bs, .sort s)) :
    ∃ bs', (e.instantiate1 v j).stripPis k = some (bs', .sort s) := by
  have hsome : ((e.instantiate1 v j).stripPis k).isSome :=
    stripPis_instantiate1_isSome k j (by rw [h]; rfl)
  cases hq : (e.instantiate1 v j).stripPis k with
  | none => rw [hq] at hsome; exact nomatch hsome
  | some q =>
    obtain ⟨qbs, qbody⟩ := q
    obtain ⟨hbody, -⟩ := stripPis_instantiate1_eq k j h hq
    exact ⟨qbs, by simp [hbody, instantiate1]⟩

/-- Level instantiation keeps a `sort`-ended `∀`-telescope's arity and
substitutes into the leaf's level. -/
theorem stripPis_instantiateLevelParams_sort {ks : List Name} {us : List Level}
    {k : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {s : Level}
    (h : e.stripPis k = some (bs, .sort s)) :
    ∃ bs', (e.instantiateLevelParams ks us).stripPis k
      = some (bs', .sort (Level.subst ks us s)) := by
  have hsome : ((e.instantiateLevelParams ks us).stripPis k).isSome :=
    stripPis_instantiateLevelParams_isSome ks us k (by rw [h]; rfl)
  cases hq : (e.instantiateLevelParams ks us).stripPis k with
  | none => rw [hq] at hsome; exact nomatch hsome
  | some q =>
    obtain ⟨qbs, qbody⟩ := q
    obtain ⟨hbody, -⟩ := stripPis_instantiateLevelParams_eq ks us k h hq
    exact ⟨qbs, by simp [hbody, instantiateLevelParams]⟩

/-- Instantiating a `∀`-telescope at `as` succeeds as soon as the
telescope has `as.length` binders to spare, and what is left is the
residual telescope with the SAME `sort` leaf: the arguments eat the
leading `as.length` binders and `instantiate1` leaves a `sort`
alone. -/
theorem instPis_stripPis_sort {s : Level} :
    ∀ (as : List Expr) {e : Expr} {n : Nat} {bs : List (Expr × BinderMeta)},
      e.stripPis (as.length + n) = some (bs, .sort s) →
      ∃ e' bs', e.instPis as = some e' ∧ e'.stripPis n = some (bs', .sort s) := by
  intro as
  induction as with
  | nil => intro e n bs h; exact ⟨e, bs, rfl, by simpa using h⟩
  | cons a as ih =>
    intro e n bs h
    rw [show (a :: as).length + n = (as.length + n) + 1 from by
      simp only [List.length_cons]; omega] at h
    match e, h with
    | .forallE d b m, h =>
      simp only [stripPis] at h
      cases hs : b.stripPis (as.length + n) with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        obtain ⟨pbs, pbody⟩ := p
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', hbs'⟩ := stripPis_instantiate1_sort (v := a) (j := 0) hs
        obtain ⟨e', bs'', he', hbs''⟩ := ih hbs'
        exact ⟨e', bs'', by simpa only [instPis] using he', hbs''⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [stripPis] at h

end Expr

/-- Closing a telescope back (`closeTelescope`, one `abstract1` per
binder) puts `bs.length` binders in front of the body's own telescope
and leaves a `sort` leaf alone — so the closed term is a syntactic
`∀`-telescope of the summed arity ending in the same sort. -/
theorem stripPis_closeTelescope {body : Expr} {n : Nat}
    {bs' : List (Expr × BinderMeta)} {s : Level}
    (h : body.stripPis n = some (bs', Expr.sort s)) :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat),
      ∃ bs'', (closeTelescope bs i body).stripPis (bs.length + n)
        = some (bs'', Expr.sort s) := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨bs', by simpa [closeTelescope] using h⟩
  | cons b bs ih =>
    obtain ⟨dom, bm⟩ := b
    intro i
    obtain ⟨bs'', hbs''⟩ := ih (i + 1)
    obtain ⟨bs₃, hbs₃⟩ := Expr.stripPis_abstract1_sort (d := i) (bs.length + n) 0 hbs''
    exact ⟨(dom, bm) :: bs₃, by
      simp only [List.length_cons, closeTelescope,
        show bs.length + 1 + n = (bs.length + n) + 1 from by omega,
        Expr.stripPis, hbs₃, Option.map_some]⟩

/-- A successful copy stores the block's parameter telescope closed
around the member's type instantiated at the pins — the `do`-block's
shape, with the two failing branches (the level-list length guard and
the instantiation) discharged. -/
theorem mkCopy_type {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {auxName : Name} {J : ContainerMember} {t : AuxType}
    (h : mkCopy pbs lvls Ds auxName J = .ok t) :
    ∃ tyI, Expr.instPis (Expr.instantiateLevelParams J.lps lvls J.type) Ds = some tyI ∧
      t.type = closeTelescope pbs 0 tyI := by
  unfold mkCopy at h
  split at h
  case h_1 _ tyI hty =>
    split at h
    · obtain ⟨_cs, -, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨tyI, hty, by rw [← h]⟩
    · simp [bind, Except.bind] at h
  case h_2 =>
    split at h <;> simp [bind, Except.bind] at h

/-- **The copy ends in the container's sort.**  If the copied member's
stored type is a `∀`-telescope of its own parameters `Ds` and `nIdx`
further binders ending in `Sort sJ`, then the copy `mkCopy` stores is a
`∀`-telescope of the BLOCK's parameters `pbs` and the same `nIdx`
further binders, ending in `Sort sJ` with the member's level parameters
instantiated at `lvls` (`Level.subst J.lps lvls`).  The copy therefore
has the shape `checkSumTele`'s first branch and `auxIdxCount` read off
it, with the index count the member had. -/
theorem mkCopy_stripPis_sort {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {auxName : Name} {J : ContainerMember} {t : AuxType}
    (h : mkCopy pbs lvls Ds auxName J = .ok t)
    {nIdx : Nat} {bsJ : List (Expr × BinderMeta)} {sJ : Level}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bsJ, .sort sJ)) :
    ∃ bs, t.type.stripPis (pbs.length + nIdx)
      = some (bs, .sort (Level.subst J.lps lvls sJ)) := by
  obtain ⟨tyI, hty, htt⟩ := mkCopy_type h
  obtain ⟨bs1, h1⟩ := Expr.stripPis_instantiateLevelParams_sort (ks := J.lps) (us := lvls) hJ
  obtain ⟨tyI', bs2, hinst, h2⟩ := Expr.instPis_stripPis_sort Ds h1
  rw [hty] at hinst
  obtain rfl : tyI' = tyI := Option.some.inj hinst.symm
  rw [htt]
  exact stripPis_closeTelescope h2 pbs 0

end ConLeche
