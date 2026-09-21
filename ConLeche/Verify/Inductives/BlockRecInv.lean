module

public import ConLeche.Kernel.Inductives.BlockRec

public section

/-!
# The recursor CHECK at k members, inverted (milestone M5)

What `ConLeche/Kernel/Inductives/BlockRec.lean`'s pieces are, said in
the form the model tier reads them:

* the generated pieces **unfolded** — `blockMotivesPis` and
  `blockIhPis` one step at a time — and their agreement
  with the one-member kit at `k = 1` (`blockRecPrefixAt_one`,
  `blockIhPis_structIhPis`), which is what makes the `k = 1` instance
  of the CHECK the one-member shapes;
* the **guarded call's characterisation** (`blockIhCall?_spine`): a
  node the abstraction replaces IS the generated recursive call
  `rec_{c'} p⃗ C⃗ m⃗ e⃗_i(a⃗) (f_i a⃗)` at its own arguments, on a field of
  THIS constructor whose kind carries the target `c'` — up to
  `Expr.resetMeta`, which is the comparison the stage makes (and the
  comparison the one-member stage has always made on rule bodies);
* the **abstraction's equations** and the fact that on a term free of
  block recursors the walk IS `liftLooseBVars` past the `ih` binders
  (`abstractIh_of_recFree`) — the base case of the substitution lemma
  `⟦body⟧[rec ↦ rec*] = ⟦body''⟧[ih ↦ ihVals rec*]` the semantics tier
  builds on;
What is NOT here, and is the semantics tier's (design §4.3): the
abstraction's own INVERSE, `body = body''[ih_i a⃗ ↦ spine]`.  Its two
halves are: `blockIhCall?_spine` (every replaced node is the spine)
and `abstractIh_of_recFree` (every other node only moved); the
substitution lemma that puts them together is stated over the
DENOTATION, `⟦body⟧[rec ↦ rec*] = ⟦body''⟧[ih ↦ ihVals rec*]`, and
belongs with the union recursor it is proved against.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-! ## The generated pieces, unfolded -/

theorem blockMotivesPis_nil {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {c : Nat} {body : Expr} :
    blockMotivesPis lps nP ℓ pw [] c body = some body := rfl

theorem blockMotivesPis_cons {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {T : Name} {nIdx : Nat} {tty : Expr} {rest : List (Name × Nat × Expr)}
    {c : Nat} {body : Expr} :
    blockMotivesPis lps nP ℓ pw ((T, nIdx, tty) :: rest) c body =
      (tty.stripPis nP).bind fun q =>
      (structMotiveTyI T lps nP nIdx ℓ q.2).bind fun mty =>
        (blockMotivesPis lps nP ℓ pw rest (c + 1) body).map fun r =>
          .forallE (mty.liftLooseBVars c 0) r ⟨pw⟩ := rfl

theorem blockIhPis_nil {nF o : Nat} {pw : PropWhen} {tgts : List Nat}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    {l : Nat} {body : Expr} :
    blockIhPis nF o pw tgts teleOf idxOf [] l body = body := rfl

theorem blockIhPis_cons {nF o : Nat} {pw : PropWhen} {tgts : List Nat}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    {i : Nat} {is : List Nat} {l : Nat} {body : Expr} :
    blockIhPis nF o pw tgts teleOf idxOf (i :: is) l body =
      .forallE
        (Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i))
          (Expr.mkAppN (.bvar (nF + o - 1 + l + (teleOf i).length - tgts.getD i 0))
            ((idxOf i).map (structIdxAt nF o i l (teleOf i).length) ++
              [Expr.mkAppN (.bvar (nF - 1 - i + l + (teleOf i).length))
                (structTeleVars (teleOf i).length)])))
        (blockIhPis nF o pw tgts teleOf idxOf is (l + 1) body) ⟨pw⟩ := rfl

/-! ## The `k = 1` agreement with the one-member kit -/

/-- At ONE member the recursor's leading spine is the one-member
one. -/
theorem blockRecPrefixAt_one (nP N nF d : Nat) :
    blockRecPrefixAt nP 1 N nF d = structRecPrefixAt nP N nF d := by
  simp only [blockRecPrefixAt, structRecPrefixAt, List.range_one, List.map_cons,
    List.map_nil, Nat.add_sub_cancel, Nat.sub_zero]

/-- With every recursive field's target `0` — the only target a
one-member block has — the `ih` telescope is the one-member one. -/
theorem blockIhPis_structIhPis {nF o : Nat} {pw : PropWhen} {tgts : List Nat}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (h : ∀ i, tgts.getD i 0 = 0) :
    ∀ (is : List Nat) (l : Nat) (body : Expr),
      blockIhPis nF o pw tgts teleOf idxOf is l body
        = structIhPis nF o pw teleOf idxOf is l body
  | [], _, _ => rfl
  | i :: is, l, body => by
    simp only [blockIhPis_cons, structIhPis, h i, Nat.sub_zero,
      blockIhPis_structIhPis h is (l + 1) body]

/-! ## The guarded recursive call -/

set_option maxHeartbeats 1000000 in

/-- **A node the abstraction replaces IS the generated recursive
call.**  `blockIhCall? fr d e = some (r, as)` says: the node's head is
a block recursor `rec_{c'}` at the block's own level arguments; the
`ih` binder `r` belongs to a field `i` of THIS constructor whose kind
names the target `c'`; the call's arguments `as` are as many as that
field's telescope has binders and mention no block recursor; and the
whole node is `blockIhSpinePis` — the generated call
`rec_{c'} p⃗ C⃗ m⃗ e⃗_i(a⃗) (f_i a⃗)` at the rule body's frame —
instantiated at `as`, up to `Expr.resetMeta`.

`resetMeta` is the comparison the stage makes, and the one the
one-member stage has always made on a rule body (`nativeRulesOk`): the
binder data inside a rule's right-hand side is the annotation pass's,
not the generator's. -/
theorem blockIhCall?_spine {fr : BlockRuleFrame} {d : Nat} {e : Expr} {r : Nat}
    {as : List Expr} (h : blockIhCall? fr d e = some (r, as)) :
    ∃ (nm : Name) (c' i : Nat) (expected : Expr),
      e.getAppFn = .const nm fr.rlvls ∧
      nameIdxOf? fr.recNames nm = some c' ∧
      natIdxOf? fr.recIdx i = some r ∧
      (fr.ks.getD i .ordinary).tgt? = some c' ∧
      as.length = (fr.teleOf i).length ∧
      (as.any fun a => a.mentionsAnyConst fr.recNames) = false ∧
      Expr.instPisAtLift as
          (blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.k fr.N fr.nF i d (fr.teleOf i)
            (fr.idxOf i)) = some expected ∧
      Expr.resetMeta e = Expr.resetMeta expected := by
  simp only [blockIhCall?] at h
  split at h
  case h_2 => exact nomatch h
  case h_1 nm us hfn =>
  split at h
  case h_1 => exact nomatch h
  case h_2 c' hnm =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hus =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hlen =>
  split at h
  case h_1 => exact nomatch h
  case h_2 maj hmaj =>
  split at h
  case h_2 => exact nomatch h
  case h_1 b hb =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hrange =>
  split at h
  case isTrue => exact nomatch h
  case isFalse htgt =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hasl =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hfree =>
  split at h
  case h_1 => exact nomatch h
  case h_2 expected hexp =>
  split at h
  case isTrue => exact nomatch h
  case isFalse hcmp =>
  split at h
  case h_1 => exact nomatch h
  case h_2 rpos hrpos =>
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hus' : us = fr.rlvls := by simpa using hus
  have hasl' : maj.getAppArgs.length = (fr.teleOf (d + fr.nF - 1 - b)).length := by simpa using hasl
  have hfree' : (maj.getAppArgs.any fun a => a.mentionsAnyConst fr.recNames) = false := by simpa using hfree
  have hcmp' : e.resetMeta = expected.resetMeta := by simpa using hcmp
  have htgt' : (fr.ks.getD (d + fr.nF - 1 - b) BlockFieldKind.ordinary).tgt? = some c' := by
    simpa using htgt
  exact ⟨nm, c', d + fr.nF - 1 - b, expected, hus' ▸ hfn, hnm, hrpos, htgt', hasl',
    hfree', hexp, hcmp'⟩


/-! ## The abstraction -/

@[simp] theorem abstractIh_bvar {fr : BlockRuleFrame} {d j : Nat} :
    abstractIh fr d (.bvar j) = some (if j < d then .bvar j else .bvar (j + fr.nR)) := rfl

@[simp] theorem abstractIh_sort {fr : BlockRuleFrame} {d : Nat} {u : Level} :
    abstractIh fr d (.sort u) = some (.sort u) := rfl

@[simp] theorem abstractIh_lit {fr : BlockRuleFrame} {d : Nat} {l : Literal} :
    abstractIh fr d (.lit l) = some (.lit l) := rfl

@[simp] theorem abstractIh_const {fr : BlockRuleFrame} {d : Nat} {n : Name} {us : List Level} :
    abstractIh fr d (.const n us)
      = if fr.recNames.contains n then none else some (.const n us) := rfl

@[simp] theorem abstractIh_fvar {fr : BlockRuleFrame} {d i : Nat} {ty : Expr} :
    abstractIh fr d (.fvar i ty) = none := rfl

theorem abstractIh_app {fr : BlockRuleFrame} {d : Nat} {f a : Expr} :
    abstractIh fr d (.app f a) =
      (match blockIhCall? fr d (.app f a) with
       | some (rpos, as) =>
         some (Expr.mkAppN (.bvar (d + fr.nR - 1 - rpos))
           (as.map fun x => x.liftLooseBVars fr.nR d))
       | none =>
         (abstractIh fr d f).bind fun f' =>
           (abstractIh fr d a).map fun a' => .app f' a') := rfl

/-- A head that is a block recursor makes the node mention one. -/
theorem mentionsAnyConst_of_getAppFn {names : List Name} {nm : Name} {us : List Level} :
    ∀ {e : Expr}, e.getAppFn = .const nm us → names.contains nm = true →
      e.mentionsAnyConst names = true
  | .app f a, h, hn => by
    have : (Expr.app f a).getAppFn = f.getAppFn := rfl
    simp only [Expr.mentionsAnyConst, mentionsAnyConst_of_getAppFn (this ▸ h) hn,
      Bool.true_or]
  | .const n _, h, hn => by
    cases h; simpa [Expr.mentionsAnyConst] using hn
  | .bvar _, h, _ | .sort _, h, _ | .lit _, h, _ | .fvar .., h, _
  | .lam .., h, _ | .forallE .., h, _ | .letE .., h, _ | .proj .., h, _ => nomatch h

/-- **A node free of block recursors is no guarded call**: the call's
head has to BE a block recursor. -/
theorem blockIhCall?_eq_none_of_recFree {fr : BlockRuleFrame} {d : Nat} {e : Expr}
    (h : e.mentionsAnyConst fr.recNames = false) : blockIhCall? fr d e = none := by
  unfold blockIhCall?
  split
  · rename_i nm us hfn
    split
    · rfl
    · rename_i c' hnm
      refine absurd (mentionsAnyConst_of_getAppFn (names := fr.recNames) hfn ?_) (by simp [h])
      obtain ⟨hval, hlt, -⟩ :
          fr.recNames[c']?.getD default = nm ∧ c' < fr.recNames.length ∧
            ∀ j, j < c' → ¬ fr.recNames[j]?.getD default = nm := by
        simpa [nameIdxOf?] using hnm
      rw [← hval, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.elem_eq_true_of_mem (List.getElem_mem hlt)
  · rfl

/-- **On a term free of block recursors the abstraction IS the lift
past the `ih` binders.**  This is the substitution lemma's base case:
everything the abstraction did not replace it only moved. -/
theorem abstractIh_of_recFree {fr : BlockRuleFrame} :
    ∀ {e : Expr} {d : Nat}, e.mentionsAnyConst fr.recNames = false → e.hasFvar = false →
      abstractIh fr d e = some (e.liftLooseBVars fr.nR d)
  | .bvar j, d, _, _ => by
    simp only [abstractIh_bvar, Expr.liftLooseBVars]
    split <;> rename_i hj
    · rw [if_neg (by omega)]
    · rw [if_pos (by omega), Nat.add_comm]
  | .sort _, _, _, _ => rfl
  | .lit _, _, _, _ => rfl
  | .const n us, d, h, _ => by
    simp only [Expr.mentionsAnyConst] at h
    simp only [abstractIh_const, h, Bool.false_eq_true, if_false, Expr.liftLooseBVars]
  | .fvar _ _, _, _, hf => absurd hf (by simp [Expr.hasFvar])
  | .lam ty b bi, d, h, hf => by
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [abstractIh, abstractIh_of_recFree h.1 hf.1,
      abstractIh_of_recFree h.2 hf.2, Option.bind_some, Option.map_some,
      Expr.liftLooseBVars]
  | .forallE ty b bi, d, h, hf => by
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [abstractIh, abstractIh_of_recFree h.1 hf.1,
      abstractIh_of_recFree h.2 hf.2, Option.bind_some, Option.map_some,
      Expr.liftLooseBVars]
  | .letE ty v b, d, h, hf => by
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [abstractIh, abstractIh_of_recFree h.1.1 hf.1.1,
      abstractIh_of_recFree h.1.2 hf.1.2, abstractIh_of_recFree h.2 hf.2,
      Option.bind_some, Option.map_some, Expr.liftLooseBVars]
  | .proj s i e, d, h, hf => by
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Expr.hasFvar] at hf
    simp only [abstractIh, h.1, Bool.false_eq_true, if_false,
      abstractIh_of_recFree h.2 hf, Option.map_some, Expr.liftLooseBVars]
  | .app f a, d, h, hf => by
    have hnone : blockIhCall? fr d (.app f a) = none := blockIhCall?_eq_none_of_recFree h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [abstractIh_app, hnone, abstractIh_of_recFree h.1 hf.1,
      abstractIh_of_recFree h.2 hf.2, Option.bind_some, Option.map_some,
      Expr.liftLooseBVars]

end ConLeche
