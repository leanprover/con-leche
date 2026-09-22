module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Level
public import ConLeche.Verify.Subst
import ConLeche.Verify.InstList
import ConLeche.Verify.InstSpine

public section

/-!
# The recursor CHECK at k members, inverted (milestone M5)

What `ConLeche/Kernel/Inductives/BlockRec.lean`'s pieces are, said in
the form the model tier reads them:

* the **guarded call's characterisation** (`blockIhCall?_spine`): a
  node the abstraction replaces IS the generated recursive call
  `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)` at its own arguments, on a field of
  THIS constructor whose kind names the member `rec_{c'}` eliminates —
  up to
  `Expr.resetMeta`, which is the comparison the stage makes (and the
  comparison the one-member stage has always made on rule bodies);
* the **abstraction's equations** and the fact that on a term free of
  block recursors the walk IS `liftLooseBVars` past the `ih` binders
  (`abstractIh_of_recFree`) — the base case of the substitution lemma
  `⟦body⟧[rec ↦ rec*] = ⟦body''⟧[ih ↦ ihVals rec*]` the semantics tier
  builds on.

## The rule check's two ENVIRONMENT claims (G1, G2)

Two facts about `checkBlockRule`
(`ConLeche/Kernel/Inductives/BlockInstall.lean`) that the model's
typing consumer needs by name.  The stage is handed `opsR`/`envR` for
the ANNOTATION and `opsT`/`envT` for both of these, and
`checkBlockRecK` instantiates `envT` with the CONSTRUCTORS'
environment — the one it was called at, before `consBlockRecsBare`.

* **G1 — the abstracted residue is typed at `envT`.**
  `opsT.inferType envT depth bodyO` and
  `opsT.isDefEq envT depth tyB <the recursor's own conclusion at the
  rule's prefix, the constructor's indices and `C_J p⃗ f⃗`>` run at the
  constructors' environment, NOT at the one holding the `k` rule-less
  recursors.  The residue and its whole opened frame (the recursor's
  own prefix, the fields, the `ih` openers) are recursor-free by
  construction — `abstractIh_of_recFree` below is that fact's
  syntactic half — and a model of an environment holding the
  recursors would owe every constant's leaf a type, the recursors'
  being the recursion theorem the certificate is feeding.  The
  annotation stays at `envR`: a rule mentions the recursors, and its
  annotate-claims are not consumable at any model for the same
  reason.

* **G2 — the rule's λ-domains are compared BINDER BY BINDER** with the
  opened STORED recursor type's frame:
  `checkDefEqList opsT envT (rP+nF) ((fvsPref ++ fvsF).map
  Expr.fvarTypeD) ldoms`, where `ldoms` comes from
  `Expr.instLamsAt (fvsPref ++ fvsF) rhsA` — `checkIotaRule`'s move
  (`ConLeche/Kernel/Inductives/Modeled.lean`).  Stage (b)'s whole-type
  `isDefEq` compares two CLOSED Π-types and does not give per-binder
  equality of their readings: at `ℓ = 0` both read to a truth value,
  and at `ℓ ≠ 0` an empty fibre makes two Π-readings agree at
  different domains.  The STORED right-hand side is the annotated
  STREAM one, whose λ-tower the ι step applies at frames of the
  STORED type, so the model must read those binders.

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

/-! ## The guarded recursive call -/

set_option maxHeartbeats 1000000 in

/-- **A node the abstraction replaces IS the generated recursive
call.**  `blockIhCall? fr d e = some (r, as)` says: the node's head is
a block recursor `rec_{c'}` at the block's own level arguments and at
the rule's OWN prefix (which forces `rP_{c'} = rP`); the `ih` binder
`r` — the opener of the (field, callee) key `(i, c')` — belongs to a
field `i` of THIS constructor whose kind names the member `rec_{c'}`
eliminates; the call's arguments `as` are as many as that
field's telescope has binders and mention no block recursor; and the
whole node IS `blockIhSpinePis` — the generated call
`rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)` at the rule body's frame — instantiated
at `as`, EXACTLY: `e = expected` as terms, binder data included, so
the field's index expressions `e⃗_i(a⃗)` in the node are the ANNOTATED
ones the constructor's stored type carries, not merely their erasures.

The equality has to be exact because the model's reading is not
`Expr.resetMeta`-invariant (`not_denoteMeta_resetMeta_invariant`,
`ConLeche/Model/Inductives/BlockRecRead.lean`): `resetMeta` forces
every binder datum to `.never` (bit `1`) while a datum that holds
reads `0`, and `interp` takes the bit.  This equality is the only tie
between the stored right-hand side's call node and the spine the ι law
is stated at, so it is stated at the terms the reading sees. -/
theorem blockIhCall?_spine {fr : BlockRuleFrame} {d : Nat} {e : Expr} {r : Nat}
    {as : List Expr} (h : blockIhCall? fr d e = some (r, as)) :
    ∃ (nm : Name) (c' i : Nat) (expected : Expr),
      e.getAppFn = .const nm fr.rlvls ∧
      nameIdxOf? fr.recNames nm = some c' ∧
      pairIdxOf? fr.ihKeys (i, c') = some r ∧
      (fr.ks.getD i .ordinary).tgt? = some (fr.recTgts.getD c' fr.recTgts.length) ∧
      fr.rPs.getD c' 0 = fr.rP ∧
      e.getAppArgs.length = fr.mIs.getD c' 0 + 1 ∧
      as.length = (fr.teleOf i).length ∧
      (as.any fun a => a.mentionsAnyConst fr.recNames) = false ∧
      Expr.instPisAtLift as
          (blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d (fr.teleOf i)
            (fr.idxOf i)) = some expected ∧
      e = expected := by
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
  case isFalse hrp =>
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
  have hcmp' : e = expected := by simpa using hcmp
  have htgt' : (fr.ks.getD (d + fr.nF - 1 - b) BlockFieldKind.ordinary).tgt?
      = some (fr.recTgts.getD c' fr.recTgts.length) := by
    simpa using htgt
  have hrp' : fr.rPs.getD c' 0 = fr.rP := by simpa using hrp
  exact ⟨nm, c', d + fr.nF - 1 - b, expected, hus' ▸ hfn, hnm, hrpos, htgt', hrp',
    by simpa using hlen, hasl', hfree', hexp, hcmp'⟩


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

/-! ## Stage (a)'s two NAME checks, exposed

`checkBlockRecPins` refuses a recursor named for one of the constants
the environment's own guards look up (`reservedRecName`) and, since
the maintainer's ruling of 2026-09-21 ("no red tutorial tests"), a
block whose recursor names are not, as a SET, official's
`{T_m.rec | m a member}`.  The first is what the MODEL consumes — it
makes `natLitSupported` and `strLitSupported` congruent across the
recursors' cons (`strLitSupported_consBlockRecs`,
`ConLeche/Verify/Inductives/BlockWF.lean`); the second has no model
consumer at all (it only shrinks the accept set) and is exposed here
so that what the stage guarantees about names is read in ONE place. -/

/-- Stage (a)'s guards, inverted. -/
theorem checkBlockRecPins_inv {p : BlockParts}
    (h : checkBlockRecPins (m := CheckM) p = .ok ()) :
    blockRecLpsOk p.toBlockShape = true ∧
    blockRecNamesUnreserved p.toBlockShape = true ∧
    blockRecNameSetOk p.toBlockShape = true ∧
    p.recPinned = true := by
  unfold checkBlockRecPins at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  by_cases h1 : blockRecLpsOk p.toBlockShape = true
  case neg => simp only [h1] at h; exact nomatch h
  by_cases h2 : blockRecNamesUnreserved p.toBlockShape = true
  case neg => simp only [h1, h2] at h; exact nomatch h
  by_cases h3 : blockRecNameSetOk p.toBlockShape = true
  case neg => simp only [h1, h2, h3] at h; exact nomatch h
  by_cases h4 : p.recPinned = true
  case neg => simp only [h1, h2, h3, h4] at h; exact nomatch h
  exact ⟨h1, h2, h3, h4⟩

/-- **No recursor of a checked block takes a name the environment's
own guards look up** — a pinned basis name, a slot of the `Nat` or
`String` literal guard, or a certified `Nat` operation.  This is the
fact the model reads: the two literal guards are then CONGRUENT across
the recursors' cons, so a literal denotes the same thing below the
block's recursors and above them. -/
theorem checkBlockRecPins_reserved {p : BlockParts}
    (h : checkBlockRecPins (m := CheckM) p = .ok ()) :
    ∀ rc ∈ p.recs, reservedRecName rc.cvR.name = false := by
  intro rc hrc
  have := List.all_eq_true.mp (checkBlockRecPins_inv h).2.1 rc hrc
  exact eq_of_beq (by simpa using this)

/-- **A checked block carries one recursor per member, named
`T_m.rec`** (the conformance ruling of 2026-09-21): as many recursors
as members, each named for a member and each member named by one.
WHICH recursor is which member's is NOT said here — that is its
MAJOR's business (`RecShape.tgt`). -/
theorem checkBlockRecPins_names {p : BlockParts}
    (h : checkBlockRecPins (m := CheckM) p = .ok ()) :
    p.recs.length = p.members.length ∧
    (∀ rc ∈ p.recs, ∃ ms ∈ p.members, rc.cvR.name = ms.cvT.name.str "rec") ∧
    (∀ ms ∈ p.members, ∃ rc ∈ p.recs, rc.cvR.name = ms.cvT.name.str "rec") := by
  have hset := (checkBlockRecPins_inv h).2.2.1
  unfold blockRecNameSetOk at hset
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at hset
  obtain ⟨⟨hlen, hwant⟩, hgot⟩ := hset
  refine ⟨hlen, ?_, ?_⟩
  · intro rc hrc
    have hmem := List.elem_iff.mp
      (List.all_eq_true.mp hgot rc.cvR.name (List.mem_map_of_mem hrc))
    obtain ⟨ms, hms, hn⟩ := List.mem_map.mp hmem
    exact ⟨ms, hms, hn.symm⟩
  · intro ms hms
    have hmem := List.elem_iff.mp
      (List.all_eq_true.mp hwant (ms.cvT.name.str "rec") (List.mem_map_of_mem hms))
    obtain ⟨rc, hrc, hn⟩ := List.mem_map.mp hmem
    exact ⟨rc, hrc, hn⟩

/-! ## D-d: ONE elimination level per family

The type stage returns, with each recursor's record, the sort the
kernel's own sort check gave its CONCLUSION; `checkBlockRecElimAgree`
is the family check over exactly that list.  So the fact the model
needs — one `ℓ` for the whole family — is a statement about the list
and nothing else. -/

/-- **D-d, exposed**: every recursor of the block eliminates at a level
equivalent to the first one's, so the model may take ONE `ℓ` per
family. -/
theorem blockRecElimAgree_inv {us : List Level}
    (h : checkBlockRecElimAgree (m := CheckM) us = .ok ()) :
    ∀ u ∈ us, Level.isEquiv u (us.headD .zero) = some true := by
  cases us with
  | nil => intro u hu; exact nomatch hu
  | cons u0 rest =>
    rw [checkBlockRecElimAgree] at h
    split at h
    · next hall =>
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact Level.isEquiv_of_beq (beq_self_eq_true _)
      · exact eq_of_beq (List.all_eq_true.mp hall u hu)
    · exact nomatch h

/-! ## The two capture-avoiding substitutions, at bvar-closed arguments

`blockIhCall?`, `blockIhPis` and `checkBlockRule`'s conclusion are all
built with `Expr.instPisAtLift`, and the ih telescope is opened with
`Expr.instantiateList`; neither has a reading lemma, because both are
written for arguments that may mention the ambient binders.  **At
arguments that are bvar-closed — which is what they are once the rule
body is OPENED, the frame `denoteMeta` reads at — both collapse onto
operations the model already owns**: `instPisAtLift` onto `instPisAt`
(nothing to lift, `instantiate1Lift_eq_instantiate1`), and
`instantiateList` onto `instSeq` (through `instSpine`).  These are the
two syntactic halves of the batteries the M5 model half needs. -/

/-- **`instPisAtLift` is `instPisAt` at bvar-closed arguments.** -/
theorem instPisAtLift_eq_instPisAt :
    ∀ {as : List Expr} {t : Expr}, (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      Expr.instPisAtLift as t = (Expr.instPisAt as t).map (·.2) := by
  intro as
  induction as with
  | nil => intro t _; rfl
  | cons a as ih =>
    intro t h
    cases t with
    | forallE dom body bi =>
      rw [Expr.instPisAtLift, Expr.instPisAt,
        Expr.instantiate1Lift_eq_instantiate1 (h a List.mem_cons_self) body 0,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
    | _ => rfl

/-- **`instantiateList` is `instSeq` on the reversed list.**  The
`denoteMeta` battery for `instSeq` (`denoteMeta_openRev`) therefore
covers the ih telescope's opening. -/
theorem instantiateList_eq_instSeq {vs : List Expr} (hne : vs ≠ []) (e : Expr) :
    e.instantiateList vs 0 = Expr.instSeq vs.reverse (vs.length - 1) e := by
  have hlen : vs.reverse.length = (vs.length - 1) + 1 := by
    rw [List.length_reverse]
    cases vs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  rw [← Expr.instSpine_eq_instSeq,
    Expr.instSpine_eq_instantiateList vs.reverse (vs.length - 1) e hlen,
    List.reverse_reverse]

/-! ## The family's shared rule PREFIX (the ruling of 2026-09-22)

Stage (b') compares every recursor's opened rule prefix with the FIRST
one's, binder by binder, up to defeq.  What the model needs of it is
the per-position `isDefEq`, at the two openings — the fact that lets
it identify the classes' prefix domains and so put a guarded call's
predecessor in the CALLEE's class (the lane's `hpref'`). -/

/-- **`checkBlockDefEqList`, inverted**: the lists have the same length
and every position is defeq at the stage's depth. -/
theorem checkBlockDefEqList_inv {env : Env} {F depth : Nat} {what : String} :
    ∀ {as bs : List Expr},
      checkBlockDefEqList (fueledOps mode F) env depth what as bs = .ok () →
      as.length = bs.length ∧
      ∀ l, l < as.length →
        isDefEqCore mode env F depth (as.getD l default) (bs.getD l default) = .ok true
  | [], [], _ => ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  | [], _ :: _, h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | _ :: _, [], h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | a :: as, b :: bs, h => by
    rw [checkBlockDefEqList] at h
    simp only [fueledOps_isDefEq] at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    by_cases hcb : c = true
    case neg =>
      rw [Bool.not_eq_true] at hcb
      subst hcb
      simp only [Bool.false_eq_true, if_false, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind] at h
      exact nomatch h
    subst hcb
    simp only [if_pos, Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨hlen, hall⟩ := checkBlockDefEqList_inv h
    refine ⟨by simp [hlen], fun l hl => ?_⟩
    cases l with
    | zero => simpa using hc
    | succ l => simpa using hall l (by simpa using hl)

/-- **The walk, inverted**: at every position of the tail the prefix
LENGTH is the reference's and the opened domains are defeq to it. -/
theorem checkBlockRecPrefixAt_inv {env : Env} {p : BlockShape} {rP0 F : Nat}
    {doms0 : List Expr} :
    ∀ {cvRs : List ConstantVal} {ri : Nat},
      checkBlockRecPrefixAt (fueledOps mode F) env p rP0 doms0 cvRs ri = .ok () →
      ∀ (i : Nat) (cv : ConstantVal), cvRs[i]? = some cv →
        p.rulePrefixAt (ri + i) = rP0 ∧
        ∃ (fvs : List Expr) (o : Expr),
          openPisAtFvars rP0 cv.type 0 = some (fvs, o) ∧
          doms0.length = fvs.length ∧
          ∀ l, l < doms0.length →
            isDefEqCore mode env F rP0 (doms0.getD l default)
              ((fvs.map Expr.fvarTypeD).getD l default) = .ok true
  | [], _, _, i, _, hi => by simp at hi
  | cv :: rest, ri, h, i, cvi, hi => by
    rw [checkBlockRecPrefixAt] at h
    by_cases hlen : (p.rulePrefixAt ri == rP0) = true
    case neg =>
      rw [if_neg hlen] at h
      simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      exact nomatch h
    rw [if_pos hlen] at h
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs, o⟩ := x1
    have hop : openPisAtFvars rP0 cv.type 0 = some (fvs, o) := unwrapOr_ok hx1
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    obtain ⟨hl, hall⟩ := checkBlockDefEqList_inv (what := "the block's recursors do not \
      share their rule prefix") (by cases u; exact hu)
    cases i with
    | zero =>
      have hcv : cv = cvi := by simpa using hi
      subst hcv
      refine ⟨by simpa using eq_of_beq hlen, fvs, o, hop, by simpa using hl, ?_⟩
      intro l hll
      exact hall l hll
    | succ i =>
      obtain ⟨hr, hrest⟩ := checkBlockRecPrefixAt_inv h i cvi (by simpa using hi)
      exact ⟨by rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hr, hrest⟩

/-- **Stage (b'), inverted**: the FIRST recursor's opening is the
reference, and every later recursor's prefix has its length and is
defeq to it binder by binder. -/
theorem checkBlockRecPrefixAgree_inv {env : Env} {p : BlockShape} {F : Nat}
    {cvRs : List ConstantVal} {cv0 : ConstantVal}
    (h : checkBlockRecPrefixAgree (fueledOps mode F) env p cvRs = .ok ())
    (h0 : cvRs[0]? = some cv0) :
    ∃ (fvs0 : List Expr) (o0 : Expr),
      openPisAtFvars (p.rulePrefixAt 0) cv0.type 0 = some (fvs0, o0) ∧
      ∀ (i : Nat) (cv : ConstantVal), cvRs[i]? = some cv → 0 < i →
        p.rulePrefixAt i = p.rulePrefixAt 0 ∧
        ∃ (fvs : List Expr) (o : Expr),
          openPisAtFvars (p.rulePrefixAt 0) cv.type 0 = some (fvs, o) ∧
          fvs0.length = fvs.length ∧
          ∀ l, l < fvs0.length →
            isDefEqCore mode env F (p.rulePrefixAt 0)
              ((fvs0.map Expr.fvarTypeD).getD l default)
              ((fvs.map Expr.fvarTypeD).getD l default) = .ok true := by
  match cvRs, h0 with
  | cv :: rest, h0 =>
    have hcv : cv = cv0 := by simpa using h0
    rw [checkBlockRecPrefixAgree] at h
    simp only [Bind.bind, Except.bind] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs0, o0⟩ := x1
    have hop : openPisAtFvars (p.rulePrefixAt 0) cv0.type 0 = some (fvs0, o0) := by
      rw [← hcv]; exact unwrapOr_ok hx1
    refine ⟨fvs0, o0, hop, fun i cvi hi hipos => ?_⟩
    match i, hipos with
    | i + 1, _ =>
      obtain ⟨hr, fvs, o, hop', hlen, hall⟩ :=
        checkBlockRecPrefixAt_inv h i cvi (by simpa using hi)
      refine ⟨by rw [show i + 1 = 1 + i from by omega]; exact hr, fvs, o, hop',
        by simpa using hlen, fun l hl => ?_⟩
      have := hall l (by simpa using hl)
      simpa using this

end ConLeche
