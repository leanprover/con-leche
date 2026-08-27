import Setlec.TTVerify.DeclBasis
import Setlec.Verify.Extend.Iota
import Setlec.TTVerify.TeleOpen

/-!
# `DeclIndTT`: the modeled-inductive install

The tentpole, opened.  §14.3 names five obligations; this module holds
the pieces they share, and `EtaFoldTT`/`UnitFoldTT` first, because they
are the smallest and they close `CapsOkTT` — which `majorToCtor`'s
rescues already consume.

> **START AT `DESIGN.md` §14.6.**  The next lemma's design, the
> remaining-work map for all five obligations, and the working-memory
> notes a successor cannot recover from the code (the annotated-vs-raw
> declaration trap, `extendBasisTT`'s positional argument order, why
> the `*RhsV` defs exist, the elaboration gotchas) are written there
> and are *not* repeated here.  This header covers only what this
> module contains.

**What the scouting settled** (§14.1's gate, discharged): the whole
*syntactic* layer of the install — `EtaPins`, `checkEtaThm_inv`,
`checkUnitThm_inv`, `EtaPins.step`, `EtaPins.transport` — is already
`V`-free and lives in `Setlec/Verify/Extend/Iota.lean`, so the bridge
imports it rather than duplicating it.  Only the *assembly* of
`EtaPins` from a successful `checkIndDecl` exists solely inside the
model's proof (`Setlec/Model/Extend/Decl.lean:150`), and it is nine
lines; `etaPinsT_of_caps` below re-derives it.  It is `V`-free and a
candidate for sharing under #123's criterion — recorded here rather
than moved, because moving it would be a change to a file the model
path is mid-flight in.

**The counting that matters for the two folds.**  The model's
`unit_rule_fold` (`Setlec/Model/EtaInstall.lean:581`) has 21
hypotheses: **12 `V`-free syntactic** (find?s, `stripPis` shapes,
telescope-domain matches, `hasFvar = false`) and **9 semantic**
(`RenameOk`, `ConstValParams`, the `Eq` former's value, the theorem's
`∈ˢ` membership, `AnnotOk`, and the use site's `TeleFit`).  The bridge
inherits all twelve syntactic ones unchanged and replaces the nine:
`interpClosed`/`∈ˢ` become `denote`/`HasType`, `TeleFit` becomes
`VTeleTyped`, the `Eq` former's value becomes `EnvTT.eq_law`, and
`AnnotOk` — as everywhere in this hierarchy — disappears.  `RenameOk`
and `ConstValParams` have transposes in `EnvTT`'s own fields.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The shared final step

Both folds, and `ProjBottomTT` after them, end the same way: a
*checked theorem* is a closed term whose type is a Π-telescope ending
in the pinned `Eq` former applied to three arguments.  Fit the
telescope with the use site's spine, and the theorem's inhabitant
becomes a proof of that spine's equation — which §11's law turns into
a `Deq`.

This is the transpose of `eta_rule_fold`'s "the theorem's inhabitant is
eliminated through the statement, and the equality collapses to the
value identity", and it is *short* where the model's is not, for a
reason worth naming: the model has to produce a set-theoretic
inhabitant of an interpreted equality and then read equality of
*values* off it, while the layer's equality is a syntactic former and
`Deq.intro` is the whole elimination. -/

/-- **A checked equality theorem, fired at a use site.**  The last step
of `EtaFoldTT`, `UnitFoldTT` and `ProjBottomTT`.

Stated over `cval` and `EqLawTT` rather than over an `EnvTT`, because
the folds run at the *extended* environment of a block member's
install, where the `EnvTT` being built is exactly what is not yet
available (the same reason `unit_rule_fold` takes unpacked hypotheses
rather than an `EnvModel`). -/
theorem Deq.ofEqThm {env : Env} {cval : TConstVal} (heq : EqLawTT env cval)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Δ : List VExpr} {v Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType Δ v Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.intro (Setlec.TT.Deq.conv (hfit.appN hv)
    (heq hE ψ Δ A a b hA ha hb))

/-- The same, when the theorem's term is *closed* — which is how every
checked `_model.*` theorem reaches a use site.  The equality's own
level assignment is a separate argument: the statement's `Eq.{ℓA}` is
read at `ℓA`, not at the constant's parameters. -/
theorem Deq.ofEqThmClosed {env : Env} {cval : TConstVal}
    (heq : EqLawTT env cval)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Δ : List VExpr} {v Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType [] v Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.ofEqThm heq hE ψ (HasType.weakenNil hv Δ) hfit hA ha hb

/-! ## The install's syntactic pins, assembled

`EtaPins` (`Setlec/Verify/Extend/Iota.lean:917`) is the conjunction of
both capability pins, each guarded by its flag.  The model builds it
inline; here it is a lemma, so that the two folds can take it as a
hypothesis and `DeclIndTT` can supply it once. -/

/-- **`EtaPins` from the stored capabilities.**  `indBlockCaps` sets
`eta` and `unitlike` from `checkEtaThm`/`checkUnitThm`, so the flags
holding *is* the checks having passed, and the two inversions do the
rest.  Nine lines, and the only part of the install's syntactic layer
the bridge has to write for itself. -/
theorem etaPinsT_of_caps {env : Env} {cvT cvC : ConstantVal} {nP nF : Nat} :
    EtaPins env cvT.name cvT.levelParams (indBlockCaps env cvT cvC nP nF) := by
  refine ⟨fun hcape => ?_, fun hcapu => ?_⟩
  · refine checkEtaThm_inv ?_
    simp only [indBlockCaps, Bool.and_eq_true] at hcape
    exact hcape.2
  · refine checkUnitThm_inv ?_
    simp only [indBlockCaps] at hcapu
    exact hcapu

/-! ## The phase's block-independent half

Each phase of this bridge has needed exactly one shared spine lemma
before any of its cases could be written: the basis blocks needed
`BetaSpine` (fire a λ-tower at a spine) and then `inst_chain₁₋₄`
(collapse what firing leaves behind).  This phase needs a third, and
it is worth naming the pattern: **the shared piece is always the one
that moves a spine between two descriptions of the same telescope.**

Here the two descriptions are the *public* type former's telescope,
which the use site's `VTeleTyped` is stated against, and the *checked
theorem's* statement telescope, which the fold has to apply the
theorem along.  The install's pins say the two agree binder for binder
(`sbinders[k].2.1 = tbindersM[k].2.1`, and the public-vs-model half by
`checkMemberVal_inv`'s `eqUpToNames`, which `denote_erasedEq`
(`Setlec/TTVerify/Inst.lean:265`) turns into equal denotations).  What
is missing is the step that *uses* that agreement: a spine that fits
one telescope fits the other.

That the domains agree while the *bodies* do not is the whole reason
this cannot be a rewrite — the public type former ends in a sort and
the statement ends in an equation, so only the fitting transfers, not
the residual.

**The pattern predicts the next phase's piece, and the prediction is
worth cashing early.**  If the shared piece is always the spine-mover
between two descriptions of a telescope, then the *bottoms*' shared
piece is whatever moves the **constructor** spine between the rule's
description of it and the fired redex's — and that is exactly where
§8.2's index premise lives (`ruleLhsAux` fills the recursor's index
slots with the constructor's canonical tuple; the fired form leaves
them free).  So the index-premise plumbing is not a *second* cost on
top of the bottoms' spine lemma: **it is that spine lemma.**  Two
anticipated pieces collapse into one, which is the first time this
bridge's pattern-noticing has bought a schedule change rather than an
explanation. -/

/-- Two `VExpr` telescopes met by the same spine, agreeing binder for
binder — **and both residuals named**.  Only the domains are
constrained, and only at the positions the spine reaches.

Naming the second residual is not decoration: a fold has to *continue*
past the retarget (the statement's telescope does not end where the
type former's does), so "some residual exists" is exactly the fact it
cannot use. -/
inductive TeleAlign : VExpr → VExpr → List VExpr → VExpr → VExpr → Prop
  | nil {T T' : VExpr} : TeleAlign T T' [] T T'
  | cons {A B B' x r r' : VExpr} {xs : List VExpr} :
      TeleAlign (B.inst x) (B'.inst x) xs r r' →
      TeleAlign (.pi A B) (.pi A B') (x :: xs) r r'

/-- **Retargeting a fitted spine.**  A spine that fits one telescope
fits any telescope aligned with it — at the residual the alignment
names.  The argument typings are *reused*, not re-derived, which is the
point: at a fold's use site they are hypotheses, not things the proof
can rebuild. -/
theorem VTeleTyped.retarget {Δ : List VExpr} :
    ∀ {T T' : VExpr} {xs : List VExpr} {rest rest' : VExpr},
      VTeleTyped Δ T xs rest → TeleAlign T T' xs rest rest' →
      VTeleTyped Δ T' xs rest' := by
  intro T T' xs rest rest' h
  induction h generalizing T' with
  | nil => intro ha; cases ha with | nil => exact .nil
  | @cons A B x xs rest hx _ ih =>
    intro ha
    cases ha with
    | cons ha' => exact .cons hx (ih ha')

/-- The alignment a fitting already carries: every telescope is aligned
with itself along any spine that fits it.  Note this is *not*
reflexivity of `TeleAlign` — a non-`∀` type has no domains to agree
about, so the relation is genuinely partial and the witness has to come
from a fitting. -/
theorem VTeleTyped.teleAlign {Δ : List VExpr} :
    ∀ {T rest : VExpr} {ys : List VExpr},
      VTeleTyped Δ T ys rest → TeleAlign T T ys rest rest := by
  intro T rest ys h
  induction h with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ih

/-- `retarget`, with the fitting's own residual *identified*.  A fold
needs both halves: `TeleAlign` determines the residual on each side
from the telescope and the spine, so the fitting it was handed is the
alignment's first residual, and there is nothing to reconcile. -/
theorem VTeleTyped.retarget' {Δ : List VExpr} :
    ∀ {T T' : VExpr} {xs : List VExpr} {rest r r' : VExpr},
      VTeleTyped Δ T xs rest → TeleAlign T T' xs r r' →
      rest = r ∧ VTeleTyped Δ T' xs r' := by
  intro T T' xs rest r r' h
  induction h generalizing T' r r' with
  | nil => intro ha; cases ha with | nil => exact ⟨rfl, .nil⟩
  | @cons A B x xs rest hx _ ih =>
    intro ha
    cases ha with
    | cons ha' =>
      obtain ⟨he, hf⟩ := ih ha'
      exact ⟨he, .cons hx hf⟩

/-! ## The tower, separated from the spine

**A retraction, and the reason it is one.**  `teleAlign_of_stripPis`
was first attempted as a single induction from `stripPis` straight to
`TeleAlign`, with the residual named as `VExpr.instSeq xs (k-1) R`.
It does not go through, and the obstruction is worth recording because
it is §0's fifth tell firing a second time on this same relation:

> `TeleAlign S S' ys r r' → TeleAlign (S.inst x j) (S'.inst x j) ys
> (r.inst x j) (r'.inst x j)` is **false**.

`inst_inst_comm` says the two orders differ by `x' .inst x j` on the
*other* spine elements, and a spine over an open context `Δ` has some.
So `TeleAlign` does not commute with substitution — which is the
relation announcing, once more, that **the spine is doing work**: the
statement being proved by induction must not mention it.

The fix is to slice one step earlier.  `PiTower k S S' R R'` is
`TeleAlign` with the spine deleted: `S` and `S'` are `k` nested `.pi`s
with pairwise equal domains, over bodies `R` and `R'`.  The syntactic
induction (`piTower_of_stripPis`) produces *that*, where it does go
through — a tower substituted is a tower — and the spine is fitted
afterwards in one step (`PiTower.teleAlign`), where `VExpr.instSeq`'s
recursion lines up with `TeleAlign`'s peel by construction. -/

/-- Two `VExpr` telescopes of the same depth with pairwise equal
domains — `TeleAlign` with the spine deleted. -/
inductive PiTower : Nat → VExpr → VExpr → VExpr → VExpr → Prop
  | nil {R R' : VExpr} : PiTower 0 R R' R R'
  | cons {k : Nat} {A B B' R R' : VExpr} :
      PiTower k B B' R R' → PiTower (k + 1) (.pi A B) (.pi A B') R R'

/-- A substituted tower is a tower — the step `TeleAlign` cannot
take. -/
theorem PiTower.inst :
    ∀ {k : Nat} {S S' R R' : VExpr}, PiTower k S S' R R' →
      ∀ (x : VExpr) (j : Nat),
        PiTower k (S.inst x j) (S'.inst x j)
          (R.inst x (j + k)) (R'.inst x (j + k)) := by
  intro k S S' R R' h
  induction h with
  | nil => intro x j; simpa using PiTower.nil
  | @cons k A B B' R R' _ ih =>
    intro x j
    have h1 := ih x (j + 1)
    rw [show j + 1 + k = j + (k + 1) from by omega] at h1
    exact PiTower.cons (A := A.inst x j) h1

/-- **Fitting the spine.**  A tower of depth `k` is aligned along any
spine of length `k`, and the residuals are the bodies with the spine
substituted at descending cuts — which is exactly `VExpr.instSeq`,
because that is how `TeleAlign` peels. -/
theorem PiTower.teleAlign :
    ∀ (k : Nat) {S S' R R' : VExpr}, PiTower k S S' R R' →
      ∀ {xs : List VExpr}, xs.length = k →
        TeleAlign S S' xs (VExpr.instSeq xs (k - 1) R)
          (VExpr.instSeq xs (k - 1) R') := by
  intro k
  induction k with
  | zero =>
    intro S S' R R' h xs hlen
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
    cases h
    exact .nil
  | succ k ih =>
    intro S S' R R' h xs hlen
    cases h with
    | @cons _ A B B' _ _ ht =>
      match xs, hlen with
      | x :: xs', hlen =>
        have hlen' : xs'.length = k := by simpa using hlen
        have h2 := ht.inst x 0
        rw [Nat.zero_add] at h2
        refine TeleAlign.cons ?_
        simpa only [VExpr.instSeq_cons, Nat.add_sub_cancel] using ih h2 hlen'

/-- **The syntactic half: a `stripPis` pair with matching domains
denotes to a tower.**  The two telescopes are opened together at the
*same* canonical variables — legitimate because `denote` reads neither
a binder's name nor an `fvar`'s annotation, and because `RenEqT.fvar`
says the two sides' own opening variables are related regardless.

The bodies are left where `stripPis` leaves them: with `k` loose
bvars, opened by `Expr.instSeq` at `openFvars`.  Substituting the use
site's spine is `PiTower.teleAlign`'s job, and keeping the two steps
apart is what makes this induction go through (see the retraction
above). -/
theorem piTower_of_stripPis {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {f : Name → Name} (hro : RenameOkT cval env f) :
    ∀ (k : Nat) {e e' : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr} {d : Nat} {v v' : VExpr},
      e.stripPis k = some (bs, body) →
      e'.stripPis k = some (bs', body') →
      PiDomsRenEqT f k e e' →
      denote cval env φ d e = some v →
      denote cval env φ d e' = some v' →
      ∃ R R' : VExpr,
        denote cval env φ (d + k)
          (Expr.instSeq (openFvars d k) (k - 1) body) = some R ∧
        denote cval env φ (d + k)
          (Expr.instSeq (openFvars d k) (k - 1) body') = some R' ∧
        PiTower k v v' R R' := by
  intro k
  induction k with
  | zero =>
    intro e e' bs bs' body body' d v v' h1 h2 _ hv hv'
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl⟩ := h2
    exact ⟨v, v', by simpa [openFvars, Expr.instSeq] using hv,
      by simpa [openFvars, Expr.instSeq] using hv', .nil⟩
  | succ k ih =>
    intro e e' bs bs' body body' d v v' h1 h2 hdoms hv hv'
    match e, h1, hdoms with
    | .forallE n ty b m, h1, hdoms =>
    obtain ⟨n', ty', b', m', rfl, hdty, hdb⟩ := hdoms
    simp only [Expr.stripPis] at h1 h2
    cases hs1 : b.stripPis k with
    | none => rw [hs1] at h1; exact nomatch h1
    | some p1 => ?_
    cases hs2 : b'.stripPis k with
    | none => rw [hs2] at h2; exact nomatch h2
    | some p2 => ?_
    rw [hs1] at h1
    rw [hs2] at h2
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl⟩ := h2
    -- the two heads
    rw [denote_forallE] at hv hv'
    cases hA : denote cval env φ d ty with
    | none => rw [hA] at hv; exact nomatch hv
    | some A => ?_
    rw [hA] at hv
    cases hB : denote cval env φ (d + 1) (b.instantiate1 (.fvar d n ty)) with
    | none => rw [hB] at hv; exact nomatch hv
    | some B => ?_
    rw [hB] at hv
    obtain rfl : v = .pi A B := (Option.some.inj hv).symm
    rw [RenEqT.denote hro hdty d, hA] at hv'
    cases hB' : denote cval env φ (d + 1)
        (b'.instantiate1 (.fvar d n' ty')) with
    | none => rw [hB'] at hv'; exact nomatch hv'
    | some B' => ?_
    rw [hB'] at hv'
    obtain rfl : v' = .pi A B' := (Option.some.inj hv').symm
    -- the opened tails, and their telescopes
    obtain ⟨q1, hq1⟩ := Option.isSome_iff_exists.mp
      (Expr.stripPis_instantiate1_isSome (v := .fvar d n ty) k 0
        (by rw [hs1]; rfl))
    obtain ⟨q2, hq2⟩ := Option.isSome_iff_exists.mp
      (Expr.stripPis_instantiate1_isSome (v := .fvar d n' ty') k 0
        (by rw [hs2]; rfl))
    obtain ⟨hbody1, -⟩ := Expr.stripPis_instantiate1_eq k 0 hs1 hq1
    obtain ⟨hbody2, -⟩ := Expr.stripPis_instantiate1_eq k 0 hs2 hq2
    obtain ⟨R, R', hR, hR', htow⟩ :=
      ih (bs := q1.1) (bs' := q2.1) (body := q1.2) (body' := q2.2)
        (by rw [hq1]) (by rw [hq2])
        (PiDomsRenEqT.instantiate1 RenEqT.fvar k 0 hdb) hB hB'
    simp only [Nat.zero_add] at hbody1 hbody2
    rw [hbody1] at hR
    rw [hbody2] at hR'
    refine ⟨R, R', ?_, ?_, PiTower.cons htow⟩
    · rw [show d + (k + 1) = d + 1 + k from by omega, openFvars_succ,
        Nat.add_sub_cancel, Expr.instSeq]
      rw [denote_erasedEq (Expr.instSeq_erasedEq _ (k - 1)
        (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl _)
          (show Expr.ErasedEq (Expr.fvar d Name.anonymous (.sort .zero))
            (Expr.fvar d n ty) from rfl)))]
      exact hR
    · rw [show d + (k + 1) = d + 1 + k from by omega, openFvars_succ,
        Nat.add_sub_cancel, Expr.instSeq]
      rw [denote_erasedEq (Expr.instSeq_erasedEq _ (k - 1)
        (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl _)
          (show Expr.ErasedEq (Expr.fvar d Name.anonymous (.sort .zero))
            (Expr.fvar d n' ty') from rfl)))]
      exact hR'

/-- **The alignment, assembled.**  `piTower_of_stripPis` for the
syntax, `PiTower.teleAlign` for the spine.  This is the lemma the two
folds and the two bottoms consume. -/
theorem teleAlign_of_stripPis {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {f : Name → Name} (hro : RenameOkT cval env f) (k : Nat)
    {e e' : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
    {body body' : Expr} {d : Nat} {v v' : VExpr} {xs : List VExpr}
    (h1 : e.stripPis k = some (bs, body))
    (h2 : e'.stripPis k = some (bs', body'))
    (hdoms : PiDomsRenEqT f k e e')
    (hv : denote cval env φ d e = some v)
    (hv' : denote cval env φ d e' = some v')
    (hlen : xs.length = k) :
    ∃ R R' : VExpr,
      denote cval env φ (d + k)
        (Expr.instSeq (openFvars d k) (k - 1) body) = some R ∧
      denote cval env φ (d + k)
        (Expr.instSeq (openFvars d k) (k - 1) body') = some R' ∧
      TeleAlign v v' xs (VExpr.instSeq xs (k - 1) R)
        (VExpr.instSeq xs (k - 1) R') := by
  obtain ⟨R, R', hR, hR', htow⟩ :=
    piTower_of_stripPis hro k h1 h2 hdoms hv hv'
  exact ⟨R, R', hR, hR', htow.teleAlign k hlen⟩


/-! ## The pinned parameter tuple

Every pinned domain of a capability statement is the *same* thing: the
model former applied to the statement's parameter variables, at some
bvar shift.  Opened, denoted and fitted with the use site's spine it
becomes the public former applied to that spine — which is exactly the
type `UnitLawTT`'s two subjects are given at.

Done once here, at a shift `c`, because the unit statement uses it
three times (the `x` domain at `c = 0`, the `y` domain at `c = 1`, the
equation's type slot at `c = 2`) and the eta statement uses it again. -/

/-- Indexing a list by its own `range` is mapping it. -/
private theorem map_range_getD {α β : Type} [Inhabited α] (xs : List α)
    (g : α → β) :
    (List.range xs.length).map (fun l => g (xs.getD l default)) = xs.map g := by
  refine List.ext_getElem? ?_
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem?_range h, List.getElem?_eq_getElem h]
    simp [List.getD, List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
    rfl

/-- **The parameter tuple, opened and denoted.**  The `k`-th pinned
parameter variable is the `k`-th opening variable, whose denotation at
depth `d + nP + c` is `bvar (c + nP - 1 - k)`. -/
theorem denote_paramTuple {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d nP c dd : Nat} {n : Name} {us : List Level} {vc : VExpr}
    (hdd : dd = d + nP + c)
    (hc : denote cval env φ dd (.const n us) = some vc) :
    denote cval env φ dd
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (Expr.mkAppN (.const n us)
          ((List.range nP).map fun l => Expr.bvar (nP - 1 - l)))) =
      some (VExpr.mkAppN vc
        ((List.range nP).map fun l => VExpr.bvar (c + nP - 1 - l))) := by
  subst hdd
  rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
  refine denote_mkAppN ?_ hc
  rw [List.map_map]
  refine DenoteSpine.map ?_
  intro l hl
  have hlt : l < nP := by simpa using List.mem_range.mp hl
  have hb := Expr.instSeq_bvar (openFvars d nP) (nP - 1) (nP - 1 - l)
    (openFvars_bounded d nP) (by omega) (by simp; omega)
  rw [show nP - 1 - (nP - 1 - l) = l from by omega,
    openFvars_getElem? hlt] at hb
  simp only [Function.comp_apply]
  rw [← Option.some.inj hb, denote_fvar]
  simp only [Option.some.injEq, VExpr.bvar.injEq]
  omega

/-- **The parameter tuple, fitted.**  The same tuple with the use
site's spine substituted, lifted past the `c` binders the residual sits
under — lifts the consumer's own `inst` absorbs. -/
theorem instSeq_paramTuple {vc : VExpr} (hvc : VExpr.Closed vc)
    {nP c t : Nat} {xs : List VExpr} (ht : t = c + nP - 1)
    (hlen : xs.length = nP) :
    VExpr.instSeq xs t
      (VExpr.mkAppN vc ((List.range nP).map fun l =>
        VExpr.bvar (c + nP - 1 - l))) =
      VExpr.mkAppN vc (xs.map (VExpr.liftN c · 0)) := by
  subst ht
  rw [VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hvc, List.map_map]
  congr 1
  rw [← hlen, ← map_range_getD xs (VExpr.liftN c · 0)]
  refine List.map_congr_left ?_
  intro l hl
  have hlt : l < xs.length := by simpa using List.mem_range.mp hl
  simp only [Function.comp_apply]
  rw [show c + xs.length - 1 - l = c + (xs.length - 1 - l) from by omega]
  rw [VExpr.instSeq_bvar_hit xs c (xs.length - 1 - l)
    (xs.getD l default)
    (by rw [show xs.length - 1 - (xs.length - 1 - l) = l from by omega]
        simp [List.getD, List.getElem?_eq_getElem hlt]) (by omega)]


/-- `instSeq` at `nP - 1 + 1` is `instSeq` at `nP` — trivially when
`nP ≥ 1`, and vacuously when the argument list is empty. -/
private theorem instSeq_len_succ {args : List Expr} {nP : Nat}
    (h : args.length = nP) (e : Expr) :
    Expr.instSeq args (nP - 1 + 1) e = Expr.instSeq args nP e := by
  rcases Nat.eq_zero_or_pos nP with h0 | h0
  · subst h0
    rw [List.eq_nil_of_length_eq_zero h]
    rfl
  · rw [show nP - 1 + 1 = nP from by omega]

/-- The same, on the term side. -/
private theorem instSeqV_len_succ {xs : List VExpr} {nP : Nat}
    (h : xs.length = nP) (e : VExpr) :
    VExpr.instSeq xs (nP - 1 + 1) e = VExpr.instSeq xs nP e := by
  rcases Nat.eq_zero_or_pos nP with h0 | h0
  · subst h0
    rw [List.eq_nil_of_length_eq_zero h]
    rfl
  · rw [show nP - 1 + 1 = nP from by omega]

/-- Instantiating a parameter tuple below its range: every index drops
by one. -/
private theorem paramTuple_inst (Tm : Name) (lvls : List Level) (nP c : Nat)
    (w : Expr) (g g' : Nat → Nat)
    (hg : ∀ k, k < nP → c < g k ∧ g k - 1 = g' k) :
    (Expr.mkAppN (.const Tm lvls)
        ((List.range nP).map fun k => Expr.bvar (g k))).instantiate1 w c =
      Expr.mkAppN (.const Tm lvls)
        ((List.range nP).map fun k => Expr.bvar (g' k)) := by
  rw [Expr.mkAppN_instantiate1]
  congr 1
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro k hk
  obtain ⟨h1, h2⟩ := hg k (List.mem_range.mp hk)
  simp only [Function.comp_apply, Expr.instantiate1]
  rw [if_neg (by omega), if_pos (by omega), h2]

/-- **The unit statement's residual, computed.**  Opening the `nP`
parameter binders and denoting leaves the two subject domains and the
equation, all three built from the same parameter tuple at shifts
`0`, `1` and `2`. -/
theorem denote_unitResidual {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d nP : Nat} {nx ny : Name} {mx my : BinderMeta} {Tm : Name}
    {lvls : List Level} {lA : Level} {vT veq : VExpr}
    (hcT : ∀ dd : Nat, denote cval env φ dd (.const Tm lvls) = some vT)
    (hcE : ∀ dd : Nat, denote cval env φ dd (.const eqName [lA]) = some veq) :
    denote cval env φ (d + nP)
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (.forallE nx
          (Expr.mkAppN (.const Tm lvls)
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)))
          (.forallE ny
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map fun k => Expr.bvar (nP - k)))
            (Expr.mkAppN (.const eqName [lA])
              [Expr.mkAppN (.const Tm lvls)
                ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)),
               Expr.bvar 1, Expr.bvar 0]) my) mx)) =
      some (.pi
        (VExpr.mkAppN vT ((List.range nP).map fun l => VExpr.bvar (0 + nP - 1 - l)))
        (.pi
          (VExpr.mkAppN vT ((List.range nP).map fun l => VExpr.bvar (1 + nP - 1 - l)))
          (VExpr.mkAppN veq
            [VExpr.mkAppN vT
              ((List.range nP).map fun l => VExpr.bvar (2 + nP - 1 - l)),
             VExpr.bvar 1, VExpr.bvar 0]))) := by
  have hargsb := openFvars_bounded d nP
  have hargslen := openFvars_length d nP
  have hle : (openFvars d nP).length ≤ nP - 1 + 1 := by rw [hargslen]; omega
  -- the outer binder
  rw [Expr.instSeq_forallE _ _ _ _ _ _ hle, instSeq_len_succ hargslen,
    denote_forallE,
    denote_paramTuple (c := 0) (d := d) (nP := nP) (dd := d + nP) rfl
      (hcT (d + nP))]
  -- open it, and push the opening past the parameter substitution
  rw [instSeq_instantiate1_in (b := Expr.fvar (d + nP) nx
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))))) rfl
    _ nP hargsb (Nat.le_of_eq hargslen)]
  -- the second binder: the `y` domain is the `x` domain, one index down
  rw [show (Expr.forallE ny
        (Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map fun k => Expr.bvar (nP - k)))
        (Expr.mkAppN (.const eqName [lA])
          [Expr.mkAppN (.const Tm lvls)
            ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)),
           Expr.bvar 1, Expr.bvar 0]) my).instantiate1
        (Expr.fvar (d + nP) nx
          (Expr.instSeq (openFvars d nP) (nP - 1)
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))))) 0 =
      Expr.forallE ny
        (Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)))
        ((Expr.mkAppN (.const eqName [lA])
          [Expr.mkAppN (.const Tm lvls)
            ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)),
           Expr.bvar 1, Expr.bvar 0]).instantiate1
          (Expr.fvar (d + nP) nx
            (Expr.instSeq (openFvars d nP) (nP - 1)
              (Expr.mkAppN (.const Tm lvls)
                ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))))) 1) my from by
    show Expr.forallE ny _ _ my = _
    rw [paramTuple_inst Tm lvls nP 0 _ (fun k => nP - k) (fun k => nP - 1 - k)
      (fun k hk => ⟨by omega, by omega⟩)]]
  -- the second binder
  rw [Expr.instSeq_forallE _ _ _ _ _ _ hle, instSeq_len_succ hargslen,
    denote_forallE,
    denote_paramTuple (c := 1) (d := d) (nP := nP) (dd := d + nP + 1) rfl
      (hcT (d + nP + 1))]
  rw [instSeq_instantiate1_in (b := Expr.fvar (d + nP + 1) ny
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))))) rfl
    _ nP hargsb (Nat.le_of_eq hargslen)]
  -- the equation: both subject slots become the opening variables, and
  -- the type slot drops back to the parameter tuple
  have hEqBody : ((Expr.mkAppN (.const eqName [lA])
        [Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map (fun k => Expr.bvar (nP + 1 - k))),
         Expr.bvar 1, Expr.bvar 0]).instantiate1
        (Expr.fvar (d + nP) nx
          (Expr.instSeq (openFvars d nP) (nP - 1)
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k)))))) 1).instantiate1
        (Expr.fvar (d + nP + 1) ny
          (Expr.instSeq (openFvars d nP) (nP - 1)
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k)))))) 0 =
      Expr.mkAppN (.const eqName [lA])
        [Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))),
         Expr.fvar (d + nP) nx
          (Expr.instSeq (openFvars d nP) (nP - 1)
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))))),
         Expr.fvar (d + nP + 1) ny
          (Expr.instSeq (openFvars d nP) (nP - 1)
            (Expr.mkAppN (.const Tm lvls)
              ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k)))))] := by
    rw [Expr.mkAppN_instantiate1, Expr.mkAppN_instantiate1]
    simp only [List.map_cons, List.map_nil]
    rw [paramTuple_inst Tm lvls nP 1 _ (fun k => nP + 1 - k) (fun k => nP - k)
      (fun k hk => ⟨by omega, by omega⟩),
      paramTuple_inst Tm lvls nP 0 _ (fun k => nP - k) (fun k => nP - 1 - k)
      (fun k hk => ⟨by omega, by omega⟩)]
    rfl
  rw [hEqBody]
  -- denote the equation spine
  rw [Expr.instSeq_mkAppN]
  simp only [List.map_cons, List.map_nil]
  rw [Expr.instSeq_eq_self (e := Expr.const eqName [lA]) _ _ (by rfl),
    Expr.instSeq_eq_self (e := Expr.fvar (d + nP) nx _) _ _ (by rfl),
    Expr.instSeq_eq_self (e := Expr.fvar (d + nP + 1) ny _) _ _ (by rfl)]
  rw [denote_mkAppN (vs := [VExpr.mkAppN vT
        ((List.range nP).map fun l => VExpr.bvar (2 + nP - 1 - l)),
      VExpr.bvar 1, VExpr.bvar 0])
    (.cons (denote_paramTuple (c := 2) (d := d) (nP := nP)
        (dd := d + nP + 1 + 1) rfl (hcT (d + nP + 1 + 1)))
      (.cons (by rw [denote_fvar]
                 simp only [Option.some.injEq, VExpr.bvar.injEq]
                 omega)
        (.cons (by rw [denote_fvar]
                   simp only [Option.some.injEq, VExpr.bvar.injEq]
                   omega) .nil)))
    (hcE (d + nP + 1 + 1))]

/-- The unit residual, fitted with the use site's spine.  The three
parameter tuples come back as the *same* spine at three lifts, which
is what the two `VTeleTyped.cons` steps then absorb. -/
theorem instSeq_unitResidual {vT veq : VExpr} (hvT : VExpr.Closed vT)
    (hveq : VExpr.Closed veq) {nP : Nat} {xs : List VExpr}
    (hlen : xs.length = nP) :
    VExpr.instSeq xs (nP - 1)
      (.pi
        (VExpr.mkAppN vT
          ((List.range nP).map fun l => VExpr.bvar (0 + nP - 1 - l)))
        (.pi
          (VExpr.mkAppN vT
            ((List.range nP).map fun l => VExpr.bvar (1 + nP - 1 - l)))
          (VExpr.mkAppN veq
            [VExpr.mkAppN vT
              ((List.range nP).map fun l => VExpr.bvar (2 + nP - 1 - l)),
             VExpr.bvar 1, VExpr.bvar 0]))) =
      .pi (VExpr.mkAppN vT xs)
        (.pi (VExpr.mkAppN vT (xs.map (VExpr.liftN 1 · 0)))
          (VExpr.mkAppN veq
            [VExpr.mkAppN vT (xs.map (VExpr.liftN 2 · 0)),
             VExpr.bvar 1, VExpr.bvar 0])) := by
  rw [VExpr.instSeq_pi _ _ _ _ (by rw [hlen]; omega), instSeqV_len_succ hlen,
    VExpr.instSeq_pi _ _ _ _ (by rw [hlen]; omega),
    instSeq_paramTuple hvT (c := 0) (by omega) hlen,
    instSeq_paramTuple hvT (c := 1) (by omega) hlen,
    VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hveq]
  simp only [List.map_cons, List.map_nil]
  rw [instSeq_paramTuple hvT (c := 2) (by omega) hlen,
    VExpr.instSeq_bvar_lt xs (nP + 1) 1 (by rw [hlen]; omega),
    VExpr.instSeq_bvar_lt xs (nP + 1) 0 (by rw [hlen]; omega)]
  congr 2
  rw [show (fun x => VExpr.liftN 0 x 0) = (id : VExpr → VExpr) from by
    funext x; exact VExpr.liftN_zero x 0]
  exact List.map_id xs

/-! ## `UnitFoldTT`

The first of §14.3's five obligations.  Hypotheses are the *unpacked*
pins, exactly as `unit_rule_fold` takes them — a fold runs at the
extended environment of a block member's install, where the `EnvTT`
being built is precisely what is not yet available.

**The unitlike theorem's *name* is not a hypothesis**, and that is a
finding rather than an omission: the fold consumes only its pinned type
shape and its inhabitation (`hthmty`), never `env.find?`.  The `find?`
fact was written in from `unit_rule_fold`, which needs it for
`interpClosed_extend_fresh`; the bridge's `denote_depth_closed` needs
nothing.  Dropped rather than `_`-prefixed, per §8.2 — a hypothesis a
proof does not read is a claim about the contract that is not true.

**`hTmSort` is a pin the checker does not yet make.**  `EqLawTT` fires
`eqValT`'s first β-step, whose premise is `⊢ Â : Sort (ψ uNT)` with
`ψ uNT = ⟦ℓA⟧` — the level the *statement's* `Eq.{ℓA}` carries.  The
set model gets that membership from `AnnotOk`, which this bridge drops;
inversion cannot recover it, because reading the sort back out of the
`Eq` spine needs Π-injectivity, and Π-injectivity is refuted
(`Setlec/TTVerify/Inversion.lean`).  So it has to be *supplied*, and
the cheapest supplier is a syntactic pin the checker already computes
and discards: `checkUnitThm` binds the model type's residual (`_`) and
the equation's level (`_ℓ`) and compares neither.  With
`tbodyM = .sort ℓA` in hand the fact is derived here, from
`EnvTT.has_type` at `T._model` and a *second* use of
`teleAlign_of_stripPis` — which is why the hypothesis is isolated to
one line rather than threaded.  Recorded in `DESIGN.md`; until the pin
lands, `DeclIndTT` cannot discharge it. -/

set_option maxHeartbeats 1600000 in
/-- **The unit-like law, from the checked `T._model.unitlike`
theorem.**  Transpose of `unit_rule_fold`. -/
theorem UnitFoldTT {env : Env} {cval : TConstVal}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (hvp : ValParams env cval)
    (heqlaw : EqLawTT env cval)
    {f : Name → Name} (hro : RenameOkT cval env f)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    {tcv cvmT : ConstantVal} {mvalT : Expr}
    {hmT : ReducibilityHint}
    {sbinders tbindersM : List (Name × Expr × BinderMeta)}
    {sbody tbodyM tySlot : Expr} {lA : Level}
    (hTmE : env.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmT))
    (hTmlps : cvmT.levelParams = cvT.levelParams)
    (heqfE : env.find? eqName = some eqA)
    (hS_strip : tcv.type.stripPis (caps.unitParams + 2) =
      some (sbinders, sbody))
    (hTm_strip : cvmT.type.stripPis caps.unitParams = some (tbindersM, tbodyM))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      k < caps.unitParams → sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1)
    (hxdom : ∃ nx mx, sbinders[caps.unitParams]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (cvT.levelParams.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - 1 - k)), mx))
    (hydom : ∃ ny my, sbinders[caps.unitParams + 1]? = some (ny,
      Expr.mkAppN (.const (T.str "_model") (cvT.levelParams.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - k)), my))
    (hsbody : sbody =
      Expr.mkAppN (.const eqName [lA]) [tySlot, .bvar 1, .bvar 0])
    (htySlot : tySlot = Expr.mkAppN
      (.const (T.str "_model") (cvT.levelParams.map .param))
      ((List.range caps.unitParams).map fun k =>
        Expr.bvar (caps.unitParams + 1 - k)))
    (hTmSort : tbodyM = Expr.sort lA)
    (hSw : tcv.type.hasFvar = false)
    (hSb : tcv.type.looseBVarsBounded 0 = true)
    (hTmw : cvmT.type.hasFvar = false)
    (hTmb : cvmT.type.looseBVarsBounded 0 = true)
    (hren : Expr.eqUpToNames (cvT.type.renameConsts f) cvmT.type = true)
    (hthmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval env psi tcv.type = some t ∧
      HasType [] (cval tcv.name psi) t)
    (hTmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval env psi cvmT.type = some t ∧
      HasType [] (cval (T.str "_model") psi) t)
    (hvT : ∀ psi : Name → Nat, cval T psi = cval (T.str "_model") psi) :
    UnitLawTT env cval T cvT caps := by
  intro φ d Δ us xs TV rest B B' hlen hTV hfit hB hB'
  obtain ⟨nx, mx, hxdom'⟩ := hxdom
  obtain ⟨ny, my, hydom'⟩ := hydom
  subst hsbody htySlot hTmSort
  -- the ambient level assignment
  have hcTm : ∀ dd : Nat,
      denote cval env (Level.substFn φ cvT.levelParams us) dd
        (.const (T.str "_model") (cvT.levelParams.map .param)) =
      some (cval (T.str "_model") (Level.substFn φ cvT.levelParams us)) := by
    intro dd
    rw [denote_const, hTmE]
    dsimp only
    rw [if_pos (by simp [ConstantInfo.toConstantVal, hTmlps])]
    have hsub : Level.substFn (Level.substFn φ cvT.levelParams us)
        (ConstantInfo.defnInfo cvmT mvalT hmT).toConstantVal.levelParams
        (List.map Level.param cvT.levelParams) =
        Level.substFn φ cvT.levelParams us := by
      have hlp : (ConstantInfo.defnInfo cvmT mvalT hmT).toConstantVal.levelParams
          = cvT.levelParams := by simp [ConstantInfo.toConstantVal, hTmlps]
      rw [hlp]
      funext p
      exact Level.substFn_map_param
    rw [hsub]
  have hcEq : ∀ dd : Nat,
      denote cval env (Level.substFn φ cvT.levelParams us) dd
        (.const eqName [lA]) =
      some (cval eqName (Level.substFn
        (Level.substFn φ cvT.levelParams us) eqA.toConstantVal.levelParams
        [lA])) := by
    intro dd
    rw [denote_const, heqfE]
    dsimp only
    rw [if_pos (by rfl)]
  -- (1) the public telescope, level-instantiated away
  rw [denote_instLevels hvp (ks := cvT.levelParams) (us := us) φ d cvT.type]
    at hTV
  -- (2) the public telescope's own strip, through the rename chain
  obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
    Expr.ErasedEq.stripPis_inv caps.unitParams
      (Expr.ErasedEq.of_eqUpToNames hren) hTm_strip
  obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
    Expr.stripPis_renameConsts_inv (f := f) caps.unitParams hstripR
  have hdomsPub : ∀ (i : Nat) (b₁ b₂ : Name × Expr × BinderMeta),
      tbinders[i]? = some b₁ → tbindersM[i]? = some b₂ →
      RenEqT f b₁.2.1 b₂.2.1 := by
    intro i b₁ b₂ hb₁ hb₂
    have hbR : bsR[i]? = some (b₁.1, (b₁.2.1).renameConsts f, b₁.2.2) := by
      rw [hbsmap, List.getElem?_map, hb₁]; rfl
    exact (hdomsR i _ _ hbR hb₂).1
  -- (3) the statement's prefix strip, with the pinned domains
  obtain ⟨ny', dy', my', hyb, hstrip1⟩ :=
    Expr.stripPis_snoc (caps.unitParams + 1) hS_strip
  obtain ⟨nx', dx', mx', hxb, hstrip0⟩ :=
    Expr.stripPis_snoc caps.unitParams hstrip1
  have hxb' : sbinders[caps.unitParams]? = some (nx', dx', mx') := by
    rw [← List.getElem?_take_of_lt (show caps.unitParams < caps.unitParams + 1
      by omega)]
    exact hxb
  have hdx : dx' = Expr.mkAppN
      (.const (T.str "_model") (cvT.levelParams.map .param))
      ((List.range caps.unitParams).map fun k =>
        Expr.bvar (caps.unitParams - 1 - k)) :=
    congrArg (fun t => t.2.1) (Option.some.inj (hxb'.symm.trans hxdom'))
  have hdy : dy' = Expr.mkAppN
      (.const (T.str "_model") (cvT.levelParams.map .param))
      ((List.range caps.unitParams).map fun k =>
        Expr.bvar (caps.unitParams - k)) :=
    congrArg (fun t => t.2.1) (Option.some.inj (hyb.symm.trans hydom'))
  subst hdx hdy
  -- (4) the two derivations the invariant supplies
  obtain ⟨Tstmt, hTstmtC, hthmv⟩ := hthmty (Level.substFn φ cvT.levelParams us)
  have hTstmt : denote cval env (Level.substFn φ cvT.levelParams us) d
      tcv.type = some Tstmt := by
    rw [denote_depth_closed hcl hSw hSb d]; exact hTstmtC
  obtain ⟨Tmod, hTmodC, hTmodv⟩ := hTmty (Level.substFn φ cvT.levelParams us)
  have hTmod : denote cval env (Level.substFn φ cvT.levelParams us) d
      cvmT.type = some Tmod := by
    rw [denote_depth_closed hcl hTmw hTmb d]; exact hTmodC
  -- (5) the two domain-agreement prefixes
  have hpiM : PiDomsRenEqT f caps.unitParams cvT.type cvmT.type :=
    PiDomsRenEqT.of_pointwise caps.unitParams hT_strip hTm_strip hdomsPub
  have hpiS : PiDomsRenEqT f caps.unitParams cvT.type tcv.type := by
    refine PiDomsRenEqT.of_pointwise caps.unitParams hT_strip hstrip0 ?_
    intro i b₁ b₂ hb₁ hb₂
    have hi : i < caps.unitParams := by
      rcases Nat.lt_or_ge i caps.unitParams with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [Expr.stripPis_length caps.unitParams hT_strip]; omega)] at hb₁
        exact nomatch hb₁
    have hilt : i < tbindersM.length := by
      rw [Expr.stripPis_length caps.unitParams hTm_strip]; exact hi
    have hbM : tbindersM[i]? = some tbindersM[i] :=
      List.getElem?_eq_getElem hilt
    rw [List.getElem?_take_of_lt hi,
      List.getElem?_take_of_lt (show i < caps.unitParams + 1 by omega)] at hb₂
    rw [hsdoms i b₂ tbindersM[i] hi hb₂ hbM]
    exact hdomsPub i b₁ tbindersM[i] hb₁ hbM
  -- (6) the two alignments, and the retarget
  obtain ⟨R, RS, hR, hRS, halignS⟩ :=
    teleAlign_of_stripPis hro caps.unitParams hT_strip hstrip0 hpiS hTV hTstmt
      hlen
  obtain ⟨R', RM, hR', hRM, halignM⟩ :=
    teleAlign_of_stripPis hro caps.unitParams hT_strip hTm_strip hpiM hTV hTmod
      hlen
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  obtain ⟨-, hfitS⟩ := hfit.retarget' halignS
  obtain ⟨-, hfitM⟩ := hfit.retarget' halignM
  -- (7) the type slot's sort, off the pending pin
  obtain rfl : RM = VExpr.sort (Level.eval (Level.substFn φ cvT.levelParams us)
      lA) := by
    rw [Expr.instSeq_eq_self _ _ (by rfl), denote_sort] at hRM
    exact (Option.some.inj hRM).symm
  rw [VExpr.instSeq_sort] at hfitM
  have hAsort : HasType Δ
      (VExpr.mkAppN (cval (T.str "_model")
        (Level.substFn φ cvT.levelParams us)) xs)
      (.sort (Level.eval (Level.substFn φ cvT.levelParams us) lA)) :=
    hfitM.appN (HasType.weakenNil hTmodv Δ)
  -- (8) the residual, computed and fitted
  rw [denote_unitResidual hcTm hcEq] at hRS
  obtain rfl := Option.some.inj hRS
  rw [instSeq_unitResidual (hcl _ _) (hcl _ _) hlen] at hfitS
  -- (9) fire the theorem at the two subjects
  simp only [hvT] at hB hB'
  have hpsi2 : Level.substFn (Level.substFn φ cvT.levelParams us)
      eqA.toConstantVal.levelParams [lA] uNT =
      Level.eval (Level.substFn φ cvT.levelParams us) lA := rfl
  refine Deq.ofEqThmClosed heqlaw heqfE
    (Level.substFn (Level.substFn φ cvT.levelParams us)
      eqA.toConstantVal.levelParams [lA]) (args := xs ++ [B, B']) hthmv ?_
    (by rw [hpsi2]; exact hAsort) hB hB'
  refine hfitS.append (VTeleTyped.cons hB (VTeleTyped.cons ?_ ?_))
  · have habs : (xs.map (VExpr.liftN 1 · 0)).map (VExpr.inst · B 0) = xs := by
      rw [List.map_map]
      refine Eq.trans (List.map_congr_left ?_) (List.map_id xs)
      intro x _
      show VExpr.inst (VExpr.liftN 1 x 0) B 0 = x
      rw [VExpr.inst_liftN_absorb x (Nat.zero_le 0) (Nat.le_refl 0) B,
        VExpr.liftN_zero]
    rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed (hcl _ _), habs]
    exact hB'
  · have habs2 : (xs.map (VExpr.liftN 2 · 0)).map (VExpr.inst · B 1) =
        xs.map (VExpr.liftN 1 · 0) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro x _
      show VExpr.inst (VExpr.liftN 2 x 0) B 1 = VExpr.liftN 1 x 0
      exact VExpr.inst_liftN_absorb x (Nat.zero_le 1) (by omega) B
    have habs3 : (xs.map (VExpr.liftN 1 · 0)).map (VExpr.inst · B' 0) = xs := by
      rw [List.map_map]
      refine Eq.trans (List.map_congr_left ?_) (List.map_id xs)
      intro x _
      show VExpr.inst (VExpr.liftN 1 x 0) B' 0 = x
      rw [VExpr.inst_liftN_absorb x (Nat.zero_le 0) (Nat.le_refl 0) B',
        VExpr.liftN_zero]
    have hres : ∀ VE VT : VExpr, VExpr.Closed VE → VExpr.Closed VT →
        ((VExpr.mkAppN VE [VExpr.mkAppN VT (xs.map (VExpr.liftN 2 · 0)),
            VExpr.bvar 1, VExpr.bvar 0]).inst B 1).inst B' 0 =
          VExpr.mkAppN VE [VExpr.mkAppN VT xs, B, B'] := by
      intro VE VT hVE hVT
      have h1 : (VExpr.mkAppN VE [VExpr.mkAppN VT (xs.map (VExpr.liftN 2 · 0)),
          VExpr.bvar 1, VExpr.bvar 0]).inst B 1 =
          VExpr.mkAppN VE [VExpr.mkAppN VT (xs.map (VExpr.liftN 1 · 0)),
            VExpr.liftN 1 B 0, VExpr.bvar 0] := by
        rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVE]
        simp only [List.map_cons, List.map_nil]
        rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVT, habs2]
        simp only [VExpr.inst_bvar, Nat.lt_irrefl, if_false, Nat.zero_lt_one,
          if_true]
      rw [h1, VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVE]
      simp only [List.map_cons, List.map_nil]
      rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVT, habs3,
        VExpr.inst_liftN_absorb B (Nat.zero_le 0) (Nat.le_refl 0) B',
        VExpr.liftN_zero]
      simp only [VExpr.inst_bvar, Nat.lt_irrefl, if_false, if_true,
        VExpr.liftN_zero]
    simp only [Nat.zero_add]
    rw [hres _ _ (hcl _ _) (hcl _ _)]
    exact VTeleTyped.nil

end Setlec.TTVerify
