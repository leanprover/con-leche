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
of `EtaFoldTT`, `UnitFoldTT` and `ProjBottomTT`. -/
theorem Deq.ofEqThm {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Δ : List VExpr} {v Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType Δ v Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (m.cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.intro (Setlec.TT.Deq.conv (hfit.appN hv)
    (m.eq_law hE ψ Δ A a b hA ha hb))

/-- The same, when the theorem is a *closed* constant's valuation —
which is how every checked `_model.*` theorem reaches a use site. -/
theorem Deq.ofEqThmClosed {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) {n : Name}
    {Δ : List VExpr} {Tstmt A a b : VExpr} {args : List VExpr}
    (hv : HasType [] (m.cval n ψ) Tstmt)
    (hfit : VTeleTyped Δ Tstmt args
      (VExpr.mkAppN (m.cval eqName ψ) [A, a, b]))
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ a b :=
  Deq.ofEqThm m hE ψ (HasType.weakenNil hv Δ) hfit hA ha hb

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

end Setlec.TTVerify
