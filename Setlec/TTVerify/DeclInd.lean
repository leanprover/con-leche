import Setlec.TTVerify.DeclBasis
import Setlec.Verify.Extend.Iota
import Setlec.Verify.Denote.TeleOpen
import Setlec.Verify.Denote.IndFrame

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
    (hA : HasType Δ A (.sort (ψ uN))) (ha : HasType Δ a A)
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
    (hA : HasType Δ A (.sort (ψ uN))) (ha : HasType Δ a A)
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
    EtaPins mode env cvT.name cvT.levelParams (indBlockCaps mode env cvT cvC nP nF) := by
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
(`Setlec/Verify/Denote/Inst.lean:265`) turns into equal denotations).  What
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


/-! ## The one premise no pin supplies (task #135)

Named once, and consumed by every obligation of `DeclIndTT`, so that
the checker-side landing is a **single supplier change** rather than
one edit per obligation.  `DESIGN.md` §14.7.4 has the argument: the
`Eq` law's first β-step wants the equation's type slot at the sort its
`Eq.{ℓ}` names, the set model reads that off `AnnotOk`, and no
inversion can recover it because Π-injectivity is refuted.

Measured before being asked for: 1 069 sites across the whole fixture
corpus, zero counterexamples. -/

/-- **Task #135's conjunct — landed.**  A modeled former's telescope
residual is the sort the capability statement's `Eq.{ℓ}` names.

`checkEtaThmF`/`checkUnitThmF` computed both sides and compared
neither; #135 added the comparison, and `EtaPins`' last conjunct in
each half is `tbodyM = Expr.sort ℓA` — this definition verbatim, so
`checkEtaThm_inv`/`checkUnitThm_inv` discharge these hypotheses by
`exact`.  Kept as a *definition* rather than an inlined equation so
that `grep StatementSortPin` stays the list of sites it serves. -/
def StatementSortPin (tbody : Expr) (l : Level) : Prop :=
  tbody = Expr.sort l

/-! **Task #136's conjunct** (`CtorResidualPin`, now defined in
`Setlec/TTVerify/EnvTT.lean` where the `ctor_residual` field consumes
it).  An eta-capable modeled family's
constructor returns *the family applied to its parameters*.

This is literally the check `checkDirectCtor` already makes on the
direct path (`Setlec/Kernel/Checker.lean:125`,
`cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF`), moved to
the modeled path and **guarded on the eta capability** — the guard is
not cosmetic: unguarded, the conjunct is *refuted by the corpus*, at
99 indexed families (`Acc`, `HEq`, `Int.NonNeg`, `IndexedSingleton`,
`SortElimProp`, …) whose residual is `T p⃗ i⃗` and which must keep
installing with `eta = false`.  Guarded it is corpus-clean: 978/978
eta-capable and 91/91 unit-capable blocks satisfy it.  The table is
`DESIGN.md` §14.7.9.

**Spelling matters here, so it is fixed in advance.**  This is the
shape the bridge consumes — `stripPis` at the *full* constructor
telescope, binder list unconstrained, residual literally `directFam` —
so that the discharge of `EtaFoldTT`'s `EtaRhsTyped` is `exact` from
the inversion, the way `StatementSortPin` made #135's swap `exact`.
The suffix `nF` in `directFam …  nP nF` is the field count, matching
`checkDirectCtor`'s call and *not* the `0` used for a recursor's major
premise.

Stated over the *public* constructor's stored `ConstantVal`: the model
side cannot serve it, because a model's own residual is unpinned
(models are stored opaque), which is what §14.7.9's reading
established. -/

/-- **The equation type slot's sort, derived from the pin.**  The
spine lemma paying twice: a *second* alignment, this time between the
public former's telescope and the model former's, carries the use
site's fitting onto the model type — whose residual the pin says is a
sort.  Shared verbatim by `UnitFoldTT` and `EtaFoldTT`, whose type
slots are both the model former applied to the parameter spine. -/
theorem eqSlotSort_of_sortPin {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {f : Name → Name} (hro : RenameOkT cval env f)
    {nP : Nat} {tyPub tyMod : Expr}
    {bsP bsM : List (Name × Expr × BinderMeta)} {bodyP bodyM : Expr}
    {lA : Level} {vMod : VExpr} {d : Nat} {Δ : List VExpr}
    {xs : List VExpr} {TV rest Tmod : VExpr}
    (hP_strip : tyPub.stripPis nP = some (bsP, bodyP))
    (hM_strip : tyMod.stripPis nP = some (bsM, bodyM))
    (hpin : StatementSortPin bodyM lA)
    (hpi : PiDomsRenEqT f nP tyPub tyMod)
    (hTV : denote cval env φ d tyPub = some TV)
    (hTmod : denote cval env φ d tyMod = some Tmod)
    (hTmodv : HasType [] vMod Tmod)
    (hfit : VTeleTyped Δ TV xs rest) (hlen : xs.length = nP) :
    HasType Δ (VExpr.mkAppN vMod xs) (.sort (Level.eval φ lA)) := by
  obtain ⟨R, RM, hR, hRM, halign⟩ :=
    teleAlign_of_stripPis hro nP hP_strip hM_strip hpi hTV hTmod hlen
  obtain ⟨-, hfitM⟩ := hfit.retarget' halign
  obtain rfl : RM = VExpr.sort (Level.eval φ lA) := by
    rw [show bodyM = Expr.sort lA from hpin,
      Expr.instSeq_eq_self _ _ (by rfl), denote_sort] at hRM
    exact (Option.some.inj hRM).symm
  rw [VExpr.instSeq_sort] at hfitM
  exact hfitM.appN (HasType.weakenNil hTmodv Δ)


/-! ## The pinned parameter tuple

Every pinned domain of a capability statement is the *same* thing: the
model former applied to the statement's parameter variables, at some
bvar shift.  Opened, denoted and fitted with the use site's spine it
becomes the public former applied to that spine — which is exactly the
type `UnitLawTT`'s two subjects are given at.

Done once here, at a shift `c`, because the unit statement uses it
three times (the `x` domain at `c = 0`, the `y` domain at `c = 1`, the
equation's type slot at `c = 2`) and the eta statement uses it again. -/

/- `map_range_getD` relocated to `Setlec/Verify/Denote/IndFrame.lean`. -/

/-- **The parameter tuple, opened and denoted.**  The `k`-th pinned
parameter variable is the `k`-th opening variable, whose denotation at
depth `d + nP + c` is `bvar (c + nP - 1 - k)`. -/
theorem denote_paramSpine {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d nP c dd : Nat} (hdd : dd = d + nP + c) :
    DenoteSpine cval env φ dd
      (((List.range nP).map fun l => Expr.bvar (nP - 1 - l)).map
        (Expr.instSeq (openFvars d nP) (nP - 1)))
      ((List.range nP).map fun l => VExpr.bvar (c + nP - 1 - l)) := by
  subst hdd
  rw [List.map_map]
  refine DenoteSpine.map ?_
  intro l hl
  have hlt : l < nP := List.mem_range.mp hl
  have hb := Expr.instSeq_bvar (openFvars d nP) (nP - 1) (nP - 1 - l)
    (openFvars_bounded d nP) (by omega) (by simp; omega)
  rw [show nP - 1 - (nP - 1 - l) = l from by omega,
    openFvars_getElem? hlt] at hb
  simp only [Function.comp_apply]
  rw [← Option.some.inj hb, denote_fvar]
  simp only [Option.some.injEq, VExpr.bvar.injEq]
  omega

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
  rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (by rfl)]
  exact denote_mkAppN (denote_paramSpine hdd) hc

/-- **The parameter tuple, fitted.**  The same tuple with the use
site's spine substituted, lifted past the `c` binders the residual sits
under — lifts the consumer's own `inst` absorbs. -/
theorem instSeq_paramList {nP c t : Nat} {xs : List VExpr}
    (ht : t = c + nP - 1) (hlen : xs.length = nP) :
    ((List.range nP).map fun l => VExpr.bvar (c + nP - 1 - l)).map
        (VExpr.instSeq xs t) = xs.map (VExpr.liftN c · 0) := by
  subst ht
  rw [List.map_map, ← hlen, ← map_range_getD xs (VExpr.liftN c · 0)]
  refine List.map_congr_left ?_
  intro l hl
  have hlt : l < xs.length := List.mem_range.mp hl
  simp only [Function.comp_apply]
  rw [show c + xs.length - 1 - l = c + (xs.length - 1 - l) from by omega]
  rw [VExpr.instSeq_bvar_hit xs c (xs.length - 1 - l)
    (xs.getD l default)
    (by rw [show xs.length - 1 - (xs.length - 1 - l) = l from by omega]
        simp [List.getD, List.getElem?_eq_getElem hlt]) (by omega)]

/-- The same, wrapped in the application the pins use. -/
theorem instSeq_paramTuple {vc : VExpr} (hvc : VExpr.Closed vc)
    {nP c t : Nat} {xs : List VExpr} (ht : t = c + nP - 1)
    (hlen : xs.length = nP) :
    VExpr.instSeq xs t
      (VExpr.mkAppN vc ((List.range nP).map fun l =>
        VExpr.bvar (c + nP - 1 - l))) =
      VExpr.mkAppN vc (xs.map (VExpr.liftN c · 0)) := by
  rw [VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hvc]
  congr 1
  exact instSeq_paramList ht hlen

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

/-- Instantiating a list of parameter variables below their range:
every index drops by one. -/
private theorem paramList_inst (nP c : Nat) (w : Expr) (g g' : Nat → Nat)
    (hg : ∀ k, k < nP → c < g k ∧ g k - 1 = g' k) :
    ((List.range nP).map fun k => Expr.bvar (g k)).map
        (Expr.instantiate1 · w c) =
      (List.range nP).map fun k => Expr.bvar (g' k) := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro k hk
  obtain ⟨h1, h2⟩ := hg k (List.mem_range.mp hk)
  simp only [Function.comp_apply, Expr.instantiate1]
  rw [if_neg (by omega), if_pos (by omega), h2]

/-- The same, wrapped in the constant application the pins use. -/
private theorem paramTuple_inst (Tm : Name) (lvls : List Level) (nP c : Nat)
    (w : Expr) (g g' : Nat → Nat)
    (hg : ∀ k, k < nP → c < g k ∧ g k - 1 = g' k) :
    (Expr.mkAppN (.const Tm lvls)
        ((List.range nP).map fun k => Expr.bvar (g k))).instantiate1 w c =
      Expr.mkAppN (.const Tm lvls)
        ((List.range nP).map fun k => Expr.bvar (g' k)) := by
  rw [Expr.mkAppN_instantiate1]
  congr 1
  exact paramList_inst nP c w g g' hg

/-- **The eta statement's fabricated constructor spine, opened.**  The
parameters drop an index and the subject variable becomes the opening
variable — inside the projection applications too. -/
private theorem etaCtor_inst (Cm : Name) (pm : Nat → Name)
    (lvls : List Level) (nP nF : Nat) (w : Expr) :
    (Expr.mkAppN (.const Cm lvls)
        (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
         (List.range nF).map (fun j => Expr.mkAppN (.const (pm j) lvls)
           (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
            [Expr.bvar 0])))).instantiate1 w 0 =
      Expr.mkAppN (.const Cm lvls)
        (((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))) ++
         (List.range nF).map (fun j => Expr.mkAppN (.const (pm j) lvls)
           (((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))) ++
            [w]))) := by
  rw [Expr.mkAppN_instantiate1]
  congr 1
  rw [List.map_append,
    paramList_inst nP 0 w (fun k => nP - k) (fun k => nP - 1 - k)
      (fun k hk => ⟨by omega, by omega⟩), List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro j _
  simp only [Function.comp_apply]
  rw [Expr.mkAppN_instantiate1]
  congr 1
  rw [List.map_append, List.map_cons, List.map_nil,
    paramList_inst nP 0 w (fun k => nP - k) (fun k => nP - 1 - k)
      (fun k hk => ⟨by omega, by omega⟩)]
  rfl

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

/-- **The eta statement's equation, opened at the subject binder.** -/
private theorem etaBody_inst (Tm Cm : Name) (pm : Nat → Name)
    (lvls : List Level) (lA : Level) (nP nF : Nat) (w : Expr) :
    (Expr.mkAppN (.const eqName [lA])
        [Expr.mkAppN (.const Tm lvls)
           ((List.range nP).map (fun k => Expr.bvar (nP - k))),
         Expr.bvar 0,
         Expr.mkAppN (.const Cm lvls)
           (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
            (List.range nF).map (fun j => Expr.mkAppN (.const (pm j) lvls)
              (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
               [Expr.bvar 0])))]).instantiate1 w 0 =
      Expr.mkAppN (.const eqName [lA])
        [Expr.mkAppN (.const Tm lvls)
           ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))),
         w,
         Expr.mkAppN (.const Cm lvls)
           (((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))) ++
            (List.range nF).map (fun j => Expr.mkAppN (.const (pm j) lvls)
              (((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))) ++
               [w])))] := by
  rw [Expr.mkAppN_instantiate1]
  simp only [List.map_cons, List.map_nil]
  rw [paramTuple_inst Tm lvls nP 0 w (fun k => nP - k) (fun k => nP - 1 - k)
    (fun k hk => ⟨by omega, by omega⟩), etaCtor_inst]
  rfl

/-- **The eta statement's residual, computed.**  One subject binder,
then the equation whose right-hand side is the fabricated constructor
spine — the same parameter tuple at shift `1` throughout, inside the
projection applications too. -/
theorem denote_etaResidual {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d nP nF : Nat} {nx : Name} {mx : BinderMeta} {Tm Cm : Name}
    {pm : Nat → Name} {lvls : List Level} {lA : Level}
    {vT vC veq : VExpr} {vP : Nat → VExpr}
    (hcT : ∀ dd : Nat, denote cval env φ dd (.const Tm lvls) = some vT)
    (hcC : ∀ dd : Nat, denote cval env φ dd (.const Cm lvls) = some vC)
    (hcP : ∀ (j : Nat), j < nF → ∀ dd : Nat,
      denote cval env φ dd (.const (pm j) lvls) = some (vP j))
    (hcE : ∀ dd : Nat, denote cval env φ dd (.const eqName [lA]) = some veq) :
    denote cval env φ (d + nP)
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (.forallE nx
          (Expr.mkAppN (.const Tm lvls)
            ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k))))
          (Expr.mkAppN (.const eqName [lA])
            [Expr.mkAppN (.const Tm lvls)
               ((List.range nP).map (fun k => Expr.bvar (nP - k))),
             Expr.bvar 0,
             Expr.mkAppN (.const Cm lvls)
               (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
                (List.range nF).map (fun j => Expr.mkAppN (.const (pm j) lvls)
                  (((List.range nP).map (fun k => Expr.bvar (nP - k))) ++
                   [Expr.bvar 0])))]) mx)) =
      some (.pi
        (VExpr.mkAppN vT
          ((List.range nP).map (fun l => VExpr.bvar (0 + nP - 1 - l))))
        (VExpr.mkAppN veq
          [VExpr.mkAppN vT
             ((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))),
           VExpr.bvar 0,
           VExpr.mkAppN vC
             (((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
              (List.range nF).map (fun j => VExpr.mkAppN (vP j)
                (((List.range nP).map
                   (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
                 [VExpr.bvar 0])))])) := by
  have hargsb := openFvars_bounded d nP
  have hargslen := openFvars_length d nP
  have hle : (openFvars d nP).length ≤ nP - 1 + 1 := by rw [hargslen]; omega
  rw [Expr.instSeq_forallE _ _ _ _ _ _ hle, instSeq_len_succ hargslen,
    denote_forallE,
    denote_paramTuple (c := 0) (d := d) (nP := nP) (dd := d + nP) rfl
      (hcT (d + nP))]
  rw [instSeq_instantiate1_in (b := Expr.fvar (d + nP) nx
      (Expr.instSeq (openFvars d nP) (nP - 1)
        (Expr.mkAppN (.const Tm lvls)
          ((List.range nP).map (fun k => Expr.bvar (nP - 1 - k)))))) rfl
    _ nP hargsb (Nat.le_of_eq hargslen)]
  rw [etaBody_inst Tm Cm pm lvls lA nP nF, Expr.instSeq_mkAppN,
    Expr.instSeq_eq_self (e := Expr.const eqName [lA]) _ _ (by rfl)]
  simp only [List.map_cons, List.map_nil]
  rw [denote_mkAppN (vs :=
      [VExpr.mkAppN vT
         ((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))),
       VExpr.bvar 0,
       VExpr.mkAppN vC
         (((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
          (List.range nF).map (fun j => VExpr.mkAppN (vP j)
            (((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
             [VExpr.bvar 0])))])
    (.cons (denote_paramTuple (c := 1) (d := d) (nP := nP)
        (dd := d + nP + 1) rfl (hcT (d + nP + 1)))
      (.cons (by
          rw [Expr.instSeq_eq_self _ _ (by rfl), denote_fvar]
          simp only [Option.some.injEq, VExpr.bvar.injEq]
          omega)
        (.cons (by
            rw [Expr.instSeq_mkAppN,
              Expr.instSeq_eq_self (e := Expr.const Cm lvls) _ _ (by rfl),
              List.map_append]
            refine denote_mkAppN (DenoteSpine.append
              (denote_paramSpine (c := 1) (d := d) (nP := nP) rfl) ?_)
              (hcC (d + nP + 1))
            rw [List.map_map]
            refine DenoteSpine.map ?_
            intro j hj
            simp only [Function.comp_apply]
            rw [Expr.instSeq_mkAppN,
              Expr.instSeq_eq_self (e := Expr.const (pm j) lvls) _ _ (by rfl),
              List.map_append, List.map_cons, List.map_nil]
            refine denote_mkAppN (DenoteSpine.append
              (denote_paramSpine (c := 1) (d := d) (nP := nP) rfl)
              (.cons ?_ .nil)) (hcP j (List.mem_range.mp hj) (d + nP + 1))
            rw [Expr.instSeq_eq_self _ _ (by rfl), denote_fvar]
            simp only [Option.some.injEq, VExpr.bvar.injEq]
            omega) .nil)))
    (hcE (d + nP + 1))]

/-- The eta residual, fitted with the use site's spine. -/
theorem instSeq_etaResidual {vT vC veq : VExpr} {vP : Nat → VExpr}
    (hvT : VExpr.Closed vT) (hvC : VExpr.Closed vC) (hveq : VExpr.Closed veq)
    (hvP : ∀ j, VExpr.Closed (vP j)) {nP nF : Nat} {xs : List VExpr}
    (hlen : xs.length = nP) :
    VExpr.instSeq xs (nP - 1)
      (.pi
        (VExpr.mkAppN vT
          ((List.range nP).map (fun l => VExpr.bvar (0 + nP - 1 - l))))
        (VExpr.mkAppN veq
          [VExpr.mkAppN vT
             ((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))),
           VExpr.bvar 0,
           VExpr.mkAppN vC
             (((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
              (List.range nF).map (fun j => VExpr.mkAppN (vP j)
                (((List.range nP).map
                   (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
                 [VExpr.bvar 0])))])) =
      .pi (VExpr.mkAppN vT xs)
        (VExpr.mkAppN veq
          [VExpr.mkAppN vT (xs.map (VExpr.liftN 1 · 0)),
           VExpr.bvar 0,
           VExpr.mkAppN vC ((xs.map (VExpr.liftN 1 · 0)) ++
             (List.range nF).map (fun j => VExpr.mkAppN (vP j)
               ((xs.map (VExpr.liftN 1 · 0)) ++ [VExpr.bvar 0])))]) := by
  have hz : xs.map (VExpr.liftN 0 · 0) = xs := by
    refine Eq.trans (List.map_congr_left ?_) (List.map_id xs)
    intro x _
    exact VExpr.liftN_zero x 0
  have hproj : ((List.range nF).map (fun j => VExpr.mkAppN (vP j)
        (((List.range nP).map (fun l => VExpr.bvar (1 + nP - 1 - l))) ++
         [VExpr.bvar 0]))).map (VExpr.instSeq xs nP) =
      (List.range nF).map (fun j => VExpr.mkAppN (vP j)
        ((xs.map (VExpr.liftN 1 · 0)) ++ [VExpr.bvar 0])) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro j _
    simp only [Function.comp_apply]
    rw [VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed (hvP j),
      List.map_append, List.map_cons, List.map_nil,
      instSeq_paramList (c := 1) (by omega) hlen,
      VExpr.instSeq_bvar_lt xs nP 0 (by rw [hlen]; omega)]
  rw [VExpr.instSeq_pi _ _ _ _ (by rw [hlen]; omega), instSeqV_len_succ hlen,
    instSeq_paramTuple hvT (c := 0) (by omega) hlen, hz,
    VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hveq]
  simp only [List.map_cons, List.map_nil]
  rw [instSeq_paramTuple hvT (c := 1) (by omega) hlen,
    VExpr.instSeq_bvar_lt xs nP 0 (by rw [hlen]; omega),
    VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hvC,
    List.map_append, instSeq_paramList (c := 1) (by omega) hlen, hproj]

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

**`hTmSort` is a pin the checker makes** (task #135, landed).
`EqLawTT` fires `eqValT`'s first β-step, whose premise is
`⊢ Â : Sort (ψ uN)` with `ψ uN = ⟦ℓA⟧` — the level the
*statement's* `Eq.{ℓA}` carries.  The
set model gets that membership from `AnnotOk`, which this bridge drops;
inversion cannot recover it, because reading the sort back out of the
`Eq` spine needs Π-injectivity, and Π-injectivity is refuted
(`Setlec/TTVerify/Inversion.lean`).  So it has to be *supplied*, and
the cheapest supplier is a syntactic pin the checker already computes
and discarded: `checkUnitThm` bound the model type's residual and the
equation's level and compared neither.  Task #135 added the comparison,
so `EtaPins`' last conjunct is `tbodyM = .sort ℓA`; with it in hand the
fact is derived here, from `EnvTT.has_type` at `T._model` and a
*second* use of `teleAlign_of_stripPis` — which is why the hypothesis
is isolated to one line rather than threaded.  The supplier is
`checkUnitThm_inv`'s last conjunct; making the swap is `DeclIndTT`'s. -/

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
    (hTmSort : StatementSortPin tbodyM lA)
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
  subst hsbody htySlot
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
  obtain ⟨-, hfitS⟩ := hfit.retarget' halignS
  -- (7) the type slot's sort, off the checker's pin (task #135)
  have hAsort := eqSlotSort_of_sortPin hro hT_strip hTm_strip hTmSort hpiM
    hTV hTmod hTmodv hfit hlen
  -- (8) the residual, computed and fitted
  rw [denote_unitResidual hcTm hcEq] at hRS
  obtain rfl := Option.some.inj hRS
  rw [instSeq_unitResidual (hcl _ _) (hcl _ _) hlen] at hfitS
  -- (9) fire the theorem at the two subjects
  simp only [hvT] at hB hB'
  have hpsi2 : Level.substFn (Level.substFn φ cvT.levelParams us)
      eqA.toConstantVal.levelParams [lA] uN =
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

/-! ## `EtaFoldTT`

The second obligation.  Same skeleton as `UnitFoldTT`: one binder
fewer in the statement's telescope, and the equation's right-hand side
is the *fabricated constructor spine* instead of a second subject.

**It takes two named premises, not one** (`DESIGN.md` §14.7.7).
`StatementSortPin` is #135's, and its supplier has landed
(`checkEtaThm_inv`); `EtaRhsTyped` is the one the fabricated spine
needs, and its supplier turned out to exist already (§14.7.8's
retraction — task #71's certificate, at the *caller*).  Both are
named, so each is one supplier and one swap. -/

/-- **The second pending premise** (`DESIGN.md` §14.7.7): the eta
statement's right-hand side is the fabricated constructor spine, and
`EqLawTT`'s third β-step wants its typing.

Stated as exactly the premise `EtaLawTT` would gain — same binders,
same side conditions, the RHS typing in place of the conclusion — so
that it is neither vacuous nor stronger than the law needs.

**Its supplier is `CtorResidualPin` plus a certificate — and there are
now *two* instances of that certificate, one per consumer**
(`DESIGN.md` §14.7.8 and §14.7.12).  Task #137 added the callee-side
one inside `structEtaCertWithI`, which is what the `defeq`-path
consumer (`StructEtaCertStep.lean`) discharges from; the caller-side
one described below is kept, and is what `MajorStep.lean`'s consumer
discharges from.  They are distinct instances of provably the same
call — see §14.7.12 for why keeping both is not redundancy: `majorToCtorI`'s eta branch runs
`iotaCertsI` on the **constructor's** telescope at `margs ++ projs`
(task #71's synthetic-spine certification) immediately before calling
`structEtaCertWithI`, and `Setlec/TTVerify/MajorStep.lean`'s
`fab_reduct` already inverts it — using only the `DenoteSpine` half and
discarding the typing.  That certificate types the fabrication at the
*constructor's* residual; `CtorResidualPin` (task #136) is what
identifies that residual with `T p⃗`, and the two together discharge
this premise at `eta_rescue`. -/
def EtaRhsTyped (env : Env) (cval : TConstVal) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (us : List Level)
    (xs : List VExpr) (TV rest B : VExpr),
    xs.length = caps.etaParams →
    denote cval env φ d
      (cvT.type.instantiateLevelParams cvT.levelParams us) = some TV →
    VTeleTyped Δ TV xs rest →
    HasType Δ B
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us)) xs) →
    HasType Δ
      (VExpr.mkAppN (cval caps.etaCtor
          (Level.substFn φ (levelParamsAt env caps.etaCtor) us))
        (xs ++ (List.range caps.etaFields).map fun j =>
          VExpr.mkAppN (cval (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
            (xs ++ [B])))
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us)) xs)

set_option maxHeartbeats 1600000 in
/-- **The structural-eta law, from the checked `T._model.eta`
theorem.**  Transpose of `eta_rule_fold`. -/
theorem EtaFoldTT {env : Env} {cval : TConstVal}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (hvp : ValParams env cval)
    (heqlaw : EqLawTT env cval)
    {f : Name → Name} (hro : RenameOkT cval env f)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    {tcv cvmT cvmC : ConstantVal} {mvalT mvalC : Expr}
    {hmT hmC : ReducibilityHint}
    {sbinders tbindersM : List (Name × Expr × BinderMeta)}
    {sbody tbodyM tySlot : Expr} {lA : Level}
    (hTmE : env.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmT))
    (hTmlps : cvmT.levelParams = cvT.levelParams)
    (hCmE : env.find? (caps.etaCtor.str "_model") =
      some (.defnInfo cvmC mvalC hmC))
    (hCmlps : cvmC.levelParams = cvT.levelParams)
    (hPmE : ∀ j, j < caps.etaFields → ∃ cvmj mvalj hmj,
      env.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmj) ∧
      cvmj.levelParams = cvT.levelParams)
    (heqfE : env.find? eqName = some eqA)
    (hS_strip : tcv.type.stripPis (caps.etaParams + 1) = some (sbinders, sbody))
    (hTm_strip : cvmT.type.stripPis caps.etaParams = some (tbindersM, tbodyM))
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      k < caps.etaParams → sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1)
    (hxdom : ∃ nx mx, sbinders[caps.etaParams]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (cvT.levelParams.map .param))
        ((List.range caps.etaParams).map fun k =>
          Expr.bvar (caps.etaParams - 1 - k)), mx))
    (hsbody : sbody = Expr.mkAppN (.const eqName [lA])
      [tySlot, .bvar 0,
       Expr.mkAppN (.const (caps.etaCtor.str "_model")
           (cvT.levelParams.map .param))
         (((List.range caps.etaParams).map
             (fun k => Expr.bvar (caps.etaParams - k))) ++
          (List.range caps.etaFields).map (fun j =>
            Expr.mkAppN (.const (projModelName T j)
              (cvT.levelParams.map .param))
              (((List.range caps.etaParams).map
                  (fun k => Expr.bvar (caps.etaParams - k))) ++
               [Expr.bvar 0])))])
    (htySlot : tySlot = Expr.mkAppN
      (.const (T.str "_model") (cvT.levelParams.map .param))
      ((List.range caps.etaParams).map fun k =>
        Expr.bvar (caps.etaParams - k)))
    (hTmSort : StatementSortPin tbodyM lA)
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
    (hvT : ∀ psi : Name → Nat, cval T psi = cval (T.str "_model") psi)
    (hvC : ∀ psi : Name → Nat,
      cval caps.etaCtor psi = cval (caps.etaCtor.str "_model") psi)
    (hvP : ∀ j, j < caps.etaFields → ∀ psi : Name → Nat,
      cval (projFnName T j) psi = cval (projModelName T j) psi)
    (hlpsC : levelParamsAt env caps.etaCtor = cvT.levelParams)
    (hlpsP : ∀ j, j < caps.etaFields →
      levelParamsAt env (projFnName T j) = cvT.levelParams)
    :
    EtaLawTT env cval T cvT caps := by
  intro φ d Δ us xs TV rest B hlen hTV hfit hB hrhsT
  obtain ⟨nx, mx, hxdom'⟩ := hxdom
  subst hsbody htySlot
  -- the public/model identifications, applied once to goal and premises
  have hprojEq : ((List.range caps.etaFields).map fun j =>
      VExpr.mkAppN (cval (projFnName T j)
        (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
        (xs ++ [B])) =
      ((List.range caps.etaFields).map fun j =>
      VExpr.mkAppN (cval (projModelName T j)
        (Level.substFn φ cvT.levelParams us)) (xs ++ [B])) := by
    refine List.map_congr_left ?_
    intro j hj
    rw [hlpsP j (List.mem_range.mp hj), hvP j (List.mem_range.mp hj)]
  rw [hlpsC, hvC, hprojEq] at hrhsT ⊢
  simp only [hvT] at hB hrhsT ⊢
  -- the constants' denotations
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
  have hcCm : ∀ dd : Nat,
      denote cval env (Level.substFn φ cvT.levelParams us) dd
        (.const (caps.etaCtor.str "_model") (cvT.levelParams.map .param)) =
      some (cval (caps.etaCtor.str "_model")
        (Level.substFn φ cvT.levelParams us)) := by
    intro dd
    rw [denote_const, hCmE]
    dsimp only
    rw [if_pos (by simp [ConstantInfo.toConstantVal, hCmlps])]
    have hsub : Level.substFn (Level.substFn φ cvT.levelParams us)
        (ConstantInfo.defnInfo cvmC mvalC hmC).toConstantVal.levelParams
        (List.map Level.param cvT.levelParams) =
        Level.substFn φ cvT.levelParams us := by
      have hlp : (ConstantInfo.defnInfo cvmC mvalC hmC).toConstantVal.levelParams
          = cvT.levelParams := by simp [ConstantInfo.toConstantVal, hCmlps]
      rw [hlp]
      funext p
      exact Level.substFn_map_param
    rw [hsub]
  have hcPm : ∀ (j : Nat), j < caps.etaFields → ∀ dd : Nat,
      denote cval env (Level.substFn φ cvT.levelParams us) dd
        (.const (projModelName T j) (cvT.levelParams.map .param)) =
      some (cval (projModelName T j) (Level.substFn φ cvT.levelParams us)) := by
    intro j hj dd
    obtain ⟨cvmj, mvalj, hmj, hfj, hlpj⟩ := hPmE j hj
    rw [denote_const, hfj]
    dsimp only
    rw [if_pos (by simp [ConstantInfo.toConstantVal, hlpj])]
    have hsub : Level.substFn (Level.substFn φ cvT.levelParams us)
        (ConstantInfo.defnInfo cvmj mvalj hmj).toConstantVal.levelParams
        (List.map Level.param cvT.levelParams) =
        Level.substFn φ cvT.levelParams us := by
      have hlp : (ConstantInfo.defnInfo cvmj mvalj hmj).toConstantVal.levelParams
          = cvT.levelParams := by simp [ConstantInfo.toConstantVal, hlpj]
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
  -- (1)-(5), as in `UnitFoldTT`
  rw [denote_instLevels hvp (ks := cvT.levelParams) (us := us) φ d cvT.type]
    at hTV
  obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
    Expr.ErasedEq.stripPis_inv caps.etaParams
      (Expr.ErasedEq.of_eqUpToNames hren) hTm_strip
  obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
    Expr.stripPis_renameConsts_inv (f := f) caps.etaParams hstripR
  have hdomsPub : ∀ (i : Nat) (b₁ b₂ : Name × Expr × BinderMeta),
      tbinders[i]? = some b₁ → tbindersM[i]? = some b₂ →
      RenEqT f b₁.2.1 b₂.2.1 := by
    intro i b₁ b₂ hb₁ hb₂
    have hbR : bsR[i]? = some (b₁.1, (b₁.2.1).renameConsts f, b₁.2.2) := by
      rw [hbsmap, List.getElem?_map, hb₁]; rfl
    exact (hdomsR i _ _ hbR hb₂).1
  obtain ⟨nx', dx', mx', hxb, hstrip0⟩ :=
    Expr.stripPis_snoc caps.etaParams hS_strip
  have hdx : dx' = Expr.mkAppN
      (.const (T.str "_model") (cvT.levelParams.map .param))
      ((List.range caps.etaParams).map fun k =>
        Expr.bvar (caps.etaParams - 1 - k)) :=
    congrArg (fun t => t.2.1) (Option.some.inj (hxb.symm.trans hxdom'))
  subst hdx
  obtain ⟨Tstmt, hTstmtC, hthmv⟩ := hthmty (Level.substFn φ cvT.levelParams us)
  have hTstmt : denote cval env (Level.substFn φ cvT.levelParams us) d
      tcv.type = some Tstmt := by
    rw [denote_depth_closed hcl hSw hSb d]; exact hTstmtC
  obtain ⟨Tmod, hTmodC, hTmodv⟩ := hTmty (Level.substFn φ cvT.levelParams us)
  have hTmod : denote cval env (Level.substFn φ cvT.levelParams us) d
      cvmT.type = some Tmod := by
    rw [denote_depth_closed hcl hTmw hTmb d]; exact hTmodC
  have hpiM : PiDomsRenEqT f caps.etaParams cvT.type cvmT.type :=
    PiDomsRenEqT.of_pointwise caps.etaParams hT_strip hTm_strip hdomsPub
  have hpiS : PiDomsRenEqT f caps.etaParams cvT.type tcv.type := by
    refine PiDomsRenEqT.of_pointwise caps.etaParams hT_strip hstrip0 ?_
    intro i b₁ b₂ hb₁ hb₂
    have hi : i < caps.etaParams := by
      rcases Nat.lt_or_ge i caps.etaParams with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [Expr.stripPis_length caps.etaParams hT_strip]; omega)] at hb₁
        exact nomatch hb₁
    have hilt : i < tbindersM.length := by
      rw [Expr.stripPis_length caps.etaParams hTm_strip]; exact hi
    have hbM : tbindersM[i]? = some tbindersM[i] :=
      List.getElem?_eq_getElem hilt
    rw [List.getElem?_take_of_lt hi] at hb₂
    rw [hsdoms i b₂ tbindersM[i] hi hb₂ hbM]
    exact hdomsPub i b₁ tbindersM[i] hb₁ hbM
  obtain ⟨R, RS, hR, hRS, halignS⟩ :=
    teleAlign_of_stripPis hro caps.etaParams hT_strip hstrip0 hpiS hTV hTstmt
      hlen
  obtain ⟨-, hfitS⟩ := hfit.retarget' halignS
  have hAsort := eqSlotSort_of_sortPin hro hT_strip hTm_strip hTmSort hpiM
    hTV hTmod hTmodv hfit hlen
  -- the residual, computed and fitted
  rw [denote_etaResidual hcTm hcCm hcPm hcEq] at hRS
  obtain rfl := Option.some.inj hRS
  rw [instSeq_etaResidual (hcl _ _) (hcl _ _) (hcl _ _) (fun j => hcl _ _)
    hlen] at hfitS
  -- fire the theorem at the subject
  have hpsi2 : Level.substFn (Level.substFn φ cvT.levelParams us)
      eqA.toConstantVal.levelParams [lA] uN =
      Level.eval (Level.substFn φ cvT.levelParams us) lA := rfl
  refine Deq.ofEqThmClosed heqlaw heqfE
    (Level.substFn (Level.substFn φ cvT.levelParams us)
      eqA.toConstantVal.levelParams [lA]) (args := xs ++ [B]) hthmv ?_
    (by rw [hpsi2]; exact hAsort) hB hrhsT
  refine hfitS.append (VTeleTyped.cons hB ?_)
  have habs : (xs.map (VExpr.liftN 1 · 0)).map (VExpr.inst · B 0) = xs := by
    rw [List.map_map]
    refine Eq.trans (List.map_congr_left ?_) (List.map_id xs)
    intro x _
    show VExpr.inst (VExpr.liftN 1 x 0) B 0 = x
    rw [VExpr.inst_liftN_absorb x (Nat.zero_le 0) (Nat.le_refl 0) B,
      VExpr.liftN_zero]
  have hres : ∀ VE VT VC : VExpr, VExpr.Closed VE → VExpr.Closed VT →
      VExpr.Closed VC → (∀ j, VExpr.Closed
        (cval (projModelName T j) (Level.substFn φ cvT.levelParams us))) →
      (VExpr.mkAppN VE
          [VExpr.mkAppN VT (xs.map (VExpr.liftN 1 · 0)), VExpr.bvar 0,
           VExpr.mkAppN VC ((xs.map (VExpr.liftN 1 · 0)) ++
             (List.range caps.etaFields).map (fun j => VExpr.mkAppN
               (cval (projModelName T j)
                 (Level.substFn φ cvT.levelParams us))
               ((xs.map (VExpr.liftN 1 · 0)) ++
                [VExpr.bvar 0])))]).inst B 0 =
        VExpr.mkAppN VE
          [VExpr.mkAppN VT xs, B,
           VExpr.mkAppN VC (xs ++
             (List.range caps.etaFields).map (fun j => VExpr.mkAppN
               (cval (projModelName T j)
                 (Level.substFn φ cvT.levelParams us)) (xs ++ [B])))] := by
    intro VE VT VC hVE hVT hVC hVP
    have hprojI : ((List.range caps.etaFields).map (fun j => VExpr.mkAppN
          (cval (projModelName T j) (Level.substFn φ cvT.levelParams us))
          ((xs.map (VExpr.liftN 1 · 0)) ++ [VExpr.bvar 0]))).map
          (VExpr.inst · B 0) =
        (List.range caps.etaFields).map (fun j => VExpr.mkAppN
          (cval (projModelName T j) (Level.substFn φ cvT.levelParams us))
          (xs ++ [B])) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro j _
      simp only [Function.comp_apply]
      rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed (hVP j),
        List.map_append, List.map_cons, List.map_nil, habs]
      simp only [VExpr.inst_bvar, Nat.lt_irrefl, if_false, if_true,
        VExpr.liftN_zero]
    rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVE]
    simp only [List.map_cons, List.map_nil]
    rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVT, habs]
    rw [VExpr.inst_mkAppN, VExpr.inst_eq_self_of_closed hVC,
      List.map_append, habs, hprojI]
    simp only [VExpr.inst_bvar, Nat.lt_irrefl, if_false, if_true,
      VExpr.liftN_zero]
  rw [hres _ _ _ (hcl _ _) (hcl _ _) (hcl _ _) (fun j => hcl _ _)]
  exact VTeleTyped.nil

end Setlec.TTVerify
