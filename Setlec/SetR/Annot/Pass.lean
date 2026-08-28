import Setlec.SetR.Annot.Syntax
import Setlec.SetR.Rel

/-!
# The annotation pass, relationally (task #151, tier A)

`Setlec/SetR/Rel.lean`'s five relations are `Prop`-valued, so there is
no recursion on a derivation and therefore no *function* from a
derivation to an annotated term.  The pass is accordingly **relational**:
`Annotates μ env cval φ Δ e ea` says that `ea : AVExpr` is an annotation
of `e : VExpr` **whose every binder sort is justified in the context
`Δ`**.  Existence — "the subject of a derivation has an annotation" — is
then a theorem, proved by one induction over the family.

## The sort fact

`HasSort μ env cval φ Δ A u` is the shape the family's own premises
carry at every binder:

```
    Infer μ env cval φ Δ A tA  →  DefEq μ env cval φ Δ tA (.sort u)
```

which is literally I6's and I7's first two premises
(`Setlec/SetR/Rel.lean`).  Task #151's brief writes this shape as
`Red tA (.sort u)`; the landed family says `DefEq`, per T4's **repair A**
(the 2026-08-27 decision recorded in `Setlec/SetR/DESIGN.md`: all twenty
`Red`-at-an-inferred-type premises became `DefEq`, because the bridge's
infer-claim is stated up to the relation's own equality and directed
reduction cannot absorb the slack).  Using the landed shape is what makes
`HasSort` **conversion-invariant on the type side**: `DefEq` is
transitive and symmetric, so the fact survives any conversion of `tA`,
which is exactly what a *cached premise* has to do.

## Per-tree sort correctness

There is no separate invariant to state and maintain: `Annotates`'
binder clauses **are** the invariant.  A derivation of
`Annotates … Δ (.lam A b) (.lam u Aa ba)` contains, by construction, a
`HasSort … Δ A u`, and `Annotates`' recursor (or `cases`) hands it to
any consumer — that is the interface tier C's soundness induction reads.
Sort correctness is therefore *per tree*: within one annotation every
numeral is backed by a derivation of the family in the very context the
binder is opened in.

**No cross-tree coherence is claimed here, deliberately.**  Two
annotations of the *same* term may carry different numerals, and nothing
at this tier rules that out: `Infer` is not syntactically deterministic
(design note: `Infer.const`'s subject `cval n ψ` overlaps app-shaped
terms), and the semantic separation is not available either — see
`Setlec/SetR/Annot/Kinding.lean`, where unique kinding is proved from
`univ u = univ v` and *not* from two memberships, because the universe
tower is **cumulative** (`SetTheory.univ_mono`), so
`x ∈ˢ univ u → x ∈ˢ univ v → u = v` is false.  Cross-tree agreement is
tier C's business, where the `∀ ρ, Sat V Δ ρ → …` shape of every
statement makes a context with no satisfying valuation vacuous and the
semantic unique-kinding lemma settles the rest.

## `letE`: the pass annotates the zeta contractum

`Annotates` has **no structural `letE` clause**.  The reason is
premise-exactness, and it is forced: I10 (`Setlec/SetR/Rel.lean`)
certifies the let *body* only in instantiated form —

```
    Infer Δ T tT → DefEq Δ tT (.sort u) → Infer Δ v tv → DefEq Δ tv T →
    Infer Δ (b.inst v) B → Infer Δ (.letE T v b) B
```

— so a derivation contains **no** sub-derivation about `b` in the
extended context `T :: Δ`, and the binder sorts inside `b` have no
justification there.  Recovering one would need substitution
admissibility for the family (transporting `HasSort (T :: Δ) C u` to
`HasSort Δ (C.inst v) u` and back), and the family's only metatheory is
weakening (M1).  The pass therefore annotates a `let` node by the
annotation of its zeta contractum, `Annotates.zeta`, which is exactly
what the checker's own premise supplies.  Semantically this is free:
`interp ρ (.letE T v b) = interp (cons ⟦v⟧ ρ) b = interp ρ (b.inst v)`
(`interp_inst0`).

The price is that `erase` is exact only up to zeta, and that is what
`ZetaEq` below records: `Annotates.zetaEq` is the erase contract, and
`ZetaEq.interp_eq` (in `Kinding.lean`) is its semantic reading.
`AVExpr.letE` itself is kept — `AVExpr` is a faithful variant of `VExpr`,
`erase` is surjective, and tier B may want to state generic facts about
let nodes — but the pass never emits it.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-! ## The sort fact -/

/-- The shape every binder annotation caches: the checker's own
"this is a type" certificate at `A`, an `Infer` + `DefEq`-to-a-sort
pair (I6/I7/I10's leading premises).  Conversion-invariant on the type
side by `DefEq.trans`. -/
def HasSort (μ : CheckMode) (env : Env) (cval : TConstVal) (φ : Name → Nat)
    (Δ : List VExpr) (A : VExpr) (u : Nat) : Prop :=
  ∃ tA, Infer μ env cval φ Δ A tA ∧ DefEq μ env cval φ Δ tA (.sort u)

namespace HasSort

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- The pair spelling, as the rules present it. -/
theorem intro {Δ : List VExpr} {A tA : VExpr} {u : Nat}
    (hA : Infer μ env cval φ Δ A tA)
    (hu : DefEq μ env cval φ Δ tA (.sort u)) : HasSort μ env cval φ Δ A u :=
  ⟨tA, hA, hu⟩

/-- Conversion-invariance on the type side: the cached certificate may
be composed with any conversion of the inferred type. -/
theorem ofConv {Δ : List VExpr} {A tA tA' : VExpr} {u : Nat}
    (hA : Infer μ env cval φ Δ A tA)
    (hconv : DefEq μ env cval φ Δ tA tA')
    (hu : DefEq μ env cval φ Δ tA' (.sort u)) : HasSort μ env cval φ Δ A u :=
  ⟨tA, hA, hconv.trans hu⟩

end HasSort

/-! ## Erasure up to zeta

The pass's erase contract.  `ZetaEq e e'` says `e'` is `e` with some
`let` nodes zeta-contracted; it is the exact relation between an
annotated term's erasure and the term it annotates (`Annotates.zetaEq`),
and it collapses under `interp` (`ZetaEq.interp_eq`, in
`Kinding.lean`). -/
inductive ZetaEq : VExpr → VExpr → Prop where
  | bvar {i : Nat} : ZetaEq (.bvar i) (.bvar i)
  | sort {u : Nat} : ZetaEq (.sort u) (.sort u)
  | const {c : BConst} {us : List Nat} : ZetaEq (.const c us) (.const c us)
  | app {f f' a a' : VExpr} :
      ZetaEq f f' → ZetaEq a a' → ZetaEq (.app f a) (.app f' a')
  | lam {A A' b b' : VExpr} :
      ZetaEq A A' → ZetaEq b b' → ZetaEq (.lam A b) (.lam A' b')
  | pi {A A' B B' : VExpr} :
      ZetaEq A A' → ZetaEq B B' → ZetaEq (.pi A B) (.pi A' B')
  | letE {T T' v v' b b' : VExpr} :
      ZetaEq T T' → ZetaEq v v' → ZetaEq b b' →
      ZetaEq (.letE T v b) (.letE T' v' b')
  /-- the zeta step: a `let` node may be contracted away -/
  | zeta {T v b e : VExpr} :
      ZetaEq (b.inst v) e → ZetaEq (.letE T v b) e
  | eqE {T T' a a' b b' : VExpr} :
      ZetaEq T T' → ZetaEq a a' → ZetaEq b b' →
      ZetaEq (.eqE T a b) (.eqE T' a' b')
  | proj {i : Nat} {e e' : VExpr} : ZetaEq e e' → ZetaEq (.proj i e) (.proj i e')
  | prf : ZetaEq .prf .prf

/-- `ZetaEq` is reflexive (the structural clauses cover every node). -/
theorem ZetaEq.refl : ∀ e : VExpr, ZetaEq e e := by
  intro e
  induction e with
  | bvar i => exact .bvar
  | sort u => exact .sort
  | const c us => exact .const
  | app f a ihf iha => exact .app ihf iha
  | lam A b ihA ihb => exact .lam ihA ihb
  | pi A B ihA ihB => exact .pi ihA ihB
  | letE T v b ihT ihv ihb => exact .letE ihT ihv ihb
  | eqE T a b ihT iha ihb => exact .eqE ihT iha ihb
  | proj i e ih => exact .proj ih
  | prf => exact .prf

/-! ## The annotation relation -/

/-- `Annotates μ env cval φ Δ e ea`: `ea` is an annotation of `e` in
context `Δ`, every binder numeral of which is backed by a `HasSort`
certificate *of the family* in the context that binder is opened in.

The clauses mirror the term structure, with two deliberate departures,
both recorded in the module docstring: the binder clauses carry the
sort facts, and `letE` is annotated through its zeta contractum. -/
inductive Annotates (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → VExpr → AVExpr → Prop where
  | bvar {Δ : List VExpr} {i : Nat} :
      Annotates μ env cval φ Δ (.bvar i) (.bvar i)
  | sort {Δ : List VExpr} {u : Nat} :
      Annotates μ env cval φ Δ (.sort u) (.sort u)
  | const {Δ : List VExpr} {c : BConst} {us : List Nat} :
      Annotates μ env cval φ Δ (.const c us) (.const c us)
  | app {Δ : List VExpr} {f a : VExpr} {fa aa : AVExpr} :
      Annotates μ env cval φ Δ f fa → Annotates μ env cval φ Δ a aa →
      Annotates μ env cval φ Δ (.app f a) (.app fa aa)
  /-- I7's cached premise: the domain's sort. -/
  | lam {Δ : List VExpr} {A b : VExpr} {Aa ba : AVExpr} {u : Nat} :
      HasSort μ env cval φ Δ A u →
      Annotates μ env cval φ Δ A Aa →
      Annotates μ env cval φ (A :: Δ) b ba →
      Annotates μ env cval φ Δ (.lam A b) (.lam u Aa ba)
  /-- I6's two cached premises: the domain's and the opened body's
  sorts. -/
  | pi {Δ : List VExpr} {A B : VExpr} {Aa Ba : AVExpr} {u v : Nat} :
      HasSort μ env cval φ Δ A u →
      HasSort μ env cval φ (A :: Δ) B v →
      Annotates μ env cval φ Δ A Aa →
      Annotates μ env cval φ (A :: Δ) B Ba →
      Annotates μ env cval φ Δ (.pi A B) (.pi u v Aa Ba)
  /-- the `let` clause: the annotation of the zeta contractum, which is
  the only form I10 certifies (module docstring). -/
  | zeta {Δ : List VExpr} {T v b : VExpr} {ea : AVExpr} :
      Annotates μ env cval φ Δ (b.inst v) ea →
      Annotates μ env cval φ Δ (.letE T v b) ea
  | eqE {Δ : List VExpr} {T a b : VExpr} {Ta aa ba : AVExpr} :
      Annotates μ env cval φ Δ T Ta → Annotates μ env cval φ Δ a aa →
      Annotates μ env cval φ Δ b ba →
      Annotates μ env cval φ Δ (.eqE T a b) (.eqE Ta aa ba)
  | proj {Δ : List VExpr} {i : Nat} {e : VExpr} {ea : AVExpr} :
      Annotates μ env cval φ Δ e ea →
      Annotates μ env cval φ Δ (.proj i e) (.proj i ea)
  | prf {Δ : List VExpr} : Annotates μ env cval φ Δ .prf .prf

namespace Annotates

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- **The erase contract.**  An annotation erases to its subject, up to
zeta — exactly, at every node the pass annotates structurally, and
through `ZetaEq.zeta` at the `let` nodes it contracts. -/
theorem zetaEq {Δ : List VExpr} {e : VExpr} {ea : AVExpr}
    (h : Annotates μ env cval φ Δ e ea) : ZetaEq e ea.erase := by
  induction h with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ _ _ ihA ihB => exact .pi ihA ihB
  | zeta _ ih => exact .zeta ih
  | eqE _ _ _ ihT iha ihb => exact .eqE ihT iha ihb
  | proj _ ih => exact .proj ih
  | prf => exact .prf

/-- The `mkAppN` closure the literal cases use. -/
theorem mkAppN {Δ : List VExpr} : ∀ {as : List VExpr} {aas : List AVExpr}
    {f : VExpr} {fa : AVExpr}, Annotates μ env cval φ Δ f fa →
    List.Forall₂ (Annotates μ env cval φ Δ) as aas →
    Annotates μ env cval φ Δ (VExpr.mkAppN f as) (AVExpr.mkAppN fa aas) := by
  intro as
  induction as with
  | nil =>
    intro aas f fa hf has
    cases has
    exact hf
  | cons a as ih =>
    intro aas f fa hf has
    cases has with
    | cons ha hrest => exact ih (.app hf ha) hrest

end Annotates

/-! ## The environment hypothesis

`Infer`'s leaf rules (I3/I4/I5) have *stored-constant valuations* as
subjects — `cval n ψ` is an arbitrary `VExpr` as far as this tier is
concerned, so its binders' sorts cannot come from the derivation.  They
come from the environment, exactly as `EnvSHyp.annot_okV` supplies
`AnnotOkV` for the same subjects on the soundness side
(`Setlec/SetR/Sound/Motives.lean`).  This is the one hypothesis of the
existence theorem, and it is the field a future `EnvS` component
discharges. -/

/-- Every stored constant's valuation is annotatable, at every context.
The `AnnotOkV`-analogue: the [set] shadow of `EnvSHyp.annot_okV`. -/
def CvalAnnot (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : Prop :=
  ∀ (n : Name) (ψ : Name → Nat) (Δ : List VExpr),
    ∃ ea, Annotates μ env cval φ Δ (cval n ψ) ea

namespace CvalAnnot

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- `Nat`-literal valuations are annotatable: `natLitT` is a
`Nat.succ`-spine over `Nat.zero`, both stored valuations. -/
theorem natLitT (h : CvalAnnot μ env cval φ) (Δ : List VExpr)
    (zv sv : VExpr) (hz : ∃ za, Annotates μ env cval φ Δ zv za)
    (hs : ∃ sa, Annotates μ env cval φ Δ sv sa) :
    ∀ n : Nat, ∃ ea, Annotates μ env cval φ Δ (Setlec.TTVerify.natLitT zv sv n) ea := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    obtain ⟨sa, hsa⟩ := hs
    obtain ⟨ea, hea⟩ := ih
    exact ⟨.app sa ea, .app hsa hea⟩

/-- I4's subject. -/
theorem natLitV (h : CvalAnnot μ env cval φ) (Δ : List VExpr) (n : Nat) :
    ∃ ea, Annotates μ env cval φ Δ (Setlec.SetR.natLitV cval φ n) ea :=
  h.natLitT Δ _ _ (h _ _ Δ) (h _ _ Δ) n

/-- The character-list part of a string literal's constructor form. -/
theorem charListT (h : CvalAnnot μ env cval φ) (Δ : List VExpr)
    (nilV consV ofNatV zv sv : VExpr)
    (hnil : ∃ a, Annotates μ env cval φ Δ nilV a)
    (hcons : ∃ a, Annotates μ env cval φ Δ consV a)
    (hofNat : ∃ a, Annotates μ env cval φ Δ ofNatV a)
    (hz : ∃ a, Annotates μ env cval φ Δ zv a)
    (hs : ∃ a, Annotates μ env cval φ Δ sv a) :
    ∀ cs : List Char,
      ∃ ea, Annotates μ env cval φ Δ
        (Setlec.TTVerify.charListT nilV consV ofNatV zv sv cs) ea := by
  intro cs
  induction cs with
  | nil => exact hnil
  | cons c cs ih =>
    obtain ⟨ca, hca⟩ := hcons
    obtain ⟨oa, hoa⟩ := hofNat
    obtain ⟨na, hna⟩ := h.natLitT Δ zv sv hz hs c.toNat
    obtain ⟨ta, hta⟩ := ih
    exact ⟨.app (.app ca (.app oa na)) ta, .app (.app hca (.app hoa hna)) hta⟩

/-- I5's subject. -/
theorem strLitT (h : CvalAnnot μ env cval φ) (Δ : List VExpr) (s : String) :
    ∃ ea, Annotates μ env cval φ Δ (Setlec.TTVerify.strLitT cval env φ s) ea := by
  obtain ⟨fa, hfa⟩ := h stringOfListName (Level.substFn φ [] []) Δ
  obtain ⟨ca, hca⟩ := h.charListT Δ _ _ _ _ _
    (by obtain ⟨a, ha⟩ := h listNilName (Level.substFn φ (levelParamsAt env listNilName) [.zero]) Δ
        obtain ⟨b, hb⟩ := h charName (Level.substFn φ [] []) Δ
        exact ⟨.app a b, .app ha hb⟩)
    (by obtain ⟨a, ha⟩ := h listConsName (Level.substFn φ (levelParamsAt env listConsName) [.zero]) Δ
        obtain ⟨b, hb⟩ := h charName (Level.substFn φ [] []) Δ
        exact ⟨.app a b, .app ha hb⟩)
    (h charOfNatName (Level.substFn φ [] []) Δ)
    (h natZeroName (Level.substFn φ [] []) Δ)
    (h natSuccName (Level.substFn φ [] []) Δ)
    s.toList
  exact ⟨.app fa ca, .app hfa hca⟩

end CvalAnnot

/-! ## Existence

One induction over the mutual family, in the `Weaken.lean` engineering
(Lean's `induction` tactic does not drive mutual `Prop` families; the
44 minor premises are supplied positionally, in constructor declaration
order — `Red`'s 15, `Infer`'s 10, `DefEq`'s 15, `Tele`'s 2, `DefEqL`'s
2).

The grading of the motives mirrors T4's soundness architecture:

* **`Infer`** carries the content — its subject is annotatable, exactly
  as `Infer`-sound concludes its subject's `AnnotOkV`;
* **`Tele`** carries the spine's arguments (its `Infer` premises), which
  is the form R6/R11's consumers want;
* **`Red`, `DefEq`, `DefEqL` carry nothing.**  This is not laziness, it
  is forced, and the reason is worth recording: `Red.beta`'s subject
  `.app (.lam A b) a` has a λ whose domain sort **no premise supplies**
  (R4's premises are the argument's `Infer`+`DefEq` pair only), and
  `Red.zeta`'s subject is premise-free altogether.  Even the *transport*
  reading ("if the redex is annotatable so is the contractum") is
  unavailable: it would need `Annotates (A :: Δ) b ba →
  Annotates Δ a aa → Annotates Δ (b.inst a) (ba.inst aa)`, i.e.
  substitution admissibility for `HasSort`, which the family does not
  have.  Reduction is therefore annotation-opaque at this tier, and
  tier C must not expect otherwise. -/

section Existence

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- **The existence theorem for `Infer`**: the subject of an inference
has an annotation, all of whose binder sorts are justified by
sub-derivations of that very inference. -/
theorem Infer.annotates (hcv : CvalAnnot μ env cval φ) {Δ : List VExpr}
    {e T : VExpr} (h : Infer μ env cval φ Δ e T) :
    ∃ ea, Annotates μ env cval φ Δ e ea := by
  refine Infer.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Δ e _ _ => ∃ ea, Annotates μ env cval φ Δ e ea)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun Δ _ as _ _ =>
      ∀ a ∈ as, ∃ aa, Annotates μ env cval φ Δ a aa)
    (motive_5 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_
    h
  all_goals try (intros; exact trivial)
  -- I1 `sort`
  · exact fun _ _ => ⟨.sort _, .sort⟩
  -- I2 `bvar`
  · exact fun _ _ _ _ => ⟨.bvar _, .bvar⟩
  -- I3 `const`
  · exact fun Δ _ _ _ _ _ _ _ _ => hcv _ _ Δ
  -- I4 `litNat`
  · exact fun Δ _ _ => hcv.natLitV Δ _
  -- I5 `litStr`
  · exact fun Δ _ _ => hcv.strLitT Δ _
  -- I6 `pi`
  · rintro Δ A B tA tB u v hA hu hB hv - ⟨Aa, hAa⟩ - ⟨Ba, hBa⟩
    exact ⟨.pi u v Aa Ba, .pi ⟨tA, hA, hu⟩ ⟨tB, hB, hv⟩ hAa hBa⟩
  -- I7 `lam`
  · rintro Δ A b tA B u hA hu hb ⟨Aa, hAa⟩ - ⟨ba, hba⟩
    exact ⟨.lam u Aa ba, .lam ⟨tA, hA, hu⟩ hAa hba⟩
  -- I8 `app`
  · rintro Δ f a tf A B ta - - - - ⟨fa, hfa⟩ - ⟨aa, haa⟩ -
    exact ⟨.app fa aa, .app hfa haa⟩
  -- I9 `proj`
  · rintro Δ p tp TP resV i T entry ciT us ps - - - - - - - - -
      _ _ ⟨pa, hpa⟩ -
    exact ⟨.proj i pa, .proj hpa⟩
  -- I10 `letE` (the zeta clause)
  · rintro Δ T v b tT tv B u - - - - - - - - ⟨ba, hba⟩
    exact ⟨ba, .zeta hba⟩
  -- `Tele.nil`
  · intro _ _ a ha
    simp at ha
  -- `Tele.cons`
  · rintro Δ A B a ta rest as - - - ⟨aa, haa⟩ - ihs x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨aa, haa⟩
    · exact ihs x hx

/-- **The existence theorem for `Tele`**: every certified spine argument
has an annotation. -/
theorem Tele.annotates (hcv : CvalAnnot μ env cval φ) {Δ : List VExpr}
    {T : VExpr} {as : List VExpr} {rest : VExpr}
    (h : Tele μ env cval φ Δ T as rest) :
    ∀ a ∈ as, ∃ aa, Annotates μ env cval φ Δ a aa := by
  induction as generalizing T with
  | nil => intro a ha; simp at ha
  | cons a as ih =>
    cases h with
    | cons ha _ htail =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha.annotates hcv
      · exact ih htail x hx

end Existence

end Setlec.SetR
