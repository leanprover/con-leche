import Setlec.SetR.Interp2.Step2.Lit
import Setlec.SetR.Interp2.Step2.Dispatch

/-!
# `CheckStep2`, the literal clauses — the `String` half

`Sound/Lit.lean`'s `strLit_facts` onto `piR`/`AnnotOk2`/`interp2` and
`denote2`'s own character-list spine (`charListT2`, from
`Annot/Canon.lean` — exactly the former `denote2`'s `.lit strVal`
clause emits).

**Transposition, not new argument.**  The v1 block reaches the
interpretation through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed` only; all five have `interp2`
analogues, and the string half in fact needs just two of them
(`interp2_app` and — through `natLit_facts2` — nothing else).  The
`bvar`/`sort`/`pi`/`closed` uses were all *inside* v1's head-fact
derivations, which are hypotheses here (below).

## Why the head facts are arguments

As in `Step2/Lit.lean` (and as v1 factors `natHeads_facts` out of
`natLit_facts`), the six string heads — `String.mk`/`ofList`,
`List.nil`, `List.cons`, `Char.ofNat`, `Nat.zero`, `Nat.succ`, each
already applied to its type arguments the way `denote2` emits them —
enter as explicit membership and truthfulness hypotheses.

Here that is not merely convenient, it is *forced*: v1 derives the
heads by computing `denote` of the stored types, and `denote`'s
`forallE` clause is numeral-free, so `strLitSupported`'s syntactic
inversion pins the denotation outright.  `denote2`'s `forallE` clause
instead calls `sortOfE` — `inferTypeCore` + `whnf` on the stored type
— which the guard does not constrain at all.  So `EnvS2.mem_type2`
cannot be aimed at a *known* annotated type from the guard alone; the
supplier has to come from the annotation pass (`Annotates`/`HasSort`),
not from a `denote2` computation.  See the report at the end of
`Setlec/SetR/DESIGN.md`'s tier-B ledger.

## The positive-kind saving

Every product in the string spine is at result sort `1` — `Char`,
`List Char`, `String` and `Nat` are all `Type`-level — so
`app_mem_piR_pos` applies with no fibre premise throughout and every
`AnnotOk2` app slot's kind-`0` component is vacuous.  v1 needed
`TeleFitV`/`appN_annot` telescope walks with per-argument
`inst_eq_self_of_closed` bookkeeping for the same steps.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- **The character-list facts.**  Every `denote2` character-list
spine is truthful and inhabits the stored `List Char`'s
interpretation — by induction on the character list, from the nil
head's membership, the cons head's two-argument `piR` membership and
`natLit_facts2` under `Char.ofNat`.

`nilA`/`consA` are the heads *already applied to `Char`*, which is how
`denote2`'s `.lit strVal` clause spells them; that is what keeps the
`List`-type-argument walk (v1's `hnilFit`/`hconsOk`, the `interp_pi`
and `interp_bvar` uses) out of this proof. -/
theorem charList_facts2 {ρ : Nat → V}
    {za sa nilA consA ofNatA natA charA lcA : AVExpr}
    (hokz : AnnotOk2 V ρ za) (hoks : AnnotOk2 V ρ sa)
    (hz : interp2 V ρ za ∈ˢ interp2 V ρ natA)
    (hsucc : interp2 V ρ sa
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA)
    (hokNil : AnnotOk2 V ρ nilA) (hokCons : AnnotOk2 V ρ consA)
    (hokOfNat : AnnotOk2 V ρ ofNatA)
    (hnil : interp2 V ρ nilA ∈ˢ interp2 V ρ lcA)
    (hcons : interp2 V ρ consA ∈ˢ piR 1 (interp2 V ρ charA)
      fun _ => piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ lcA)
    (hofNat : interp2 V ρ ofNatA
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ charA) :
    ∀ cs : List Char,
      AnnotOk2 V ρ (charListT2 nilA consA ofNatA za sa cs) ∧
        interp2 V ρ (charListT2 nilA consA ofNatA za sa cs)
          ∈ˢ interp2 V ρ lcA := by
  -- one character: `Char.ofNat` applied to the numeral
  have helem : ∀ c : Char,
      AnnotOk2 V ρ (.app ofNatA (natLitT2 za sa c.toNat)) ∧
        interp2 V ρ (.app ofNatA (natLitT2 za sa c.toNat))
          ∈ˢ interp2 V ρ charA := by
    intro c
    obtain ⟨hnA, hnm⟩ := natLit_facts2 hokz hoks hz hsucc c.toNat
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_app]
      exact ⟨hokOfNat, hnA, 1, _, _, hofNat, hnm,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp2_app]
      exact app_mem_piR_pos Nat.one_ne_zero hofNat hnm
  intro cs
  induction cs with
  | nil => exact ⟨hokNil, hnil⟩
  | cons c cs ih =>
    obtain ⟨ihA, ihm⟩ := ih
    obtain ⟨heA, hem⟩ := helem c
    -- the partially applied cons: `List.cons (Char.ofNat ⌜c⌝)`
    have hpm : interp2 V ρ
          (.app consA (.app ofNatA (natLitT2 za sa c.toNat)))
        ∈ˢ piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ lcA := by
      rw [interp2_app]
      exact app_mem_piR_pos Nat.one_ne_zero hcons hem
    have hpA : AnnotOk2 V ρ
        (.app consA (.app ofNatA (natLitT2 za sa c.toNat))) := by
      rw [AnnotOk2_app]
      exact ⟨hokCons, heA, 1, _, _, hcons, hem,
        fun h => absurd h Nat.one_ne_zero⟩
    refine ⟨?_, ?_⟩
    · show AnnotOk2 V ρ (.app (.app consA _) _)
      rw [AnnotOk2_app]
      exact ⟨hpA, ihA, 1, _, _, hpm, ihm,
        fun h => absurd h Nat.one_ne_zero⟩
    · show interp2 V ρ (.app (.app consA _) _) ∈ˢ _
      rw [interp2_app]
      exact app_mem_piR_pos Nat.one_ne_zero hpm ihm

/-- **The string facts.**  Every `denote2` string literal is truthful
and inhabits the stored `String`'s interpretation — the character-list
walk under the outer `String.ofList`.

The statement's subject is literally `denote2`'s `.lit strVal`
emission (`Annot/Canon.lean`), with the six heads as arguments. -/
theorem strLit_facts2 {ρ : Nat → V}
    {za sa nilA consA ofNatA ofListA natA charA lcA strA : AVExpr}
    (hokz : AnnotOk2 V ρ za) (hoks : AnnotOk2 V ρ sa)
    (hz : interp2 V ρ za ∈ˢ interp2 V ρ natA)
    (hsucc : interp2 V ρ sa
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA)
    (hokNil : AnnotOk2 V ρ nilA) (hokCons : AnnotOk2 V ρ consA)
    (hokOfNat : AnnotOk2 V ρ ofNatA) (hokOfList : AnnotOk2 V ρ ofListA)
    (hnil : interp2 V ρ nilA ∈ˢ interp2 V ρ lcA)
    (hcons : interp2 V ρ consA ∈ˢ piR 1 (interp2 V ρ charA)
      fun _ => piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ lcA)
    (hofNat : interp2 V ρ ofNatA
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ charA)
    (hofList : interp2 V ρ ofListA
      ∈ˢ piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ strA)
    (s : String) :
    AnnotOk2 V ρ
        (.app ofListA (charListT2 nilA consA ofNatA za sa s.toList)) ∧
      interp2 V ρ
          (.app ofListA (charListT2 nilA consA ofNatA za sa s.toList))
        ∈ˢ interp2 V ρ strA := by
  obtain ⟨hclA, hclm⟩ :=
    charList_facts2 hokz hoks hz hsucc hokNil hokCons hokOfNat hnil
      hcons hofNat s.toList
  refine ⟨?_, ?_⟩
  · rw [AnnotOk2_app]
    exact ⟨hokOfList, hclA, 1, _, _, hofList, hclm,
      fun h => absurd h Nat.one_ne_zero⟩
  · rw [interp2_app]
    exact app_mem_piR_pos Nat.one_ne_zero hofList hclm

/-! ## Re-pointed to `Claims2A` (seal 6)

As in `Step2/Lit.lean`: `charList_facts2` and `strLit_facts2` mention
no fuel, no `denote2` and no mode, so all four repairs pass straight
through them.  The clause below is the part that had to move.
-/

open Setlec (CheckMode Env Expr Name Level inferTypeCore inferBody
  viewM strLitSupported)

variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **I11A (`.lit strVal`), amended.**  The checker returns
`.const String []`, a **fuel-free** `acval` leaf, so `F' = F` here too:
the whole literal layer leaves R3's slack unspent, and the two
witnesses that forced R3 (`.const`, `.fvar`) really are the only ones.

The six heads stay **abstract**, with `hea` saying only that `denote2`
emits the spine over them.  That is a change from `Step2/Lit.lean`,
where they are spelled concretely so that `EnvS2.acval_ok2` can
discharge the truthfulness side, and the reason is structural: `nilA`
and `consA` are `List.nil`/`List.cons` **already applied to `Char`**,
so they are `.app` nodes, not stored leaves, and `acval_ok2` cannot
reach them — their `AnnotOk2` is an `AnnotOk2_app` needing the very
membership facts this clause takes as premises.  Abstracting is
therefore not laziness but the honest shape; a consumer holding the
concrete heads instantiates `_hea` by the `denote2` equation.

`_hea` is carried and **not consumed**: with the subject's annotation
spelled out in the conclusion there is nothing left for it to say, and
the clause's whole content is on the type side.  It stays in the
statement because it is what pins this lemma to its subject — the same
reason the amended `.bvar` clause carries one. -/
theorem infer_strLit_claim2A (m : EnvS2U V env) {d F : Nat} {s : String}
    {t : Expr} {Δa : List AVExpr}
    {nilA consA ofNatA ofListA za sa natA charA lcA strA : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t)
    (_hea : denote2 μ m.acval env φ F d (.lit (.strVal s))
      = some (.app ofListA
          (charListT2 nilA consA ofNatA za sa s.toList)))
    (hty : denote2 μ m.acval env φ F d (.const Setlec.stringName [])
      = some strA)
    (hokz : ∀ ρ : Nat → V, AnnotOk2 V ρ za)
    (hoks : ∀ ρ : Nat → V, AnnotOk2 V ρ sa)
    (hokNil : ∀ ρ : Nat → V, AnnotOk2 V ρ nilA)
    (hokCons : ∀ ρ : Nat → V, AnnotOk2 V ρ consA)
    (hokOfNat : ∀ ρ : Nat → V, AnnotOk2 V ρ ofNatA)
    (hokOfList : ∀ ρ : Nat → V, AnnotOk2 V ρ ofListA)
    (hz : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ za ∈ˢ interp2 V ρ natA)
    (hsucc : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ sa
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA)
    (hnil : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ nilA ∈ˢ interp2 V ρ lcA)
    (hcons : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ consA ∈ˢ piR 1 (interp2 V ρ charA)
        fun _ => piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ lcA)
    (hofNat : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ofNatA
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ charA)
    (hofList : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ofListA
      ∈ˢ piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ strA) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ (.app ofListA
            (charListT2 nilA consA ofNatA za sa s.toList)) ∧
          interp2 V ρ (.app ofListA
            (charListT2 nilA consA ofNatA za sa s.toList))
            ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨F, strA, Nat.le_refl F, hty, fun ρ hρ => ?_⟩
    exact strLit_facts2 (hokz ρ) (hoks ρ) (hz ρ hρ) (hsucc ρ hρ)
      (hokNil ρ) (hokCons ρ) (hokOfNat ρ) (hokOfList ρ) (hnil ρ hρ)
      (hcons ρ hρ) (hofNat ρ hρ) (hofList ρ hρ) s
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Re-pointed to `Claims2C` (seal 14)

`InferClaims2C` asks for the **returned type's** `AnnotOk2` alongside
the subject's, ρ-uniformly.  For this clause the returned type is
`.const String []`, whose annotation `denote2` reads straight out of
the canonical valuation — so `EnvS2.acval_ok2` discharges it, at every
`ρ`, with no `Sat2` spent.  The literal layer therefore pays nothing
for the extension, which is what the lemma below records. -/

/-- **I11C (`.lit strVal`), re-pointed.**  The sealed conclusion
re-associated into `Claims2C`'s three conjuncts, with the new one
(`AnnotOk2` of the returned type) free from `acval_ok2`.  `F' = F`
still: nothing in this clause spends R3's slack. -/
theorem infer_strLit_claim2C (m : EnvS2U V env) {d F : Nat} {s : String}
    {t : Expr} {Δa : List AVExpr}
    {nilA consA ofNatA ofListA za sa natA charA lcA strA : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t)
    (_hea : denote2 μ m.acval env φ F d (.lit (.strVal s))
      = some (.app ofListA
          (charListT2 nilA consA ofNatA za sa s.toList)))
    (hty : denote2 μ m.acval env φ F d (.const Setlec.stringName [])
      = some strA)
    (hokz : ∀ ρ : Nat → V, AnnotOk2 V ρ za)
    (hoks : ∀ ρ : Nat → V, AnnotOk2 V ρ sa)
    (hokNil : ∀ ρ : Nat → V, AnnotOk2 V ρ nilA)
    (hokCons : ∀ ρ : Nat → V, AnnotOk2 V ρ consA)
    (hokOfNat : ∀ ρ : Nat → V, AnnotOk2 V ρ ofNatA)
    (hokOfList : ∀ ρ : Nat → V, AnnotOk2 V ρ ofListA)
    (hz : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ za ∈ˢ interp2 V ρ natA)
    (hsucc : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ sa
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA)
    (hnil : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ nilA ∈ˢ interp2 V ρ lcA)
    (hcons : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ consA ∈ˢ piR 1 (interp2 V ρ charA)
        fun _ => piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ lcA)
    (hofNat : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ofNatA
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ charA)
    (hofList : ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ofListA
      ∈ˢ piR 1 (interp2 V ρ lcA) fun _ => interp2 V ρ strA) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ (.app ofListA
          (charListT2 nilA consA ofNatA za sa s.toList))) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ (.app ofListA
          (charListT2 nilA consA ofNatA za sa s.toList))
          ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    have hfacts : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ (.app ofListA
            (charListT2 nilA consA ofNatA za sa s.toList)) ∧
          interp2 V ρ (.app ofListA
            (charListT2 nilA consA ofNatA za sa s.toList))
            ∈ˢ interp2 V ρ strA := fun ρ hρ =>
      strLit_facts2 (hokz ρ) (hoks ρ) (hz ρ hρ) (hsucc ρ hρ)
        (hokNil ρ) (hokCons ρ) (hokOfNat ρ) (hokOfList ρ) (hnil ρ hρ)
        (hcons ρ hρ) (hofNat ρ hρ) (hofList ρ hρ) s
    exact ⟨F, strA, Nat.le_refl F, hty, fun ρ hρ => (hfacts ρ hρ).1,
      fun ρ _ => annotOk2_of_denote2_const hty ρ,
      fun ρ hρ => (hfacts ρ hρ).2⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end Setlec.SetR.Interp2
