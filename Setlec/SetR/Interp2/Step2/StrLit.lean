import Setlec.SetR.Interp2.Step2.Lit

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

end Setlec.SetR.Interp2
