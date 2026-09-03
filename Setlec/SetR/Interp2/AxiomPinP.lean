import Setlec.SetR.Interp2.AxiomMemP
import Setlec.SetR.StdAxiomKey

/-!
# The pin tier, at the validated-annotation currency (task #161,
ENDGAME A part 2)

`DeclAxiomR`'s four branches at the P invariant.  Two of them land
here; the other two are blocked on one named fact, and the block is
recorded rather than papered over.

## What a branch owes

`harvestAxiomP` (`Interp2/HarvestP.lean`) is the wrapper: the *type*
side is harvested from `ConstantValR`'s own run (`accepted_reads` is a
theorem since part 1, so nothing is routed), and what the branch must
supply is the leaf `A` with

* `hAerase`/`hAclosed`/`hAparams` — syntactic, from the branch key and
  the `EnvS2Core` fields;
* `hAok`/`hAvalid` — free at a `BConst` or `acval` leaf (`AnnotOk2`'s
  and `AnnotValidV`'s `.const`/`.prf` clauses are `True`, and an
  `acval` leaf carries both as invariant fields);
* `hmemA` — **the semantic content**: `interp2` of the leaf inhabits
  `interp2` of the *stored* type's `denoteP` reading.

## THE WALL, named: the stored type's reading is not the pin's

`hmemA` speaks about the reading of `type'`, the *stored* annotated
type.  Every branch key knows the type only through `matchesPin`,
which compares `erasePw ∘ eraseNames` — so the pin fixes the stored
type **up to binder names and binder `pw` data**.

At v1 that costs nothing: `denote` reads neither, so
`denote_matchesPin` (`Verify/Denote/Inst.lean:422`) turns a pin hit
into an equality of denotations and every consumer computes on the
pin.  **At the P currency the analogue is FALSE**, and not marginally:
`denoteP`'s binder clauses read `pwBit φ mb.pw`, and `erasePw`
normalizes every datum to `.never`, whose bit is `1`.  So
`denoteP (e.erasePw) = denoteP e` fails at the very first Prop-codomain
binder, and with it any `denoteP_erasePw`/`denoteP_pinEq`/
`denoteP_matchesPin` chain stated the v1 way.  This is the erasePw
RULING's own point 2, met: the P tier must take the bits from the
front door's recorded run, never from the match verdict.

Concretely, what each remaining branch needs is:

> **`pwBitsAgree`**: at `μ.verified`, for each binder of the stored
> type, `pwBit φ` of the stored datum equals `pwBit φ` of the pin's
> generated datum.

and the route is fixed by the ruling: `ConstantValR`'s run conjunct
(H1) gives `inferTypeCore μ env F 0 type' = .ok stype`; inverting it
through `inferTypeCore_forall_inv` once per binder yields the
validation conjunct `(Level.zeronessOf v).equiv mb.pw = true`, hence
(`pwBit_of_equiv_zeronessOf`) `pwBit φ mb.pw = 0 ↔ Level.eval φ v = 0`;
the pin's datum is that same zero-ness *by construction*, so the two
bits agree **once `Level.eval φ v` is known**.

And that last step is the content that is not yet in the tree: `v` is
`ensureSort` of the inferred type of the *opened body*, so knowing it
means executing the checker's inference symbolically along the pinned
telescope (for `propext`: that `a = b` infers to `Prop`, from the
stored `Eq`'s own pinned type).  The telescope collapse makes it one
fact per pin rather than one per binder — `imax x y = 0 ↔ y = 0`, so
every binder of a chain carries the innermost codomain's bit — but it
is one genuine symbolic-inference lemma per pinned family.

That lemma is `AxiomBitsP`'s, and the two standard axioms' memberships
are `AxiomMemP`'s, so `axiomStdP` below closes the branch that record
named.  Read the ENDGAME C seal for what the memberships actually cost:
the *companions'* bits are not reachable by any bit lemma, and two of
the three obstructions that follow from that were removed
(`pi_sort_bit_ne_zero`, the vacuous minor) rather than assumed.

## THE SECOND WALL: `ofReduce*` needs a `ReduceOpsP` field

`ofReduceNat`/`ofReduceBool` are **not** blocked on their bits.  Their
bits are the easy half: the pin's innermost body is
`Eq.{1} E (op a) b`, an `Eq`-spine over the *nose-pinned* `Eq`
(`ofReduceAxOk`'s own first conjunct), so `inferTypeCore_eqSpineS`
applies verbatim and `propext_bitsP`'s three moves transpose
unchanged — all three binders carry bit `0`.  (The ENDGAME B seal
predicted "their move 2 goes through the stored `Nat`/`Bool` families";
it does not — the codomain is the `Eq`, and `Nat`/`Bool` appear only as
the spine's *type* argument, which `inferTypeCore_eqSpineS` never
looks at.)

The block is the **membership**, and it is an invariant gap.  With all
three bits `0` the reading's products are truth values, the witness is
forced to `pt`, and the innermost obligation is

> for every `a`, `b` in the element type, `eqv (op a) b` inhabited must
> force `eqv a b` inhabited — that is, `op a = a`.

That is exactly `EnvS.reduce_ops` (`ReduceOpsV`, `EnvS.lean:138`): *the
trusted operation is the identity on its element type*.  The field
exists, at the **v1 currency** — `interp`, `cval` — and `EnvS2PM` has
no mirror.  Nor can one be derived: the transfer would be an erasure
factoring of `interp2` through `interp`, refuted at exactly the λ-nodes
the operation's leaf is made of (the literal-tier seal II finding 1,
the same refutation that makes `eq_lawP` a field rather than a
theorem).

**STOP-AND-NAME**: `ofReduceNat`/`ofReduceBool` are blocked on a
`ReduceOpsP` field of `EnvS2PM` — `ReduceOpsV`'s mirror at `interp2`
and `acval` — established wherever `reduce_ops` is, and on nothing
else.  This is the same species as ENDGAME B's `rec_rules` wall and as
`eq_lawP`/`caps_ok`'s own existence: an environment law whose only
supplier is the install that fixes the leaf.  Recorded rather than
assumed; a premise for it would be a conditional form, and
`axiomStepPB_of` is therefore **not stated**.

## What lands here

* **the tolerated skip** — `axiomSkipP`: the environment does not
  move, so the P invariant is the one already held;
* **`Lean.trustCompiler`** — `axiomTrustCompilerP`: the one pinned
  axiom whose type is a **bare constant**.  `.const` carries no binder
  and therefore no datum, so `erasePw`'s forgiveness is empty on it
  and the pin fixes `type' = .const trueName []` **on the nose**
  (`erasePw_const_invS ∘ eraseNames_const_invS`).  The wall above
  simply is not there, and the branch goes through: the leaf is the
  stored `True.intro`'s annotated valuation and `hmemA` is
  `EnvS2PM.mem_typeP` at that constant, both readings being the same
  `acval trueName ψ`.

That is also why this branch was landed first: it exercises the whole
`harvestAxiomP` bill end to end — extension, agreement, the four
syntactic leaf facts and the membership — so the remaining branches
inherit tested scaffolding;
* **the two standard axioms** — `axiomStdP`, both halves, on
  `AxiomBitsP`'s bits and `AxiomMemP`'s memberships.

Three of `DeclAxiomR`'s four branches, then.  The fourth is the second
WALL above.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The tolerated skip -/

/-- **The tolerated-axiom skip.**  `DeclAxiomR`'s fourth branch stores
nothing (`env₂ = env`), so there is no leaf, no extension and no
crossing: the P invariant at the successor environment *is* the one
held at the prefix. -/
theorem axiomSkipP (mp : EnvS2PM V μ env) :
    Nonempty (EnvS2PM V μ env) := ⟨mp⟩

/-! ## `Lean.trustCompiler` -/

/-- **The `trustCompiler` branch, discharged.**

The pin fixes the axiom's type to the stored `True` *on the nose* —
`ConstantVal.matchesPin` compares through `erasePw ∘ eraseNames`, and
neither erasure moves a `.const` — so this is the one pinned axiom
whose `denoteP` reading is computable from the pin alone (see the
module docstring's WALL).  The leaf is the stored `True.intro`'s
annotated valuation, and the membership is that constant's own
`mem_typeP`, whose type reads to the same `acval trueName ψ` the
axiom's does. -/
theorem axiomTrustCompilerP (hμ : μ.verified = true)
    (mp : EnvS2PM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValR μ F env mp.base2.base.cval cv type')
    (hname : cv.name = Setlec.trustCompilerName)
    (hok : Setlec.trustCompilerOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvS2PM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT, hfrontT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the guard's two pin hits, unpacked exactly as `trustCompilerKeyS`
  -- unpacks them
  have hokc := hok
  simp only [Setlec.trustCompilerOk, Bool.and_eq_true] at hokc
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hokc
  cases hfT : env.find? Setlec.trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? Setlec.trueIntroName with
  | none => rw [hfTi] at hTi; exact nomatch hTi
  | some ciTi =>
  rw [hfT] at hT
  rw [hfTi] at hTi
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    cases ciT with
    | indInfo cvT caps =>
      simp only [ConstantVal.matchesPin, Bool.and_eq_true,
        decide_eq_true_eq] at hT
      exact hT.1.2
    | _ => exact nomatch hT
  obtain ⟨hlpTi, htyTi⟩ : ciTi.toConstantVal.levelParams = [] ∧
      ciTi.toConstantVal.type = .const Setlec.trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, erasePw_const_invS (eraseNames_const_invS hTi.2)⟩
    | _ => exact nomatch hTi
  -- **the pin bites on the nose**: a `.const` has no binder, so
  -- `erasePw` forgives nothing here
  have htyA : type' = .const Setlec.trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact erasePw_const_invS (eraseNames_const_invS hA.2)
  have hnameTi : ciTi.name = Setlec.trueIntroName := Env.find?_name hfTi
  -- the v1 extension, at the *named* valuation.  `trustCompilerKeyS`
  -- would supply one, but only under an `∃` — and this branch needs to
  -- know **which** leaf was installed (the annotated twin must erase to
  -- it), so the witness is re-chosen here rather than unpacked.  It is
  -- the key's own: the stored `True.intro`'s valuation.
  have hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed mp.base2.base.cval env ψ type' = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.base.cval Setlec.trueIntroName ψ)
          ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t := by
    intro ψ
    obtain ⟨t, ht, hlaw⟩ := mp.base2.base.cval_memType hfTi ψ
    rw [htyTi, show denoteClosed mp.base2.base.cval env ψ
        (Expr.const Setlec.trueName [])
        = denote mp.base2.base.cval env ψ 0 (.const Setlec.trueName [])
        from rfl, denote_const_nolevelsS hfT hlpT ψ 0] at ht
    obtain rfl := Option.some.inj ht
    refine ⟨mp.base2.base.cval Setlec.trueName ψ, ?_, hlaw⟩
    rw [htyA]
    show denote mp.base2.base.cval env ψ 0 (.const Setlec.trueName []) = _
    rw [denote_const_nolevelsS hfT hlpT ψ 0]
  have hwfc : Setlec.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine Setlec.EnvWF.cons mp.base2.base.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  obtain ⟨m', hag, hself⟩ :=
    extendAxiomS mp.base2.base (cv := ⟨cv.name, cv.levelParams, type'⟩)
      (Vf := fun ψ => mp.base2.base.cval Setlec.trueIntroName ψ)
      hfresh hwfc (fun ψ => mp.base2.base.cval_closed _ ψ)
      (fun φ₁ φ₂ _ => mp.base2.base.val_params Setlec.trueIntroName ciTi
        hfTi φ₁ φ₂ (by rw [hlpTi]; intro p hp; exact nomatch hp))
      (fun ψ ρ => mp.base2.base.annot_okV _ ψ ρ) hkey hnres
      (by rw [hname]; decide)
  -- the leaf: the stored `True.intro`'s *annotated* valuation
  refine harvestAxiomP (V := V) hμ mp hcv m' hag
    (A := fun ψ => mp.base2.acval Setlec.trueIntroName ψ) ?_ ?_ ?_ ?_ ?_ ?_
    -- `trustCompiler` is not a compiler-trust *operation*: the pin
    -- fixes the name, and the two operations are installed as opaques
    (by rw [hname]; decide)
  · -- `hAerase`: the leaf erases to the installed valuation, which is
    -- `Vf` — the stored `True.intro`'s
    intro ψ
    rw [mp.base2.acval_erase, hself ψ]
  · -- `hAclosed`
    exact fun ψ k => mp.base2.acval_closed _ ψ k
  · -- `hAparams`: `True.intro` is level-monomorphic, so the premise is
    -- vacuous
    intro ψ₁ ψ₂ _
    exact mp.base2.acval_params _ ciTi hfTi ψ₁ ψ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · exact fun ψ ρ => mp.base2.acval_ok2 _ ψ ρ
  · exact fun ψ ρ => mp.acval_validV _ ψ ρ
  · -- `hmemA`: the axiom's type and `True.intro`'s stored type are the
    -- *same* bare constant, so they have the same reading, and the
    -- membership is that constant's own `mem_typeP`
    intro ψ ta hta ρ
    rw [htyA, denoteP_levelless_const hfT hlpT] at hta
    obtain rfl : ta = mp.base2.acval Setlec.trueName ψ :=
      (Option.some.inj hta).symm
    have hmem := mp.mem_typeP ciTi (Env.find?_mem hfTi) ψ
      (mp.base2.acval Setlec.trueName ψ)
      (by rw [htyTi]; exact denoteP_levelless_const hfT hlpT) ρ
    rwa [hnameTi] at hmem

/-! ## The two standard axioms

`DeclAxiomR`'s first branch, both halves.  The bits come from
`AxiomBitsP` (the axiom's *own* recorded run) and the memberships from
`AxiomMemP`; the v1 extension is `extendAxiomS` at the **named**
witness, which `StdAxiomKey.lean`'s `propextKeyS_mem`/`choiceKeyS_mem`
now expose — the `trustCompiler` branch's lesson, that the key's `∃` is
one currency too coarse for a P leaf, generalized. -/

/-- **The standard-axiom branch, discharged.**  The leaf is the layer's
own constant in both halves, so every syntactic obligation is `rfl` or
a `const` clause, and the whole content is the membership. -/
theorem axiomStdP (hμ : μ.verified = true)
    (mp : EnvS2PM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValR μ F env mp.base2.base.cval cv type')
    (hok : Setlec.stdAxiomOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvS2PM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT, hfrontT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  obtain ⟨stype, usort, hst, hens⟩ := hrunT
  have hwfc : Setlec.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine Setlec.EnvWF.cons mp.base2.base.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  by_cases hn : cv.name = propextName
  · obtain ⟨m', hag, hself⟩ :=
      extendAxiomS mp.base2.base (cv := ⟨cv.name, cv.levelParams, type'⟩)
        (Vf := fun _ => .const .propext [])
        hfresh hwfc (fun _ => trivial) (fun _ _ _ => rfl)
        (fun _ _ => trivial)
        (fun ψ => propextKeyS_mem mp.base2.base hok hn ψ) hnres
        (by rw [show (⟨cv.name, cv.levelParams, type'⟩ :
          ConstantVal).name = cv.name from rfl, hn]; decide)
    refine harvestAxiomP (V := V) hμ mp hcv m' hag
      (A := fun _ => .const .propext []) (fun ψ => by rw [hself ψ]; rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp)
      (fun _ _ => by simp) ?_ (by rw [hn]; decide)
    intro ψ ta hta ρ
    exact propext_memP hμ mp hok hn hst ψ ta hta ρ
  · by_cases hn2 : cv.name = choiceName
    · -- the pin fixes the axiom's one level parameter, so both the v1
      -- witness and the P leaf read only `ψ uN`
      have huN : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → ψ₁ uN = ψ₂ uN := by
        intro ψ₁ ψ₂ hp
        obtain ⟨-, -, -, hApin⟩ := nonempty_shapes hok hn2
        have hlpA : cv.levelParams = choiceA.levelParams :=
          (matchesPin_invT hApin).2
        refine hp uN ?_
        rw [hlpA, show choiceA.levelParams = [uN] from rfl]
        exact List.Mem.head _
      obtain ⟨m', hag, hself⟩ :=
        extendAxiomS mp.base2.base
          (cv := ⟨cv.name, cv.levelParams, type'⟩)
          (Vf := fun ψ => .const .choice [ψ uN])
          hfresh hwfc (fun _ => trivial)
          (fun ψ₁ ψ₂ hp => by
            show VExpr.const .choice [ψ₁ uN] = VExpr.const .choice [ψ₂ uN]
            rw [huN ψ₁ ψ₂ hp])
          (fun _ _ => trivial)
          (fun ψ => choiceKeyS_mem mp.base2.base hok hn2 ψ) hnres
          (by rw [show (⟨cv.name, cv.levelParams, type'⟩ :
            ConstantVal).name = cv.name from rfl, hn2]; decide)
      refine harvestAxiomP (V := V) hμ mp hcv m' hag
        (A := fun ψ => .const .choice [ψ uN])
        (fun ψ => by rw [hself ψ]; rfl)
        (fun _ _ => rfl)
        (fun ψ₁ ψ₂ hp => by
          show AVExpr.const .choice [ψ₁ uN] = AVExpr.const .choice [ψ₂ uN]
          rw [huN ψ₁ ψ₂ hp])
        (fun _ _ => by simp) (fun _ _ => by simp) ?_
        (by rw [hn2]; decide)
      intro ψ ta hta ρ
      exact choice_memP hμ mp hok hn2 hst ψ ta hta ρ
    · exfalso
      unfold Setlec.stdAxiomOk at hok
      rw [show (⟨cv.name, cv.levelParams, type'⟩ : ConstantVal).name
        = cv.name from rfl] at hok
      rw [if_neg hn, if_neg hn2] at hok
      exact nomatch hok

end Setlec.SetR.Interp2
