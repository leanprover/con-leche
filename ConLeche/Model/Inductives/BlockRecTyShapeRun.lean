module

public import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyping

public section

/-!
# The recursor type's binder SHAPE, at the run

`BlockRecTyShapeOne` (`Model/Inductives/BlockRecTyping.lean`) is what the
recursor model reads off the stored recursor types: the arity, the
parameters, the eliminated member's index telescope and the major.
This file produces it from the recursor stage's run and the members'
own former data.

It is a LEAF module and it has to be: it consumes `prefixDoms_spineFit`
(`BlockRecPreRun`) and `recStage_tyPis`
(`BlockRecMem`, which `BlockRecPreRun` sits above), so it can be an
addition to neither.

**What the check actually pins**, and what each clause is therefore
bounded by (`targetRecTy`, `Kernel/Inductives/RecCheck.lean`):

* `nP ≤ rP` and `mI = rP + nIdx_m` are the stage's own two `unless`es
  — clauses 1 and 2, arithmetic once the member's index count is
  identified with `nIdx_m` (`FormerData.len`);
* the first `nP` binder DOMAINS are compared BINDER BY BINDER with the
  member's own opened former telescope — clause 3, and it is an `↔`
  between FITS (never a syntactic equality: the two spellings are only
  ever certified defeq).  BOTH directions are paid the same way, which
  is why the clause is an `↔` and clause 4 is not:
  `prefixDoms_spineFit` is symmetric in its two openings (it takes the
  comparison as an `Or`, so the swapped call is the same hop with the
  disjunct on the other side), and the member-to-member parameter
  agreement (`paramsIff`) is an `↔` already;
* the binders `nP … rP-1` and the INDEX binders are never looked
  inside at all.  Clause 4 therefore does not read them: it reads the
  MAJOR, whose domain is `T_m p⃗ ı⃗` on the nose, so its reading is a
  spine against the member's FORMER — a λ-tower — and the spine's
  grading carries the fit (`spineFit_of_major_grading`).  The tower's
  binder numeral is `w ψ + 1`, never zero, so this survives a
  `Prop`-valued block;
* the MAJOR's syntactic pin is clause 6, read off the opening's own
  fvars (`interp_of_major_reading`).

The OPPOSITE direction of clause 4 is not produced: nothing in the run
ties the recursor's index binders to the member's telescope except the
per-argument `isDefEq` inside `checkConstantVal`'s inference of the
major's domain, and no consumer needs it (stage (b'')'s converse,
`blockRecIdxConv_run`, is what the model reads instead).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. Kit -/

/-! ## 2. The member-side run facts

Five statements about the members, all of them the block install's
own: the shape agreement (`d.nP`, `d.k`), the per-member former data
(`BlockFormerFacts.fdOf` at the CONSTRUCTORS' environment, which is
where the recursor stage runs), the member record's name and index
count, the leaf's λ-TOWER shape (whose binder numeral is
`w ψ + 1` — never zero, which is why the index clause survives a
`Prop`-valued block), and official's parameter agreement
(`BlockFormerFacts.paramsIff`).

It is a bundle and not five premises because every clause below needs
two or three of them, and it has exactly one consumer, the shape's
producer. -/
@[expose] def BlockMembersRun {envC : Env} (mo : EnvModel V envC) (d : BlockData V)
    (q : ConLeche.BlockShape) (cvTas : List ConstantVal) : Prop :=
  d.nP = q.nP ∧ d.k = q.members.length ∧
  cvTas.length = d.k ∧
  (∀ (m : Nat) (cvTb : ConstantVal), cvTas[m]? = some cvTb →
    d.memberName m = cvTb.name ∧ cvTb.levelParams = q.lps ∧
    (∃ caps, envC.find? cvTb.name = some (.indInfo cvTb caps)) ∧
    cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
    FormerData mo cvTb (d.nP + d.nIdxAt m) d.resSort (d.ppsM m)) ∧
  (∀ (m : Nat) (ms : ConLeche.MemberShape), q.members[m]? = some ms →
    d.memberName m = ms.cvT.name ∧ d.nIdxAt m = ms.nIdx) ∧
  (∀ (m : Nat) (ψ : Name → Nat), m < d.k →
    ∃ B, mo.acval (d.memberName m) ψ = mkLamsC (d.w ψ + 1) (d.ppsM m ψ) B) ∧
  (∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ ↔ Sat V (d.params ψ).reverse ρ)

section Run

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V}

/-! ## 3. The MAJOR's reading, and the arity

One theorem, because the major's reading is what identifies the
recursor's member and the arity is what its position is read at. -/

/-! ## 4. The INDEX clause's payable half, at the run

The recursor's own index binders are never inspected by the check, so
nothing here reads them: what carries the fit is the MAJOR, whose
domain is the member's FORMER applied to the prefix and index binders.
The former is a λ-tower whose binder numeral is `w ψ + 1` — **never
zero**, so this clause survives a `Prop`-valued block, where the
rule contract's own fit conjunct is refutable. -/

/-! ## 5. The PARAMETER clause, at the run

`targetRecTy` compares the recursor's first `nP` binder domains
BINDER BY BINDER with the ELIMINATED member's own opened former
telescope — never with the block's, and never syntactically: it is an
`isDefEq` per position.  So the clause is an `↔` between FITS
(`prefixDoms_spineFit`, the certified hop, called once each way),
composed with the members' own parameter agreement
(`BlockFormerFacts.paramsIff`, itself an `↔`) between the eliminated
member's telescope and the block's `d.params`.

**A clause is stated in the direction(s) that have producers.**  This
one has both, which is what separates it from the index clause: the
hop takes its comparison as an `Or` of the two `isDefEq` orientations
and proves the transfer either way, so swapping its two openings costs
nothing. -/

/-! ## 6. THE SHAPE, at the run -/

/-! ## 7. The `ih` KEY's block facts -/

section Keys

/-- **A member's index arity**: the index telescope a member
contributes has that member's index count — the one that ties the
field's readings to the CALLEE's telescope. -/
theorem blockMembers_IdsM_length {envC : Env} {mo : EnvModel V envC} {d : BlockData V}
    {q : ConLeche.BlockShape} {cvTas : List ConstantVal}
    (hmr : BlockMembersRun mo d q cvTas) {mm : Nat} (hmm : mm < d.k) (ψ : Name → Nat) :
    (d.IdsM mm ψ).length = d.nIdxAt mm := by
  obtain ⟨-, -, hlenCv, hcvF, -, -, -⟩ := hmr
  obtain ⟨cvTb, hcvTa⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hmm)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hcvF _ _ hcvTa
  rw [BlockData.IdsM, List.length_map, List.length_drop, hFD.len ψ]
  omega

end Keys

/-! ## `WalkCtx` at the rule's opened frame

The walk's ENTRY context `hW` is at the rule frame, and the rule
frame is the one `ctxOk_blockFrame` (`BlockRecTyping.lean`) already
describes: three openings at the offsets `0`, `rP` and `rP + nF`, the
context `ihdoms.reverse ++ (pdoms ++ fdoms).reverse`, and a valuation
`consList ihvals (consList (xs ++ fs) ρ₀)`.

**`WalkCtx` is `CtxOk`'s inputs, re-indexed.**  `ctxOk_blockFrame`
reads the openers ASCENDING (opener `i` at depth `i`, context slot
`D - 1 - i`); `WalkCtx` carries the opening LIST, which the walk
conses onto, so it reads them DESCENDING (`as2 = L.reverse`, slot `j`
at depth `D - 1 - j`).  The two are the same statement under
`List.getElem?_reverse`, and `D - 1 - (D - 1 - j) = j` below `D` is
the whole of the translation.

What `WalkCtx` asks beyond `CtxOk` is the frame's three HEREDITARY
facts — the openers' annotations are `looseBVarsBounded 0`, bounded by
`envT`, and draw their own leaves from the frame again, all stated
over the opener list. -/

/-- **`WalkCtx` at the rule stage's opened frame** — `hW` at the
entry, from exactly `residueOk_blockFrame`'s inputs plus the frame's
three hereditary facts.

No `w` hypothesis anywhere: the evidence is the two `SpineFit`s and
the openers' readings, never a membership in the carrier. -/
theorem walkCtx_blockFrame {envT : Env} {mT : EnvModel V envT} {ψ : Name → Nat}
    {rP nF nR : Nat} {recTy crest ihTele : Expr}
    {fvsPref fvsF fvsIh : List Expr} {o₁ o₂ o₃ : Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    {pdoms fdoms ihdoms : List AnnotTerm}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hdoms : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta mT.acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default))
    (hokΔ : ∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default))
    (hlbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hcbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ConstsBound envT x)
    (hclF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    WalkCtx V mT ψ (rP + nF + nR) (consList ihvals (consList (xs ++ fs) ρ₀))
      (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) (fvsPref ++ fvsF ++ fvsIh).reverse := by
  have hlenL : (fvsPref ++ fvsF ++ fvsIh).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, openPisAtFvars_length rP h₁,
      openPisAtFvars_length nF h₂, openPisAtFvars_length nR h₃]
  refine ⟨sat_blockFrame_length hp hf hidx, sat_blockFrame hsp hih, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    have hj : j < rP + nF + nR := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [List.length_reverse, hlenL] at this
      exact this
    rw [List.getElem?_reverse (by rw [hlenL]; exact hj), hlenL] at hx
    have h := hdoms _ x hx
    rwa [show rP + nF + nR - 1 - (rP + nF + nR - 1 - j) = j from by omega] at h
  · intro s hs ρ hρ
    have h := hokΔ (rP + nF + nR - 1 - s) (by omega) ρ hρ
    rwa [show rP + nF + nR - 1 - (rP + nF + nR - 1 - s) = s from by omega] at h
  · exact fun x hx => hlbF x (List.mem_reverse.mp hx)
  · exact fun x hx => hcbF x (List.mem_reverse.mp hx)
  · exact fun x hx l hl => List.mem_reverse.mpr (hclF x (List.mem_reverse.mp hx) l hl)

end Run

end ConLeche.Model
