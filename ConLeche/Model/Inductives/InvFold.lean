module

public import ConLeche.Model.Inductives.FoldChoice
public import ConLeche.Semantics.NoBVar
public import ConLeche.Model.Inductives.FixNoBVar
public import ConLeche.Model.Inductives.FixShadow
public import ConLeche.Model.Inductives.FixChains
import ConLeche.Model.Inductives.FixChainFacts
import ConLeche.Model.Inductives.StructCtorFrames
import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.MutualChains
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.FixRecPre
public section

/-!
# The inverse fold `ψ⁻¹`: the kit at the auxiliary datum (task #279 M-B′)

`FoldChoice` types and fires a member's recursor at a motive/minor
CHOICE.  This module is the choice that spells `ψ⁻¹` — the map from
an auxiliary copy `A` (a member of the scratch block) back to its
container at the pins, `⟦J Ds⟧`, and the identity on a real member —
over the AUXILIARY datum `d` (task #278's mutual datum of the scratch
block: every member real, the pins the parameter variables):

* the TARGETS `invTgAV L pinsT t := λ ı⃗, L t (pinsT t) ı⃗` — a leaf `L t`
  at pins `pinsT t` (both the consumer's: the container's leaf at the
  pin's readings for a copy, the member's own leaf at the parameter
  variables for a real member), constant in the major;
* the BODIES `invBodyAV head useIh J` — a head `head J` at the
  parameter frame (the container's constructor at the pins for a copy's
  constructor, the member's own at the parameters for a real one)
  applied to the MIXED variable spine: the inductive hypothesis where
  `useIh J i` (every aux-recursive field of a copy's constructor — the
  fold rebuilds with the RESTORED constructor, whose fields at those
  positions are the containers) and the field itself elsewhere (every
  field of a real member's constructor: `ψ⁻¹` is the identity there).

**What the kit asks of the consumer, and what this module supplies.**
`choice_prefix_fit`/`choice_fold_iota` take, per constructor, the
field-side facts `hfield`/`hEs` and the body's fact `hleaf`.  `hleaf`
is proved here from ONE hypothesis in the aux datum's vocabulary,
`CtorAtPins`: the head inhabits a graded Π-tower whose binders accept
every spine fitting the TARGET-FORM field domains (`tgFieldAV`: the
target of the field's member at the field's index readings, under the
field's telescope, where `useIh`; the field's own domain elsewhere)
and whose body at such a spine is the member's target at the
constructor's index readings.  For a real member's constructor it is
the constructor's own reading (`ctorAtPins_real`, from
`FixCtorFactsAt`); for a copy's it is the container constructor's
reading at the pins — the discharge from the container's datum
(`d_J.ctors` at the level instantiation, `instSeq` at the pins) and
the elimination ledger (`mkCopy_inv`/`elimCtors_getElem?`) is the next
step, and needs the pins typed at the scratch environment
(`pinsOkAux`, task #279 K.2).

**The first lemma: the syntactic-to-semantic bridge.**  The body
types `head J` at a MIXED spine — inductive hypotheses where the fields
were — so every field domain, telescope entry and index expression is
read at a frame that differs from the fields' at the recursive slots.
`FixCtorDataI.noBVar_entries` reads the datum's `mentionsFvar` facts
(`FixOpened.recF`/`reflF`: a recursive variable is a leaf of no later
domain nor of the residual) as `NoBVar` of the readings over the
recursive slots below them, and `interp_congr_shadowRel` is the
transport between two spines agreeing off those slots
(`agreeOff_shadow`).  The family view proves the same inside
`fixChainFacts_of`/`mutualRealChainNb`; here it is a standalone lemma
over the datum, because the consumer is not a chain walk.

**The fits are the leaf's λ-shape.**  `hfield`/`hEs` need the index
readings of a constructor (and of every recursive field) to FIT its
member's index telescope, and `FixCtorFactsAt` records the entries'
spellings and gradings, not the fits.  The routes derive the fits at
install from the LEAF's shape — a graded application of a λ-tower
forces its arguments into the tower's binders
(`spineFit_of_wellDenoted_lams`, `leafSpineFit`) — and the clause does
not record that shape.  This module takes it as the hypothesis
`LeafShape` (per real member: `∃ B, ⟦T_t⟧ = mkLamsC (w+1) (ppsM t) B`,
the routes' own `hleafT`) and derives the fits (`ctorFits_of_leafShape`);
recording it on `IndRep` is the datum finding of DESIGN §M.18.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The bridge: the datum's `mentionsFvar` facts as `NoBVar` -/

/-- **A recursive constructor's readings mention no recursive slot
below them** (`FixOpened.recF`/`reflF`'s `mentionsFvar`, read
semantically): field `i`'s domain, a reflexive field's telescope
entries and index expressions, and the residual's index readings are
`NoBVar` over the recursive slots strictly below the position they are
read at.  `fixChainFacts_of`'s `nb`/`nbT`/`nbE`/`nbEs`, standalone over
the datum and without the `recAt` guard (a non-recursive field's
telescope and index expressions are empty). -/
theorem FixCtorDataI.noBVar_entries {env₀ : Env} {m : EnvModel V env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {tgtOf : Nat → Name}
    {nIdxOf : Nat → Nat}
    (hD : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks
      fvsP xFvs xrest Eiss tss tgtOf nIdxOf)
    (hcf : cvC.type.hasFvar = false) (hcb : cvC.type.looseBVarsBounded 0 = true)
    (ψ : Name → Nat) :
    (∀ i, i < nF → NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i))
      ((ds ψ).getD (nP + i) default).2.2) ∧
    (∀ i, i < nF → ∀ k d, ((tss ψ).getD i [])[k]? = some d →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + k)) d.2.2) ∧
    (∀ i, i < nF → ∀ E ∈ (Eiss ψ).getD i [],
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + ((tss ψ).getD i []).length)) E) ∧
    (∀ E ∈ Es ψ, NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + nF) (nP + nF)) E) := by
  -- the openings, the opened record
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  have hO : Opened m ψ (nP + nF) cvC.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI m T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  -- a recursive variable is a leaf of no later domain nor of the residual
  have hrecGet : ∀ i, recAt nP ks (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · obtain ⟨-, -, -, -, hlater, hres⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, hres⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
  -- field `i`'s opened domain: scoped, leaf-free of the recursive
  -- variables below it
  have hdom : ∀ i, i < nF → ∃ x, xFvs[i]? = some x ∧ Expr.WScoped (nP + i) x.fvarTypeD ∧
      (∀ l ∈ x.fvarTypeD.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) := by
    intro i hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hxA : (fvsP ++ xFvs)[nP + i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) := by
      rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
      exact hx
    obtain ⟨-, hws, -, -, -⟩ := hO.var (nP + i) _ hxA
    refine ⟨_, hx, hws, ?_⟩
    intro l hl ⟨hr, hlt⟩
    have hge := hr.1
    obtain ⟨x', hx', hlater, -⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    have hmem : (xFvs[i]'(by rw [hD.xLen]; exact hi)) ∈ xFvs.drop (l.1 - nP + 1) := by
      refine List.mem_of_getElem? (i := i - (l.1 - nP + 1)) ?_
      rw [List.getElem?_drop, show l.1 - nP + 1 + (i - (l.1 - nP + 1)) = i from by omega]
      exact hx
    exact mentionsFvar_false (hlater _ hmem) l hl (by omega)
  -- a reflexive field's opened telescope
  have hreflGet : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive → i < nF →
      ∃ afvs body,
        openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a → Expr.WScoped (nP + i + k) a.fvarTypeD ∧
          (∀ l ∈ a.fvarTypeD.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) ∧
          denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
            = some (((tss ψ).getD i []).getD k default).2.2) ∧
        Expr.WScoped (nP + i + ((tss ψ).getD i []).length) body ∧
        (∀ l ∈ body.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) ∧
        DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss ψ).getD i []) := by
    intro i x hx hk hi
    obtain ⟨afvs, body, hop, -, hdoms, hsp⟩ := hD.reflOpen ψ i x hx hk
    obtain ⟨x', hx', hws, hlf⟩ := hdom i hi
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    have hleaves := openPisAtFvars_leaf_bound hop
    have hwsAll := openPisAtFvars_WScoped _ _ _ hop hws
    refine ⟨afvs, body, hop, fun k a hk' => ⟨openPisAtFvars_typeWScoped _ hop hws k a hk',
      fun l hl ⟨hr, hlt⟩ => ?_, hdoms k a hk'⟩, hwsAll.2, fun l hl ⟨hr, hlt⟩ => ?_, hsp⟩
    · rcases hleaves.1 a (List.mem_of_getElem? hk') l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
    · rcases hleaves.2 l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
  have hQlt : ∀ i q, recAt nP ks q ∧ q < nP + i → q < nP + i := fun _ _ h => h.2
  have hne_refl : ∀ i, ks.getD i .ordinary = .recursive → ks.getD i .ordinary ≠ .reflexive := by
    intro i hk h
    rw [hk] at h
    cases h
  have hne_refl' : ∀ i, ks.getD i .ordinary = .ordinary → ks.getD i .ordinary ≠ .reflexive := by
    intro i hk h
    rw [hk] at h
    cases h
  have hne_rec' : ∀ i, ks.getD i .ordinary = .ordinary → ks.getD i .ordinary ≠ .recursive := by
    intro i hk h
    rw [hk] at h
    cases h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the entries mention no recursive slot below them
    intro i hi
    obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
    exact noBVar_of_leaf_free m (nP + i) x.fvarTypeD hws (hQlt i) hlf (hD.domRead ψ i x hx)
  · -- nor do a reflexive field's telescope domains
    intro i hi k dd hkd
    rcases hD.opened.kinds i hi with hk | hk | hk
    · rw [hD.tssNone ψ i (hne_refl' i hk)] at hkd
      exact nomatch hkd
    · rw [hD.tssNone ψ i (hne_refl i hk)] at hkd
      exact nomatch hkd
    · obtain ⟨x, hx, -, -⟩ := hdom i hi
      obtain ⟨afvs, body, hop, hdoms, -, -, -⟩ := hreflGet i x hx hk hi
      have hlenA := openPisAtFvars_length _ hop
      have hk' : k < afvs.length := by
        rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hkd).1
      obtain ⟨hws, hlf, hread⟩ := hdoms k _ (List.getElem?_eq_getElem hk')
      have hd : dd.2.2 = (((tss ψ).getD i []).getD k default).2.2 := by
        rw [List.getD_eq_getElem?_getD, hkd]; rfl
      rw [hd]
      exact noBVar_of_leaf_free m (nP + i + k) _ hws (fun q h => by have := h.2; omega)
        hlf hread
  · -- nor do the recursive slots' index expressions
    intro i hi E hE
    rcases hD.opened.kinds i hi with hk | hk | hk
    · rw [hD.ordNone ψ i (hne_rec' i hk) (hne_refl' i hk)] at hE
      exact nomatch hE
    · obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
      rw [hD.tssNone ψ i (hne_refl i hk), List.length_nil, Nat.add_zero]
      obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.eisRead ψ i x hx hk) E hE
      have ha' : a ∈ x.fvarTypeD.getAppArgs := List.mem_of_mem_drop ha
      exact noBVar_of_leaf_free m (nP + i) a (WScoped_of_mem_getAppArgs _ a hws ha')
        (hQlt i) (fun l hl => hlf l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
    · obtain ⟨x, hx, -, -⟩ := hdom i hi
      obtain ⟨afvs, body, hop, -, hwsB, hlfB, hspB⟩ := hreflGet i x hx hk hi
      obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv hspB E hE
      have ha' : a ∈ body.getAppArgs := List.mem_of_mem_drop ha
      exact noBVar_of_leaf_free m _ a (WScoped_of_mem_getAppArgs _ a hwsB ha')
        (fun q h => by have := h.2; omega)
        (fun l hl => hlfB l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
  · -- nor do the residual's index readings
    intro E hE
    obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.idxRead ψ) E hE
    rw [hD.idxEq] at ha
    have ha' : a ∈ xrest.getAppArgs := List.mem_of_mem_drop ha
    refine noBVar_of_leaf_free m (nP + nF) a
      (WScoped_of_mem_getAppArgs _ a hO.bodyScoped.1 ha') (hQlt nF) ?_ hra
    intro l hl ⟨hr, hlt⟩
    have hge := hr.1
    obtain ⟨-, -, -, hres⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    exact mentionsFvar_false hres l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl) (by omega)

/-! ## Spines agreeing off the recursive slots -/

/-- A prefix of two spines agreeing off the recursive slots agrees
likewise. -/
theorem ShadowRel.take {nP : Nat} {ks : List RecFieldKind} {fs vs : List V}
    (h : ShadowRel nP ks fs vs) (i : Nat) : ShadowRel nP ks (fs.take i) (vs.take i) := by
  refine ⟨by rw [List.length_take, List.length_take, h.1], fun l hl hr => ?_⟩
  rw [List.length_take] at hl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact h.2 l (by omega) hr

omit [SetTheory V] in
/-- Two frames agreeing off the excluded slots at depth `dd` agree off
them under any further binders (`agreeOff_cons` iterated, with the
depth shifted). -/
theorem agreeOff_consList_exclP {Q : Nat → Prop} :
    ∀ (as : List V) {dd : Nat} {σ σ' : Nat → V}, (∀ q, Q q → q < dd) →
      AgreeOff (exclP Q dd) σ σ' →
      AgreeOff (exclP Q (dd + as.length)) (consList as σ) (consList as σ')
  | [], _, _, _, _, h => by simpa using h
  | a :: as, dd, σ, σ', hQ, h => by
    rw [consList_cons, consList_cons, List.length_cons,
      show dd + (as.length + 1) = (dd + 1) + as.length from by omega]
    refine agreeOff_consList_exclP as (fun q hq => by have := hQ q hq; omega) ?_
    intro i hi
    refine agreeOff_cons h a i ?_
    intro hs
    exact hi ((shiftP_exclP Q dd hQ i).mp hs)

/-- **The transport between two spines agreeing off the recursive
slots**: a reading that mentions no recursive slot below depth
`nP + fs.length`, read under `as` more binders, is the same at the
two spines' frames. -/
theorem interp_congr_shadowRel {nP : Nat} {ks : List RecFieldKind} {fs vs : List V}
    (h : ShadowRel nP ks fs vs) (σ : Nat → V) (as : List V) {E : AnnotTerm}
    (hnb : NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + fs.length) (nP + fs.length + as.length)) E) :
    interp V (consList as (consList fs σ)) E = interp V (consList as (consList vs σ)) E :=
  interp_congr_noBVar E hnb
    (agreeOff_consList_exclP as (fun _ hq => hq.2) (agreeOff_shadow h σ))

/-- `WellDenoted` transports the same way. -/
theorem wellDenoted_congr_shadowRel {nP : Nat} {ks : List RecFieldKind} {fs vs : List V}
    (h : ShadowRel nP ks fs vs) (σ : Nat → V) (as : List V) {E : AnnotTerm}
    (hnb : NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + fs.length) (nP + fs.length + as.length)) E) :
    WellDenoted V (consList as (consList fs σ)) E ↔ WellDenoted V (consList as (consList vs σ)) E :=
  WellDenoted_congr_noBVar E hnb
    (agreeOff_consList_exclP as (fun _ hq => hq.2) (agreeOff_shadow h σ))

end ConLeche.Model
