module

public import ConLeche.Model.Inductives.FoldChoice
import ConLeche.Semantics.NoBVar
import ConLeche.Model.Inductives.FixNoBVar
import ConLeche.Model.Inductives.FixShadow
public import ConLeche.Model.Inductives.FixChains
import ConLeche.Model.Inductives.FixChainFacts
import ConLeche.Model.Inductives.StructCtorFrames
import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.MutualChains
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.FixRecPre
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.IndPinGrade
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

/-! ## The fits from the leaf's λ-shape -/

/-- **A graded application of a λ-tower leaf fits the whole tower**
(`leafSpineFit`, keeping the parameters' fit): the parameter values
are the frame's first `nP` entries below the `e` extra binders, the
index readings' values follow. -/
theorem leafSpineFit_full {L : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {nP nIdx w : Nat}
    {ρp : Nat → V} {σas : List V} {e : Nat} {Eis : List AnnotTerm}
    (hlen : pps.length = nP + nIdx) (hLclosed : Term.bvarsBelow 0 L.erase)
    (hL : ∃ B, L = mkLamsC (w + 1) pps B)
    (he : σas.length = e) (hEl : Eis.length = nIdx)
    (hokA : WellDenoted V (consList σas ρp)
      (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + e) ++ Eis))) :
    SpineFit (fun j => ρp (j + nP)) (pps.map (·.2.2))
      ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList σas ρp))) := by
  obtain ⟨B, hB⟩ := hL
  have hK : Term.bvarsBelow 0 (mkLamsC (w + 1) pps B).erase := by rw [← hB]; exact hLclosed
  have hf : interp V (consList σas ρp) L
      = interp V (fun j => ρp (j + nP)) (mkLamsC (w + 1) pps B) := by
    rw [hB]; exact interp_closed (V := V) hK _ _
  have hlenArgs : (paramBvarsAt nP (nP + e) ++ Eis).length = nP + nIdx := by
    simp [paramBvarsAt, hEl]
  have hfit := spineFit_of_wellDenoted_lams (u := w + 1) (Nat.succ_ne_zero _) (b := B)
    (args := paramBvarsAt nP (nP + e) ++ Eis) (ds := pps)
    (σ := fun j => ρp (j + nP)) (ρ := consList σas ρp) (f := L)
    (by rw [hlenArgs, hlen]; exact Nat.le_refl _) hokA hf
  rw [hlenArgs, List.take_of_length_le (by rw [hlen]; exact Nat.le_refl _), List.map_append] at hfit
  have hps : (paramBvarsAt nP (nP + e)).map (interp V (consList σas ρp))
      = (List.range nP).reverse.map ρp := by
    apply map_paramBvarsAt_interp
    intro j
    rw [← he]; exact consList_apply_add σas ρp j
  rw [hps] at hfit
  exact hfit

/-- The parameter variables at the parameter frame read to the
frame's parameter values. -/
theorem interp_paramBvarsAt_self {nP : Nat} {as : List V} (hlen : as.length = nP) (σ : Nat → V) :
    (paramBvarsAt nP nP).map (interp V (consList as σ)) = as :=
  map_fieldBvars_interp hlen σ

omit [SetTheory V] in
/-- The reversed range under a consed spine of the right length. -/
theorem range_reverse_map_consList' {n : Nat} {as : List V} (hlen : as.length = n) (ρ : Nat → V) :
    (List.range n).reverse.map (consList as ρ) = as := by
  subst hlen; exact range_reverse_map_consList as ρ

/-- **A graded application of a λ-tower leaf lands in the leaf's sort**:
the leaf inhabits its Π-tower into `Sort w`, the arguments fit
(`leafSpineFit_full`), so the value is in `univ w`. -/
theorem leafApp_mem_univ {L : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {nP nIdx w : Nat}
    {ρp : Nat → V} {σas : List V} {e : Nat} {Eis : List AnnotTerm}
    (hlen : pps.length = nP + nIdx) (hLclosed : Term.bvarsBelow 0 L.erase)
    (hL : ∃ B, L = mkLamsC (w + 1) pps B)
    (he : σas.length = e) (hEl : Eis.length = nIdx)
    (hokA : WellDenoted V (consList σas ρp)
      (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + e) ++ Eis)))
    (hmem : ∀ ρ : Nat → V, interp V ρ L ∈ˢ interp V ρ (mkPisAV pps (.sort w)))
    (hbits : ∀ dd ∈ pps, dd.2.1 ≠ 0) :
    interp V (consList σas ρp) (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + e) ++ Eis))
      ∈ˢ (univ w : V) := by
  have hfit := leafSpineFit_full hlen hLclosed hL he hEl hokA
  have hps : (paramBvarsAt nP (nP + e)).map (interp V (consList σas ρp))
      = (List.range nP).reverse.map ρp := by
    apply map_paramBvarsAt_interp
    intro j
    rw [← he]; exact consList_apply_add σas ρp j
  rw [interp_mkAppN_map, List.map_append, hps,
    interp_closed (V := V) hLclosed _ (fun j => ρp (j + nP))]
  have := mkPisAV_fold_mem (m := 1)
    (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbits dd hd)⟩)
    (fun h => absurd h Nat.one_ne_zero) (hmem (fun j => ρp (j + nP))) hfit
  rw [interp_sort] at this
  exact this

/-- **A fit into one parameter telescope is a fit into a `Sat`-equivalent
one** (`paramsIff`'s use): through `sat_of_spineFit`/`spineFit_of_sat`
at the empty ambient context. -/
theorem spineFit_of_paramsIff {ρ : Nat → V} {Ps Ds : List AnnotTerm} {as : List V} {nP : Nat}
    (has : as.length = nP) (hDs : Ds.length = nP) (hfit : SpineFit ρ Ps as)
    (hiff : ∀ ρ' : Nat → V, Sat V Ps.reverse ρ' ↔ Sat V Ds.reverse ρ') :
    SpineFit ρ Ds as := by
  have hsat := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hfit
  rw [List.append_nil] at hsat
  have hsat' := (hiff _).mp hsat
  have h2 := spineFit_of_sat (Δ₀ := []) (ρ := consList as ρ) (Ds := Ds)
    (by rw [List.append_nil]; exact hsat')
  rw [hDs] at h2
  have e1 : (fun j => consList as ρ (j + nP)) = ρ := by
    funext j
    rw [← has]; exact consList_apply_add _ _ _
  rw [e1, range_reverse_map_consList' has] at h2
  exact h2

/-! ## Variables under a lift, towers under a rebit -/

omit [SetTheory V] in
/-- A term lifted by `n` at depth `k` mentions no variable in
`[k, k + n)`. -/
theorem NoBVar_liftN {n : Nat} :
    ∀ (e : AnnotTerm) {k : Nat} {P : Nat → Prop}, (∀ i, P i → k ≤ i ∧ i < k + n) →
      NoBVar P (e.liftN n k)
  | .bvar i, k, P, hP => by
    show ¬ P (if i < k then i else i + n)
    intro h
    have := hP _ h
    split at this <;> omega
  | .sort _, _, _, _ => trivial
  | .const _ _, _, _, _ => trivial
  | .prf, _, _, _ => trivial
  | .app f a, _, _, hP => ⟨NoBVar_liftN f hP, NoBVar_liftN a hP⟩
  | .lam _ A b, k, P, hP =>
    ⟨NoBVar_liftN A hP, NoBVar_liftN b (k := k + 1) (P := shiftP P) fun i hi => by
      cases i with
      | zero => exact (hi : False).elim
      | succ j => have := hP j hi; omega⟩
  | .pi _ _ A B, k, P, hP =>
    ⟨NoBVar_liftN A hP, NoBVar_liftN B (k := k + 1) (P := shiftP P) fun i hi => by
      cases i with
      | zero => exact (hi : False).elim
      | succ j => have := hP j hi; omega⟩
  | .eqE a b, _, _, hP => ⟨NoBVar_liftN a hP, NoBVar_liftN b hP⟩
  | .fst e, _, _, hP => NoBVar_liftN e hP
  | .snd e, _, _, hP => NoBVar_liftN e hP

/-- `WellDenoted` of a Π-tower does not see the codomain bits. -/
theorem wellDenoted_mkPisAV_rebit {T : AnnotTerm} (b : Nat) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV ds T) → WellDenoted V σ (mkPisAV (rebit b ds) T)
  | [], _, h => h
  | d :: ds, σ, h => by
    simp only [mkPisAV, rebit_cons, WellDenoted_pi] at h ⊢
    exact ⟨h.1, fun x hx => wellDenoted_mkPisAV_rebit b (h.2 x hx)⟩

/-- A bit-valid Π-tower, rebit to a nonzero bit and ended in a sort,
is bit-valid. -/
theorem annotValid_mkPisAV_rebit_sort {T : AnnotTerm} {b u : Nat} (hb : b ≠ 0) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV ds T) → AnnotValid V σ (mkPisAV (rebit b ds) (.sort u))
  | [], _, _ => by simp [mkPisAV]
  | d :: ds, σ, h => by
    simp only [mkPisAV, rebit_cons, AnnotValid_pi] at h ⊢
    exact ⟨h.1, fun x hx => annotValid_mkPisAV_rebit_sort hb (h.2.1 x hx), fun h0 => absurd h0 hb⟩

/-- A bit-valid Π-tower's body is bit-valid at every fitting spine. -/
theorem annotValid_mkPisAV_body {T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV ds T) →
      ∀ as, SpineFit σ (ds.map (·.2.2)) as → AnnotValid V (consList as σ) T
  | [], _, h, [], _ => h
  | [], _, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, [], hsp => hsp.elim
  | d :: ds, σ, h, a :: as, hsp => by
    simp only [mkPisAV, AnnotValid_pi] at h
    rw [consList_cons]
    exact annotValid_mkPisAV_body (h.2.1 a hsp.1) as hsp.2

/-! ## Positions, lifts, and Π-towers over the excluded slots -/

omit [SetTheory V] in
/-- A member of a list sits at its `idxOf`. -/
theorem getElem?_idxOf_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : l[l.idxOf a]? = some a := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h)]; simp

omit [SetTheory V] in
theorem rebit_getElem? (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) :
    (rebit b ds)[k]? = (ds[k]?).map fun dd => (dd.1, b, dd.2.2) := by
  simp [rebit]

omit [SetTheory V] in
/-- A Π-tower mentions no excluded slot below its depth when its
binder domains (at their depths) and its body (under all binders) do
not. -/
theorem NoBVar_mkPisAV_exclP {Q : Nat → Prop} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) {D : Nat} {body : AnnotTerm}, (∀ q, Q q → q < D) →
      (∀ k dd, ds[k]? = some dd → NoBVar (exclP Q (D + k)) dd.2.2) →
      NoBVar (exclP Q (D + ds.length)) body →
      NoBVar (exclP Q D) (mkPisAV ds body)
  | [], D, body, _, _, hb => by simp only [mkPisAV, List.length_nil, Nat.add_zero] at hb ⊢; exact hb
  | dd :: ds, D, body, hQ, hds, hb => by
    refine ⟨by simpa using hds 0 dd rfl, ?_⟩
    have ih := NoBVar_mkPisAV_exclP ds (D := D + 1) (body := body)
      (fun q hq => by have := hQ q hq; omega)
      (fun k dd' hk => by
        have := hds (k + 1) dd' (by simpa using hk)
        rwa [show D + (k + 1) = D + 1 + k from by omega] at this)
      (by rwa [show D + (dd :: ds).length = D + 1 + ds.length from by simp; omega] at hb)
    exact NoBVar_congr (fun i => (shiftP_exclP Q D hQ i).symm) _ ih

omit [SetTheory V] in
theorem ihDataTg_length (Tg : Nat → AnnotTerm) (moti : Nat → Nat) (nP nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    ∀ (is : List Nat) (l : Nat), (ihDataTg Tg moti nP nF o b tls Eiss is l).length = is.length
  | [], _ => rfl
  | _ :: is, l => by simp [ihDataTg, ihDataTg_length Tg moti nP nF o b tls Eiss is (l + 1)]

omit [SetTheory V] in
/-- The target-form ih binders, positionally. -/
theorem ihDataTg_getElem? (Tg : Nat → AnnotTerm) (moti : Nat → Nat) (nP nF o b : Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    ∀ (is : List Nat) (l n : Nat),
      (ihDataTg Tg moti nP nF o b tls Eiss is l)[n]?
        = (is[n]?).map fun i =>
            (0, b, tgIhDomAV Tg (moti i) nP nF o i (l + n) (rebit b (tls.getD i [])) (Eiss.getD i []))
  | [], _, _ => rfl
  | i :: is, l, 0 => by simp [ihDataTg]
  | i :: is, l, n + 1 => by
    simp only [ihDataTg, List.getElem?_cons_succ]
    rw [ihDataTg_getElem? Tg moti nP nF o b tls Eiss is (l + 1) n]
    congr 2
    funext i'
    rw [show l + 1 + n = l + (n + 1) from by omega]

/-- The transport at a prefix of the fields, the lengths explicit. -/
theorem interp_congr_shadowRel_at {nP : Nat} {ks : List RecFieldKind} {fs vs : List V}
    (h : ShadowRel nP ks fs vs) (σ : Nat → V) {n : Nat} (hn : n ≤ fs.length) {E : AnnotTerm}
    (hnb : NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + n) (nP + n)) E) :
    interp V (consList (fs.take n) σ) E = interp V (consList (vs.take n) σ) E := by
  have hlen : (fs.take n).length = n := by rw [List.length_take]; omega
  have := interp_congr_shadowRel (h.take n) σ [] (E := E) (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnb)
  simpa using this

/-! ## The mixed spine -/

/-- **The mixed variable spine** at a minor's leaf frame (the fields
then the hypotheses, innermost last): field `i` as its inductive
hypothesis (position `recIdx.idxOf i` among the `recIdx.length`
hypotheses) where `useIh i`, the field variable otherwise. -/
@[expose] def mixedVarsAV (recIdx : List Nat) (useIh : Nat → Bool) (nF : Nat) : List AnnotTerm :=
  (List.range nF).map fun i =>
    if useIh i then AnnotTerm.bvar (recIdx.length - 1 - recIdx.idxOf i)
    else AnnotTerm.bvar (nF + recIdx.length - 1 - i)

/-- The mixed values: the hypothesis value where `useIh`, the field
value otherwise. -/
noncomputable def mixedVals (recIdx : List Nat) (useIh : Nat → Bool) (fs ihs : List V) : List V :=
  (List.range fs.length).map fun i => if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt

theorem mixedVals_length (recIdx : List Nat) (useIh : Nat → Bool) (fs ihs : List V) :
    (mixedVals recIdx useIh fs ihs).length = fs.length := by simp [mixedVals]

theorem mixedVals_getD (recIdx : List Nat) (useIh : Nat → Bool) (fs ihs : List V) {i : Nat}
    (hi : i < fs.length) :
    (mixedVals recIdx useIh fs ihs).getD i pt
      = if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt := by
  simp [mixedVals, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- **The mixed variable spine reads to the mixed values** at the
minor's leaf frame. -/
theorem interp_mixedVarsAV {recIdx : List Nat} {useIh : Nat → Bool} (huse : ∀ i, useIh i = true → i ∈ recIdx)
    {fs ihs : List V} (hihs : ihs.length = recIdx.length) (σ : Nat → V) :
    (mixedVarsAV recIdx useIh fs.length).map (interp V (consList (fs ++ ihs) σ))
      = mixedVals recIdx useIh fs ihs := by
  apply List.ext_getElem
  · simp [mixedVarsAV, mixedVals]
  · intro i h1 h2
    have hi : i < fs.length := by simpa [mixedVarsAV] using h1
    simp only [mixedVarsAV, mixedVals, List.getElem_map, List.getElem_range]
    split
    · next hu =>
      have hmem := huse i hu
      have hlt := List.idxOf_lt_length_of_mem hmem
      rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
        List.length_append, hihs, List.getD_eq_getElem?_getD,
        show fs.length + recIdx.length - 1 - (recIdx.length - 1 - recIdx.idxOf i)
          = fs.length + recIdx.idxOf i from by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]
    · rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
        List.length_append, hihs, List.getD_eq_getElem?_getD,
        show fs.length + recIdx.length - 1 - (fs.length + recIdx.length - 1 - i) = i from by omega,
        List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

namespace IndRepData

variable (d : IndRepData V)

/-- A real member's leaf, by position. -/
theorem Ls_getD_eq (m : EnvModel V env) (ψ : Name → Nat) {t : Nat} (ht : t < d.k) :
    (d.Ls m ψ).getD t default = m.acval (d.memberName t) ψ := by
  simp [Ls, List.getD_eq_getElem?_getD, List.getElem?_range ht, memberName]

omit [SetTheory V] in
/-- A real member's index binder data, by position. -/
theorem ipss_getD (ψ : Name → Nat) {t : Nat} (ht : t < d.k) :
    (d.ipss ψ).getD t [] = (d.ppsM t ψ).drop d.nP := by
  simp [ipss, List.getD_eq_getElem?_getD, List.getElem?_range ht]

/-- The family at the parameter variables, read at the parameter frame
and the index values: the leaf at the parameters and the indices. -/
theorem interp_famAppAV_params {L : AnnotTerm} (hL : Term.bvarsBelow 0 L.erase)
    {nP nIdx : Nat} {as is : List V} (has : as.length = nP) (his : is.length = nIdx)
    (ρ : Nat → V) :
    interp V (consList is (consList as ρ)) (famAppAV L (paramBvarsAt nP nP) nP (nP + nIdx) nIdx)
      = (as ++ is).foldl SetTheory.app (interp V ρ L) := by
  subst his
  have := interp_famAppAV_at (L := L) (fun σ₁ σ₂ => interp_closed (V := V) hL σ₁ σ₂)
    (paramBvarsAt nP nP) nP (extra := []) (is := is) (σ := consList as ρ)
  simp only [consList_nil, List.length_nil, Nat.add_zero] at this
  rw [this, interp_paramBvarsAt_self has, interp_closed (V := V) hL _ ρ]

/-- **The kit's field-side facts of constructor `J`** —
`choice_prefix_fit`/`choice_fold_iota`'s `hfield` and `hEs`, verbatim:
every recursive field's value along its telescope lands in its
member's family at the field's index readings, which fit the member's
index telescope; the constructor at the fields lands in its member's
family at its index readings, which fit likewise. -/
@[expose] def CtorFieldFacts (m : EnvModel V env) (ψ : Name → Nat) (ρ : Nat → V)
    (ps : List AnnotTerm) (J : Nat) (C : Name) (ds : List (Nat × Nat × AnnotTerm))
    (Es : List AnnotTerm) (recIdx : List Nat) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) : Prop :=
  (∀ i ∈ recIdx, ∀ fs : List V,
    SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
    ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        ((tls.getD i []).map (·.2.2)) as →
      SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR J i) [])).map (·.2.2))
          ((Eiss.getD i []).map
            (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
        as.foldl SetTheory.app (fs.getD i pt)
          ∈ˢ interp V (consList ((Eiss.getD i []).map
              (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
              (consList (ps.map (interp V ρ)) ρ))
            (famAppAV ((d.Ls m ψ).getD (d.tgtsR J i) default) (d.pinsOf ψ (d.tgtsR J i)) d.nP
              (d.nP + d.nIdxs.getD (d.tgtsR J i) 0) (d.nIdxs.getD (d.tgtsR J i) 0))) ∧
  (∀ fs : List V,
    SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
    SpineFit (consList (ps.map (interp V ρ)) ρ)
        ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2))
        (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))) ∧
      fs.foldl SetTheory.app
          (interp V (consList (ps.map (interp V ρ)) ρ)
            (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J))))
        ∈ˢ interp V (consList (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))))
            (consList (ps.map (interp V ρ)) ρ))
          (famAppAV ((d.Ls m ψ).getD (d.mems J) default) (d.pinsOf ψ (d.mems J)) d.nP
            (d.nP + d.nIdxs.getD (d.mems J) 0) (d.nIdxs.getD (d.mems J) 0)))

/-- **The former's facts a member's fits are read off**: its parameter
and index telescope's length and nonzero bits, and its leaf inhabiting
the tower into the block's sort at every frame (`formersRead` +
`mem_type`, at the consumer). -/
@[expose] def FormerFacts (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) : Prop :=
  (d.ppsM t ψ).length = d.nP + d.nIdxAt t ∧
  (∀ dd ∈ d.ppsM t ψ, dd.2.1 ≠ 0) ∧
  (∀ ρ : Nat → V, interp V ρ (m.acval (d.memberName t) ψ)
    ∈ˢ interp V ρ (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ)))) ∧
  ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ)))

/-- **The leaf's λ-shape**: a real member's leaf is the constant-bit
λ-tower over its parameter and index data (the routes' `hleafT`; the
datum finding of DESIGN §M.18). -/
@[expose] def LeafShape (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) : Prop :=
  ∃ B, m.acval (d.memberName t) ψ = mkLamsC (d.w ψ + 1) (d.ppsM t ψ) B

set_option maxHeartbeats 1600000 in
/-- **The field-side facts of a real constructor, from the datum and
the leaves' shapes.**  The fits are `leafSpineFit` at the graded
entries (the constructor's tower is graded, `okTy`; each entry's
grading at a fitting prefix, `wellDenoted_mkPisAV_dom`); the values
are the entries' spellings (`recEntry`/`reflEntry`, `ctorBodyAVI`)
folded (`mkPisAV_fold_mem` at the constructor's own reading through
`mem_type`, at a reflexive entry's telescope); the `Prop` side
condition of the folds is the leaf's sort (`leafApp_mem_univ`).  The
parameters' fit into the constructor's own parameter domains comes
from the former's through `paramsIff` (`hpIff`). -/
theorem ctorFieldFacts_of {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} (hps : ps.length = d.nP)
    (hpins : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP)
    (hLS : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hFF : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    {J : Nat} {cA : ConstantVal × Nat}
    (hC : FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i)))
    (hpIff : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hmem : d.mems J < d.k) (htgt : ∀ i, d.tgts J i < d.k)
    (htgtR : ∀ i, d.tgtsR J i = d.tgts J i) :
    d.CtorFieldFacts mp.base2 ψ ρ ps J cA.1.name (d.dsF J ψ) (d.esF J ψ)
      (ConLeche.recIdxOf (d.ksF J)) (d.eissF J ψ) (d.tssF J ψ) := by
  obtain ⟨hfind, -, hD⟩ := hC
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hclosed : ∀ t, Term.bvarsBelow 0 (mp.base2.acval (d.memberName t) ψ).erase :=
    fun t => mp.base2.cval_closedL _ ψ
  have hlenDs := hD.len ψ
  -- the parameters fit the constructor's own parameter domains
  have hfitP : SpineFit ρ (((d.dsF J ψ).take d.nP).map (·.2.2)) (ps.map (interp V ρ)) :=
    spineFit_of_paramsIff hpsLen (by simp [hlenDs]) hparams hpIff
  have hsplit : (d.dsF J ψ).map (·.2.2)
      = ((d.dsF J ψ).take d.nP).map (·.2.2) ++ ((d.dsF J ψ).drop d.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  -- the whole spine fits
  have hfitAll : ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) (((d.dsF J ψ).drop d.nP).map (·.2.2)) fs →
      SpineFit ρ ((d.dsF J ψ).map (·.2.2)) (ps.map (interp V ρ) ++ fs) := by
    intro fs hfs
    rw [hsplit]; exact SpineFit.append hfitP hfs
  -- the leaf's sort at a graded application (the `Prop` side conditions)
  have hzero : ∀ t, t < d.k → ∀ (ρp : Nat → V) (σas : List V) (e : Nat) (Eis : List AnnotTerm),
      σas.length = e → Eis.length = d.nIdxAt t →
      WellDenoted V (consList σas ρp)
        (AnnotTerm.mkAppN (mp.base2.acval (d.memberName t) ψ) (paramBvarsAt d.nP (d.nP + e) ++ Eis)) →
      interp V (consList σas ρp)
        (AnnotTerm.mkAppN (mp.base2.acval (d.memberName t) ψ) (paramBvarsAt d.nP (d.nP + e) ++ Eis))
        ∈ˢ (univ (d.w ψ) : V) := by
    intro t ht ρp σas e Eis he hEl hok
    obtain ⟨hlen, hbits, hmemL, -⟩ := hFF t ht
    exact leafApp_mem_univ hlen (hclosed t) (hLS t ht) he hEl hok hmemL hbits
  -- the body is the leaf at the parameter variables and the index readings
  have hbody : ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ)
      = AnnotTerm.mkAppN (mp.base2.acval (d.memberName (d.mems J)) ψ)
          (paramBvarsAt d.nP (d.nP + cA.2) ++ d.esF J ψ) := rfl
  -- the field frame is the whole frame
  have hframe : ∀ fs : List V, consList (ps.map (interp V ρ) ++ fs) ρ
      = consList fs (consList (ps.map (interp V ρ)) ρ) := fun fs => consList_append _ _ _
  -- the entries' grading at a fitting field prefix
  have hentryWD : ∀ (i : Nat) (fs : List V), i < cA.2 →
      SpineFit (consList (ps.map (interp V ρ)) ρ) (((d.dsF J ψ).drop d.nP).map (·.2.2)) fs →
      WellDenoted V (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        ((d.dsF J ψ).getD (d.nP + i) default).2.2 := by
    intro i fs hi hfs
    have hfsLen : fs.length = cA.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenDs]; omega
    have hlt : d.nP + i < (d.dsF J ψ).length := by rw [hlenDs]; omega
    have hpre : SpineFit ρ (((d.dsF J ψ).take (d.nP + i)).map (·.2.2))
        (ps.map (interp V ρ) ++ fs.take i) := by
      rw [List.take_add, List.map_append]
      refine SpineFit.append hfitP ?_
      rw [List.map_take]
      exact spineFit_take_prefix hfs (by rw [List.length_map, List.length_drop, hlenDs]; omega)
    have := wellDenoted_mkPisAV_dom (hD.okTy ψ ρ).1 (ps.map (interp V ρ) ++ fs.take i) (d.nP + i)
      _ (List.getElem?_eq_getElem hlt) hpre
    rw [hframe] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact this
  refine ⟨?_, ?_⟩
  · -- the recursive fields
    intro i hi fs hfs as has
    obtain ⟨hilt, hkind⟩ := mem_recIdxOf.mp hi
    rw [hD.ksLen] at hilt
    have hfsLen : fs.length = cA.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenDs]; omega
    have htakeLen : (fs.take i).length = i := by rw [List.length_take]; omega
    have hlt : d.nP + i < (d.dsF J ψ).length := by rw [hlenDs]; omega
    -- the field's value in its entry
    have hfi : fs.getD i pt ∈ˢ interp V (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        ((d.dsF J ψ).getD (d.nP + i) default).2.2 := by
      have := spineFit_getElem? hfs i (fs.getD i pt) (((d.dsF J ψ).getD (d.nP + i) default).2.2)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < fs.length)]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem hlt,
          Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
      exact this
    have hwd := hentryWD i fs hilt hfs
    rw [htgtR, d.ipss_getD ψ (htgt i), rebit_map_dom, d.Ls_getD_eq mp.base2 ψ (htgt i), hpins]
    obtain ⟨hlenT, -, -, -⟩ := hFF (d.tgts J i) (htgt i)
    rcases hkind with hk | hk
    · -- recursive: no telescope
      have htss : (d.tssF J ψ).getD i [] = [] :=
        hD.tssNone ψ i (by rw [hk]; intro h; cases h)
      rw [htss] at has
      obtain rfl : as = [] := by
        cases as with
        | nil => rfl
        | cons _ _ => exact has.elim
      have hentry := hD.recEntry ψ i hk hilt
      rw [hentry] at hfi hwd
      have hEl : ((d.eissF J ψ).getD i []).length = d.nIdxAt (d.tgts J i) := hD.eisLen ψ i hk hilt
      have hfit := leafSpineFit_full hlenT (hclosed _) (hLS _ (htgt i)) htakeLen hEl hwd
      simp only [consList_nil, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · rw [← List.take_append_drop d.nP (d.ppsM (d.tgts J i) ψ), List.map_append] at hfit
        obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
        have hlen₁ : as₁.length = d.nP := by
          have := SpineFit.length_eq h1
          rw [this, List.length_map, List.length_take, hlenT]; omega
        obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp)
        have e1 : (fun j => consList (ps.map (interp V ρ)) ρ (j + d.nP)) = ρ := by
          funext j
          rw [← hpsLen]; exact consList_apply_add _ _ _
        rw [e1, range_reverse_map_consList' hpsLen] at h2
        exact h2
      · have hnI : d.nIdxs.getD (d.tgts J i) 0 = d.nIdxAt (d.tgts J i) := rfl
        have hfam := interp_famAppAV_params (hclosed (d.tgts J i)) (nIdx := d.nIdxAt (d.tgts J i)) hpsLen
          (is := ((d.eissF J ψ).getD i []).map
            (interp V (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))
          (by rw [List.length_map]; exact hEl) ρ
        rw [hnI, hfam]
        rw [interp_mkAppN_map, List.map_append,
          map_paramBvarsAt_interp (ρp := consList (ps.map (interp V ρ)) ρ)
            (fun j => by
              have h := consList_apply_add (fs.take i) (consList (ps.map (interp V ρ)) ρ) j
              rw [htakeLen] at h; exact h),
          range_reverse_map_consList' hpsLen, interp_closed (V := V) (hclosed _) _ ρ] at hfi
        exact hfi
    · -- reflexive: along the telescope
      have hentry := hD.reflEntry ψ i hk hilt
      rw [hentry, Nat.add_assoc d.nP i] at hfi hwd
      have hEl : ((d.eissF J ψ).getD i []).length = d.nIdxAt (d.tgts J i) :=
        hD.eisLenRefl ψ i hk hilt
      have hasLen : as.length = ((d.tssF J ψ).getD i []).length := by
        rw [has.length_eq, List.length_map]
      have hframeT : consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
          = consList (fs.take i ++ as) (consList (ps.map (interp V ρ)) ρ) :=
        (consList_append _ _ _).symm
      have hlenTA : (fs.take i ++ as).length = i + ((d.tssF J ψ).getD i []).length := by
        rw [List.length_append, htakeLen, hasLen]
      -- the entry's body is graded under the telescope
      have hwdB := wellDenoted_mkPisAV_body hwd as has
      rw [hframeT] at hwdB
      have hfit := leafSpineFit_full hlenT (hclosed _) (hLS _ (htgt i)) hlenTA hEl hwdB
      refine ⟨?_, ?_⟩
      · rw [← List.take_append_drop d.nP (d.ppsM (d.tgts J i) ψ), List.map_append] at hfit
        obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
        have hlen₁ : as₁.length = d.nP := by
          have := SpineFit.length_eq h1
          rw [this, List.length_map, List.length_take, hlenT]; omega
        obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp)
        have e1 : (fun j => consList (ps.map (interp V ρ)) ρ (j + d.nP)) = ρ := by
          funext j
          rw [← hpsLen]; exact consList_apply_add _ _ _
        rw [e1, range_reverse_map_consList' hpsLen] at h2
        rw [hframeT]
        exact h2
      · have hfold := mkPisAV_fold_mem (m := d.w ψ) (fun dd hd => (hD.tssBits ψ i dd hd).symm)
          (fun h0 as' has' => by
            have hasLen' : as'.length = ((d.tssF J ψ).getD i []).length := by
              rw [has'.length_eq, List.length_map]
            have hwdB' := wellDenoted_mkPisAV_body hwd as' has'
            rw [← consList_append] at hwdB' ⊢
            have := hzero (d.tgts J i) (htgt i) _ (fs.take i ++ as') _ _
              (by rw [List.length_append, htakeLen, hasLen']) hEl hwdB'
            rw [h0, univ_zero] at this
            exact this) hfi has
        have hnI : d.nIdxs.getD (d.tgts J i) 0 = d.nIdxAt (d.tgts J i) := rfl
        rw [hframeT] at hfold ⊢
        have hfam := interp_famAppAV_params (hclosed (d.tgts J i)) (nIdx := d.nIdxAt (d.tgts J i)) hpsLen
          (is := ((d.eissF J ψ).getD i []).map
            (interp V (consList (fs.take i ++ as) (consList (ps.map (interp V ρ)) ρ))))
          (by rw [List.length_map]; exact hEl) ρ
        rw [hnI, hfam]
        rw [interp_mkAppN_map, List.map_append,
          map_paramBvarsAt_interp (ρp := consList (ps.map (interp V ρ)) ρ)
            (fun j => by
              have h := consList_apply_add (fs.take i ++ as) (consList (ps.map (interp V ρ)) ρ) j
              rw [hlenTA] at h; exact h),
          range_reverse_map_consList' hpsLen, interp_closed (V := V) (hclosed _) _ ρ] at hfold
        exact hfold
  · -- the constructor's index readings and value
    intro fs hfs
    have hfsLen : fs.length = cA.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenDs]; omega
    have hall := hfitAll fs hfs
    -- the body, graded at the spine
    have hwdB := wellDenoted_mkPisAV_body (hD.okTy ψ ρ).1 _ hall
    rw [hframe, hbody] at hwdB
    have hEl : (d.esF J ψ).length = d.nIdxAt (d.mems J) := hD.lenE ψ
    obtain ⟨hlenM, -, -, -⟩ := hFF (d.mems J) hmem
    have hfit := leafSpineFit_full hlenM (hclosed _) (hLS _ hmem) hfsLen hEl hwdB
    rw [d.ipss_getD ψ hmem, rebit_map_dom, d.Ls_getD_eq mp.base2 ψ hmem, hpins]
    refine ⟨?_, ?_⟩
    · rw [← List.take_append_drop d.nP (d.ppsM (d.mems J) ψ), List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = d.nP := by
        have := SpineFit.length_eq h1
        rw [this, List.length_map, List.length_take, hlenM]; omega
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp)
      have e1 : (fun j => consList (ps.map (interp V ρ)) ρ (j + d.nP)) = ρ := by
        funext j
        rw [← hpsLen]; exact consList_apply_add _ _ _
      rw [e1, range_reverse_map_consList' hpsLen] at h2
      exact h2
    · -- the constructor's leaf in its tower
      have hcmem : interp V ρ (mp.base2.acval cA.1.name ψ)
          ∈ˢ interp V ρ (mkPisAV (d.dsF J ψ)
              (ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) :=
        mp.mem_type _ (Env.find?_mem hfind) ψ _ (hD.read ψ) ρ
      have hfold := mkPisAV_fold_mem (m := d.w ψ) (fun dd hd => hD.bits ψ dd hd)
        (fun h0 as' has' => by
          obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv (by rw [← hsplit]; exact has')
          have hlen₁ : as₁.length = d.nP := by
            rw [h1.length_eq, List.length_map, List.length_take, hlenDs]; omega
          have hlen₂ : as₂.length = cA.2 := by
            rw [h2.length_eq, List.length_map, List.length_drop, hlenDs]; omega
          subst heq
          have hwd' := wellDenoted_mkPisAV_body (hD.okTy ψ ρ).1 _ has'
          rw [consList_append, hbody] at hwd' ⊢
          have := hzero (d.mems J) hmem _ as₂ _ _ hlen₂ hEl hwd'
          rw [h0, univ_zero] at this
          exact this) hcmem hall
      have hnI : d.nIdxs.getD (d.mems J) 0 = d.nIdxAt (d.mems J) := rfl
      have hfam := interp_famAppAV_params (hclosed (d.mems J)) (nIdx := d.nIdxAt (d.mems J)) hpsLen
        (is := (d.esF J ψ).map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))))
        (by rw [List.length_map]; exact hEl) ρ
      rw [interp_mkAppN_map, interp_paramBvarsAt_self hpsLen, ← List.foldl_append,
        interp_closed (V := V) (mp.base2.cval_closedL _ ψ) _ ρ, hnI, hfam]
      rw [hframe, hbody, interp_mkAppN_map, List.map_append,
        map_paramBvarsAt_interp (ρp := consList (ps.map (interp V ρ)) ρ)
          (fun j => by
            have h := consList_apply_add fs (consList (ps.map (interp V ρ)) ρ) j
            rw [hfsLen] at h; exact h),
        range_reverse_map_consList' hpsLen, interp_closed (V := V) (hclosed _) _ ρ] at hfold
      exact hfold

/-! ## The choice's targets -/

/-- **The target of member `t`**: `λ ı⃗, L t (pinsT t) ı⃗` — the leaf `L t`
at the pins `pinsT t` (at the parameter frame) and the index
variables, over the member's own index binder data at the never-bit
(as the tower's motives), at the fold's frame through the parameter
spine (`instSeq`, as `motChoiceAV`). -/
@[expose] def invTgAV (ψ : Name → Nat) (ps : List AnnotTerm) (L : Nat → AnnotTerm)
    (pinsT : Nat → List AnnotTerm) (t : Nat) : AnnotTerm :=
  ConLeche.Model.AnnotTerm.instSeq ps (ps.length - 1)
    (mkLamsAV ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map
        fun x => (x.2.1, x.2.2))
      (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)))

/-- **A member's target fact** at the parameter frame: its index
telescope (never-bit) is graded into a sort-ended tower, and at every
fitting index spine the family at the pins is graded and lies in the
elimination universe.  For a real member it follows from the former
(`targetOk_real`); for a copy it is the pins' typing at the scratch
environment (`pinsOkAux`) read through the container's former. -/
@[expose] def TargetOk (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (t : Nat) : Prop :=
  WellDenotedV V (consList (ps.map (interp V ρ)) ρ)
    (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
      (.sort (d.elimL.eval ψ))) ∧
  ∀ is : List V,
    SpineFit (consList (ps.map (interp V ρ)) ρ)
      ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is →
    WellDenotedV V (consList is (consList (ps.map (interp V ρ)) ρ))
      (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) ∧
    interp V (consList is (consList (ps.map (interp V ρ)) ρ))
      (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))
      ∈ˢ (univ (d.elimL.eval ψ) : V)

/-- **The target is what the kit's `hTg` asks**: graded at the fold's
frame, and in the sort-ended tower over the member's index telescope
at the parameter frame — a λ-tower with the binders' own bits
(`mkLamsAV_bits_mem`/`_wellDenoted`/`_validV`) under `instSeq`
(`wellDenotedV_instSeq`). -/
theorem invTg_fact (ψ : Name → Nat) {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {t : Nat} (hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p)
    (hT : d.TargetOk ψ ρ ps L pinsT t) :
    WellDenotedV V ρ (d.invTgAV ψ ps L pinsT t) ∧
    interp V ρ (d.invTgAV ψ ps L pinsT t)
      ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ)
        (mkPisAV (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))
          (.sort (d.elimL.eval ψ))) := by
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  have hbits : ∀ x ∈ rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []),
      (pwBit ψ ConLeche.PropWhen.never = 0 ↔ x.2.1 = 0) := fun x hx => by rw [mem_rebit hx]
  have hunder : UnderTowerOk (pwBit ψ ConLeche.PropWhen.never) (consList (ps.map (interp V ρ)) ρ)
      (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))
      (.sort (d.elimL.eval ψ)) (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])) :=
    underTowerOk_of_wellDenoted hT.1.1 fun as hsp =>
      ⟨(hT.2 as hsp).1.1, by rw [interp_sort]; exact (hT.2 as hsp).2, fun h0 => absurd h0 hb⟩
  have hvalid : UnderTowerValid (consList (ps.map (interp V ρ)) ρ)
      (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))
      (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])) :=
    underTowerValid_of (fun k dd hk as hsp => annotValid_mkPisAV_dom hT.1.2 as k dd hk hsp)
      (fun as hsp => (hT.2 as hsp).1.2)
  refine ⟨?_, ?_⟩
  · unfold invTgAV
    refine wellDenotedV_instSeq ps hpsWD ?_
    have hch : chain V ρ ps = consList (ps.map (interp V ρ)) ρ := by
      unfold chain; exact consN_eq_consList _ _
    rw [hch]
    exact ⟨mkLamsAV_bits_wellDenoted hbits hunder, mkLamsAV_bits_validV hvalid⟩
  · unfold invTgAV
    rw [interp_instSeq_consList]
    exact mkLamsAV_bits_mem hbits hunder

set_option maxHeartbeats 800000 in
/-- **A real member's target fact, from its former**: the index
telescope's grading is the former's below the parameters; the family
at the parameters and fitting indices lies in `Sort w` by the leaf in
its tower (`mem_type`, `FormerFacts`), graded by the tower lifted to
the index frame (`wellDenotedV_mkAppN_of_spineFit`).  `hpIffM` is the
per-member twin of `paramsIff` (the parameters fit MEMBER `t`'s own
parameter telescope; the datum records it for member `0` only —
DESIGN §M.18); `hlev` is the consumer's choice of the elimination
universe. -/
theorem targetOk_real {μ : CheckMode} (mp : EnvModelM V μ env) {ψ : Name → Nat} {ρ : Nat → V}
    {ps : List AnnotTerm} (hps : ps.length = d.nP) {t : Nat} (ht : t < d.k)
    (hFF : d.FormerFacts mp.base2 ψ t)
    (hpIffM : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ) :
    d.TargetOk ψ ρ ps (fun t => mp.base2.acval (d.memberName t) ψ) (fun _ => paramBvarsAt d.nP d.nP)
      t := by
  obtain ⟨hlen, hbits, hmemL, hokF⟩ := hFF
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hclosed : Term.bvarsBelow 0 (mp.base2.acval (d.memberName t) ψ).erase :=
    mp.base2.cval_closedL _ ψ
  have hfitP : SpineFit ρ (((d.ppsM t ψ).take d.nP).map (·.2.2)) (ps.map (interp V ρ)) :=
    spineFit_of_paramsIff hpsLen (by rw [List.length_map, List.length_take, hlen]; omega) hparams
      hpIffM
  have hsplitT : mkPisAV (d.ppsM t ψ) (.sort (d.w ψ))
      = mkPisAV ((d.ppsM t ψ).take d.nP) (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))) := by
    rw [← mkPisAV_append, List.take_append_drop]
  have hsplit : (d.ppsM t ψ).map (·.2.2)
      = ((d.ppsM t ψ).take d.nP).map (·.2.2) ++ ((d.ppsM t ψ).drop d.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  have hWD : WellDenotedV V (consList (ps.map (interp V ρ)) ρ)
      (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))) := by
    have h := hokF ρ
    rw [hsplitT] at h
    exact ⟨wellDenoted_mkPisAV_body h.1 _ hfitP, annotValid_mkPisAV_body h.2 _ hfitP⟩
  refine ⟨?_, ?_⟩
  · rw [d.ipss_getD ψ ht, hlev]
    exact ⟨wellDenoted_mkPisAV_rebit _ hWD.1, annotValid_mkPisAV_rebit_sort hb hWD.2⟩
  · intro is hsp
    rw [d.ipss_getD ψ ht, rebit_map_dom] at hsp
    have hisLen : is.length = d.nIdxAt t := by
      rw [hsp.length_eq, List.length_map, List.length_drop, hlen]; omega
    have hnI : d.nIdxs.getD t 0 = d.nIdxAt t := rfl
    have hfitAll : SpineFit ρ ((d.ppsM t ψ).map (·.2.2)) (ps.map (interp V ρ) ++ is) := by
      rw [hsplit]; exact SpineFit.append hfitP hsp
    have hframe : consList is (consList (ps.map (interp V ρ)) ρ)
        = consList (ps.map (interp V ρ) ++ is) ρ := (consList_append _ _ _).symm
    have hshift : shiftE (d.nP + d.nIdxAt t) 0 (consList is (consList (ps.map (interp V ρ)) ρ)) = ρ := by
      rw [hframe, show d.nP + d.nIdxAt t = (ps.map (interp V ρ) ++ is).length from by
          rw [List.length_append, hpsLen, hisLen]]
      exact shiftE_consList _ ρ
    refine ⟨?_, ?_⟩
    · -- graded: the tower lifted to the index frame, applied along the
      -- parameter and index variables
      rw [hnI, famAppAV_params _ _ _ _ (Nat.le_add_right _ _)]
      have hT : WellDenotedV V (consList is (consList (ps.map (interp V ρ)) ρ))
          (mkPisAV (liftDoms (d.nP + d.nIdxAt t) 0 (d.ppsM t ψ))
            ((AnnotTerm.sort (d.w ψ)).liftN (d.nP + d.nIdxAt t) (0 + (d.ppsM t ψ).length))) := by
        rw [← liftN_mkPisAV, WellDenotedV_liftN, hshift]
        exact hokF ρ
      have hmem : interp V (consList is (consList (ps.map (interp V ρ)) ρ))
            (mp.base2.acval (d.memberName t) ψ)
          ∈ˢ interp V (consList is (consList (ps.map (interp V ρ)) ρ))
            (mkPisAV (liftDoms (d.nP + d.nIdxAt t) 0 (d.ppsM t ψ))
              ((AnnotTerm.sort (d.w ψ)).liftN (d.nP + d.nIdxAt t) (0 + (d.ppsM t ψ).length))) := by
        rw [← liftN_mkPisAV, interp_liftN, hshift, interp_closed (V := V) hclosed _ ρ]
        exact hmemL ρ
      have hfit : SpineFit (consList is (consList (ps.map (interp V ρ)) ρ))
          ((liftDoms (d.nP + d.nIdxAt t) 0 (d.ppsM t ψ)).map (·.2.2))
          ((paramBvarsAt d.nP (d.nP + d.nIdxAt t) ++ fieldBvars (d.nIdxAt t)).map
            (interp V (consList is (consList (ps.map (interp V ρ)) ρ)))) := by
        rw [spineFit_liftDoms, hshift, List.map_append,
          map_paramBvarsAt_interp (ρp := consList (ps.map (interp V ρ)) ρ)
            (fun j => by
              have h := consList_apply_add is (consList (ps.map (interp V ρ)) ρ) j
              rw [hisLen] at h; exact h),
          range_reverse_map_consList' hpsLen,
          show fieldBvars (d.nIdxAt t)
            = (List.range (d.nIdxAt t)).map (fun k => AnnotTerm.bvar (d.nIdxAt t - 1 - k)) from rfl,
          map_fieldBvars_interp hisLen]
        exact hfitAll
      exact (wellDenotedV_mkAppN_of_spineFit hT
        ⟨mp.base2.acval_wellDenoted _ ψ _, mp.acval_validV _ ψ _⟩
        (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
            exact ⟨by simp, by simp⟩
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
            exact ⟨by simp, by simp⟩) hmem hfit).1
    · rw [hnI, interp_famAppAV_params hclosed (nIdx := d.nIdxAt t) hpsLen hisLen ρ, hlev]
      have := mkPisAV_fold_mem (m := 1)
        (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbits dd hd)⟩)
        (fun h => absurd h Nat.one_ne_zero) (hmemL ρ) hfitAll
      rw [interp_sort] at this
      exact this

/-! ## The choice's bodies -/

/-- **The body of constructor `J`**: the head (the container's
constructor at the pins for a copy's constructor, the member's own at
the parameter variables for a real one — at the parameter frame,
lifted over the motives, the earlier minors, the fields and the
hypotheses) at the mixed variable spine. -/
@[expose] def invBodyAV (head : Nat → AnnotTerm) (useIh : Nat → Nat → Bool) (J : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN
    ((head J).liftN
      (d.k + J + (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length) 0)
    (mixedVarsAV (ConLeche.recIdxOf (d.ksR J)) (useIh J) (d.ctorsAll.getD J default).2)

end IndRepData

/-- **Field `i`'s domain in TARGET form** (at the parameter frame, under
the earlier fields): where `useIh`, the target of the field's member
at the field's index readings under the field's telescope (rebit to
the elimination bit, as the tower's ih binders) — the domain of the
inductive hypothesis; the field's own domain otherwise. -/
@[expose] def tgFieldAV (Tg : Nat → AnnotTerm) (useIh : Nat → Bool) (nP b : Nat) (tgt : Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) (i : Nat) : AnnotTerm :=
  if useIh i then
    mkPisAV (rebit b (tls.getD i []))
      (AnnotTerm.mkAppN ((Tg (tgt i)).liftN (nP + i + (tls.getD i []).length) 0) (Eiss.getD i []))
  else (ds.getD (nP + i) default).2.2

/-- The target-form field domains. -/
@[expose] def tgFieldsAV (Tg : Nat → AnnotTerm) (useIh : Nat → Bool) (nP b : Nat) (tgt : Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) (nF : Nat) : List AnnotTerm :=
  (List.range nF).map (tgFieldAV Tg useIh nP b tgt ds Eiss tls)

namespace IndRepData

variable (d : IndRepData V)

/-- **The constructor at the pins** — the ONE hypothesis the body's fact
needs, in the aux datum's vocabulary: at the parameter frame, the
head inhabits a graded Π-tower over `nF` binders whose binders accept
every spine fitting the target-form field domains, and whose body at
such a spine is the member's target at the constructor's index
readings.  For a real member's constructor it is the constructor's
own reading (`ctorAtPins_real`); for a copy's it is the container
constructor's at the pins. -/
@[expose] def CtorAtPins (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm) (Tg : Nat → AnnotTerm)
    (useIh : Nat → Bool) (J : Nat) (head : AnnotTerm) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm))
    (Es : List AnnotTerm) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) : Prop :=
  ∃ (dsC : List (Nat × Nat × AnnotTerm)) (bodyC : AnnotTerm),
    dsC.length = nF ∧
    WellDenotedV V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC) ∧
    WellDenotedV V (consList (ps.map (interp V ρ)) ρ) head ∧
    interp V (consList (ps.map (interp V ρ)) ρ) head
      ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC) ∧
    ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ)
        (tgFieldsAV Tg useIh d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF) vs →
      SpineFit (consList (ps.map (interp V ρ)) ρ) (dsC.map (·.2.2)) vs ∧
      interp V (consList vs (consList (ps.map (interp V ρ)) ρ)) bodyC
        = (Es.map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ)))).foldl
            SetTheory.app (interp V ρ (Tg (d.mems J)))

set_option maxHeartbeats 3200000 in
/-- **The body's fact** (the kit's `hleaf`) from `CtorAtPins`: at a
spine of fields and target-form hypotheses, the mixed values fit the
target-form field domains — each read at the MIXED prefix, the same
as at the fields' by the bridge (`interp_congr_shadowRel_at` at the
datum's `NoBVar` facts) — so the head at the mixed spine is graded
(`wellDenotedV_mkAppN_of_spineFit` at the tower lifted to the leaf
frame) and lands in the member's target at the constructor's index
readings (read at the fields, by the bridge again). -/
theorem invBody_leaf {ψ : Name → Nat} {ρ : Nat → V} {ps Ms prior : List AnnotTerm}
    (hps : ps.length = d.nP) (hMs : Ms.length = d.k) (hk : 0 < d.k) {J : Nat}
    (hprior : prior.length = J) {Tg : Nat → AnnotTerm} {head : Nat → AnnotTerm}
    {useIh : Nat → Nat → Bool} {C : Name} {nF : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Es : List AnnotTerm} {recIdx : List Nat} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    (hcd : (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls))
    (hds : ds.length = d.nP + nF)
    (hnb : ∀ i, i < nF → NoBVar (exclP (fun q => recAt d.nP (d.ksR J) q ∧ q < d.nP + i) (d.nP + i))
      ((ds.getD (d.nP + i) default).2.2))
    (hnbT : ∀ i, i < nF → ∀ k dd, (tls.getD i [])[k]? = some dd →
      NoBVar (exclP (fun q => recAt d.nP (d.ksR J) q ∧ q < d.nP + i) (d.nP + i + k)) dd.2.2)
    (hnbE : ∀ i, i < nF → ∀ E ∈ Eiss.getD i [],
      NoBVar (exclP (fun q => recAt d.nP (d.ksR J) q ∧ q < d.nP + i) (d.nP + i + (tls.getD i []).length)) E)
    (hnbEs : ∀ E ∈ Es, NoBVar (exclP (fun q => recAt d.nP (d.ksR J) q ∧ q < d.nP + nF) (d.nP + nF)) E)
    (huse : ∀ i, useIh J i = true → i ∈ recIdx)
    (hCAP : d.CtorAtPins ψ ρ ps Tg (useIh J) J (head J) nF ds Es Eiss tls)
    (hzero : d.bb ψ = 0 → ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
        SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)) :
    ∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
      SpineFit (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ)
        ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
        (fs ++ ihs) →
      WellDenotedV V (consList (fs ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
        (d.invBodyAV head useIh J) ∧
      interp V (consList (fs ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
          (d.invBodyAV head useIh J)
        ∈ˢ (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
            SetTheory.app (interp V ρ (Tg (d.mems J))) ∧
      (d.bb ψ = 0 →
        (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
          SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)) := by
  intro fs ihs hfs hihs hfit
  -- the constructor's shape from the datum list
  have hcd' := hcd
  unfold cdsR at hcd'
  rw [fixCtorDataList_getElem?, Nat.zero_add] at hcd'
  obtain ⟨cA, hcA, hcAeq⟩ := Option.map_eq_some_iff.mp hcd'
  simp only [Prod.mk.injEq] at hcAeq
  obtain ⟨-, hnFc, -, -, hrec, -, -⟩ := hcAeq
  have hnFget : (d.ctorsAll.getD J default).2 = nF := by
    rw [List.getD_eq_getElem?_getD, hcA]; exact hnFc
  -- the frames
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hσ' : consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ
      = consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
          (consList (ps.map (interp V ρ)) ρ)) := by
    rw [List.map_append, List.map_append, consList_append, consList_append]
  have hshiftO : shiftE (d.k + J) 0 (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
      (consList (ps.map (interp V ρ)) ρ))) = consList (ps.map (interp V ρ)) ρ := by
    rw [← consList_append, show d.k + J = (Ms.map (interp V ρ) ++ prior.map (interp V ρ)).length from by
        rw [List.length_append, List.length_map, List.length_map, hMs, hprior]]
    exact shiftE_consList _ _
  -- the fit, split into the fields and the hypotheses
  rw [hσ'] at hfit
  unfold minorDataTg at hfit
  rw [List.map_append] at hfit
  obtain ⟨fs', ihs', heq, hfitF, hfitI⟩ := spineFit_append_inv hfit
  have hlenF' : fs'.length = nF := by
    rw [hfitF.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hds]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlenF', hfs])
  -- the fields fit their domains at the parameter frame
  have hfsFit : SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs := by
    rw [rebit_map_dom, spineFit_liftDoms, hshiftO] at hfitF
    exact hfitF
  -- a hypothesis lands in the target-form domain of its field, read at
  -- the fields' prefix
  have hb : ∀ dd ∈ rebit (d.bb ψ) (tls.getD 0 []), True := fun _ _ => trivial
  have hih : ∀ l i, recIdx[l]? = some i → i < nF →
      ihs.getD l pt ∈ˢ interp V (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        (mkPisAV (rebit (d.bb ψ) (tls.getD i []))
          (AnnotTerm.mkAppN ((Tg (d.tgtsR J i)).liftN (d.nP + i + (tls.getD i []).length) 0)
            (Eiss.getD i []))) := by
    intro l i hl hi
    have hlLt : l < recIdx.length := (List.getElem?_eq_some_iff.mp hl).1
    have hmemI := spineFit_getElem? hfitI l (ihs.getD l pt)
      (tgIhDomAV Tg (d.tgtsR J i) d.nP nF (d.k + J) i l (rebit (d.bb ψ) (tls.getD i []))
        (Eiss.getD i []))
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl)
      (by simp only [List.getElem?_map, ihDataTg_getElem?, hl, Option.map_some, Nat.zero_add])
    have hbits : ∀ dd ∈ rebit (d.bb ψ) (tls.getD i []), (dd.2.1 = 0 ↔ d.bb ψ = 0) :=
      fun dd hd => by rw [mem_rebit hd]
    rw [interp_tgIhDomAV (ps := ps.map (interp V ρ)) (Ms := Ms.map (interp V ρ))
      (ms := prior.map (interp V ρ)) hpsLen (by rw [List.length_map, List.length_map, hprior, hMs]; omega)
      (by rw [List.length_map, hMs]; exact hk) hfs (by rw [List.length_take]; omega) hi hbits] at hmemI
    rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := d.bb ψ) (acc := [])
      (B := fun as => ((Eiss.getD i []).map
        (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))).foldl
          SetTheory.app (interp V ρ (Tg (d.tgtsR J i)))) hbits]
    · exact hmemI
    · intro as hsp
      have hasLen : as.length = (tls.getD i []).length := by
        rw [hsp.length_eq, List.length_map, rebit_length]
      rw [List.nil_append, interp_mkAppN_map, interp_liftN, ← consList_append, ← consList_append,
        show d.nP + i + (tls.getD i []).length
          = (ps.map (interp V ρ) ++ (fs.take i ++ as)).length from by
            rw [List.length_append, List.length_append, hpsLen, List.length_take, hasLen]; omega,
        shiftE_consList, consList_append, consList_append]
  -- the mixed values
  obtain ⟨vs, hvs⟩ : ∃ vs, vs = mixedVals recIdx (useIh J) fs ihs := ⟨_, rfl⟩
  have hvsLen : vs.length = nF := by rw [hvs, mixedVals_length, hfs]
  have hvsGet : ∀ i, i < nF → vs.getD i pt
      = if useIh J i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt := by
    intro i hi
    rw [hvs, mixedVals_getD _ _ _ _ (by rw [hfs]; exact hi)]
  have hrecAt : ∀ i, useIh J i = true → recAt d.nP (d.ksR J) (d.nP + i) := by
    intro i hu
    have := mem_recIdxOf.mp (by rw [hrec]; exact huse i hu)
    exact ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact this.2⟩
  have hSR : ShadowRel d.nP (d.ksR J) fs vs := by
    refine ⟨by rw [hvsLen, hfs], fun l hl hr => ?_⟩
    rw [hvsGet l (by omega), if_neg]
    intro hu
    exact hr (hrecAt l hu)
  -- the mixed values fit the target-form domains
  have hvsFit : SpineFit (consList (ps.map (interp V ρ)) ρ)
      (tgFieldsAV Tg (useIh J) d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF) vs := by
    refine spineFit_of_getElem? (by rw [hvsLen]; simp [tgFieldsAV]) ?_
    intro n v F hv hF
    have hn : n < nF := by
      have := (List.getElem?_eq_some_iff.mp hv).1
      rw [hvsLen] at this; exact this
    have hFeq : F = tgFieldAV Tg (useIh J) d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls n := by
      unfold tgFieldsAV at hF
      rw [List.getElem?_map, List.getElem?_range hn] at hF
      exact (Option.some.inj hF).symm
    have hveq : v = vs.getD n pt := by
      rw [List.getD_eq_getElem?_getD, hv]; rfl
    subst hFeq
    rw [hveq, hvsGet n hn]
    have hQ : ∀ q, (recAt d.nP (d.ksR J) q ∧ q < d.nP + n) → q < d.nP + n := fun _ h => h.2
    unfold tgFieldAV
    split
    · next hu =>
      have hmem := huse n hu
      have hl : recIdx[recIdx.idxOf n]? = some n := getElem?_idxOf_of_mem hmem
      have hm := hih (recIdx.idxOf n) n hl hn
      rw [interp_congr_shadowRel_at hSR _ (by rw [hfs]; exact Nat.le_of_lt hn)] at hm
      · exact hm
      · refine NoBVar_mkPisAV_exclP _ hQ ?_ ?_
        · intro k dd hk
          rw [rebit_getElem?] at hk
          obtain ⟨dd', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
          exact hnbT n hn k dd' hk'
        · rw [rebit_length]
          refine NoBVar_mkAppN (NoBVar_liftN _ fun i hi => ⟨Nat.zero_le _, ?_⟩) _ (hnbE n hn)
          obtain ⟨q, -, hq, rfl⟩ := hi
          omega
    · have hlt : d.nP + n < ds.length := by rw [hds]; omega
      have hm := spineFit_getElem? hfsFit n (fs.getD n pt) ((ds.getD (d.nP + n) default).2.2)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < fs.length)]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem hlt,
          Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
      rw [interp_congr_shadowRel_at hSR _ (by rw [hfs]; exact Nat.le_of_lt hn) (hnb n hn)] at hm
      exact hm
  -- the constructor at the pins
  obtain ⟨dsC, bodyC, hdsC, hTC, hheadWD, hheadMem, hvsC⟩ := hCAP
  obtain ⟨hvsFitC, hbodyC⟩ := hvsC vs hvsFit
  -- the index readings at the mixed values are those at the fields
  have hEsEq : Es.map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ)))
      = Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))) := by
    apply List.map_congr_left
    intro E hE
    have := interp_congr_shadowRel hSR (consList (ps.map (interp V ρ)) ρ) [] (E := E)
      (by rw [hfs, List.length_nil, Nat.add_zero]; exact hnbEs E hE)
    simpa using this.symm
  -- the body at the leaf frame
  have hσb : consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ)))
      = consList (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs ++ ihs)
          (consList (ps.map (interp V ρ)) ρ) := by
    rw [consList_append, consList_append, consList_append, consList_append]
  have hshiftB : shiftE (d.k + J + nF + recIdx.length) 0
      (consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ)))) = consList (ps.map (interp V ρ)) ρ := by
    rw [hσb, show d.k + J + nF + recIdx.length
        = (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs ++ ihs).length from by
          simp [hMs, hprior, hfs, hihs]; omega]
    exact shiftE_consList _ _
  rw [hσ']
  unfold invBodyAV
  rw [hnFget, hrec]
  have hvars : (mixedVarsAV recIdx (useIh J) nF).map
      (interp V (consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ))))) = vs := by
    rw [← hfs, interp_mixedVarsAV huse hihs, hvs]
  have hmain := wellDenotedV_mkAppN_of_spineFit
    (σ := consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
      (consList (ps.map (interp V ρ)) ρ))))
    (ds := liftDoms (d.k + J + nF + recIdx.length) 0 dsC)
    (C := bodyC.liftN (d.k + J + nF + recIdx.length) (0 + dsC.length))
    (f := (head J).liftN (d.k + J + nF + recIdx.length) 0)
    (as := mixedVarsAV recIdx (useIh J) nF)
    (by rw [← liftN_mkPisAV, WellDenotedV_liftN, hshiftB]; exact hTC)
    (by rw [WellDenotedV_liftN, hshiftB]; exact hheadWD)
    (fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      split <;> exact ⟨by simp, by simp⟩)
    (by rw [← liftN_mkPisAV, interp_liftN, interp_liftN, hshiftB]; exact hheadMem)
    (by rw [spineFit_liftDoms, hshiftB, hvars]; exact hvsFitC)
  refine ⟨hmain.1, ?_, fun h0 => hzero h0 fs hfsFit⟩
  have h2 := hmain.2
  have hlen0 : 0 + dsC.length = vs.length := by rw [Nat.zero_add, hdsC, hvsLen]
  rw [hvars, interp_liftN, hlen0, shiftE_consList_len, hshiftB, hbodyC, hEsEq] at h2
  exact h2

/-! ## The target's β, and a real constructor at the pins -/

/-- **The target's β**: applied along fitting index values, the target
is the family at the pins at those values (`mkLamsAV_fold` under
`instSeq`). -/
theorem invTg_fold (ψ : Name → Nat) {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {t : Nat} {is : List V}
    (hfit : SpineFit (consList (ps.map (interp V ρ)) ρ)
      ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is) :
    is.foldl SetTheory.app (interp V ρ (d.invTgAV ψ ps L pinsT t))
      = interp V (consList is (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  unfold invTgAV
  rw [interp_instSeq_consList]
  refine mkLamsAV_fold (fun x hx => ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    show y.2.1 ≠ 0
    rw [mem_rebit hy]; exact hb
  · rw [List.map_map]; exact hfit

omit [SetTheory V] in
/-- Without hypotheses in use, the target-form field domains are the
constructor's own. -/
theorem tgFieldsAV_false (Tg : Nat → AnnotTerm) (nP b : Nat) (tgt : Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) {nF : Nat} (hds : ds.length = nP + nF) :
    tgFieldsAV Tg (fun _ => false) nP b tgt ds Eiss tls nF = (ds.drop nP).map (·.2.2) := by
  apply List.ext_getElem
  · simp [tgFieldsAV, hds]
  · intro i h1 h2
    have hi : i < nF := by simpa [tgFieldsAV] using h1
    simp only [tgFieldsAV, tgFieldAV, List.getElem_map, List.getElem_range, Bool.false_eq_true,
      if_false, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show nP + i < ds.length by omega), Option.getD_some]

set_option maxHeartbeats 1600000 in
/-- **A real member's constructor at the pins**: its `CtorAtPins` at the
identity choice — head the constructor at the parameter variables, no
hypotheses in use — from the constructor's own reading
(`FixCtorFactsAt`, `mem_type`): the tower below the parameters
(`hfitP` through `paramsIff`), the head graded and in it by the tower
lifted to the parameter frame, and the body at the fields the target
(`invTgAV` at the member's own leaf) at the index readings, whose fit
is `hEsFit` (`CtorFieldFacts`'s). -/
theorem ctorAtPins_real {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} (hps : ps.length = d.nP)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    {J : Nat} {cA : ConstantVal × Nat}
    (hC : FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i)))
    (hpIff : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hEsFit : ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) (((d.dsF J ψ).drop d.nP).map (·.2.2)) fs →
      SpineFit (consList (ps.map (interp V ρ)) ρ)
        ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2))
        ((d.esF J ψ).map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))))
    {Eiss : List (List AnnotTerm)} {tls : List (List (Nat × Nat × AnnotTerm))} :
    d.CtorAtPins ψ ρ ps
      (d.invTgAV ψ ps (fun t => mp.base2.acval (d.memberName t) ψ) (fun _ => paramBvarsAt d.nP d.nP))
      (fun _ => false) J (AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (paramBvarsAt d.nP d.nP))
      cA.2 (d.dsF J ψ) (d.esF J ψ) Eiss tls := by
  obtain ⟨hfind, -, hD⟩ := hC
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hlenDs := hD.len ψ
  have hclosedC : Term.bvarsBelow 0 (mp.base2.acval cA.1.name ψ).erase := mp.base2.cval_closedL _ ψ
  have hclosedT : Term.bvarsBelow 0 (mp.base2.acval (d.memberName (d.mems J)) ψ).erase :=
    mp.base2.cval_closedL _ ψ
  have hfitP : SpineFit ρ (((d.dsF J ψ).take d.nP).map (·.2.2)) (ps.map (interp V ρ)) :=
    spineFit_of_paramsIff hpsLen (by simp [hlenDs]) hparams hpIff
  have hsplitT : mkPisAV (d.dsF J ψ) (ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))
      = mkPisAV ((d.dsF J ψ).take d.nP)
          (mkPisAV ((d.dsF J ψ).drop d.nP)
            (ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) := by
    rw [← mkPisAV_append, List.take_append_drop]
  have hshift : shiftE d.nP 0 (consList (ps.map (interp V ρ)) ρ) = ρ := by
    rw [← hpsLen]; exact shiftE_consList _ _
  have hcmem : interp V ρ (mp.base2.acval cA.1.name ψ)
      ∈ˢ interp V ρ (mkPisAV (d.dsF J ψ)
          (ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) :=
    mp.mem_type _ (Env.find?_mem hfind) ψ _ (hD.read ψ) ρ
  -- the head, at the parameter frame: the tower lifted there
  have hhead := wellDenotedV_mkAppN_of_spineFit (σ := consList (ps.map (interp V ρ)) ρ)
    (ds := liftDoms d.nP 0 ((d.dsF J ψ).take d.nP))
    (C := (mkPisAV ((d.dsF J ψ).drop d.nP)
      (ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))).liftN d.nP
        (0 + ((d.dsF J ψ).take d.nP).length))
    (f := mp.base2.acval cA.1.name ψ) (as := paramBvarsAt d.nP d.nP)
    (by rw [← liftN_mkPisAV, ← hsplitT, WellDenotedV_liftN, hshift]; exact hD.okTy ψ ρ)
    ⟨mp.base2.acval_wellDenoted _ ψ _, mp.acval_validV _ ψ _⟩
    (fun a ha => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp, by simp⟩)
    (by rw [← liftN_mkPisAV, ← hsplitT, interp_liftN, hshift, interp_closed (V := V) hclosedC _ ρ]
        exact hcmem)
    (by rw [spineFit_liftDoms, hshift, interp_paramBvarsAt_self hpsLen]; exact hfitP)
  have htakeLen : 0 + ((d.dsF J ψ).take d.nP).length = (ps.map (interp V ρ)).length := by
    rw [Nat.zero_add, List.length_take, hlenDs, hpsLen]; omega
  rw [interp_paramBvarsAt_self hpsLen, interp_liftN, htakeLen, shiftE_consList_len, hshift] at hhead
  refine ⟨(d.dsF J ψ).drop d.nP,
    ctorBodyAVI mp.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ),
    by rw [List.length_drop, hlenDs]; omega, ?_, hhead.1, hhead.2, ?_⟩
  · have h := hD.okTy ψ ρ
    rw [hsplitT] at h
    exact ⟨wellDenoted_mkPisAV_body h.1 _ hfitP, annotValid_mkPisAV_body h.2 _ hfitP⟩
  · intro vs hvs
    rw [tgFieldsAV_false _ _ _ _ _ _ _ hlenDs] at hvs
    refine ⟨hvs, ?_⟩
    have hvsLen : vs.length = cA.2 := by
      rw [hvs.length_eq, List.length_map, List.length_drop, hlenDs]; omega
    have hEl : (d.esF J ψ).length = d.nIdxAt (d.mems J) := hD.lenE ψ
    have hnI : d.nIdxs.getD (d.mems J) 0 = d.nIdxAt (d.mems J) := rfl
    have hfam := interp_famAppAV_params hclosedT (nIdx := d.nIdxAt (d.mems J)) hpsLen
      (is := (d.esF J ψ).map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ))))
      (by rw [List.length_map]; exact hEl) ρ
    rw [d.invTg_fold ψ (hEsFit vs hvs), hnI, hfam]
    show interp V (consList vs (consList (ps.map (interp V ρ)) ρ))
      (AnnotTerm.mkAppN (mp.base2.acval (d.memberName (d.mems J)) ψ)
        (paramBvarsAt d.nP (d.nP + cA.2) ++ d.esF J ψ)) = _
    rw [interp_mkAppN_map, List.map_append,
      map_paramBvarsAt_interp (ρp := consList (ps.map (interp V ρ)) ρ)
        (fun j => by
          have h := consList_apply_add vs (consList (ps.map (interp V ρ)) ρ) j
          rw [hvsLen] at h; exact h),
      range_reverse_map_consList' hpsLen, interp_closed (V := V) hclosedT _ ρ]

/-! ## Spines against a telescope ending in one binder -/

/-- A spine fits `Fs ++ [F]` iff it is a spine fitting `Fs` followed by
one value in `F` at that spine's frame. -/
theorem spineFit_append_singleton_iff {ρ : Nat → V} {Fs : List AnnotTerm} {F : AnnotTerm}
    {vs : List V} :
    SpineFit ρ (Fs ++ [F]) vs ↔
      ∃ as x, vs = as ++ [x] ∧ SpineFit ρ Fs as ∧ x ∈ˢ interp V (consList as ρ) F := by
  constructor
  · intro h
    obtain ⟨as, bs, rfl, h1, h2⟩ := spineFit_append_inv h
    cases bs with
    | nil => exact h2.elim
    | cons x bs =>
      cases bs with
      | nil => exact ⟨as, x, rfl, h1, h2.1⟩
      | cons _ _ => exact h2.2.elim
  · rintro ⟨as, x, rfl, h1, h2⟩
    exact SpineFit.append h1 ⟨h2, trivial⟩

/-- **The trailer's fit is the motive binder's fit at the parameter
frame**: the index telescope lifted under the motives and the minors
fits iff it fits at the parameter frame, and the major's family (at
the deeper frame) reads as the motive's (at the parameter frame). -/
theorem spineFit_recPostAV_iff (m : EnvModel V env) (ψ : Name → Nat) {t : Nat} (ht : t < d.k)
    (hipsLen : ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0)
    {ρ : Nat → V} {psV MsV NsV : List V} (hMs : MsV.length = d.k) (hNs : NsV.length = d.nAll)
    (vs : List V) :
    SpineFit (consList (psV ++ MsV ++ NsV) ρ) ((d.recPostAV m ψ t).map (·.2.2)) vs ↔
      SpineFit (consList psV ρ) ((d.motDataAV m ψ t).map (·.2.2)) vs := by
  have hLcl : ∀ σ₁ σ₂ : Nat → V, interp V σ₁ ((d.Ls m ψ).getD t default)
      = interp V σ₂ ((d.Ls m ψ).getD t default) := d.Ls_getD_closed m ψ ht
  have hframe : consList (psV ++ MsV ++ NsV) ρ = consList (MsV ++ NsV) (consList psV ρ) := by
    rw [List.append_assoc, consList_append]
  have hshift : shiftE (d.k + d.nAll) 0 (consList (MsV ++ NsV) (consList psV ρ)) = consList psV ρ := by
    rw [show d.k + d.nAll = (MsV ++ NsV).length from by rw [List.length_append, hMs, hNs]]
    exact shiftE_consList _ _
  unfold recPostAV motDataAV majorAVP
  rw [hframe, List.map_append, List.map_append, rebit_map_dom, rebit_map_dom, List.map_singleton,
    List.map_singleton, d.Ls_length, d.cdsR_length, spineFit_append_singleton_iff,
    spineFit_append_singleton_iff]
  constructor
  · rintro ⟨as, x, rfl, h1, h2⟩
    rw [spineFit_liftDoms, hshift] at h1
    refine ⟨as, x, rfl, h1, ?_⟩
    have hasLen : as.length = d.nIdxs.getD t 0 := by
      rw [h1.length_eq, List.length_map, hipsLen]
    have e1 := interp_famAppAV_at hLcl (d.pinsOf ψ t) d.nP (extra := MsV ++ NsV) (is := as)
      (σ := consList psV ρ)
    rw [List.length_append, hMs, hNs, hasLen, show d.nP + (d.k + d.nAll) + d.nIdxs.getD t 0
        = d.nP + d.k + d.nAll + d.nIdxs.getD t 0 from by omega] at e1
    have e2 := interp_famAppAV_at hLcl (d.pinsOf ψ t) d.nP (extra := []) (is := as)
      (σ := consList psV ρ)
    rw [List.length_nil, hasLen, Nat.add_zero, consList_nil] at e2
    rw [e2, ← e1]
    exact h2
  · rintro ⟨as, x, rfl, h1, h2⟩
    refine ⟨as, x, rfl, by rw [spineFit_liftDoms, hshift]; exact h1, ?_⟩
    have hasLen : as.length = d.nIdxs.getD t 0 := by
      rw [h1.length_eq, List.length_map, hipsLen]
    have e1 := interp_famAppAV_at hLcl (d.pinsOf ψ t) d.nP (extra := MsV ++ NsV) (is := as)
      (σ := consList psV ρ)
    rw [List.length_append, hMs, hNs, hasLen, show d.nP + (d.k + d.nAll) + d.nIdxs.getD t 0
        = d.nP + d.k + d.nAll + d.nIdxs.getD t 0 from by omega] at e1
    have e2 := interp_famAppAV_at hLcl (d.pinsOf ψ t) d.nP (extra := []) (is := as)
      (σ := consList psV ρ)
    rw [List.length_nil, hasLen, Nat.add_zero, consList_nil] at e2
    rw [e1, ← e2]
    exact h2

/-! ## The assembly -/

/-- **The kit's per-constructor bundle** (`choice_prefix_fit`/
`choice_fold_iota`'s `hmin`, verbatim). -/
@[expose] def KitMin (m : EnvModel V env) (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm)
    (Tg : Nat → AnnotTerm) (bodies : Nat → AnnotTerm) : Prop :=
  ∀ J, J < d.nAll → ∀ (C : Name) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm))
    (Es : List AnnotTerm) (recIdx : List Nat) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))),
    (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls) →
    ds.length = d.nP + nF ∧ d.mems J < d.k ∧ (∀ i ∈ recIdx, i < nF ∧ d.tgtsR J i < d.k) ∧
    (∀ i ∈ recIdx, ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
          ((tls.getD i []).map (·.2.2)) as →
        SpineFit (consList (ps.map (interp V ρ)) ρ)
            ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR J i) [])).map (·.2.2))
            ((Eiss.getD i []).map
              (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ∧
          as.foldl SetTheory.app (fs.getD i pt)
            ∈ˢ interp V (consList ((Eiss.getD i []).map
                (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))))
                (consList (ps.map (interp V ρ)) ρ))
              (famAppAV ((d.Ls m ψ).getD (d.tgtsR J i) default) (d.pinsOf ψ (d.tgtsR J i))
                d.nP (d.nP + d.nIdxs.getD (d.tgtsR J i) 0) (d.nIdxs.getD (d.tgtsR J i) 0))) ∧
    (∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems J) [])).map (·.2.2))
          (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))) ∧
        fs.foldl SetTheory.app
            (interp V (consList (ps.map (interp V ρ)) ρ)
              (AnnotTerm.mkAppN (m.acval C ψ) (d.pinsOf ψ (d.mems J))))
          ∈ˢ interp V (consList (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))))
              (consList (ps.map (interp V ρ)) ρ))
            (famAppAV ((d.Ls m ψ).getD (d.mems J) default) (d.pinsOf ψ (d.mems J)) d.nP
              (d.nP + d.nIdxs.getD (d.mems J) 0) (d.nIdxs.getD (d.mems J) 0))) ∧
    (∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
      SpineFit (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ)
        ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
        (fs ++ ihs) →
      WellDenotedV V (consList (fs ++ ihs)
          (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
            d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ))
          (bodies J) ∧
        interp V (consList (fs ++ ihs)
            (consList ((ps ++ d.motChoiceAVs m ψ ps Tg ++
              d.minChoiceAVs ψ ps (d.motChoiceAVs m ψ ps Tg) bodies J).map (interp V ρ)) ρ))
            (bodies J)
          ∈ˢ (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
              SetTheory.app (interp V ρ (Tg (d.mems J))) ∧
        (d.bb ψ = 0 →
          (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
              SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)))

/-- **The ψ⁻¹ choice's setup** over the auxiliary datum `d` (a plain
mutual datum: no copy members, the pins the parameter variables, the
recursor view the family view): the fold's frame and parameters, the
datum's clauses the instance reads (`RecReadAt` for every member,
`ctors`, `paramsIff`, and the two facts recorded as findings —
`LeafShape`, `FormerFacts`), and the consumer's choice — the leaves
`L` at pins `pinsT` with their `TargetOk` (real members:
`targetOk_real`; copies: the pins' typing), the heads with their
`CtorAtPins` (real constructors: `ctorAtPins_real`; copies: the
container constructor's at the pins), and which fields use their
hypothesis. -/
structure InvSetup {μ : CheckMode} (mp : EnvModelM V μ env) (lps lpsT : List Name)
    (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm) (L : Nat → AnnotTerm)
    (pinsT : Nat → List AnnotTerm) (head : Nat → AnnotTerm) (useIh : Nat → Nat → Bool) : Prop where
  hR : ∀ t, t < d.k → RecReadAt mp.base2 d lps t
  hps : ps.length = d.nP
  hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p
  hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ))
  hpps : ((d.ppsM 0 ψ).take d.nP).length = d.nP
  hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0
  hk : 0 < d.k
  hctorsC : d.ctorsC = []
  hpins : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP
  hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
    d.tssR J = d.tssF J
  hLS : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t
  hFF : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t
  hctors : ∀ J cA, d.ctorsA[J]? = some cA →
    FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i))
  hpIff : ∀ J cA, d.ctorsA[J]? = some cA → ∀ ρ' : Nat → V,
    Sat V (d.params ψ).reverse ρ' ↔ Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ'
  hmems : ∀ J, J < d.ctorsA.length → d.mems J < d.k
  htgts : ∀ J i, d.tgts J i < d.k
  hTg : ∀ t, t < d.k → d.TargetOk ψ ρ ps L pinsT t
  hCAP : ∀ J cA, d.ctorsA[J]? = some cA →
    d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ) (d.esF J ψ)
      (d.eissR J ψ) (d.tssR J ψ)
  huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)

namespace InvSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}

/-- Every constructor of the recursor's block is real. -/
theorem nAll_eq (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) :
    d.nAll = d.ctorsA.length := by
  unfold IndRepData.nAll; rw [S.hctorsC]; rfl

theorem ctorsAll_eq (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) :
    d.ctorsAll = d.ctorsA := by
  unfold IndRepData.ctorsAll; rw [S.hctorsC, List.append_nil]

set_option maxHeartbeats 3200000 in
/-- **The kit's per-constructor bundle holds of the ψ⁻¹ choice.** -/
theorem hmin (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) :
    d.KitMin mp.base2 ψ ρ ps (d.invTgAV ψ ps L pinsT) (d.invBodyAV head useIh) := by
  intro J hJ C nF ds Es recIdx Eiss tls hcd
  have hcd' := hcd
  unfold IndRepData.cdsR at hcd'
  rw [fixCtorDataList_getElem?, Nat.zero_add, S.ctorsAll_eq] at hcd'
  obtain ⟨cA, hcA, hcAeq⟩ := Option.map_eq_some_iff.mp hcd'
  simp only [Prod.mk.injEq] at hcAeq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcAeq
  have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
  obtain ⟨hks, htgtR, heiss, htss⟩ := S.hview J
  have hC := S.hctors J cA hcA
  have hfind := hC.1
  have hD := hC.2.2
  have hwf := mp.base2.wf _ (Env.find?_mem hfind)
  have hcf : cA.1.type.hasFvar = false := hwf.1
  have hcb : cA.1.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
  have hmemJ : d.mems J < d.k := S.hmems J hJA
  have htgtR' : ∀ i, d.tgtsR J i = d.tgts J i := fun i => by rw [htgtR]
  have cff := d.ctorFieldFacts_of mp S.hps S.hpins S.hLS S.hFF S.hparams hC (S.hpIff J cA hcA)
    hmemJ (S.htgts J) htgtR'
  obtain ⟨hnb, hnbT, hnbE, hnbEs⟩ := FixCtorDataI.noBVar_entries hD hcf hcb ψ
  refine ⟨hD.len ψ, hmemJ, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hks] at hi
    obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hi
    rw [hD.ksLen] at hlt
    exact ⟨hlt, by rw [htgtR]; exact S.htgts J i⟩
  · rw [hks, heiss, htss]; exact cff.1
  · exact cff.2
  · refine d.invBody_leaf S.hps (d.motChoiceAVs_length _ _ _ _) S.hk
      (d.minChoiceAVs_length _ _ _ _ _) hcd (hD.len ψ) ?_ ?_ ?_ ?_ (S.huse J) (S.hCAP J cA hcA) ?_
    · rw [hks]; exact hnb
    · rw [hks, htss]; exact hnbT
    · rw [hks, htss, heiss]; exact hnbE
    · rw [hks]; exact hnbEs
    · intro h0 fs hfs
      have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp h0
      rw [d.invTg_fold ψ (cff.2 fs hfs).1]
      have := ((S.hTg (d.mems J) hmemJ).2 _ (cff.2 fs hfs).1).2
      rw [h0', univ_zero] at this
      exact this

/-- **The choice's prefix fits the recursor tower.** -/
theorem prefixFit (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) :
    SpineFit ρ ((d.recPrefixAV mp.base2 ψ).map (·.2.2))
      ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
        d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
          (d.invBodyAV head useIh) d.nAll).map (interp V ρ)) :=
  d.choice_prefix_fit mp.base2 (d.invBodyAV head useIh) S.hps S.hk S.hpps S.hipsLen
    ((S.hR 0 S.hk).tower_wellDenotedV mp ψ ρ)
    (by rw [rebit_map_dom]; exact S.hparams)
    (fun t ht => d.invTg_fact ψ S.hpsWD (S.hTg t ht)) S.hmin

set_option maxHeartbeats 1600000 in
/-- **ψ⁻¹ is typed**: member `t`'s recursor at the choice's prefix, at
index readings and a major fitting the member's motive binder at the
parameter frame, lands in the member's target at those indices — the
leaf `L t` at the pins `pinsT t` at the index values. -/
theorem fold_mem (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) {t : Nat} (ht : t < d.k)
    {is' : List AnnotTerm} {x' : AnnotTerm}
    (hfitM : SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV mp.base2 ψ t).map (·.2.2))
      ((is' ++ [x']).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.invBodyAV head useIh) d.nAll ++ is' ++ [x']))
      ∈ˢ interp V (consList (is'.map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨Ns, hNs⟩ : ∃ Ns, Ns = d.minChoiceAVs ψ ps Ms (d.invBodyAV head useIh) d.nAll := ⟨_, rfl⟩
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hNsLen : Ns.length = d.nAll := by rw [hNs]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpre := S.prefixFit
  rw [← hMs, ← hNs] at hpre ⊢
  have h1 := recFold_mem mp (S.hR t ht) ψ hpre
  have hframe : consList ((ps ++ Ms ++ Ns).map (interp V ρ)) ρ
      = consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ := by
    rw [List.map_append, List.map_append]
  rw [hframe] at h1
  have hiff := d.spineFit_recPostAV_iff mp.base2 ψ ht (S.hipsLen t ht) (ρ := ρ)
    (psV := ps.map (interp V ρ)) (MsV := Ms.map (interp V ρ)) (NsV := Ns.map (interp V ρ))
    (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
  -- the conclusion at any fitting trailer spine is the target at the indices
  have hconc : ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      ∃ is x, vs = is ++ [x] ∧
        SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is ∧
        interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)
          = interp V (consList is (consList (ps.map (interp V ρ)) ρ))
              (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
    intro vs hvs
    have hvsM := (hiff vs).mp hvs
    have hsplit := hvsM
    unfold IndRepData.motDataAV at hsplit
    rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hsplit
    obtain ⟨is, x, rfl, hisFit, -⟩ := hsplit
    refine ⟨is, x, rfl, hisFit, ?_⟩
    have hisLen : is.length = d.nIdxAt t := by
      rw [hisFit.length_eq, List.length_map, rebit_length]; exact S.hipsLen t ht
    rw [← consList_append, ← List.append_assoc,
      interp_mutualConcAV_frame (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
        hisLen ht,
      hMs, d.motChoiceAVs_getD mp.base2 ψ ps _ ρ ht]
    have hfold := d.motChoiceAV_fold mp.base2 (Tg := d.invTgAV ψ ps L pinsT) S.hps (S.hipsLen t ht)
      hvsM
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hfold
    rw [hfold, d.invTg_fold ψ hisFit]
  have h0 : d.bb ψ = 0 → ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
        Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) ∈ˢ (univZero : V) := by
    intro hb0 vs hvs
    obtain ⟨is, x, rfl, hisFit, heq⟩ := hconc vs hvs
    rw [heq]
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp hb0
    have := ((S.hTg t ht).2 is hisFit).2
    rw [h0', univ_zero] at this
    exact this
  have hfitPost : SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
      Ns.map (interp V ρ)) ρ) ((d.recPostAV mp.base2 ψ t).map (·.2.2)) ((is' ++ [x']).map (interp V ρ)) :=
    (hiff _).mpr hfitM
  have h2 := mkPisAV_fold_mem (m := d.bb ψ) (fun dd hd => by rw [d.mem_recPostAV hd]) h0 h1 hfitPost
  obtain ⟨is, x, heq, hisFit, hconcEq⟩ := hconc _ hfitPost
  rw [hconcEq] at h2
  rw [List.map_append, List.map_singleton] at heq
  obtain ⟨rfl, -⟩ := List.append_inj heq (by
    have h1 := hfitM.length_eq
    rw [List.length_map, List.length_append, List.length_singleton, List.length_map] at h1
    unfold IndRepData.motDataAV at h1
    rw [List.length_append, rebit_length, List.length_singleton, S.hipsLen t ht] at h1
    have h2 := hisFit.length_eq
    rw [List.length_map, rebit_length, S.hipsLen t ht] at h2
    rw [List.length_map]
    omega)
  rw [show ps ++ Ms ++ Ns ++ is' ++ [x'] = (ps ++ Ms ++ Ns) ++ (is' ++ [x']) from by
      simp only [List.append_assoc],
    AnnotTerm.mkAppN_append, interp_mkAppN_map]
  exact h2

set_option maxHeartbeats 1600000 in
/-- **ψ⁻¹ is typed, at VALUES** (task #279 M-C′ step 5, the mirror of
`PsiSetup.fold_mem_vals`): member `t`'s fold term applied to index
values and a major fitting the member's motive binder at the parameter
frame lands in the member's target at those indices. -/
theorem fold_mem_vals (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) {t : Nat}
    (ht : t < d.k) {is : List V} {x : V}
    (hfitM : SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV mp.base2 ψ t).map (·.2.2))
      (is ++ [x])) :
    (is ++ [x]).foldl SetTheory.app
        (interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
          (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
            d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
              (d.invBodyAV head useIh) d.nAll)))
      ∈ˢ interp V (consList is (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨Ns, hNs⟩ : ∃ Ns, Ns = d.minChoiceAVs ψ ps Ms (d.invBodyAV head useIh) d.nAll := ⟨_, rfl⟩
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hNsLen : Ns.length = d.nAll := by rw [hNs]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpre := S.prefixFit
  rw [← hMs, ← hNs] at hpre ⊢
  have h1 := recFold_mem mp (S.hR t ht) ψ hpre
  have hframe : consList ((ps ++ Ms ++ Ns).map (interp V ρ)) ρ
      = consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ := by
    rw [List.map_append, List.map_append]
  rw [hframe] at h1
  have hiff := d.spineFit_recPostAV_iff mp.base2 ψ ht (S.hipsLen t ht) (ρ := ρ)
    (psV := ps.map (interp V ρ)) (MsV := Ms.map (interp V ρ)) (NsV := Ns.map (interp V ρ))
    (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
  have hconc : ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      ∃ is x, vs = is ++ [x] ∧
        SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is ∧
        interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)
          = interp V (consList is (consList (ps.map (interp V ρ)) ρ))
              (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
    intro vs hvs
    have hvsM := (hiff vs).mp hvs
    have hsplit := hvsM
    unfold IndRepData.motDataAV at hsplit
    rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hsplit
    obtain ⟨is, x, rfl, hisFit, -⟩ := hsplit
    refine ⟨is, x, rfl, hisFit, ?_⟩
    have hisLen : is.length = d.nIdxAt t := by
      rw [hisFit.length_eq, List.length_map, rebit_length]; exact S.hipsLen t ht
    rw [← consList_append, ← List.append_assoc,
      interp_mutualConcAV_frame (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
        hisLen ht,
      hMs, d.motChoiceAVs_getD mp.base2 ψ ps _ ρ ht]
    have hfold := d.motChoiceAV_fold mp.base2 (Tg := d.invTgAV ψ ps L pinsT) S.hps (S.hipsLen t ht)
      hvsM
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hfold
    rw [hfold, d.invTg_fold ψ hisFit]
  have h0 : d.bb ψ = 0 → ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
        Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) ∈ˢ (univZero : V) := by
    intro hb0 vs hvs
    obtain ⟨is, x, rfl, hisFit, heq⟩ := hconc vs hvs
    rw [heq]
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp hb0
    have := ((S.hTg t ht).2 is hisFit).2
    rw [h0', univ_zero] at this
    exact this
  have hfitPost : SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
      Ns.map (interp V ρ)) ρ) ((d.recPostAV mp.base2 ψ t).map (·.2.2)) (is ++ [x]) :=
    (hiff _).mpr hfitM
  have h2 := mkPisAV_fold_mem (m := d.bb ψ) (fun dd hd => by rw [d.mem_recPostAV hd]) h0 h1 hfitPost
  obtain ⟨is₂, x₂, heq, hisFit, hconcEq⟩ := hconc _ hfitPost
  rw [hconcEq] at h2
  obtain ⟨rfl, -⟩ := List.append_inj heq (by
    have h1 := hfitM.length_eq
    rw [List.length_map, List.length_append, List.length_singleton] at h1
    unfold IndRepData.motDataAV at h1
    rw [List.length_append, rebit_length, List.length_singleton, S.hipsLen t ht] at h1
    have h2 := hisFit.length_eq
    rw [List.length_map, rebit_length, S.hipsLen t ht] at h2
    omega)
  exact h2

set_option maxHeartbeats 1600000 in
/-- **ι of ψ⁻¹**: at real constructor `J`'s index readings and at
`C p⃗ f⃗`, the fold is the head at the MIXED values — the fields, and at
the hypothesis positions the target-fold hypotheses (each recursive
field's hypothesis the λ-tower over its telescope of its member's
fold at the same choice). -/
theorem fold_iota (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) (hb : d.bb ψ ≠ 0)
    {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA) {fs : List AnnotTerm}
    (hfitC : SpineFit ρ ((d.dsF J ψ).map (·.2.2)) ((ps ++ fs).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames (d.mems J)) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.invBodyAV head useIh) d.nAll ++
          d.ctorIdxAt ψ J (ps ++ fs) ++
          [AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (ps ++ fs)]))
      = (mixedVals (ConLeche.recIdxOf (d.ksR J)) (useIh J) (fs.map (interp V ρ))
          ((ConLeche.recIdxOf (d.ksR J)).map fun i =>
            lamTower (d.bb ψ)
              (consList ((fs.map (interp V ρ)).take i) (consList (ps.map (interp V ρ)) ρ))
              ((d.tssR J ψ).getD i []) fun σ' =>
                (ps.map (interp V ρ) ++
                  (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ) ++
                  (d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
                    (d.invBodyAV head useIh) d.nAll).map (interp V ρ) ++
                  ((d.eissR J ψ).getD i []).map (interp V σ') ++
                  [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ').foldl
                    SetTheory.app ((fs.map (interp V ρ)).getD i pt)]).foldl
                  SetTheory.app (interp V ρ (mp.base2.acval (d.recNames (d.tgtsR J i)) ψ)))).foldl
          SetTheory.app (interp V (consList (ps.map (interp V ρ)) ρ) (head J)) := by
  have hJA : J < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjAll : d.ctorsAll[J]? = some cA := by rw [S.ctorsAll_eq]; exact hj
  have hC := S.hctors J cA hj
  have hD := hC.2.2
  have hks : (d.ksR J).length = cA.2 := by rw [(S.hview J).1]; exact hD.ksLen
  have hiota := d.choice_fold_iota mp S.hR (d.invBodyAV head useIh) S.hps S.hk S.hpps S.hipsLen hb
    (by rw [rebit_map_dom]; exact S.hparams)
    (fun t ht => d.invTg_fact ψ S.hpsWD (S.hTg t ht)) S.hmin hjAll hJA hC hks
    (S.hpins (d.mems J)) hfitC
  rw [hiota]
  -- the body at the leaf frame
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨prior, hprior⟩ : ∃ prior, prior = d.minChoiceAVs ψ ps Ms (d.invBodyAV head useIh) J :=
    ⟨_, rfl⟩
  obtain ⟨ihs, hihs⟩ : ∃ ihs : List V, ihs = (ConLeche.recIdxOf (d.ksR J)).map fun i =>
      lamTower (d.bb ψ)
        (consList ((fs.map (interp V ρ)).take i) (consList (ps.map (interp V ρ)) ρ))
        ((d.tssR J ψ).getD i []) fun σ' =>
          (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            (d.minChoiceAVs ψ ps Ms (d.invBodyAV head useIh) d.nAll).map (interp V ρ) ++
            ((d.eissR J ψ).getD i []).map (interp V σ') ++
            [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ').foldl
              SetTheory.app ((fs.map (interp V ρ)).getD i pt)]).foldl
            SetTheory.app (interp V ρ (mp.base2.acval (d.recNames (d.tgtsR J i)) ψ)) := ⟨_, rfl⟩
  rw [← hMs, ← hprior, ← hihs]
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hpriorLen : prior.length = J := by rw [hprior]; exact d.minChoiceAVs_length _ _ _ _ _
  have hihsLen : ihs.length = (ConLeche.recIdxOf (d.ksR J)).length := by
    rw [hihs, List.length_map]
  have hfsLen : (fs.map (interp V ρ)).length = cA.2 := by
    have := hfitC.length_eq
    rw [List.length_map, List.length_append, List.length_map, hD.len ψ, S.hps] at this
    rw [List.length_map]; omega
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [S.hps]
  have hnFget : (d.ctorsAll.getD J default).2 = cA.2 := by
    rw [List.getD_eq_getElem?_getD, hjAll]; rfl
  have hσb : consList (fs.map (interp V ρ) ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ)
      = consList (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs.map (interp V ρ) ++ ihs)
          (consList (ps.map (interp V ρ)) ρ) := by
    simp only [List.map_append, consList_append]
  have hshiftB : shiftE (d.k + J + cA.2 + (ConLeche.recIdxOf (d.ksR J)).length) 0
      (consList (fs.map (interp V ρ) ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
      = consList (ps.map (interp V ρ)) ρ := by
    rw [hσb, show d.k + J + cA.2 + (ConLeche.recIdxOf (d.ksR J)).length
        = (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs.map (interp V ρ) ++ ihs).length from by
          have hfsLen' : fs.length = cA.2 := by rw [List.length_map] at hfsLen; exact hfsLen
          simp only [List.length_append, List.length_map, hMsLen, hpriorLen, hihsLen, hfsLen']]
    exact shiftE_consList _ _
  unfold IndRepData.invBodyAV
  rw [hnFget, interp_mkAppN_map, ← hfsLen,
    interp_mixedVarsAV (S.huse J) hihsLen, hfsLen, interp_liftN, hshiftB]

end InvSetup

end IndRepData

end ConLeche.Model
