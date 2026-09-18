module

public import ConLeche.Model.Inductives.NestedFit

public section

/-!
# The entry identity at a PARAMETER-HEADED container field domain (task #315 L-B)

**What this module is about, named because two obligations on this
route share a proof and a summary true of one was once stated of both:
the subject here is THE CONTAINER'S FIELD DOMAIN, read at a frame.**
It is not about a target's reading — that is `auxTarget_reads`
(`NestedPinLeafAll.lean`), a different object with a different theorem,
and the two must not be summarised together.

`EntryReadF` (`NestedFit.lean`) is the reading law with the target's
frame, the target's reading VALUE and THIS COPY's own frame `frSelf`
supplied.  Of its three moving parameters only `frSelf` carries the
obligation: `cAs` occurs solely in the hypothesis's spine fit, while the
container's field domain is read at `frSelf` inside `CopyEntryAtF`.  So
`EntryReadF` is a statement about what that domain evaluates to at a
given frame, and its arms split by WHAT THE DOMAIN IS — read off the
domain's recorded shape, never off a target's head.

**THE RESTRICTION, and it is the whole point of this module.**  Three
arms, and only the second is here:

* a MEMBER target is not an edge at all; the block's own carrier
  segment is handled by Bekić (`ofNested_lfp`);
* a **PARAMETER-HEADED** domain at a pin target — the domain IS a
  reference to one of the container's parameters, applied to index
  arguments — needs NO conclusion at another pin.  Its value at a frame
  is that frame's value at the parameter position, so the entry identity
  is the frame's own property plus the slot's algebra.  **That arm is
  this module.**
* a **CONSTANT-HEADED** domain at a pin target — `List α` with `α` the
  candidate component, say — evaluates to the CONTAINER's LEAST TUPLE at
  that argument (the inner pin's `pinLfpAt`), not to the inner pin's
  carrier.  Closing that gap IS the conclusion at the inner pin.  **The
  candidate frame does not remove it, K.57's consumer survives there,
  and nothing in this module touches it.**

**WHAT IS STILL OWED, and by whom.**  This arm is stated at an arbitrary
`frSelf` constrained only at the field's own parameter position
(`hfr`), which is as unconditional as the arm gets: it assumes nothing
about a candidate family, and any such family will satisfy `hfr` by
construction at a pin-valued component.  What it does NOT do is produce
that family — no construction of one is in the tree
(`CandParamFit`/`CandIdxAgree` are side conditions ON a family), and
this lane does not carry one abstractly.  So this module is a reduction,
not a close.
-/

namespace ConLeche.Model

open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-- **THE ENTRY IDENTITY AT A PARAMETER-HEADED CONTAINER FIELD DOMAIN**
(task #315 L-B): when the CONTAINER's `l`-th field domain is a
reference to the parameter at position `v` applied to a spine `args`,
the reading law holds at any frame whose value at `v` is the target's
reading.

The four hypotheses are each about a named object and none is at
another pin:

* `hdom` — the DOMAIN's recorded shape (a parameter reference applied);
* `hfr` — the FRAME's value at that parameter position: it is the
  target's reading.  This is the candidate frame's defining property at
  a pin-valued component, and the only thing about the frame this arm
  uses;
* `htls` — the COPY's telescope at this field is empty (a finitary
  field, `BlockCtorData.tssNone`), so the slot is one application;
* `hargs` — the domain's arguments and the copy's recorded index
  expressions have the same values, each read on its own side;
* `hidx` — those values fit the TARGET's index telescope, which is what
  lets the reading law be applied.

**Not covered**: a constant-headed domain, where the value is the
container's least tuple at the argument rather than the frame's entry.
See this module's header. -/
theorem entryReadF_of_paramHeadDom
    {TV : TargetView V} {dJ : BlockModel V} {ψJ : Name → Nat}
    {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} {ρp : Nat → V} {i j l : Nat}
    {cAs : Nat → List V} {EAv : Nat → V} {frSelf : Nat → V}
    {v : Nat} {args : List AnnotTerm}
    (hdom : ((dJ.Fss i ψJ).getD j []).getD l default
      = AnnotTerm.mkAppN (.bvar (v + l)) args)
    (hfr : frSelf v = EAv (tg l))
    (htls : tls.getD l [] = [])
    (hargs : ∀ fs₁ : List V, fs₁.length = l →
      SpineFit frSelf (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      args.map (interp V (consList fs₁ frSelf))
        = (Eis.getD l []).map (interp V (consList fs₁ ρp)))
    (hidx : ∀ fs₁ : List V, fs₁.length = l →
      SpineFit frSelf (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      SpineFit (TV.frameAt cAs ρp (tg l)) (TV.Ids (tg l))
        ((Eis.getD l []).map (interp V (consList fs₁ ρp)))) :
    EntryReadF TV dJ ψJ tg tls Eis ρp i j cAs EAv frSelf l := by
  intro Z hZ fs₁ hfs hsp
  rw [hdom, interp_mkAppN_foldl, htls, slotSet_nil, hZ _ (hidx fs₁ hfs hsp),
    hargs fs₁ hfs hsp]
  have hhead : interp V (consList fs₁ frSelf) (AnnotTerm.bvar (v + l)) = EAv (tg l) := by
    have hlen : v + l = v + fs₁.length := by rw [hfs]
    show consList fs₁ frSelf (v + l) = EAv (tg l)
    rw [hlen, consList_apply_add, hfr]
  rw [hhead]

end ConLeche.Model
