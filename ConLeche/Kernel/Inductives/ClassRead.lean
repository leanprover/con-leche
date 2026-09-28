module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The class checker's PRE-PASS (UNVERIFIED — soundness never depends on it)

The class checker (`ConLeche/Kernel/Inductives/ClassCheck.lean`) needs
three pieces of data the stream's recursor family carries and the
declaration does not spell out:

* the CLASSES — the majors of the recursor family, one per MOTIVE of the
  shared rule prefix (a motive `∀ ı⃗ (t : I.{us} D⃗ ı⃗), Sort ℓ` names the
  class `I.{us} D⃗`);
* the LAYOUT of the prefix — which binder after the parameters is which
  motive, which is the minor premise of which constructor of which class;
* per minor premise, which fields have an inductive hypothesis and at
  which class (`∀ a⃗, motive_t e⃗ (f_i a⃗)`), and per recursor the class its
  conclusion eliminates.

This file READS that data off the recursor types, syntactically, and
checks nothing.  Everything it returns is re-established by the checker:
the classes are checked (check 1), the constructors' fields are walked
and compared with the inductive hypotheses read here (check 3), and every
recursor type and rule is GENERATED from the classes and the walk and
compared by `isDefEq` with the stream's (check 6).  A wrong reading can
only make the generated recursor differ from the stream's, i.e. reject.
-/

namespace ConLeche

/-- A class: an inductive `ind` at the levels `lvls` and the parameters
`ds` (over the block's parameter variables `fvar 0 … fvar (nP-1)`). -/
structure ClassKey where
  ind : Name
  lvls : List Level
  ds : List Expr
  deriving Inhabited

/-- One binder of the recursors' shared prefix after the parameters. -/
inductive ClassSlot where
  /-- a motive; its class -/
  | motive (key : ClassKey)
  /-- a minor premise: the class (motive ordinal) it concludes at, the
  constructor it builds, and its inductive hypotheses `(field, class)` in
  binder order -/
  | minor (cls : Nat) (ctor : Name) (ihs : List (Nat × Nat))
  deriving Inhabited

/-- What the pre-pass read. -/
structure ClassRead where
  /-- the prefix after the parameters, in the stream's order -/
  slots : List ClassSlot
  /-- per recursor (the block's order), the class its conclusion eliminates -/
  recCls : List Nat
  deriving Inhabited

namespace ClassRead

/-- The classes (the motives' keys), in prefix order. -/
def classes (r : ClassRead) : List ClassKey :=
  r.slots.filterMap fun | .motive k => some k | _ => none

/-- The prefix position (after the parameters) of class `c`'s motive. -/
def motiveSlot (r : ClassRead) (c : Nat) : Option Nat :=
  let ms := (List.range r.slots.length).filter fun s =>
    match r.slots[s]? with | some (.motive _) => true | _ => false
  ms[c]?

end ClassRead

/-- The motive ordinal of the prefix variable `fvar p` (`nP ≤ p`), when
that binder is a motive. -/
def classOfMotiveVar (nP : Nat) (motPos : List Nat) (p : Nat) : Option Nat :=
  if nP ≤ p then motPos.findIdx? (· == p - nP) else none

/-- Read one minor premise's type `dom`, opened at depth `d`. -/
def classReadMinor (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    Option ClassSlot := do
  let n := dom.piBinders.1.length
  let (fvs, concl) ← openPisAtFvars n dom d
  let .fvar p _ := concl.getAppFn | none
  let c ← classOfMotiveVar nP motPos p
  let .const C _ := (← concl.getAppArgs.getLast?).getAppFn | none
  -- every binder whose own conclusion is a motive is an ih; the others
  -- are the fields, before them
  let ihs := (List.range fvs.length).filterMap fun q =>
    match (fvs.getD q default).fvarTypeD.piResult.getAppFn with
    | .fvar p' _ =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match (fvs.getD q default).fvarTypeD.piResult.getAppArgs.getLast? with
        | some a =>
          match a.getAppFn with
          | .fvar f _ => if d ≤ f then some (f - d, t) else none
          | _ => none
        | none => none
      | none => none
    | _ => none
  pure (.minor c C ihs)

/-- Read the prefix binders `nP … rP-1` of a recursor type opened at the
parameters (`body`, depth `d`), classifying each as a motive (its
telescope ends in a sort) or a minor premise. -/
def classReadSlots (nPc : Name → Nat) (np : Nat) :
    Nat → List Nat → Nat → Expr → Option (List ClassSlot)
  | 0, _, _, _ => some []
  | n + 1, motPos, d, .forallE dom body _ => do
    let slot ← match dom.piResult with
      | .sort _ => do
        let (bs, _) := dom.piBinders
        let (mdom, _) ← bs.getLast?
        let .const I us := mdom.getAppFn | none
        pure (ClassSlot.motive ⟨I, us, mdom.getAppArgs.take (nPc I)⟩)
      | _ => classReadMinor np motPos d dom
    let motPos' := match slot with | .motive _ => motPos ++ [d - np] | _ => motPos
    let rest ← classReadSlots nPc np n motPos' (d + 1) (body.instantiate1 (.fvar d dom))
    pure (slot :: rest)
  | _ + 1, _, _, _ => none

/-- **The pre-pass**: the prefix layout off the FIRST recursor's type
(`nPc I` is an inductive's parameter count), and every recursor's class
off its conclusion `motive_c ı⃗ t`.  `none` when the family is not of the
generated shape — the checker then rejects. -/
def classRead (nP : Nat) (nPc : Name → Nat) (recs : List RecShape) : Option ClassRead := do
  let rc0 ← recs.head?
  let (_, body) ← openPisAtFvars nP rc0.cvR.type 0
  let slots ← classReadSlots nPc nP (rc0.rP - nP) [] nP body
  let motPos := (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false
  let recCls ← recs.mapM fun rc => do
    let (_, concl) ← openPisAtFvars (rc.mI + 1) rc.cvR.type 0
    let .fvar p _ := concl.getAppFn | none
    classOfMotiveVar nP motPos p
  pure ⟨slots, recCls⟩

end ConLeche
