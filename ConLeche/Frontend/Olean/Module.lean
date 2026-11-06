module

public import ConLeche.Frontend.Olean.Lazy
public import Std.Data.HashMap.Basic

@[expose] public section

/-!
# Reading `.olean` files: a module's views against each other

`checkViews`: what a module's home checks of its three parts, over the load of its
private view (`loadAt`, its theorems' values left in the file).  A mismatch is a
malformed file at its home (`.invalid`, exit 1):

* the server and private parts are of a module of the module system, and the server
  part's imports are those at the start of `M.olean` (the private view's are, or it
  would not load);
* the exported and server parts' name tables list their constants (`constNamesOk`),
  as the keys Lean's import stores them under;
* every constant of the exported part, and of the server part, is the private
  view's constant of its name or that constant with its value hidden
  (`expoOfParts`).  The same object is decided by position; a hidden value by the
  statement; only where neither holds is the exported constant decoded, and then the
  private one too if its value was left in the file.

A reader of one view (`parseView`) does not need any of this: Lean's own import
at that level does not compare the files either.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The levels of a module's constants -/

/-- **A private constant at the exported level.** -/
inductive Expo where
  /-- the exported part stores the same constant -/
  | same
  /-- the exported part stores it as an axiom of the same name, level
  parameters and type: its value is hidden -/
  | hidden
  /-- the exported part does not store it -/
  | absent
  deriving Inhabited, DecidableEq, Repr

def hintsEq : HintsRec → HintsRec → Bool
  | .abbrev, .abbrev | .opaque, .opaque => true
  | .regular a, .regular b => a == b
  | _, _ => false

def rulesEq : List (Name × Nat × Expr) → List (Name × Nat × Expr) → Bool
  | [], [] => true
  | (a, b, c) :: xs, (a', b', c') :: ys => a == a' && b == b' && c == c' && rulesEq xs ys
  | _, _ => false

/-- Structural equality of two stored constants (expressions by the
checker's equality, pointer-equal first). -/
def entrySame (a b : CEntryF Name Expr) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a.kind, b.kind with
  | .ax u, .ax u' => u == u'
  | .defn v h s, .defn v' h' s' => v == v' && hintsEq h h' && s == s'
  | .thm v al, .thm v' al' => v == v' && al == al'
  | .opaq v u, .opaq v' u' => v == v' && u == u'
  | .quot k, .quot k' => k == k'
  | .induct a b c d e f g h, .induct a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h'
  | .ctor a b c d e, .ctor a' b' c' d' e' =>
    a == a' && b == b' && c == c' && d == d' && e == e'
  | .recur a b c d e f g h, .recur a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && rulesEq f f' && g == g' && h == h'
  | _, _ => false

/-- A stored constant's kind, for messages. -/
def kindWord : CKind → String
  | .ax u => s!"axiom{if u then " (unsafe)" else ""}"
  | .defn _ _ s => s!"definition ({s})"
  | .thm .. => "theorem"
  | .opaq _ u => s!"opaque{if u then " (unsafe)" else ""}"
  | .quot _ => "quotient"
  | .induct .. => "inductive"
  | .ctor .. => "constructor"
  | .recur .. => "recursor"

/-- **The exported level of one private constant**, given the exported
part's constant of that name: the same constant, or the private one
with its value hidden; `none` is a constant the exported part does not
refine. -/
def expoOf (priv ex : CEntryF Name Expr) : Option Expo :=
  if entrySame priv ex then some .same
  else if priv.name == ex.name && priv.levelParams == ex.levelParams && priv.type == ex.type then
    -- the axiom Lean exports in its place (`addDeclCore`): unsafe exactly
    -- when the definition is not safe or the opaque constant is unsafe
    match priv.kind, ex.kind with
    | .defn _ _ s, .ax u => if u == (s != "safe") then some .hidden else none
    | .thm .., .ax u => if !u then some .hidden else none
    | .opaq _ u', .ax u => if u == u' then some .hidden else none
    | _, _ => none
  else none

/-- **The exported level of a module's private constants**: for each
exported constant, the private constant it stands for — the same object
(the private part points into the exported part), the same skeleton
(names and expressions as pointers), the same constant decoded, or an
axiom of the same name, level parameters and type (by pointer, else
decoded) where the private one is a definition, theorem or opaque
constant.  `none` with the reason: an exported view that is not a
refinement of the private one. -/
def expoOfParts (r : Region) (privAddr expAddr : UInt64) (cs : Array (CEntryF Name Expr)) :
    Except String (Array Expo) := do
  let some skP := moduleSkel r privAddr | throw "malformed private part"
  let some skE := moduleSkel r expAddr | throw "malformed exported part"
  let privLoc : Std.HashMap Nat Nat :=
    skP.consts.foldl (fun (m, i) c => (m.insert c i, i + 1)) ({}, 0) |>.1
  let privLocs := skP.consts.toArray
  let privIdx : Std.HashMap Name Nat :=
    cs.size.fold (init := {}) fun i _ acc => acc.insert cs[i].name i
  let mut expo : Array Expo := cs.map fun _ => .absent
  for c in skE.consts do
    if let some i := privLoc[c]? then
      expo := expo.set! i .same
    else
      let some se := constSkel r c | throw "malformed exported constant"
      let some en := nameP r se.name | throw "malformed exported constant"
      let some i := privIdx[en]? | throw s!"the exported constant {en} is not stored at the private level"
      let some sp := (privLocs[i]?).bind (constSkel r) | throw "malformed private constant"
      let samePtrs : Bool := se.type == sp.type && se.levelParams == sp.levelParams
      let hiddenKind : Bool := match se.kind, sp.kind with
        | .ax u, .defn _ _ s => u == (s != "safe")
        | .ax u, .thm .. => !u
        | .ax u, .opaq _ u' => u == u'
        | _, _ => false
      if hiddenKind && samePtrs then expo := expo.set! i .hidden
      else
        -- the fallback: decode the exported constant
        let some e := entryAt r c | throw "malformed exported constant"
        -- the private constant whole: a theorem's value is left out of the load
        let pc ← match cs[i]!.kind with
          | .thm .. => match (privLocs[i]?).bind (entryAt r) with
            | some pc => pure pc
            | none => throw "malformed private constant"
          | _ => pure cs[i]!
        match expoOf pc e with
        | some x => expo := expo.set! i x
        | none => throw s!"the exported view of {en} is not a refinement of its private \
            constant ({kindWord cs[i]!.kind} / {kindWord e.kind})"
  return expo

/-! ## The views against each other -/

/-- **The views of a module against each other**: for each private constant, its
exported level.  Every constant is `.same` in a classic module, whose views are
one. -/
def checkViews (m : Name) (f : ModFiles) (l : Loaded) : Except CheckError (Array Expo) := do
  let bad (what : String) : CheckError := .invalid s!"module {m}: {what}"
  let cs := l.constants.map (·.toCEntryF)
  match f.server, f.private with
  | some s, some p =>
    unless f.isModule do return cs.map fun _ => .same
    let r ← Region.ofParts #[f.exported, s, p]
    for (part, a) in [("server", s.moduleDataAddr), ("private", p.moduleDataAddr)] do
      unless (moduleSkel r a).any (·.isModule) do
        .error (bad s!"the {part} part is not of a module of the module system, the exported \
          part is")
    let simps := (moduleSkel r s.moduleDataAddr).bind fun sk =>
      (sk.imports.mapM (ImportF.mapM (nameP r))).map List.toArray
    unless importsPre f.exported.bytes == simps do
      .error (bad "the server part's imports are not those at the start of its .olean")
    let exp := f.exported.moduleDataAddr
    for (part, a) in [("exported", exp), ("server", s.moduleDataAddr)] do
      unless constNamesOk r a do
        .error (bad s!"the {part} part's name table (constNames) does not list its constants' \
          names, each once")
    match expoOfParts r p.moduleDataAddr exp cs,
        expoOfParts r p.moduleDataAddr s.moduleDataAddr cs with
    | .ok expo, .ok _ => pure expo
    | .error msg, _ => .error (bad s!"the exported part: {msg}")
    | _, .error msg => .error (bad s!"the server part: {msg}")
  | _, _ => pure (cs.map fun _ => .same)

end ConLeche.Frontend.Olean
