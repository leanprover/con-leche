/- Task #451: InLean against the official kernel on declarations (mostly inductive) the official kernel
   rejects (and two it accepts); and, at con-leche's axiom policy, cases where InLean must decline
   what the official kernel accepts (`policyCases`, on a prelude environment built here).  `lake build InLean && lake env lean --run scripts/inlean_negtest.lean`;
   exit 0 when every verdict agrees. -/
import InLean
open Lean

def nat : Expr := .const `Nat []
def ty0 : Expr := .sort 1

def mkInd (n : Name) (ty : Expr) (ctors : List (Name × Expr)) (lps : List Name := []) (np := 0) :
    Declaration :=
  .inductDecl lps np [{ name := n, type := ty, ctors := ctors.map fun (c, t) => { name := c, type := t } }] false

def cases : List (String × Declaration) := [
  ("non-positive", mkInd `Bad ty0 [(`Bad.mk, .forallE `f (.forallE `x (.const `Bad []) nat .default) (.const `Bad []) .default)]),
  ("universe too big", mkInd `Big ty0 [(`Big.mk, .forallE `t ty0 (.const `Big []) .default)]),
  ("wrong return type", mkInd `Wr ty0 [(`Wr.mk, nat)]),
  ("nested non-positive", mkInd `Bad2 ty0 [(`Bad2.mk,
      .forallE `l (.app (.const `List [0]) (.forallE `x (.const `Bad2 []) nat .default)) (.const `Bad2 []) .default)]),
  ("good nested", mkInd `Tree ty0 [(`Tree.node, .forallE `l (.app (.const `List [0]) (.const `Tree [])) (.const `Tree []) .default)]),
  ("good prop small elim", mkInd `Ex (.sort 0) [(`Ex.intro, .forallE `n nat (.const `Ex []) .default)]),
  ("non-uniform param", mkInd `NU (.forallE `n nat ty0 .default)
      [(`NU.mk, .forallE `n nat (.forallE `x (.app (.const `NU []) (.app (.const `Nat.succ []) (.bvar 0))) (.app (.const `NU []) (.bvar 1)) .default) .default)] [] 1),
  ("duplicate name", mkInd `Nat ty0 []),
  -- the generated constants' names are distinct
  ("duplicate constructor", mkInd `Dup ty0 [(`Dup.a, .const `Dup []), (`Dup.a, .const `Dup [])]),
  ("constructor at the recursor's name", mkInd `DR ty0 [(`DR.rec, .const `DR [])]),
  -- a safe check does not see an unsafe constant (`FEnv.sees`); a name is
  -- fresh in the environment itself
  ("safe definition using an unsafe one", .defnDecl
    { name := `useUnsafe, levelParams := [], type := .const `Bool [], hints := .abbrev, safety := .safe,
      all := [`useUnsafe],
      value := mkApp3 (.const `ptrEq [0]) nat (.lit (.natVal 0)) (.lit (.natVal 0)) }),
  ("inductive at an unsafe constant's name", mkInd `ptrEq ty0 [])
]

def prop : Expr := .sort 0
def lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
def pi (n : Name) (t b : Expr) : Expr := .forallE n t b .default
def defn (n : Name) (lps : List Name) (ty v : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := lps, type := ty, value := v, hints := .abbrev, safety := .safe, all := [n] }

/-- `Iff` as definitions at the pinned types (a Church encoding, no inductive):
master's `stdAxiomOk` reads `Iff` an inductive, `Iff.intro` a constructor with
two parameters and two fields, `Iff.rec` a recursor (task #451, lane O6). -/
def iffDefs : List Declaration :=
  -- `Iff a b := ∀ p, ((a → b) → (b → a) → p) → p`
  let kT (a b p : Nat) : Expr :=   -- `(a → b) → (b → a) → p` at the given indices
    pi `mp (pi `x (.bvar a) (.bvar (b + 1))) (pi `mpr (pi `y (.bvar (b + 1)) (.bvar (a + 2))) (.bvar (p + 2)))
  let iffV := lam `a prop (lam `b prop (pi `p prop (pi `k (kT 2 1 0) (.bvar 1))))
  -- `Iff.intro a b mp mpr := fun p k => k mp mpr`
  let introV := lam `a prop (lam `b prop (lam `mp (pi `x (.bvar 1) (.bvar 1))
    (lam `mpr (pi `y (.bvar 1) (.bvar 3)) (lam `p prop (lam `k (kT 4 3 0)
      (mkApp2 (.bvar 0) (.bvar 3) (.bvar 2)))))))
  -- `Iff.rec a b motive intro t := intro (t (a → b) fun mp _ => mp) (t (b → a) fun _ mpr => mpr)`,
  -- typed by proof irrelevance
  let recTy := InLean.iffRecPin.type
  let k (body : Expr) : Expr :=
    lam `mp (pi `x (.bvar 4) (.bvar 4)) (lam `mpr (pi `y (.bvar 4) (.bvar 6)) body)
  let recV : Expr := match recTy with
    | .forallE _ ta (.forallE _ tb (.forallE _ tm (.forallE _ ti (.forallE _ tt _ _) _) _) _) _ =>
      lam `a ta (lam `b tb (lam `motive tm (lam `intro ti (lam `t tt
        (mkApp2 (.bvar 1)
          (mkApp2 (.bvar 0) (pi `x (.bvar 4) (.bvar 4)) (k (.bvar 1)))
          (mkApp2 (.bvar 0) (pi `y (.bvar 3) (.bvar 5)) (k (.bvar 0))))))))
    | _ => .sort 0
  [defn InLean.iffName [] InLean.iffPin.type iffV,
   defn InLean.iffIntroName [] InLean.iffIntroPin.type introV,
   defn InLean.iffRecName InLean.iffRecPin.lps recTy recV]

/-- At con-leche's axiom policy InLean must decline these (the official kernel
accepts any axiom): each case is a prelude, added through InLean and required
to be accepted, then the declaration InLean must not accept. -/
def policyCases (init : Kernel.Environment) : List (String × List Declaration × Declaration) :=
  let eqDecl : List Declaration := match init.find? ``Eq, init.find? ``Eq.refl with
    | some (.inductInfo v), some (.ctorInfo c) =>
      [.inductDecl v.levelParams v.numParams
        [{ name := v.name, type := v.type, ctors := [{ name := c.name, type := c.type }] }] false]
    | _, _ => []
  let nonemptyDecl : List Declaration := match init.find? ``Nonempty, init.find? ``Nonempty.intro with
    | some (.inductInfo v), some (.ctorInfo c) =>
      [.inductDecl v.levelParams v.numParams
        [{ name := v.name, type := v.type, ctors := [{ name := c.name, type := c.type }] }] false]
    | _, _ => []
  -- master's `matchesPin` reads the level parameters as named
  let choiceV := InLean.choicePin.type.instantiateLevelParams InLean.choicePin.lps [.param `v]
  [("Classical.choice at another level name", nonemptyDecl,
    .axiomDecl { name := InLean.choiceName, levelParams := [`v], type := choiceV, isUnsafe := false }),
   ("propext over an Iff of definitions", eqDecl ++ iffDefs,
    .axiomDecl { name := InLean.propextName, levelParams := [], type := InLean.propextPin.type, isUnsafe := false })]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env := (← importModules #[{module := `Init}] {} (loadExts := false) (level := .private)).toKernelEnv
  let mut bad := 0
  -- `Quot.sound` again, at its own type: the pin matches, the name is taken
  let dupSound := (env.find? ``Quot.sound).map fun ci =>
    ("duplicate Quot.sound", Declaration.axiomDecl
      { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false })
  for (label, d) in cases ++ dupSound.toList do
    let off := (env.addDeclCore 0 0 d none).isOk
    let mine ← match InLean.addDecl env d with
      | .ok _ => pure "accept"
      | .error (.other m) => pure s!"reject: {m}"
      | .error _ => pure "reject"
    let agree := off == (mine == "accept")
    if !agree then bad := bad + 1
    IO.println s!"{if agree then "ok  " else "DIFF"} {label}: official {if off then "accept" else "reject"}, InLean {mine}"
  let empty := (← importModules #[] {} (loadExts := false)).toKernelEnv
  for (label, pre, d) in policyCases env do
    let mut e := empty
    let mut setupOk := true
    for p in pre do
      match InLean.addDecl e p with
      | .ok e' => e := e'
      | .error (.other m) => setupOk := false; IO.println s!"DIFF {label}: prelude rejected: {m}"
      | .error _ => setupOk := false; IO.println s!"DIFF {label}: prelude rejected"
    let off := (e.addDeclCore 0 0 d none).isOk
    let mine ← match InLean.addDecl e d with
      | .ok _ => pure "accept"
      | .error (.other m) => pure s!"reject: {m}"
      | .error _ => pure "reject"
    let agree := setupOk && mine != "accept"
    if !agree then bad := bad + 1
    IO.println s!"{if agree then "ok  " else "DIFF"} {label}: official {if off then "accept" else "reject"}, InLean {mine} (con-leche's policy: not accept)"
  return if bad == 0 then 0 else 1
