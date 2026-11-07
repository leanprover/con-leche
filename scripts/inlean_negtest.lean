/- Task #451: InLean against the official kernel on declarations (mostly inductive) the official kernel
   rejects (and two it accepts).  `lake build InLean && lake env lean --run scripts/inlean_negtest.lean`;
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
  -- a safe check does not see an unsafe constant (`FEnv.sees`); a name is
  -- fresh in the environment itself
  ("safe definition using an unsafe one", .defnDecl
    { name := `useUnsafe, levelParams := [], type := .const `Bool [], hints := .abbrev, safety := .safe,
      all := [`useUnsafe],
      value := mkApp3 (.const `ptrEq [0]) nat (.lit (.natVal 0)) (.lit (.natVal 0)) }),
  ("inductive at an unsafe constant's name", mkInd `ptrEq ty0 [])
]

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
  return if bad == 0 then 0 else 1
