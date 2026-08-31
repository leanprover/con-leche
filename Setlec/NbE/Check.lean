import Setlec.NbE.Conv

/-!
# NbE pilot: the front-door checker

Declarations are typed **once, on entry** (infer-style; kernel terms
carry λ-domain annotations, so no bidirectional check-mode is needed in
this slice).  After the front door nothing carries types: `conv` runs
untyped on values, and the environment stores the declared (checked)
syntax only.

The one place the NbE regime forces readback into the checking path:
`infer` of a λ obtains the body's type as a *value* over a fresh
variable and must re-close it into a Π — `quote` turns it back into a
term, and `freshEnv` re-closes it over the ambient telescope.  The
readback uses the glued spine, so no definition unfolds for it.

Sort story (recorded for the pilot memo): fresh variables created here
and in `conv` carry **no sort and no type**.  The checker computes
sorts only at Π-formation (`imax`) and at the `sort`/`sort` leaf of
`conv` — always within a single run, from the syntax itself.  Nothing
in this slice compares sorts computed by two independent runs against
each other except through `Level.isEquiv` on carried syntax.
-/

namespace Setlec.NbE

/-- Force to a sort and return its level. -/
def toSort (E : Env) (fuel : Nat) (v : Value) : Option Level :=
  match forceV E fuel v with
  | some (.sort u) => some u
  | _ => none

/-- Force to a Π and return domain and codomain closure. -/
def toPi (E : Env) (fuel : Nat) (v : Value) : Option (Value × Closure) :=
  match forceV E fuel v with
  | some (.pi d cl) => some (d, cl)
  | _ => none

/-- Infer the type (as a value) of `t`.

`k` is the fresh-variable frontier; `Γ` (types) and `ρ` (values —
always fresh variables here) are parallel, innermost-first, with
`bvar i ↦ ρ[i] = freshV (k - 1 - i) : Γ[i]`. -/
def infer (E : Env) (fuel : Nat) : Nat → List Value → List Value → Term → Option Value
  | _, Γ, _, .bvar i => Γ[i]?
  | _, _, _, .sort u => some (.sort (.succ u))
  | _, _, _, .const n us =>
    match E.lookup n with
    | some ci =>
      if ci.lvlParams.length = us.length then
        eval E fuel [] (ci.type.instL ci.lvlParams us)
      else none
    | none => none
  | k, Γ, ρ, .app f a =>
    match infer E fuel k Γ ρ f with
    | some tf =>
      match toPi E fuel tf with
      | some (d, cl) =>
        match infer E fuel k Γ ρ a with
        | some ta =>
          match conv E fuel k ta d with
          | some true =>
            match eval E fuel ρ a with
            | some va => applyCl E fuel cl va
            | none => none
          | _ => none
        | none => none
      | none => none
    | none => none
  | k, Γ, ρ, .lam d b =>
    match infer E fuel k Γ ρ d with
    | some td =>
      match toSort E fuel td with
      | some _ =>
        match eval E fuel ρ d with
        | some vd =>
          match infer E fuel (k + 1) (vd :: Γ) (freshV k :: ρ) b with
          | some tb =>
            match quote E fuel (k + 1) tb with
            | some qtb => some (.pi vd (.mk (freshEnv k) qtb))
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | k, Γ, ρ, .pi d b =>
    match infer E fuel k Γ ρ d with
    | some td =>
      match toSort E fuel td with
      | some u1 =>
        match eval E fuel ρ d with
        | some vd =>
          match infer E fuel (k + 1) (vd :: Γ) (freshV k :: ρ) b with
          | some tb =>
            match toSort E fuel tb with
            | some u2 => some (.sort (.imax u1 u2))
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none

/-- Default fuel for the pilot's tests. -/
def defaultFuel : Nat := 1000

/-- Check one declaration against the environment-so-far. -/
def checkDecl (E : Env) (ci : ConstInfo) (fuel : Nat := defaultFuel) : Bool :=
  Name.nodup ci.lvlParams
    && ci.type.lvlDefined ci.lvlParams
    && ci.value.lvlDefined ci.lvlParams
    && (E.lookup ci.name).isNone
    && (match infer E fuel 0 [] [] ci.type with
        | some tT => (toSort E fuel tT).isSome
        | none => false)
    && (match infer E fuel 0 [] [] ci.value, eval E fuel [] ci.type with
        | some tv, some vT => conv E fuel 0 tv vT == some true
        | _, _ => false)

/-- Check a stream of declarations, building the environment. -/
def checkDecls (fuel : Nat := defaultFuel) : Env → List ConstInfo → Option Env
  | E, [] => some E
  | E, ci :: rest =>
    if checkDecl E ci fuel then checkDecls fuel (E.push ci) rest else none

end Setlec.NbE
