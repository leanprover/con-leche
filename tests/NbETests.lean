import Setlec.NbE.Check

/-!
NbE pilot (task #159) micro-tests: `#guard`-based acceptance and
rejection cases for the environment-machine checker — identity
functions, β-chains, δ-unfolding equalities through the glued spine, a
universe-polymorphic declaration, level normalization at sorts, and
rejections.
-/

namespace NbETests

open Setlec Setlec.NbE

private def nm (s : String) : Name := .str .anonymous s

private def uP : Level := .param (nm "u")
private def l0 : Level := .zero
private def l1 : Level := .succ .zero
private def l2 : Level := .succ (.succ .zero)

/-- `id.{u} : ∀ (A : Sort u), A → A := fun A a => a` -/
private def idCi : ConstInfo :=
  { name := nm "id", lvlParams := [nm "u"]
    type := .pi (.sort uP) (.pi (.bvar 0) (.bvar 1))
    value := .lam (.sort uP) (.lam (.bvar 0) (.bvar 0)) }

/-- `id2.{u} : ∀ (A : Sort u), A → A := fun A a => id.{u} A a` —
universe-polymorphic, δ-uses `id`. -/
private def id2Ci : ConstInfo :=
  { name := nm "id2", lvlParams := [nm "u"]
    type := .pi (.sort uP) (.pi (.bvar 0) (.bvar 1))
    value := .lam (.sort uP) (.lam (.bvar 0)
      (.app (.app (.const (nm "id") [uP]) (.bvar 1)) (.bvar 0))) }

/-- `Arr : Sort 2 := Sort 1 → Sort 1` — the declared sort `2` meets the
inferred `imax 2 2`, exercising level normalization. -/
private def arrCi : ConstInfo :=
  { name := nm "Arr", lvlParams := []
    type := .sort l2
    value := .pi (.sort l1) (.sort l1) }

/-- `f : Arr := fun (A : Sort 1) => A` — the declared type is a glued
constant that must δ-unfold to a Π during conversion. -/
private def fCi : ConstInfo :=
  { name := nm "f", lvlParams := []
    type := .const (nm "Arr") []
    value := .lam (.sort l1) (.bvar 0) }

/-- `g : Sort 1 → Sort 1 := id.{2} (Sort 1)` — β through an applied
polymorphic constant; the inferred type comes out of a closure. -/
private def gCi : ConstInfo :=
  { name := nm "g", lvlParams := []
    type := .pi (.sort l1) (.sort l1)
    value := .app (.const (nm "id") [l2]) (.sort l1) }

/-- The whole stream checks and installs. -/
private def envAll : Option Env :=
  checkDecls defaultFuel ⟨[]⟩ [idCi, id2Ci, arrCi, fCi, gCi]

#guard envAll.isSome

private def E : Env := ⟨[gCi, fCi, arrCi, id2Ci, idCi]⟩

/-! ### Evaluation and conversion probes (values, untyped) -/

/- `id2.{2} (Sort 1) (Sort 0) ≡ Sort 0`: a δ(id2)–β–δ(id)–β chain,
glued neutral against a rigid sort. -/
#guard
  (match eval E defaultFuel [] (.app (.app (.const (nm "id2") [l2]) (.sort l1)) (.sort l0)),
         eval E defaultFuel [] (.sort l0) with
   | some v, some w => conv E defaultFuel 0 v w == some true
   | _, _ => false)

/- Spine-equality shortcut: same glued head under semantically equal
but syntactically different levels (`max 2 2` vs `2`), equal spines. -/
#guard
  (match eval E defaultFuel [] (.app (.const (nm "id2") [.max l2 l2]) (.sort l1)),
         eval E defaultFuel [] (.app (.const (nm "id2") [l2]) (.sort l1)) with
   | some v, some w => conv E defaultFuel 0 v w == some true
   | _, _ => false)

/- Under-binder conversion: `fun (A : Sort 1) => id.{2} (Sort 1) A` vs
`fun (A : Sort 1) => A` — closures applied to a shared fresh variable,
δ + β below the binder. -/
#guard
  (match eval E defaultFuel []
           (.lam (.sort l1) (.app (.app (.const (nm "id") [l2]) (.sort l1)) (.bvar 0))),
         eval E defaultFuel [] (.lam (.sort l1) (.bvar 0)) with
   | some v, some w => conv E defaultFuel 0 v w == some true
   | _, _ => false)

/- Readback: quoting the value of `id.{2} (Sort 1)` keeps the glued
spine (no δ-unfold in readback). -/
#guard
  (match eval E defaultFuel [] (.app (.const (nm "id") [l2]) (.sort l1)) with
   | some v => quote E defaultFuel 0 v
       == some (.app (.const (nm "id") [l2]) (.sort l1))
   | none => false)

/-! ### Rejections -/

/- `Sort 0 ≠ Sort 1`. -/
#guard
  (conv E defaultFuel 0 (.sort l0) (.sort l1) == some false)

/- `bad : Sort 0 := Sort 0` — a sort is not a member of itself. -/
#guard
  (checkDecl E { name := nm "bad", lvlParams := []
                 type := .sort l0, value := .sort l0 } == false)

/- `bad2 : ∀ (A : Sort 1), A := fun (A : Sort 1) => A` — the codomain
is a fresh variable, the body's type a sort. -/
#guard
  (checkDecl E { name := nm "bad2", lvlParams := []
                 type := .pi (.sort l1) (.bvar 0)
                 value := .lam (.sort l1) (.bvar 0) } == false)

/- Duplicate installation is refused. -/
#guard (checkDecl E idCi == false)

/- Undeclared level parameter is refused at the front door. -/
#guard
  (checkDecl E { name := nm "bad3", lvlParams := []
                 type := .sort (.succ uP), value := .sort uP } == false)

/- The installed environment is the pushed stream (sanity: `checkDecls`
really installed in order). -/
#guard envAll == some E

end NbETests
