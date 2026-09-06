import Lech.Kernel.Basis.Names

/-!
# A tiny builder for the hand-written raw pins

The pinned basis blocks, the standard-axiom prerequisite families and
the compiler-trust pins are all *raw* `ConstantInfo`s: exactly what the
lean-inductive-models preprocessor emits for them, which is exactly the
toolchain's own `Init.Prelude` declaration with every binder annotation
reset to the parser's default `⟨.default, .never⟩` (or `.implicit`
where the signature says so) and every install-computed recursor-rule
field at its parse placeholder (`ctorParams := 0`, `fire := .inert`).

Written out with `Lech.Expr`'s constructors and `Name.str` chains,
one such declaration is a single unreadable line.  The helpers below —
`pi`/`piI`/`piA`, `lm`/`lmI`, `bv`, `cnst`, `srt`, `ap2`…`ap4` — are a
one-to-one, non-abbreviating renaming of those constructors at the
*raw* binder annotations, so a reader can line the pin up against
`Init.Prelude` binder by binder and index by index.  They introduce no
new notion: every one of them is a `def` whose body is a single `Expr`
constructor application.

The annotated forms are NOT written here: they are computed from these
raw pins by the checker's own annotation pass at elaboration time
(`#annotate_basis`, `Lech/Kernel/BasisGen.lean`).
-/

namespace Lech

/-! The raw-pin builder: `Expr` constructors under the raw binder
annotations.  Opened by the pin modules (`Lech/Kernel/Basis/*`,
`Lech/Kernel/StdAxioms.lean`, `Lech/Kernel/TrustAxioms.lean`). -/

namespace BasisDSL

/-- A top-level (single-component) name: `bn "Eq"` is `Eq`. -/
def bn (s : String) : Name := .str .anonymous s

/-- The universe parameter `u` — every basis block's first one. -/
def uN : Name := bn "u"

/-- The universe parameter `u`, as a level. -/
def u : Level := .param uN

/-- The universe parameter `v` (`Quot.lift`'s target sort). -/
def vN : Name := bn "v"

/-- The universe parameter `v`, as a level. -/
def v : Level := .param vN

/-- The universe parameter `u_1` — the motive sort the exporter names
for a recursor whose type former already spends `u`. -/
def u1N : Name := bn "u_1"

/-- The universe parameter `u_1`, as a level. -/
def u1 : Level := .param u1N

/-- A bound variable, by de Bruijn index. -/
def bv (i : Nat) : Expr := .bvar i

/-- `Sort u`. -/
def srt (u : Level) : Expr := .sort u

/-- `Prop` = `Sort 0`. -/
def prop : Expr := .sort .zero

/-- `Type` = `Sort 1`. -/
def type1 : Expr := .sort (.succ .zero)

/-- A constant, at the given universe arguments. -/
def cnst (n : Name) (us : List Level := []) : Expr := .const n us

/-- `∀ (x : ty), body` — an explicit binder at the raw annotation. -/
def pi (x : String) (ty body : Expr) : Expr :=
  .forallE (bn x) ty body ⟨.default, .never⟩

/-- `∀ {x : ty}, body` — an implicit binder at the raw annotation. -/
def piI (x : String) (ty body : Expr) : Expr :=
  .forallE (bn x) ty body ⟨.implicit, .never⟩

/-- `∀ (_ : ty), body` — an anonymous explicit binder (`ty → body`). -/
def piA (ty body : Expr) : Expr :=
  .forallE .anonymous ty body ⟨.default, .never⟩

/-- `fun (x : ty) => body` — an explicit binder at the raw annotation. -/
def lm (x : String) (ty body : Expr) : Expr :=
  .lam (bn x) ty body ⟨.default, .never⟩

/-- `fun {x : ty} => body` — an implicit binder at the raw annotation. -/
def lmI (x : String) (ty body : Expr) : Expr :=
  .lam (bn x) ty body ⟨.implicit, .never⟩

/-- Binary application. -/
def ap2 (f a b : Expr) : Expr := .app (.app f a) b

/-- Ternary application. -/
def ap3 (f a b c : Expr) : Expr := .app (.app (.app f a) b) c

/-- Quaternary application. -/
def ap4 (f a b c d : Expr) : Expr := .app (.app (.app (.app f a) b) c) d

/-- A raw iota rule: the install-computed fields (`ctorParams`,
`fire`) at their parse placeholders, which is what the exporter emits
and what `#annotate_basis` recomputes. -/
def rule (ctor : Name) (nfields : Nat) (rhs : Expr) : RecRule :=
  ⟨ctor, nfields, 0, .inert, rhs⟩

end BasisDSL

end Lech
