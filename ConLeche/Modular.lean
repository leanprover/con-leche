module

public import ConLeche.Cached.Installed

@[expose] public section

/-!
# Modular checking: modules, qualified names, the local checks

The statement half of the modular theorem (`ConLeche.modular_model_exists`,
`ConLeche/MainTheorem.lean`), in the style of `ConLeche/Denotes.lean`:
definitions only, importing the checker and nothing of the proof tiers,
so that the challenge (`ConLeche/Challenge.lean`) and the driver can
both read it.

* A **development** is a family of modules `dev : Nat → Module`, a
  module's imports earlier than it.  A module has its declarations
  (`decls`), its **context** (the environment its declarations are
  checked against), its **own environment** (`own`: the context with its
  declarations installed), for each context name the import it is read
  from (`src`), which of its own constants are proofs (`proofs`), and its
  **resolution** of names to qualified names (`res`).
* A **qualified name** (`Key`) is a module and a name for an ordinary
  constant, and a name, level parameters and statement for a proof:
  two proofs of one statement are one constant (the model gives every
  proof the point), whatever their bodies or homes.
* **The local checks** (`LocalOk`) read the module and its direct
  imports' own environments and resolutions, nothing else:
  1. the imports come earlier, every context name is read from one of
     them, the context stores each name once (`below`, `src_mem`,
     `nodup`);
  2. the declarations are accepted from the context, one at a time,
     each by the fold's own install step and record check at the
     canonical index of the environment so far, and a constant flagged
     a proof is a theorem, or a definition or opaque constant that also
     passes the theorem check (its type is a proposition)
     (`accepted`, `AcceptedFrom`);
  3. every context constant refines the constant of its import's own
     environment it is read from (`context_le`, `Refines`: equal, or an
     assumption with the same level parameters and type, never at a
     pinned name), and what its laws read — the constants of its type
     and value, its rules' right-hand sides and constructors, its
     block's members and constructors, its projection table, the
     pinned names its fast path reads — is stored in the context and
     resolved there as the import resolves it (`scoping`, `EntryScoped`,
     `readsAlike`); a stored structure's table is its import's
     (`tables`, `tables_mem`);
  4. a context name resolves as its import resolves it, an own name to
     the module and the name, or, flagged a proof, to its name, level
     parameters and statement (`res_context`, `res_own`).
  The context's constant is the one scoped, not the import's: an
  importer that sees a definition as an assumption reads only its type.
-/

namespace ConLeche.Modular

open ConLeche.Cached

/-- **A qualified name**: an ordinary constant is named by its home
module and its name; a proof by its name, level parameters and
statement. -/
inductive Key where
  | qual (module : Nat) (n : Name)
  | proof (n : Name) (lparams : List Name) (type : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- **A module** (see the module docstring). -/
structure Module where
  imports : List Nat
  decls : List Declaration
  context : Env
  own : Env
  src : Name → Nat
  proofs : Name → Bool
  res : Name → Key

/-- The qualified name of an own constant of module `i`. -/
def Module.ownKey (m : Module) (i : Nat) (n : Name) (ci : ConstantInfo) : Key :=
  if m.proofs n then .proof n ci.toConstantVal.levelParams ci.toConstantVal.type else .qual i n

/-- **The pinned names**: names whose stored kind the checker's fast
paths and the model's laws read (the reserved basis, the certified
`Nat` operations, the `reduce*` opaques).  A context never presents
one of them as an assumption of something else. -/
def pinnedNames : List Name :=
  reservedBasisNames ++ natOpNames ++ natDivModNames ++ reduceOpNames

/-- **The names a pinned constant's fast path reads**, beyond its own
type and value: a certified `Nat` operation's dependencies, the `Nat`
basis and (for the `Bool`-valued and `ble`-guarded ones) the `Bool`
type and constructors; a `reduce*` opaque's element type. -/
def pinFootprint (n : Name) : List Name :=
  (if natOpNames.contains n || natDivModNames.contains n then
    natOpDeps n ++ [natName, natZeroName, natSuccName] ++
      (if n = natBeqName || n = natBleName || natDivModNames.contains n then
        [boolName, boolTrueName, boolFalseName] else [])
   else []) ++
  (if reduceOpNames.contains n then [reduceElemName n] else [])

/-- **Refinement of a constant** stored under `n`: the same constant,
or an assumption with the same name, level parameters and type standing
for a definition, theorem or assumption, at a name that is not pinned. -/
def Refines (n : Name) (ci ci' : ConstantInfo) : Prop :=
  ci = ci' ∨
    (n ∉ pinnedNames ∧ ci = .axiomInfo ci'.toConstantVal ∧
      ((∃ v h, ci' = .defnInfo ci'.toConstantVal v h) ∨ ci' = .thmInfo ci'.toConstantVal ∨
        ci' = .axiomInfo ci'.toConstantVal))

/-- **The part of module `i`'s context that it reads as import `b`
does**: the context's constants whose names `i` and `b` resolve alike. -/
def readsAlike (dev : Nat → Module) (i b : Nat) : Env :=
  ⟨(dev i).context.consts.filter fun c => (dev i).res c.name == (dev b).res c.name, []⟩

/-- **What a context constant's laws read is stored and read alike**
(check 3): `R` is the part of the context read as the constant's
import reads it (`readsAlike`), `C` the context.  The constants of the
type (and of a definition's value), a recursor's rules (right-hand
sides, nested pins, constructors), an inductive type's block members,
constructors, η constructor and projection table, and the names a
pinned constant's fast path reads (`pinFootprint`). -/
def EntryScoped (R C : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  ci.toConstantVal.type.constsResolve R = true ∧
  (∀ cv v h, ci = .defnInfo cv v h → v.constsResolve R = true) ∧
  (∀ cv mI rP rules, ci = .recInfo cv mI rP rules → ∀ r ∈ rules,
    r.rhs.constsResolve R = true ∧ (R.find? r.ctor).isSome = true ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, p.constsResolve R = true) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, (R.find? m).isSome = true) ∧
    (∀ c ∈ caps.ctors, (R.find? c).isSome = true) ∧
    (caps.eta = true → (R.find? caps.etaCtor).isSome = true) ∧
    ∀ t, C.findTable? n = some t →
      (R.find? t.ctor).isSome = true ∧ ∀ b ∈ t.bodies.toList, b.constsResolve R = true) ∧
  ∀ d ∈ pinFootprint n, (R.find? d).isSome = true

/-- **A flagged declaration is a proof**: a theorem, or a definition or
opaque constant at a name that is not pinned whose value also passes
the theorem record's check at the environment it is installed at (its
type a proposition, its value of that type). -/
def ProofDecl (mode : CheckMode) (E : Env) : Declaration → Prop
  | .thmDecl cv _ => cv.name ∉ pinnedNames
  | .defnDecl cv v _ | .opaqueDecl cv v =>
    cv.name ∉ pinnedNames ∧
      ∃ s, checkPending mode (mkFEnv E) ⟨⟨.thm, cv, v⟩, 0, (mkFEnv E).visibleBelow⟩ {}
        = .ok ((), s)
  | _ => False

/-- **A declaration list accepted from an environment** (check 2): each
declaration installed by the fold's step (`installDeclStep`) at the
canonical index of the environment so far, its record (if any) checked
(`checkPending`), and a flagged name the step stores is stored by a
proof (`ProofDecl`);
the next declaration starts at the environment the step produced. -/
inductive AcceptedFrom (mode : CheckMode) (pins : List NatOpPinSet) (proofs : Name → Bool) :
    Env → List Declaration → Env → Prop where
  | nil (E : Env) : AcceptedFrom mode pins proofs E [] E
  | cons {E E' : Env} {d : Declaration} {ds : List Declaration} {i : Nat} {fe : FEnv}
      {pend : Array PendingCheck}
      (hstep : installDeclStep mode pins (i, mkFEnv E, #[]) d = .ok (i + 1, fe, pend))
      (hrec : ∀ pc ∈ pend.toList, ∃ s, checkPending mode fe pc {} = .ok ((), s))
      (hflag : ∀ n, proofs n = true → E.find? n = none → (fe.env.find? n).isSome = true →
        ProofDecl mode E d)
      (rest : AcceptedFrom mode pins proofs fe.env ds E') :
      AcceptedFrom mode pins proofs E (d :: ds) E'

/-- **The local checks at module `i`** (see the module docstring). -/
structure LocalOk (mode : CheckMode) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) :
    Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  src_mem : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n ∈ (dev i).imports
  nodup : ((dev i).context.consts.map (·.name)).Nodup
  accepted : AcceptedFrom mode pins (dev i).proofs (dev i).context (dev i).decls (dev i).own
  context_le : ∀ n ci, (dev i).context.find? n = some ci →
    ∃ ci', (dev ((dev i).src n)).own.find? n = some ci' ∧ Refines n ci ci'
  scoping : ∀ n ci, (dev i).context.find? n = some ci →
    EntryScoped (readsAlike dev i ((dev i).src n)) (dev i).context n ci
  tables : ∀ T, ((dev i).context.find? T).isSome = true →
    (dev i).context.findTable? T = (dev ((dev i).src T)).own.findTable? T
  tables_mem : ∀ t ∈ (dev i).context.tables, (dev i).context.findTable? t.structName = some t
  res_context : ∀ n, ((dev i).context.find? n).isSome = true →
    (dev i).res n = (dev ((dev i).src n)).res n
  res_own : ∀ n ci, (dev i).own.find? n = some ci → (dev i).context.find? n = none →
    (dev i).res n = (dev i).ownKey i n ci

end ConLeche.Modular
