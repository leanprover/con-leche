module

public import ConLeche.Kernel.Name

/-!
# The zero-ness datum `PropWhen`

The reading of a sort's zero-ness predicate
`Z(l) = {φ | eval φ l = 0}`: either empty (`never`) or "every parameter
in `ps` is zero" (`ifAllZero ps`; `ps = []` is "zero at every
valuation").  The checker's head-symbol reader
(`ConLeche/Kernel/PropRead.lean`, `proofPW`) and the reading of an
inductive's sort (`formerZ`) produce it; the checker asks two questions of a
datum only, `isNever` (`formerNeverZero`, the ι case split) and "is it
`ifAllZero []`" (`PropWhen.isProp`), and compares data in no other way.

The datum is a plain list: duplicates and order are kept, so equal
parameter sets need not be equal values, and no law below says
otherwise.  The laws are the readout `holds` and the `inter`/`bindZ`
algebra the substitution laws rest on; the laws relating the datum to
`Level` (`Level.zeronessOf`, `Level.substPW`) live in
`ConLeche/Verify/PropWhen.lean`, since `Level` is defined above this
module.

Layering: this module imports `ConLeche.Kernel.Name` and nothing else.
-/

@[expose] public section

namespace ConLeche

/-- The zero-ness datum of a sort: `never` (nonzero at every
valuation) or `ifAllZero ps` (zero exactly where every parameter in
`ps` is). -/
inductive PropWhen where
  | never
  | ifAllZero (ps : List Name)
  deriving DecidableEq, Repr, Inhabited

namespace PropWhen

/-- Does the datum hold at a valuation — is the sort zero there? -/
def holds (φ : Name → Nat) : PropWhen → Bool
  | .never => false
  | .ifAllZero ps => ps.all fun n => φ n == 0

@[simp] theorem holds_never (φ : Name → Nat) : holds φ .never = false := rfl

@[simp] theorem holds_ifAllZero (φ : Name → Nat) (ps : List Name) :
    holds φ (ifAllZero ps) = ps.all fun n => φ n == 0 := rfl

/-- Is the datum `never` — is the sort nonzero at every valuation? -/
@[inline] def isNever : PropWhen → Bool
  | .never => true
  | .ifAllZero _ => false

theorem isNever_iff {pw : PropWhen} : isNever pw = true ↔ pw = never := by
  cases pw <;> simp [isNever]

/-- Are all parameters of the datum among `params`?  Level
instantiation's composition law (`Level.substPW_comp`) needs it, as the
level side needs `Level.allParamsDefined`. -/
def paramsDefined (params : List Name) : PropWhen → Bool
  | .never => true
  | .ifAllZero ps => ps.all params.contains

@[simp] theorem paramsDefined_ifAllZero (params ps : List Name) :
    paramsDefined params (ifAllZero ps) = ps.all params.contains := rfl

/-- Intersection of two zero-ness predicates (the `max` rule: a `max`
is zero iff both sides are): `never` absorbs, parameter lists
concatenate. -/
def inter : PropWhen → PropWhen → PropWhen
  | .never, _ => .never
  | .ifAllZero _, .never => .never
  | .ifAllZero ps, .ifAllZero qs => .ifAllZero (ps ++ qs)

/-- `ifAllZero []` is the right unit of `inter`. -/
theorem inter_nil (p : PropWhen) : p.inter (ifAllZero []) = p := by
  cases p <;> simp [inter]

theorem holds_inter (φ : Name → Nat) (p q : PropWhen) :
    (p.inter q).holds φ = (p.holds φ && q.holds φ) := by
  cases p <;> cases q <;> simp [inter, holds, List.all_append]

theorem inter_assoc (a b c : PropWhen) :
    (a.inter b).inter c = a.inter (b.inter c) := by
  cases a <;> cases b <;> cases c <;> simp [inter, List.append_assoc]

theorem paramsDefined_inter_of {params : List Name} {p q : PropWhen}
    (hp : p.paramsDefined params = true)
    (hq : q.paramsDefined params = true) :
    (p.inter q).paramsDefined params = true := by
  cases p <;> cases q <;> simp_all [inter, paramsDefined, List.all_append]

/-- The list-level `bindZ` fold. -/
def bindZ.go (f : Name → PropWhen) : List Name → PropWhen
  | [] => .ifAllZero []
  | n :: rest => (f n).inter (go f rest)

/-- Substitute each parameter of the datum by a whole datum and
intersect ("all of `ps` zero" becomes "all replacements zero"). -/
def bindZ (f : Name → PropWhen) : PropWhen → PropWhen
  | .never => .never
  | .ifAllZero ps => bindZ.go f ps

@[simp] theorem bindZ_ifAllZero (f : Name → PropWhen) (ps : List Name) :
    bindZ f (ifAllZero ps) = bindZ.go f ps := rfl

theorem holds_bindZ_go (φ : Name → Nat) (f : Name → PropWhen) :
    ∀ ps : List Name,
      (bindZ.go f ps).holds φ = ps.all fun n => (f n).holds φ
  | [] => rfl
  | n :: rest => by
    simp [bindZ.go, holds_inter, holds_bindZ_go φ f rest]

/-- The `bindZ` fold over an append splits. -/
theorem bindZ_go_append (g : Name → PropWhen) : ∀ ps qs : List Name,
    bindZ.go g (ps ++ qs) = (bindZ.go g ps).inter (bindZ.go g qs)
  | [], qs => by
    show bindZ.go g qs = (ifAllZero []).inter (bindZ.go g qs)
    cases bindZ.go g qs <;> rfl
  | n :: rest, qs => by
    show (g n).inter (bindZ.go g (rest ++ qs))
      = ((g n).inter (bindZ.go g rest)).inter (bindZ.go g qs)
    rw [bindZ_go_append g rest qs, inter_assoc]

theorem bindZ_inter (g : Name → PropWhen) (p q : PropWhen) :
    (p.inter q).bindZ g = (p.bindZ g).inter (q.bindZ g) := by
  cases p with
  | never => rfl
  | ifAllZero ps =>
    cases q with
    | never =>
      show PropWhen.never = (bindZ.go g ps).inter .never
      cases bindZ.go g ps <;> rfl
    | ifAllZero qs => exact bindZ_go_append g ps qs

end PropWhen

end ConLeche
