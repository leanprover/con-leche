module

public import Setlec.Kernel.Name

/-!
# The zero-ness datum `PropWhen` — representation, API and laws
(task #161; the small-list constructors, 2026-09-06)

The binder annotation of the validated-annotation design: the reading
of a codomain sort's zero-ness predicate `Z(l) = {φ | eval φ l = 0}`.

**This module is the datum's whole boundary.**  It owns the
representation, the API that is the only way to build, read and
compare a datum, and — following the `Std.HashMap` pattern that
`CLAUDE.md` licenses for a self-contained data-structure verification
— every law about the datum *alone*.  Downstream never re-proves them
and never sees a constructor:

* the readout `holds` and its algebra (`holds_inter`,
  `holds_bindZ_go`, `holds_ext`);
* the comparison `equiv`, **sound and complete** for zero-ness
  agreement at every valuation (`equiv_iff_holds`, `equiv_refl`,
  `holds_eq_of_equiv`);
* the `inter`/`bindZ` algebra the substitution laws rest on
  (`inter_assoc`, `bindZ_inter`, `bindZ_go_append`,
  `bindZ_congr_names`, `bindZ_unit`, `paramsDefined_inter_of`).

What is *not* here is what is not about the datum alone: the laws
relating it to `Level` (`Level.zeronessOf`, `Level.substPW` —
`zeronessOf_sound`, `zeronessOf_subst`, `substPW_self`,
`substPW_comp`, `holds_substPW`) live in `Setlec/Verify/PropWhen.lean`,
because `Level` is defined *above* this module, and they are proved
purely through the API exported here.

Layering: this module imports `Setlec.Kernel.Name` and nothing else.
-/

public section

namespace Setlec


/-- The private representation of the zero-ness datum (2026-09-06).
The census (DESIGN.md, "THE PACKED `pw` DATUM" §1) found the parameter
lists tiny: on init-full 605 492 data are `ifAllZero []`, 123 332 are
one name, 16 are two names and **none** is longer.  So the small cases
get dedicated constructors and only lists of length ≥ 3 keep a `List`
cell chain — `many` stored as its first three entries plus the tail,
which puts the representation in *definitional* bijection with
`List Name` and so needs no well-formedness side condition.

This type is `private`: it cannot be named, matched on or constructed
outside this module. -/
private inductive PropWhenRepr where
  | never
  | always
  | one (p : Name)
  | two (p q : Name)
  | many (p q r : Name) (rest : List Name)
  deriving DecidableEq, Inhabited, Hashable

/-- The zero-ness datum of a binder's codomain sort — the regime
discriminator of the validated-annotation design (task #161).  For
every level `l`, the set `Z(l) := {φ | eval φ l = 0}` of zeroing
valuations is either empty (`never`) or of the form "every parameter
in `ps` is zero" (`ifAllZero ps`; `ps = []` = always zero) — see
`Level.zeronessOf` and the mechanized battery in
`Setlec.Verify.PropWhen`.

`ps` is an unordered, possibly-duplicated parameter *set in list
clothing*: all structural operations (`inter`, `bindZ`,
`Level.substPW`) are shape-preserving — no sorting, no
deduplication — which is what makes level instantiation's identity
and composition laws hold *unconditionally*
(`Level.substPW_self`/`substPW_comp`).  Comparison is by the
containment test `equiv`, which is sound **and complete** for
zero-ness agreement at every valuation; the checker's validation and
defeq sites compare with `equiv`, never with `==`.

**The representation is hidden, not hidden by convention.**  The datum
is a one-field structure whose constructor *and* field are `private`,
wrapping the equally private `PropWhenRepr`.  Outside this module the
type is opaque: it cannot be pattern-matched, taken apart or built
except through the API below (`never`, `ifAllZero`, `toList`,
`toList?`, `casesZ`, the observers and their laws).  Nothing in this
module is `@[expose]`d either, so no `rfl`/`decide` downstream can
reach around the API and reduce through a body — every fact about the
datum is one of the exported theorems. -/
structure PropWhen where
  private ofRepr ::
  private repr : PropWhenRepr

namespace PropWhen

/-! ### The instances

`instance` bodies are always exposed, so they may not mention the
private representation; each therefore goes through a public (sealed)
helper that may. -/

private theorem ofRepr_repr (a : PropWhen) : ofRepr a.repr = a := rfl

private theorem repr_inj {a b : PropWhen} (h : a.repr = b.repr) : a = b := by
  rw [← ofRepr_repr a, ← ofRepr_repr b, h]

/-- Structural equality, decided on the hidden representation. -/
def decEq (a b : PropWhen) : Decidable (a = b) :=
  if h : a.repr = b.repr then isTrue (repr_inj h)
  else isFalse fun he => h (by rw [he])

instance : DecidableEq PropWhen := decEq

/-- The hash of a datum. -/
def hash' (pw : PropWhen) : UInt64 := hash pw.repr

instance : Hashable PropWhen := ⟨hash'⟩


/-! ### The encapsulation boundary

`never`, `ifAllZero`, `toList`, `toList?` and `casesZ` are the whole
interface to the shape; every observer below is stated over them, and
every fact anyone downstream needs is one of the exported equations.
-/

/-- "The codomain sort is nonzero at every valuation."  A *definition*
now, not a constructor — but `.never` reads the same at every use
site. -/
def never : PropWhen := ofRepr .never

instance : Inhabited PropWhen := ⟨never⟩

/-- **Smart constructor**: "every parameter in `ps` is zero".  Picks
the dedicated small-case representation for `ps` of length ≤ 2 and the
`many` chain otherwise.  Shape-preserving: `toList (ifAllZero ps) = ps`
for *every* `ps`, duplicates and order included. -/
@[inline] def ifAllZero : List Name → PropWhen
  | [] => ofRepr .always
  | [p] => ofRepr (.one p)
  | [p, q] => ofRepr (.two p q)
  | p :: q :: r :: rest => ofRepr (.many p q r rest)

/-- The parameter list of a datum (`never` reads as `[]` — use
`toList?` where the distinction matters). -/
def toList (pw : PropWhen) : List Name :=
  match pw.repr with
  | .never => []
  | .always => []
  | .one p => [p]
  | .two p q => [p, q]
  | .many p q r rest => p :: q :: r :: rest

/-- The parameter list of a non-`never` datum; `none` at `never`.  The
view that inverts `ifAllZero`. -/
def toList? (pw : PropWhen) : Option (List Name) :=
  match pw.repr with
  | .never => none
  | _ => some pw.toList

@[simp] theorem toList_never : toList .never = [] := by
  simp [toList, never]

@[simp] theorem toList_ifAllZero (ps : List Name) :
    (ifAllZero ps).toList = ps := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [toList, ifAllZero]

@[simp] theorem toList?_never : toList? .never = none := by
  simp [toList?, never]

@[simp] theorem toList?_ifAllZero (ps : List Name) :
    (ifAllZero ps).toList? = some ps := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [toList?, toList, ifAllZero]

/-- The smart constructor never produces `never`. -/
@[simp] theorem ifAllZero_ne_never (ps : List Name) : ifAllZero ps ≠ .never := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ =>
    simp [ifAllZero, never, PropWhen.ofRepr.injEq]

/-- **The view**: every datum is `never` or `ifAllZero ps`.  Registered
as the `cases`/`induction` eliminator, so case analysis outside this
module is written — and reads — exactly as it did against the
two-constructor datum. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def casesZ {motive : PropWhen → Sort u} (never : motive .never)
    (ifAllZero : (ps : List Name) → motive (PropWhen.ifAllZero ps)) :
    (pw : PropWhen) → motive pw
  | .ofRepr .never => never
  | .ofRepr .always => ifAllZero []
  | .ofRepr (.one p) => ifAllZero [p]
  | .ofRepr (.two p q) => ifAllZero [p, q]
  | .ofRepr (.many p q r rest) => ifAllZero (p :: q :: r :: rest)

/-- Reassembling a datum from its list — the `casesZ` companion. -/
theorem ifAllZero_toList {pw : PropWhen} (h : pw ≠ .never) :
    ifAllZero pw.toList = pw := by
  cases pw with
  | never => exact absurd rfl h
  | ifAllZero ps => rw [toList_ifAllZero]

/-- The old datum's `Repr`, kept **byte-identical**: the annotate-basis
generator (`AnnotateBasis.lean`) prints the committed `Basis/*.lean`,
`StdAxioms.lean` and `TrustAxioms.lean` literals with `repr`, and those
literals name the smart constructor.  This reproduces exactly what
`deriving Repr` emitted for the old `never | ifAllZero (ps : List Name)`
datum. -/
def reprPrec' (pw : PropWhen) (prec : Nat) : Std.Format :=
  Repr.addAppParen
    (Std.Format.group (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
      (match pw.toList? with
        | none => Std.Format.text "Setlec.PropWhen.never"
        | some ps =>
          Std.Format.text "Setlec.PropWhen.ifAllZero" ++ Std.Format.line ++
            reprArg ps)))
    prec

instance : Repr PropWhen := ⟨reprPrec'⟩

/-! ### The observers

Each is defined representation-wise (so the small cases touch no list
cells) and immediately re-stated in the `never`/`ifAllZero` form —
those equations, not the definitions, are the whole downstream
surface. -/

/-- Does the datum hold at a valuation — is the codomain sort zero
there?  (The model side's dispatch bit; the kernel never evaluates
this, it only compares data by `equiv`.) -/
def holds (φ : Name → Nat) (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => false
  | .always => true
  | .one p => φ p == 0
  | .two p q => (φ p == 0) && (φ q == 0)
  | .many p q r rest =>
    (φ p == 0) && (φ q == 0) && (φ r == 0) && rest.all fun n => φ n == 0

@[simp] theorem holds_never (φ : Name → Nat) : holds φ .never = false := by
  simp [holds, never]

@[simp] theorem holds_ifAllZero (φ : Name → Nat) (ps : List Name) :
    holds φ (ifAllZero ps) = ps.all fun n => φ n == 0 := by
  match ps with
  | [] | [_] | [_, _] => simp [holds, ifAllZero]
  | _ :: _ :: _ :: _ => simp [holds, ifAllZero, Bool.and_assoc]

/-- Is the datum `never` — "the codomain sort is nonzero at *every*
valuation", the graph regime everywhere?  This is the **only**
kernel-decidable reading of the annotation that the verification tier
licenses a check-skip on (task #161 bucket 2): the P-tier claims split
their certificate cases on `pwBit φ m.pw = 0`, and `isNever` is
exactly the ∀-`φ` uniform version of the positive branch —
`pwBit φ .never = 1` at every `φ`, and no other datum has that
property (`.ifAllZero ps` holds at the all-zero valuation).  Sound
*and* exact: `isNever_iff_forall_pwBit_ne_zero` (`SetP/Annot/Bit.lean`)
rests on `holds_never`/`holds_ifAllZero` here.

The datum may be read **only** to skip a re-check; it must never
select a reduct, a computed type, or a comparison result (law 1 as
amended at task #161: "annotations never change a reduct or a computed
type; annotation-gated check-skipping is permitted where the skip's
soundness is a P-tier theorem *and* the gate fires only where the
licensing theorems' hypotheses hold — `μ.verifiedChecks = true`").  Every
executable call site therefore carries the `μ.verifiedChecks` conjunct; see
`inferBodyIO` (`Kernel/CoreIO.lean`). -/
@[inline] def isNever (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => true
  | _ => false

@[simp] theorem isNever_never : isNever .never = true := by simp [isNever, never]

@[simp] theorem isNever_ifAllZero (ps : List Name) :
    isNever (ifAllZero ps) = false := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [isNever, ifAllZero]

/-- Does the datum mention any level parameter — is `Level.substPW`
ever non-trivial on it?  Folded into `Expr.hasLevelParam` and the
eager `eparamBs` recurrence (task #87), so the has-param shortcut of
the interned level-instantiation walk stays exact. -/
@[inline] def hasParams (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => false
  | .always => false
  | _ => true

@[simp] theorem hasParams_never : hasParams .never = false := by
  simp [hasParams, never]

@[simp] theorem hasParams_ifAllZero (ps : List Name) :
    hasParams (ifAllZero ps) = !ps.isEmpty := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [hasParams, ifAllZero]

/-- Are all parameters of the datum among `params`?  Folded into
`Expr.allLevelParamsDefined` (task #161): level instantiation's
composition law (`Level.substPW_comp`) is *false* for data whose
parameters escape the declaration's — exactly as for the levels
themselves. -/
def paramsDefined (params : List Name) (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => true
  | .always => true
  | .one p => params.contains p
  | .two p q => params.contains p && params.contains q
  | .many p q r rest =>
    params.contains p && params.contains q && params.contains r &&
      rest.all params.contains

@[simp] theorem paramsDefined_never (params : List Name) :
    paramsDefined params .never = true := by simp [paramsDefined, never]

@[simp] theorem paramsDefined_ifAllZero (params ps : List Name) :
    paramsDefined params (ifAllZero ps) = ps.all params.contains := by
  match ps with
  | [] | [_] | [_, _] => simp [paramsDefined, ifAllZero]
  | _ :: _ :: _ :: _ => simp [paramsDefined, ifAllZero, Bool.and_assoc]

/-- Intersection of two zero-ness predicates (the `max` rule: a `max`
is zero iff both sides are): `never` absorbs, sets append.  The
`always`/singleton cases are answered without touching a list cell —
they are 99.99 % of the calls (the census). -/
def inter (a b : PropWhen) : PropWhen :=
  match a.repr, b.repr with
  | .never, _ => never
  | _, .never => never
  | .always, _ => b
  | _, .always => a
  | .one x, .one y => ofRepr (.two x y)
  | _, _ => ifAllZero (a.toList ++ b.toList)

@[simp] theorem inter_never_left (q : PropWhen) : inter .never q = .never := by
  simp [inter, never]

/-- `never` absorbs on the right too. -/
@[simp] theorem inter_never_right (p : PropWhen) : p.inter .never = .never := by
  cases p with
  | never => simp
  | ifAllZero ps =>
    match ps with
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [inter, ifAllZero, never]

/-- The shape of `inter` away from `never`: the parameter lists append
(the fast arms are exactly this, spelled out). -/
theorem inter_eq_toList {p q : PropWhen} (hp : p ≠ .never) (hq : q ≠ .never) :
    p.inter q = ifAllZero (p.toList ++ q.toList) := by
  cases p with
  | never => exact absurd rfl hp
  | ifAllZero ps =>
    cases q with
    | never => exact absurd rfl hq
    | ifAllZero qs =>
      rw [toList_ifAllZero, toList_ifAllZero]
      match ps, qs with
      | [], [] | [], [_] | [], [_, _]
      | [], _ :: _ :: _ :: _ | [_], [] | [_], [_]
      | [_], [_, _] | [_], _ :: _ :: _ :: _ | [_, _], []
      | [_, _], [_] | [_, _], [_, _] | [_, _], _ :: _ :: _ :: _
      | _ :: _ :: _ :: _, [] | _ :: _ :: _ :: _, [_] | _ :: _ :: _ :: _, [_, _]
      | _ :: _ :: _ :: _, _ :: _ :: _ :: _ =>
        simp [inter, ifAllZero, toList]

@[simp] theorem inter_ifAllZero (ps qs : List Name) :
    inter (ifAllZero ps) (ifAllZero qs) = ifAllZero (ps ++ qs) := by
  rw [inter_eq_toList (ifAllZero_ne_never ps) (ifAllZero_ne_never qs),
    toList_ifAllZero, toList_ifAllZero]

/-- `ifAllZero []` is the right unit of `inter`. -/
@[simp] theorem inter_nil (p : PropWhen) : p.inter (ifAllZero []) = p := by
  cases p with
  | never => simp
  | ifAllZero ps => rw [inter_ifAllZero, List.append_nil]

/-- `ifAllZero []` is the left unit of `inter`. -/
@[simp] theorem nil_inter (q : PropWhen) : (ifAllZero []).inter q = q := by
  cases q with
  | never => simp
  | ifAllZero qs => rw [inter_ifAllZero, List.nil_append]

/-- The list-level `bindZ` fold. -/
def bindZ.go (f : Name → PropWhen) : List Name → PropWhen
  | [] => ifAllZero []
  | n :: rest => (f n).inter (go f rest)

/-- Substitute each parameter of the datum by a whole datum and
intersect ("all of `ps` zero" becomes "all replacements zero") — the
monadic bind of the zero-ness reading.  Shape-preserving: parameters
mapped to `ifAllZero [n]` reproduce the input list exactly, which is
what the unconditional substitution laws rest on. -/
def bindZ (f : Name → PropWhen) (pw : PropWhen) : PropWhen :=
  match pw.repr with
  | .never => never
  | .always => ifAllZero []
  | .one p => f p
  | .two p q => (f p).inter (f q)
  | .many p q r rest =>
    (f p).inter ((f q).inter ((f r).inter (bindZ.go f rest)))

@[simp] theorem bindZ_never (f : Name → PropWhen) :
    bindZ f .never = .never := by simp [bindZ, never]

@[simp] theorem bindZ_go_nil (f : Name → PropWhen) :
    bindZ.go f [] = ifAllZero [] := by simp [bindZ.go]

@[simp] theorem bindZ_ifAllZero (f : Name → PropWhen) (ps : List Name) :
    bindZ f (ifAllZero ps) = bindZ.go f ps := by
  match ps with
  | [] => simp [bindZ, ifAllZero, bindZ.go]
  | [p] =>
    rw [show bindZ.go f [p] = (f p).inter (bindZ.go f []) from rfl,
      bindZ_go_nil, inter_nil]
    simp [bindZ, ifAllZero]
  | [p, q] =>
    rw [show bindZ.go f [p, q]
        = (f p).inter ((f q).inter (bindZ.go f [])) from rfl,
      bindZ_go_nil, inter_nil]
    simp [bindZ, ifAllZero]
  | p :: q :: r :: rest =>
    rw [show bindZ.go f (p :: q :: r :: rest)
        = (f p).inter ((f q).inter ((f r).inter (bindZ.go f rest))) from rfl]
    simp [bindZ, ifAllZero]

/-- Decidable zero-ness agreement at *every* valuation: mutual
containment of the parameter sets (`never` only agrees with `never` —
`ifAllZero` data hold at the all-zero valuation, `never` nowhere).
Sound and complete (`equiv_iff_holds`); this is the comparison every
validation and defeq site uses. -/
def equiv (a b : PropWhen) : Bool :=
  match a.repr, b.repr with
  | .never, .never => true
  | .never, _ => false
  | _, .never => false
  | .always, .always => true
  -- `[]` is mutually contained only with `[]`, so a non-empty list
  -- disagrees with `always` without building either list.
  | .always, _ => false
  | _, .always => false
  | .one x, .one y => x == y
  | _, _ => a.toList.all b.toList.contains && b.toList.all a.toList.contains

@[simp] theorem equiv_never_never : equiv .never .never = true := by
  simp [equiv, never]

@[simp] theorem equiv_never_ifAllZero (ps : List Name) :
    equiv .never (ifAllZero ps) = false := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [equiv, ifAllZero, never]

@[simp] theorem equiv_ifAllZero_never (ps : List Name) :
    equiv (ifAllZero ps) .never = false := by
  match ps with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => simp [equiv, ifAllZero, never]

@[simp] theorem equiv_ifAllZero (ps qs : List Name) :
    equiv (ifAllZero ps) (ifAllZero qs) =
      (ps.all qs.contains && qs.all ps.contains) := by
  match ps, qs with
  | [a], [b] =>
    by_cases h : a = b
    · subst h; simp [equiv, ifAllZero]
    · simp [equiv, ifAllZero, h, Ne.symm h]
  | [], [] | [], [_] | [], [_, _]
  | [], _ :: _ :: _ :: _ | [_], [] | [_], [_, _]
  | [_], _ :: _ :: _ :: _ | [_, _], [] | [_, _], [_]
  | [_, _], [_, _] | [_, _], _ :: _ :: _ :: _ | _ :: _ :: _ :: _, []
  | _ :: _ :: _ :: _, [_] | _ :: _ :: _ :: _, [_, _] | _ :: _ :: _ :: _, _ :: _ :: _ :: _ =>
    simp [equiv, ifAllZero, toList]

end PropWhen

/-! ## The law battery

Everything below is a fact about the datum alone; it needs no `Level`
and no `Expr`.  Moved here from `Setlec/Verify/PropWhen.lean` on
2026-09-06 (the `Std.HashMap` pattern: the structure carries its
laws), statements unchanged. -/

namespace PropWhen

/-! ### `holds` characterizations -/

theorem holds_inter (φ : Name → Nat) (p q : PropWhen) :
    (p.inter q).holds φ = (p.holds φ && q.holds φ) := by
  cases p <;> cases q <;> simp [List.all_append]

theorem holds_bindZ_go (φ : Name → Nat) (f : Name → PropWhen) :
    ∀ ps : List Name,
      (bindZ.go f ps).holds φ = ps.all fun n => (f n).holds φ
  | [] => by rw [bindZ_go_nil, holds_ifAllZero]; rfl
  | n :: rest => by
    simp [bindZ.go, holds_inter, holds_bindZ_go φ f rest]

/-! ### Completeness of the comparison -/

/-- Membership-equal lists agree on every `all`. -/
private theorem all_eq_of_mem_iff {ps qs : List Name}
    (h : ∀ n, n ∈ ps ↔ n ∈ qs) (f : Name → Bool) :
    ps.all f = qs.all f := by
  cases hq : qs.all f
  · cases hp : ps.all f
    · rfl
    · rw [List.all_eq_true] at hp
      rw [List.all_eq_false] at hq
      obtain ⟨n, hn, hf⟩ := hq
      exact absurd (hp n ((h n).mpr hn)) (by simp [hf])
  · rw [List.all_eq_true] at hq ⊢
    exact fun n hn => hq n ((h n).mp hn)

private theorem mem_of_holds_eq {ps qs : List Name}
    (h : ∀ φ, holds φ (.ifAllZero ps) = holds φ (.ifAllZero qs)) :
    ∀ n, n ∈ ps → n ∈ qs := by
  intro n hin
  by_cases hout : n ∈ qs
  · exact hout
  exfalso
  have hn := h fun m => if m = n then 1 else 0
  simp only [holds_ifAllZero] at hn
  have hbs : (qs.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = true :=
    List.all_eq_true.mpr fun m hm => by
      have hne : m ≠ n := fun he => hout (he ▸ hm)
      simp [hne]
  have has : (ps.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = false :=
    List.all_eq_false.mpr ⟨n, hin, by simp⟩
  rw [has, hbs] at hn
  exact Bool.false_ne_true hn

/-- The containment test decides zero-ness agreement at every
valuation: sound **and** complete.  The separating valuations: the
all-zero valuation separates `never` from every `ifAllZero`, and
`φ n := 1, else 0` separates parameter sets that disagree on `n`. -/
theorem equiv_iff_holds (p q : PropWhen) :
    equiv p q = true ↔ ∀ φ, p.holds φ = q.holds φ := by
  constructor
  · intro h φ
    cases p with
    | never => cases q with
      | never => rfl
      | ifAllZero qs => simp at h
    | ifAllZero ps => cases q with
      | never => simp at h
      | ifAllZero qs =>
        simp only [equiv_ifAllZero, Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨hpq, hqp⟩ := h
        rw [holds_ifAllZero, holds_ifAllZero]
        exact all_eq_of_mem_iff
          (fun n => ⟨fun hn => by
              simpa [List.contains_iff_mem] using hpq n hn,
            fun hn => by
              simpa [List.contains_iff_mem] using hqp n hn⟩) _
  · intro h
    cases p with
    | never => cases q with
      | never => rfl
      | ifAllZero qs =>
        have := h fun _ => 0
        simp at this
    | ifAllZero ps => cases q with
      | never =>
        have := h fun _ => 0
        simp at this
      | ifAllZero qs =>
        have h1 := mem_of_holds_eq h
        have h2 := mem_of_holds_eq fun φ => (h φ).symm
        rw [equiv_ifAllZero]
        rw [Bool.and_eq_true]
        exact ⟨List.all_eq_true.mpr fun n hn => by
            simpa [List.contains_iff_mem] using h1 n hn,
          List.all_eq_true.mpr fun n hn => by
            simpa [List.contains_iff_mem] using h2 n hn⟩

theorem paramsDefined_inter_of {params : List Name} {p q : PropWhen}
    (hp : p.paramsDefined params = true)
    (hq : q.paramsDefined params = true) :
    (p.inter q).paramsDefined params = true := by
  cases p <;> cases q <;>
    simp_all [List.all_append]

/-- `equiv` is reflexive (the fold's vacuous self-comparison steps). -/
theorem equiv_refl (p : PropWhen) : equiv p p = true :=
  (equiv_iff_holds p p).mpr fun _ => rfl

/-! ### The bit readouts (task #161 P3)

The P3 proofs consume validated annotations only through the *bit* a
datum reads out at a ground valuation.  This is the readout law for a
passed comparison; its companion for a passed *validation* site
(`holds_of_equiv_zeronessOf`) needs `Level` and lives in
`Setlec/Verify/PropWhen.lean`. -/

/-- Equivalent data read out equal bits at every valuation (the `mp`
direction of `equiv_iff_holds`, named for the P3 API). -/
theorem holds_eq_of_equiv {p q : PropWhen} (h : equiv p q = true)
    (φ : Name → Nat) : p.holds φ = q.holds φ :=
  (equiv_iff_holds p q).mp h φ

/-- **Parameter locality**: a datum reads its valuation only at its
own parameters (the `paramsDefined` footprint) — `denoteP`'s
φ-congruence walk (`denoteP_params_ext`) rides this at every binder.
(Mirror on the canonical side: `ZPropWhen.holds_congr`, via
`parameters`.) -/
theorem holds_ext {ps : List Name} {pw : PropWhen}
    (hdef : pw.paramsDefined ps = true) {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) : pw.holds φ₁ = pw.holds φ₂ := by
  cases pw with
  | never => rfl
  | ifAllZero qs =>
    simp only [paramsDefined_ifAllZero, List.all_eq_true] at hdef
    rw [holds_ifAllZero, holds_ifAllZero]
    induction qs with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons]
      rw [hφ n (by simpa [List.contains_iff_mem] using hdef n (by simp)),
        ih fun m hm => hdef m (by simp [hm])]

/-! ### `inter` / `bindZ` algebra -/

/-- `inter` is associative (the datum is a set union in list
clothing). -/
theorem inter_assoc (a b c : PropWhen) :
    (a.inter b).inter c = a.inter (b.inter c) := by
  cases a <;> cases b <;> cases c <;> simp [List.append_assoc]

/-- The `bindZ` fold over an append splits — the list-level half of
`bindZ_inter`. -/
theorem bindZ_go_append (g : Name → PropWhen) : ∀ ps qs : List Name,
    bindZ.go g (ps ++ qs) = (bindZ.go g ps).inter (bindZ.go g qs)
  | [], qs => (nil_inter (bindZ.go g qs)).symm
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
    | never => simp
    | ifAllZero qs => simp [bindZ_go_append]

theorem bindZ_congr_names {f g : Name → PropWhen} :
    ∀ {ps : List Name}, (∀ n ∈ ps, f n = g n) →
      bindZ.go f ps = bindZ.go g ps
  | [], _ => rfl
  | n :: rest, h => by
    show (f n).inter _ = (g n).inter _
    rw [h n (by simp), bindZ_congr_names fun m hm => h m (by simp [hm])]

/-- `bindZ` at the unit (`n ↦ ifAllZero [n]`) reproduces the datum —
shape and all. -/
theorem bindZ_unit : ∀ pw : PropWhen,
    pw.bindZ (fun n => .ifAllZero [n]) = pw := by
  intro pw
  cases pw with
  | never => rfl
  | ifAllZero ps => rw [bindZ_ifAllZero]; exact bindZ_unit.go ps
where
  go : ∀ ps : List Name,
      bindZ.go (fun n => PropWhen.ifAllZero [n]) ps = .ifAllZero ps
  | [] => rfl
  | n :: rest => by
    show (PropWhen.ifAllZero [n]).inter _ = _
    rw [go rest, inter_ifAllZero]
    rfl

end PropWhen

end Setlec
