import Lech.Kernel.Expr

/-!
# Level operations

Implementation of universe level comparison, following the official kernel /
nanoda (`level.rs` there): `simplify` normalizes, `leqCore` decides
`eval l ≤ eval r + diff` with the same case order as nanoda's `leq_core`
(so reduction happens the same way), and antisymmetry gives equivalence.

`leqCore`'s termination argument is nontrivial (the `imax` by-cases rule
substitutes into both sides), so it takes fuel.  Running out of fuel — or
hitting a case that is unreachable for simplified input — is reported as
`none`, which callers must treat as an internal error, never as a verdict.

Soundness of all of this (w.r.t. evaluation of levels into `Nat`) is proved
in `Lech.Verify.Level`.
-/

namespace Lech.Level

/-- Substitute level parameters: `subst ks vs l` replaces `param k` by the
corresponding `v`.  Unlisted parameters remain. -/
def subst (ks : List Name) (vs : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (subst ks vs l)
  | .max l r => .max (subst ks vs l) (subst ks vs r)
  | .imax l r => .imax (subst ks vs l) (subst ks vs r)
  | .param n => go ks vs n
where
  go : List Name → List Level → Name → Level
  | k :: ks, v :: vs, n => if k = n then v else go ks vs n
  | _, _, n => .param n

/-- Are all parameters of `l` among `params`? -/
def allParamsDefined (params : List Name) : Level → Bool
  | .zero => true
  | .succ l => allParamsDefined params l
  | .max l r | .imax l r => allParamsDefined params l && allParamsDefined params r
  | .param n => params.contains n

/-- Is this level provably nonzero at every parameter assignment
(official kernel `is_never_zero`)?  Syntactic and incomplete, exactly
as the reference: `succ` is, `max` if either side is, `imax` if the
right side is; `zero` and `param` are not. -/
def isNeverZero : Level → Bool
  | .zero => false
  | .param _ => false
  | .succ _ => true
  | .max l r => isNeverZero l || isNeverZero r
  | .imax _ r => isNeverZero r

/-- `max` of two simplified levels, pulling out common `succ`s. -/
def combining : Level → Level → Level
  | .zero, r => r
  | l, .zero => l
  | .succ l, .succ r => .succ (combining l r)
  | l, r => .max l r

/-- Normalize a level: resolve `max`/`imax` where possible. -/
def simplify : Level → Level
  | .zero => .zero
  | .param n => .param n
  | .succ l => .succ (simplify l)
  | .max l r => combining (simplify l) (simplify r)
  | .imax l r =>
    let ls := simplify l
    let rs := simplify r
    if ls = .zero || ls = .succ .zero then rs
    else match rs with
      | .zero => .zero
      | .succ _ => combining ls rs
      | _ => .imax ls rs

mutual

/-- Decide `eval l ≤ eval r + diff` for simplified `l`, `r`. -/
def leqCore (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if l = .zero ∧ diff ≥ 0 then some true
    else if r = .zero ∧ diff < 0 then some false
    else rest fuel l r diff

/-- The cases after the cheap `zero` short-cuts, in nanoda's order. -/
def rest (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .param a, .param x => some (a = x && diff ≥ 0)
  | .param _, .zero => some false
  | .zero, .param _ => some (diff ≥ 0)
  | .succ s, _ => leqCore fuel s r (diff - 1)
  | _, .succ s => leqCore fuel l s (diff + 1)
  | .max a b, _ => do
    if ← leqCore fuel a r diff then leqCore fuel b r diff else pure false
  | .param _, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | .zero, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a = x && b = y && diff ≥ 0 then some true else imaxRules fuel l r diff
    | _, _ => imaxRules fuel l r diff

/-- The `imax` rules (nanoda's cases 10–15): case-split on a parameter, or
distribute a nested `max`/`imax` on the right of an `imax`. -/
def imaxRules (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .imax _ (.param p), _ => byCases fuel p l r diff
  | _, .imax _ (.param p) => byCases fuel p l r diff
  | .imax a (.imax x y), _ => leqCore fuel (.max (.imax a y) (.imax x y)) r diff
  | .imax a (.max x y), _ => leqCore fuel (simplify (.max (.imax a x) (.imax a y))) r diff
  | _, .imax x (.imax j k) => leqCore fuel l (.max (.imax x k) (.imax j k)) diff
  | _, .imax x (.max j k) => leqCore fuel l (simplify (.max (.imax x j) (.imax x k))) diff
  | _, _ => none  -- unreachable for simplified input; an internal error

/-- Split on the parameter `p` being zero or positive. -/
def byCases (fuel : Nat) (p : Name) (l r : Level) (diff : Int) : Option Bool := do
  let l0 := simplify (subst [p] [.zero] l)
  let r0 := simplify (subst [p] [.zero] r)
  if ← leqCore fuel l0 r0 diff then
    let ls := simplify (subst [p] [.succ (.param p)] l)
    let rs := simplify (subst [p] [.succ (.param p)] r)
    leqCore fuel ls rs diff
  else pure false

end

/-- A generous fuel bound for `leqCore`; exceeded only by pathological input
(then reported as an internal error, not a verdict). -/
def defaultFuel : Nat := 10000

/-- Decide `l ≤ r` semantically; `none` is an internal error. -/
def leq (l r : Level) : Option Bool :=
  leqCore defaultFuel (simplify l) (simplify r) 0

/-- Decide semantic equality of two levels; `none` is an internal error.
Syntactic equality decides directly — first on the levels themselves
(`l == r`, which is pointer- and hash-first, task #176 P2), then on
their simplified forms (the reference kernels' fast path); otherwise
antisymmetric `leq`, short-circuited.

**Conformance note (restrictions-are-findings, task #176 P2).**  The
first disjunct is what official's `is_equivalent` does and lech did
not: `bool is_equivalent(level const & lhs, level const & rhs) {
return lhs == rhs || normalize(lhs) == normalize(rhs); }`
(`level.cpp:518`).  It is *provably redundant* here — `l = r` implies
`simplify l = simplify r` — so the alignment is verdict-neutral by
construction, not merely accept-superset: `isEquiv_eq_withoutPtr` and
`isEquiv_of_beq` (`Verify/Level.lean`) pin both directions.  What it
buys is speed: `simplify` allocates, `l == r` on a shared level is one
pointer compare. -/
def isEquiv (l r : Level) : Option Bool := do
  if l == r then pure true
  else if simplify l = simplify r then pure true
  else if ← leq l r then leq r l else pure false

/-- Decide pointwise semantic equality of two level lists (`false` on length
mismatch). -/
def isEquivList : List Level → List Level → Option Bool
  | [], [] => some true
  | l :: ls, r :: rs => do
    if ← isEquiv l r then isEquivList ls rs else pure false
  | _, _ => some false

/-- Is this level syntactically `zero` after simplification?  (Sound but
incomplete zero test; matches what the checker needs.) -/
def isZero (l : Level) : Bool := simplify l = .zero

/-- Certainly nonzero under *every* level assignment (`succ`-headed
somewhere along every `max`, and along the `imax` right spine).
Conservative: `false` does not mean "can be zero". -/
def isNonZero : Level → Bool
  | .zero => false
  | .succ _ => true
  | .max a b => a.isNonZero || b.isNonZero
  | .imax _ b => b.isNonZero
  | .param _ => false

/-- The zero-ness datum of a level (task #161): the exact reading of
`{φ | eval φ l = 0}`.  `Lech.Verify.PropWhen` proves
`(zeronessOf l).holds φ = (eval φ l == 0)`.  Case notes: a `max` is
zero iff both sides are (`inter`); an `imax` is zero iff its right
side is (`eval (imax a b) = if eval b = 0 then 0 else max …`). -/
def zeronessOf : Level → PropWhen
  | .zero => .ifAllZero []
  | .succ _ => .never
  | .param n => .ifAllZero [n]
  | .max a b => (zeronessOf a).inter (zeronessOf b)
  | .imax _ b => zeronessOf b

/-- Push a level-parameter substitution through a zero-ness datum
(task #161): each parameter becomes its replacement's datum,
intersected — `Z(subst ks vs l)` is exactly
`substPW ks vs (zeronessOf l)` (`Verify.PropWhen.zeronessOf_subst`,
a syntactic equation).  Shape-preserving (`PropWhen.bindZ`): an
unlisted parameter reproduces `ifAllZero [n]`, so instantiating a
declaration at its own parameters is the identity here too
(`substPW_self`), with no canonical-form side condition. -/
def substPW (ks : List Name) (vs : List Level) (pw : PropWhen) :
    PropWhen :=
  pw.bindZ fun n => zeronessOf (subst.go ks vs n)

end Lech.Level

namespace Lech

/-- No duplicates in a list of names. -/
def Name.nodup : List Name → Bool
  | [] => true
  | n :: ns => !ns.contains n && Name.nodup ns

/-- Is this a `_model`-suffixed name (the shape of model companions)? -/
def Name.isModelSuffix : Name → Bool
  | .str _ "_model" => true
  | _ => false

/-- Is this shaped like an installed projection function's name
(`(T.proj).i`, the modeled path's projection functions) or a
projection table's (`(T.projTable).0`, task #175 S1)?  Both shapes
are reserved for the checker's own installs. -/
def Name.isProjFnShape : Name → Bool
  | .num (.str _ "proj") _ => true
  | .num (.str _ "projTable") _ => true
  | _ => false

/-- Substitute level parameters throughout an expression (sorts and
constant level arguments). -/
def Expr.instantiateLevelParams (ks : List Name) (us : List Level) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n (ty.instantiateLevelParams ks us)
  | .sort u => .sort (Level.subst ks us u)
  | .const n vs => .const n (vs.map (Level.subst ks us))
  | .app f a => .app (f.instantiateLevelParams ks us) (a.instantiateLevelParams ks us)
  | .lam n ty body m =>
    .lam n (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      ⟨m.bi, Level.substPW ks us m.pw⟩
  | .forallE n ty body m =>
    .forallE n (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      ⟨m.bi, Level.substPW ks us m.pw⟩
  | .letE n ty val body => .letE n (ty.instantiateLevelParams ks us)
      (val.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
  | .lit l => .lit l
  | .proj s i e => .proj s i (e.instantiateLevelParams ks us)

/-- Are all level parameters occurring in `e` among `params`?  Binder
prop-ness data included (task #161): their parameters are level
parameters of the term — `instantiateLevelParams` substitutes into
them, and its composition law needs them covered exactly as it needs
the levels'. -/
def Expr.allLevelParamsDefined (params : List Name) : Expr → Bool
  | .bvar _ => true
  | .fvar _ _ t => t.allLevelParamsDefined params
  | .sort u => u.allParamsDefined params
  | .const _ us => us.all (Level.allParamsDefined params)
  | .app f a => f.allLevelParamsDefined params && a.allLevelParamsDefined params
  | .lam _ t b m | .forallE _ t b m =>
    t.allLevelParamsDefined params && b.allLevelParamsDefined params
      && m.pw.paramsDefined params
  | .letE _ t v b => t.allLevelParamsDefined params && v.allLevelParamsDefined params
      && b.allLevelParamsDefined params
  | .lit _ => true
  | .proj _ _ e => e.allLevelParamsDefined params

end Lech
