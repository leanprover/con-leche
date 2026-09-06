import Setlec.Cached.ParsedC
import Setlec.Verify.EnvBound

/-!
# The trusted↔P agreement floor (task #172, batch B7; restated at the
twin's retirement, 2026-09-06)

The *cheap floor* of census part 4 §3: whenever the cached driver
(`Setlec/Cached/ParsedC.lean`) at the trusted config and at the
verified config both **accept** a stream, the two installed
environments carry the same constants, in the same order, with the same
install skeletons — and in particular the same names and the same
count.

**What the retirement did to the statement.**  Until 2026-09-06 the
trusted lane was a separate driver (`checkDeclsSPCachedDT`,
`Setlec/Cached/ParsedT.lean`) over a hand-written cert-skipping core,
and the floor had to prove the skeleton spec for *both* drivers, stage
by stage — the second half of this file was a clause-by-clause
duplicate of the first.  Now there is one driver, `checkDeclsSPCachedD
cfg`, and the floor is the skeleton spec proved **once, for every
`cfg : CoreCfg`** (`checkDeclsSPCachedD_skels`); the agreement of two
configs is its two instances glued by `Eq.trans`.  That is strictly
stronger than the frozen B7 statement: the old theorem is the new one
at `cfg₁ := cfgOf mode`, `cfg₂ := cfgT`, and the new one also covers
any two configs, in particular the pair the binary ships (`cfgP`,
`cfgT`).  The certification-only work the trusted config omits
(`cfg.verified`, group A) is invisible to the skeleton by construction
— the spec forgets everything a core computes — which is exactly why
the proof is config-generic without a case split.

Nothing here reasons about the cores.  The floor's whole content is
that the fold is *the same fold* at every config, and the only work is
that this is not quite true on the nose: the inductive-block clause
installs constants under **environment-dependent guards**
(`installProjFnStep*`'s model lookup).  So the induction runs on
the *install skeleton* — exactly the data those guards read, and
nothing a core computes — and the names corollary falls out.

Two facts close the remaining branches without core reasoning:

* the direct simple-structure clause (task #175 W4c, the priority
  route) installs under guards that are the block's own (the
  projection bodies' scoping, task #175 S1) or freshness checks, and
  its dispatch
  (`directPartsF?`) reads the index only through name lookups
  (`directNonRecF_skel`), so it runs on the skeleton too;
* at `.axiomDecl` the push-or-not decision is a function of the header
  name alone — `toleratedAxiomNames = [sorryAx]` installs nothing in
  both drivers, and `stdAxiomOkF` is `false` off `propext`/`choice`, so
  every other accepted axiom installs exactly one `.axiomInfo`.

See DESIGN.md, "TASK #172 — BATCH B7: THE AGREEMENT FLOOR — STATEMENT
FREEZE" for the frozen statements and the scope (accept verdicts only;
T2c untouched).
-/

namespace Setlec.Cached

open Setlec

/-! ## The kit: final-value reasoning for `CheckCM`

`CheckCM = StateT CState (Except CheckError)`.  The floor reads only
the *returned* environment, never the state, so the whole monadic
discipline it needs is: "`P` holds of every value this action can
return".  The bind rule then carries **no** hypothesis on the bound
action — which is what makes the long `do` blocks of the drivers
collapse to their final `pure`. -/

/-- `P` holds of every value the action can return. -/
def Yields {α : Type} (m : CheckCM α) (P : α → Prop) : Prop :=
  ∀ s a s', m s = .ok (a, s') → P a

theorem Yields.mono {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (h : Yields m P) (hPQ : ∀ a, P a → Q a) : Yields m Q :=
  fun s a s' hr => hPQ a (h s a s' hr)

theorem Yields.pure {α : Type} {a : α} {P : α → Prop} (h : P a) :
    Yields (Pure.pure (f := CheckCM) a) P := by
  intro s b s' hr
  simp only [Pure.pure, StateT.pure, Except.pure] at hr
  cases hr; exact h

theorem Yields.ofThrow {α : Type} {e : CheckError} {P : α → Prop} :
    Yields (throw e : CheckCM α) P := by
  intro s a s' hr; cases hr

/-- The bind rule that carries **no** hypothesis on the bound action:
the property is about the returned value only, so the long guard
chains of the drivers collapse to their final `pure`. -/
theorem Yields.bind {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {P : β → Prop} (h : ∀ a, Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm : m s with
  | error e => rw [hs, hm] at hr; cases hr
  | ok v =>
    rw [hs, hm] at hr
    exact h v.1 v.2 b s' hr

/-- The bind rule that *uses* the bound action's own rule. -/
theorem Yields.bind' {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {Q : α → Prop} {P : β → Prop} (hm : Yields m Q)
    (h : ∀ a, Q a → Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm' : m s with
  | error e => rw [hs, hm'] at hr; cases hr
  | ok v =>
    rw [hs, hm'] at hr
    exact h v.1 (hm s v.1 v.2 hm') v.2 b s' hr

/-- Do-notation elaborates its guards through *join points*
(`have __do_jp := …`), so the clause walker needs the `letFun` rule to
step past them. -/
theorem Yields.letFun {α β : Type} {v : β} {f : β → CheckCM α}
    {P : α → Prop} (h : Yields (f v) P) : Yields (letFun v f) P := h

/-- A guard's failure branch, closed without descending into the join
point it calls (which is what keeps the walk linear). -/
theorem Yields.ofThrowBind {α β : Type} {e : CheckError} {f : α → CheckCM β}
    {P : β → Prop} : Yields ((throw e : CheckCM α) >>= f) P := by
  intro s b s' hr; cases hr

/-- A `Decidable` case analysis left behind when a guard's `ite` has
already been delta-expanded (`split` normalises it that way). -/
theorem Yields.ofDecRec {α : Type} {c : Prop} {d : Decidable c}
    {a : ¬c → CheckCM α} {b : c → CheckCM α} {P : α → Prop}
    (ha : ∀ h, Yields (a h) P) (hb : ∀ h, Yields (b h) P) :
    Yields (Decidable.rec (motive := fun _ => CheckCM α) a b d) P := by
  cases d with
  | isFalse h => exact ha h
  | isTrue h => exact hb h

theorem Yields.ofDecCases {α : Type} {c : Prop} {d : Decidable c}
    {a : ¬c → CheckCM α} {b : c → CheckCM α} {P : α → Prop}
    (ha : ∀ h, Yields (a h) P) (hb : ∀ h, Yields (b h) P) :
    Yields (Decidable.casesOn (motive := fun _ => CheckCM α) d a b) P := by
  cases d with
  | isFalse h => exact ha h
  | isTrue h => exact hb h

/-- The clause walker: step past join points and guards to the `pure`
leaves of a driver clause.

**Every `apply` runs `with_reducible`.**  At default transparency the
rules unify *vacuously* — `Bind.bind ?m ?f`, `letFun ?v ?f` and
`pure ?a` all unfold far enough to match an arbitrary action, which
makes the walk loop instead of descending.  At reducible transparency
each rule matches exactly its own head, so the walk is deterministic
and linear in the clause. -/
syntax "yields_step" : tactic
macro_rules
  | `(tactic| yields_step) => `(tactic|
      first
        | with_reducible exact Yields.ofThrowBind
        | ((with_reducible apply Yields.bind); intro)
        | with_reducible apply Yields.letFun
        | with_reducible exact Yields.ofThrow
        | ((with_reducible apply Yields.ofDecRec) <;> intro)
        | ((with_reducible apply Yields.ofDecCases) <;> intro)
        | split)

syntax "yields" : tactic
macro_rules
  | `(tactic| yields) =>
      `(tactic| all_goals (first | (yields_step; yields) | skip))

/-- One join-point step (`with_reducible`, as above). -/
syntax "ylet" : tactic
macro_rules
  | `(tactic| ylet) => `(tactic| with_reducible apply Yields.letFun)

/-- One uninformative bind step (`with_reducible`, as above). -/
syntax "ybind" : tactic
macro_rules
  | `(tactic| ybind) => `(tactic| (with_reducible apply Yields.bind); intro)

/-- The fold rule, with an abstraction `R` of the accumulator: if each
step takes `R b c` to `R b' (g c a)`, the fold takes it to
`R b' (l.foldl g c)`.  This is the shape both drivers' folds have —
the *specification* accumulator `c` is a pure function of the stream,
which is exactly how the two drivers are compared. -/
theorem Yields.foldlM_rel {α β γ : Type} {R : β → γ → Prop}
    {f : β → α → CheckCM β} {g : γ → α → γ}
    (hf : ∀ b a c, R b c → Yields (f b a) (fun b' => R b' (g c a))) :
    ∀ (l : List α) (b : β) (c : γ), R b c →
      Yields (l.foldlM f b) (fun b' => R b' (l.foldl g c))
  | [], b, c, h => by
      simp only [List.foldlM_nil, List.foldl_nil]
      exact Yields.pure h
  | a :: l, b, c, h => by
      simp only [List.foldlM_cons, List.foldl_cons]
      exact Yields.bind' (hf b a c h) fun b' hb' =>
        Yields.foldlM_rel hf l b' (g c a) hb'

/-! ## The install skeleton

Exactly the data of an installed constant that the *drivers'* install
guards read.  Everything a core computes — the annotated type, the
annotated value, `IndCaps`, a rule's right-hand side and its
`plain`/`inert` fire tag — is deliberately **forgotten**: those are the
class-1/2/3 divergent data, and forgetting them is what keeps the floor
free of core reasoning. -/

/-- The install skeleton of a constant. -/
inductive InstallSkel where
  | ax   (n : Name)
  | defn (n : Name)
  | thm  (n : Name)
  | ind  (n : Name)
  | ctor (n : Name) (numParams numFields : Nat)
  | recr (n : Name) (majorIdx rulePrefix : Nat) (ctors : List Name)
  | proj (n : Name)
  deriving DecidableEq, Repr, Inhabited

/-- The declared name of a skeleton. -/
def skelName : InstallSkel → Name
  | .ax n | .defn n | .thm n | .ind n => n
  | .ctor n _ _ | .recr n _ _ _ | .proj n => n

/-- The skeleton of an installed constant. -/
def ciSkel : ConstantInfo → InstallSkel
  | .axiomInfo cv => .ax cv.name
  | .defnInfo cv _ _ => .defn cv.name
  | .thmInfo cv _ => .thm cv.name
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | .recInfo cv mI rP rules => .recr cv.name mI rP (rules.map (·.ctor))
  | .projInfo tbl => .proj (projTableName tbl.structName)

@[simp] theorem skelName_ciSkel (ci : ConstantInfo) :
    skelName (ciSkel ci) = ci.name := by
  cases ci <;> rfl

/-- The skeleton list of an environment (newest first, as `consts`). -/
def envSkels (env : Env) : List InstallSkel := env.consts.map ciSkel

/-- Lookup at the skeleton level. -/
def skFind? (sk : List InstallSkel) (n : Name) : Option InstallSkel :=
  sk.find? (fun s => skelName s == n)

theorem skFind?_map (l : List ConstantInfo) (n : Name) :
    (l.find? (fun c => c.name == n)).map ciSkel = skFind? (l.map ciSkel) n := by
  simp only [skFind?, List.find?_map, Function.comp_def, skelName_ciSkel]

/-! ## The canonical index

Both drivers thread the index by `FEnv.push` from `mkFEnv Env.empty`,
so it is always `mkFEnv` of an environment — and then `FEnv.find?`
*is* `Env.find?` (`mkFEnv_find?`), which is what turns the drivers'
index guards into skeleton-level guards. -/

/-- The index is `mkFEnv` of an environment. -/
def Canon (fe : FEnv) : Prop := ∃ env, fe = mkFEnv env

theorem canon_push {fe : FEnv} (h : Canon fe) (ci : ConstantInfo) :
    Canon (fe.push ci) := by
  obtain ⟨env, rfl⟩ := h
  exact ⟨⟨ci :: env.consts⟩, rfl⟩

theorem canon_find? {fe : FEnv} (h : Canon fe) (n : Name) :
    fe.find? n = fe.env.find? n := by
  obtain ⟨env, rfl⟩ := h
  exact mkFEnv_find? env n

theorem canon_empty : Canon (mkFEnv Env.empty) := ⟨_, rfl⟩

/-- The floor's induction hypothesis: a canonical index whose
environment has the given skeleton list. -/
def SkelIs (fe : FEnv) (sk : List InstallSkel) : Prop :=
  Canon fe ∧ envSkels fe.env = sk

theorem SkelIs.find? {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (fe.find? n).map ciSkel = skFind? sk n := by
  rw [canon_find? h.1 n, ← h.2]
  exact skFind?_map _ n

theorem SkelIs.push {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) : SkelIs (fe.push ci) (ciSkel ci :: sk) :=
  ⟨canon_push h.1 ci, by
    show (ci :: fe.env.consts).map ciSkel = _
    rw [List.map_cons]
    exact congrArg (ciSkel ci :: ·) h.2⟩

/-- Skeleton inversion at a recursor (the one place a driver guard
reads more than a name). -/
theorem recr_of_ciSkel {ci : ConstantInfo} {n : Name} {mI rP : Nat}
    {cs : List Name} (h : ciSkel ci = .recr n mI rP cs) :
    ∃ cv rules, ci = .recInfo cv mI rP rules ∧ cv.name = n ∧
      rules.map (·.ctor) = cs := by
  cases ci <;> simp only [ciSkel] at h <;> cases h <;>
    exact ⟨_, _, rfl, rfl, rfl⟩

/-! ## The specification fold

One pure function per driver clause, computing the skeletons the clause
installs from the declaration and the skeletons already installed.  It
is **total**: on inputs the drivers reject it is junk, and `Yields`
makes junk vacuous. -/

/-- The skeleton `checkIndMemberS`/`checkIndMemberT` installs (junk off
the two accepted member kinds — that branch throws). -/
def indMemberSkel : ConstantInfo → InstallSkel
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | ci => .ax ci.name

/-- The skeleton the recursor group installs for one member (junk off
`.recInfo` — `provisionRecs*` throws there). -/
def recMemberSkel : ConstantInfo → InstallSkel
  | .recInfo cv mI rP rules => .recr cv.name mI rP (rules.map (·.ctor))
  | ci => .ax ci.name

/-- The member fold's specification step. -/
def indMemberSkels (sk : List InstallSkel) (ci : ConstantInfo) :
    List InstallSkel := indMemberSkel ci :: sk

/-- The recursor group's specification step. -/
def recMemberSkels (sk : List InstallSkel) (ci : ConstantInfo) :
    List InstallSkel := recMemberSkel ci :: sk

/-- `installProjFnStep*`'s specification: the model lookup decides. -/
def projFnStepSkels (T ctorName : Name) (nP : Nat)
    (sk : List InstallSkel) (i : Nat) : List InstallSkel :=
  if (skFind? sk (projModelName T i)).isSome then
    .recr (projFnName T i) nP nP [ctorName] :: sk
  else sk

/-! The block's member classifiers.  They are *named* (rather than
inlined `match` lambdas as in the driver) for one reason: the driver's
own lambdas compile to per-declaration matcher constants, so a rewrite
with the block-shape equation `split` hands back needs a rigid head to
aim at.  Each is definitionally the driver's lambda, so the bridge is
`exact`. -/

/-- The inductive-type-former members of a block. -/
def isIndCI : ConstantInfo → Bool
  | .indInfo _ _ => true
  | _ => false

/-- The constructor members of a block. -/
def isCtorCI : ConstantInfo → Bool
  | .ctorInfo _ _ _ => true
  | _ => false

/-- The recursor members of a block. -/
def isRecCI : ConstantInfo → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- The non-recursor members of a block. -/
def isNonRecCI : ConstantInfo → Bool
  | .recInfo _ _ _ _ => false
  | _ => true

/-- The modeled inductive-block clause's specification. -/
def indDeclSkelsModeled (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  let base := (block.filter isRecCI).foldl recMemberSkels
    ((block.filter isNonRecCI).foldl indMemberSkels sk)
  match block.filter isIndCI, block.filter isCtorCI with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      (List.range nF).foldl (projFnStepSkels cvT.name cvC.name nP) base
    else base
  | _, _ => base

/-! ### The direct simple-structure clause (task #175 W4c)

The priority gate `directPartsF?` reads the block (`directPartsCore?`,
pure) and the index only through `constsResolveF` on the raw
constructor domains — skeleton-level lookups — so the dispatch is a
function of the skeleton; the direct install's own install decisions
are the projection bodies' scoping (`directProjBodies`, a function of
the annotated constructor type; task #175 S1) plus freshness checks.
Nothing a core computes enters. -/

/-- `Expr.constsResolve` at the skeleton level (lookups through
`skFind?`). -/
def constsResolveSk (sk : List InstallSkel) : Expr → Bool
  | .bvar _ => true
  | .sort _ => true
  | .lit (.natVal _) =>
    (skFind? sk natName).isSome && (skFind? sk natZeroName).isSome &&
      (skFind? sk natSuccName).isSome
  | .lit (.strVal _) =>
    (skFind? sk natName).isSome && (skFind? sk natZeroName).isSome &&
      (skFind? sk natSuccName).isSome && (skFind? sk stringName).isSome &&
      (skFind? sk stringOfListName).isSome && (skFind? sk listName).isSome &&
      (skFind? sk listNilName).isSome && (skFind? sk listConsName).isSome &&
      (skFind? sk charName).isSome && (skFind? sk charOfNatName).isSome
  | .const n _ => (skFind? sk n).isSome
  | .fvar _ _ ty => constsResolveSk sk ty
  | .app f a => constsResolveSk sk f && constsResolveSk sk a
  | .lam _ ty body _ => constsResolveSk sk ty && constsResolveSk sk body
  | .forallE _ ty body _ => constsResolveSk sk ty && constsResolveSk sk body
  | .letE _ ty val body =>
    constsResolveSk sk ty && constsResolveSk sk val && constsResolveSk sk body
  | .proj s _ e => (skFind? sk s).isSome && constsResolveSk sk e

theorem SkelIs.isSome' {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (fe.find? n).isSome = (skFind? sk n).isSome := by
  rw [← h.find? n, Option.isSome_map]

theorem constsResolveF_skel {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) : ∀ e : Expr, Expr.constsResolveF fe e = constsResolveSk sk e := by
  intro e
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | lit l =>
    cases l <;> simp only [Expr.constsResolveF, constsResolveSk, h.isSome']
  | const n us => simp only [Expr.constsResolveF, constsResolveSk, h.isSome']
  | fvar _ _ ty ih => simp only [Expr.constsResolveF, constsResolveSk, ih]
  | app f a ihf iha =>
    simp only [Expr.constsResolveF, constsResolveSk, ihf, iha]
  | lam _ ty b _ ihty ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, ihty, ihb]
  | forallE _ ty b _ ihty ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, ihty, ihb]
  | letE _ t v b iht ihv ihb =>
    simp only [Expr.constsResolveF, constsResolveSk, iht, ihv, ihb]
  | proj s _ e ihe =>
    simp only [Expr.constsResolveF, constsResolveSk, h.isSome', ihe]

/-- `directNonRecF` at the skeleton level. -/
def directNonRecSk (sk : List InstallSkel) (p : DirectParts) : Bool :=
  match p.cvC.type.stripPis (p.nP + p.nF) with
  | some (cbs, _) => cbs.all fun b => constsResolveSk sk b.2.1
  | none => false

theorem directNonRecF_skel {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (p : DirectParts) :
    directNonRecF fe p = directNonRecSk sk p := by
  unfold directNonRecF directNonRecSk
  cases p.cvC.type.stripPis (p.nP + p.nF) with
  | none => rfl
  | some q => simp only [constsResolveF_skel h]

/-- The direct install's skeleton: the former, the constructor, the
recursor, then the projection table (task #175 S1: one constant per
structure). -/
def directSkels (p : DirectParts) (sk : List InstallSkel) : List InstallSkel :=
  .proj (projTableName p.cvT.name) ::
    .recr p.cvR.name (p.nP + 2) (p.nP + 2) [p.cvC.name] ::
      .ctor p.cvC.name p.nP p.nF :: .ind p.cvT.name :: sk

/-- The inductive-block clause's specification: the priority dispatch
(`directPartsF?`, read at the skeleton) into the direct or the modeled
skeleton. -/
def indDeclSkels (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  match directPartsCore? block with
  | some p =>
    if directNonRecSk sk p then directSkels p sk else indDeclSkelsModeled block sk
  | none => indDeclSkelsModeled block sk

/-- The skeletons one declaration installs. -/
def declCSkels : DeclC → List InstallSkel → List InstallSkel
  | .defnDecl cv _ _, sk => .defn cv.name :: sk
  | .thmDecl cv _, sk => .thm cv.name :: sk
  | .opaqueDecl cv _, sk => .ax cv.name :: sk
  | .axiomDecl cv, sk =>
    if toleratedAxiomNames.contains cv.name then sk else .ax cv.name :: sk
  | .basisDecl kind, sk =>
    kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
  | .indDecl block, sk => indDeclSkels block sk





/-! ## The shared install stages

`checkConstantValF`, `checkMemberValF`, `checkIotaRule(s)F` and
`installBasisDeclF` are the *generic* stages both drivers call (they
take the engine as a `CheckerOps` record).  Their skeleton facts are
proved once. -/

theorem checkConstantValF_name (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv) (fun cvA => cvA.name = cv.name) := by
  unfold checkConstantValF
  yields
  all_goals (apply Yields.pure; rfl)

/-- The recursor stage stores the generated recursor at the stream's
name (task #175 S2). -/
theorem checkDirectRecF_name (ops : CheckerOps CheckCM) (fe : FEnv)
    (p : DirectParts) (cvTa cvCa : ConstantVal) :
    Yields (checkDirectRecF ops fe p cvTa cvCa) (fun r => r.1.name = p.cvR.name) := by
  unfold checkDirectRecF
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkMemberValF_name (ops : CheckerOps CheckCM)
    (blockNames : List Name) (fe : FEnv) (cv : ConstantVal) :
    Yields (checkMemberValF ops blockNames fe cv)
      (fun cvA => cvA.name = cv.name) := by
  unfold checkMemberValF
  refine Yields.bind' (checkConstantValF_name ops fe cv) fun cvA hcvA => ?_
  yields
  all_goals (apply Yields.pure; exact hcvA)

theorem checkIotaRuleF_ctor (mode : CheckMode) (ops : CheckerOps CheckCM)
    (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) :
    Yields (checkIotaRuleF mode ops fe' feSelf f cvName lps tyA mI rP j r)
      (fun r' => r'.ctor = r.ctor) := by
  unfold checkIotaRuleF
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkIotaRulesF_ctors (mode : CheckMode) (ops : CheckerOps CheckCM)
    (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      Yields (checkIotaRulesF mode ops fe' feSelf f cvName lps tyA mI rP j rules)
        (fun rules' => rules'.map (·.ctor) = rules.map (·.ctor))
  | _, [] => by
      unfold checkIotaRulesF
      exact Yields.pure rfl
  | j, r :: rest => by
      unfold checkIotaRulesF
      refine Yields.bind'
        (checkIotaRuleF_ctor mode ops fe' feSelf f cvName lps tyA mI rP j r)
        fun r' hr' => ?_
      refine Yields.bind'
        (checkIotaRulesF_ctors mode ops fe' feSelf f cvName lps tyA mI rP
          (j + 1) rest) fun rest' hrest' => ?_
      apply Yields.pure
      simp [hr', hrest']

theorem installBasisDeclF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => SkelIs fe' (ciSkel ci :: sk)) := by
  unfold installBasisDeclF
  yields
  all_goals (apply Yields.pure; exact h.push ci)

theorem SkelIs.isNone {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (skFind? sk n).isNone = (fe.find? n).isNone := by
  rw [← h.find? n]; cases fe.find? n <;> rfl

theorem SkelIs.isSome {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (n : Name) : (skFind? sk n).isSome = (fe.find? n).isSome := by
  rw [← h.find? n]; cases fe.find? n <;> rfl

/-! ## The cached certified driver's install stages -/

theorem checkConstantValC_name (cfg : CoreCfg) (fe : FEnv)
    (cv : ConstantValC) :
    Yields (checkConstantValC cfg fe cv) (fun p => p.1.name = cv.name) := by
  unfold checkConstantValC
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkDefnValC_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) (hint : ReducibilityHint) :
    Yields (checkDefnValC cfg fe cvA jty value hint)
      (fun fe' => SkelIs fe' (.defn cvA.name :: sk)) := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkThmValC_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) :
    Yields (checkThmValC cfg fe cvA jty value)
      (fun fe' => SkelIs fe' (.thm cvA.name :: sk)) := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkOpaqueValC_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) :
    Yields (checkOpaqueValC cfg fe cvA jty value)
      (fun fe' => SkelIs fe' (.ax cvA.name :: sk)) := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkIndMemberS_skels (cfg : CoreCfg) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) :
    Yields (checkIndMemberS cfg blockNames caps fe ci)
      (fun fe' => SkelIs fe' (indMemberSkel ci :: sk)) := by
  unfold checkIndMemberS
  ybind
  refine Yields.bind'
    (checkMemberValF_name (sharedOpsC cfg fe) blockNames fe ci.toConstantVal)
    fun cvA hcvA => ?_
  cases ci with
  | indInfo cvI capsI =>
    refine Yields.pure ?_
    have := h.push (.indInfo cvA caps)
    simpa [ciSkel, indMemberSkel, hcvA, ConstantInfo.toConstantVal] using this
  | ctorInfo cvI nP nF =>
    refine Yields.pure ?_
    have := h.push (.ctorInfo cvA nP nF)
    simpa [ciSkel, indMemberSkel, hcvA, ConstantInfo.toConstantVal] using this
  | _ => exact Yields.ofThrow

/-- The skeleton a provisioned recursor triple installs. -/
def provSkel (c : ConstantVal × Nat × Nat × List RecRule) : InstallSkel :=
  .recr c.1.name c.2.1 c.2.2.1 (c.2.2.2.map (·.ctor))

theorem provisionRecsS_spec (cfg : CoreCfg) (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) (feAcc : FEnv),
      Yields (provisionRecsS cfg blockNames feAcc recs)
        (fun p => p.2.map provSkel = recs.map recMemberSkel) := by
  intro recs
  induction recs with
  | nil => intro feAcc; unfold provisionRecsS; exact Yields.pure rfl
  | cons ci rest ih =>
    intro feAcc
    unfold provisionRecsS
    cases ci with
    | recInfo cv mI rP rules =>
      ybind
      refine Yields.bind'
        (checkMemberValF_name (sharedOpsC cfg feAcc) blockNames feAcc _)
        fun cvA hcvA => ?_
      refine Yields.bind' (ih _) fun q hq => ?_
      obtain ⟨feSelf, others⟩ := q
      refine Yields.pure ?_
      simp only [List.map_cons, provSkel, recMemberSkel, hcvA,
        ConstantInfo.toConstantVal] at hq ⊢
      rw [hq]
    | _ => exact Yields.ofThrow

theorem foldl_cons_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (b : List β),
      l.foldl (fun acc x => f x :: acc) b = (l.map f).reverse ++ b
  | [], b => rfl
  | a :: l, b => by
      simp [foldl_cons_map f l]

theorem foldl_recMemberSkels (recs : List ConstantInfo)
    (sk : List InstallSkel) :
    recs.foldl recMemberSkels sk = (recs.map recMemberSkel).reverse ++ sk :=
  foldl_cons_map recMemberSkel recs sk

theorem foldl_indMemberSkels (nonrecs : List ConstantInfo)
    (sk : List InstallSkel) :
    nonrecs.foldl indMemberSkels sk = (nonrecs.map indMemberSkel).reverse ++ sk :=
  foldl_cons_map indMemberSkel nonrecs sk

theorem checkIndRecsS_skels (cfg : CoreCfg) (blockNames : List Name)
    {fe₂ : FEnv} {sk : List InstallSkel} (h : SkelIs fe₂ sk)
    (recs : List ConstantInfo) :
    Yields (checkIndRecsS cfg blockNames fe₂ recs)
      (fun fe' => SkelIs fe' (recs.foldl recMemberSkels sk)) := by
  unfold checkIndRecsS
  simp only []
  split
  · rename_i hemp
    have hr : recs = [] := by cases recs <;> simp_all
    subst hr
    exact Yields.pure h
  · split
    · refine Yields.bind'
        (provisionRecsS_spec cfg blockNames recs fe₂) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      have hstep : ∀ (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule)
          (sk' : List InstallSkel), SkelIs acc sk' →
          Yields (do
            let rules' ← checkIotaRulesF cfg.iotaMode (sharedOpsC cfg feSelf) fe₂ feSelf
              (fun n => if blockNames.contains n then n.str "_model" else n)
              c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
            pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
            (fun acc' => SkelIs acc' (provSkel c :: sk')) := by
        intro acc c sk' hacc
        refine Yields.bind'
          (checkIotaRulesF_ctors cfg.iotaMode (sharedOpsC cfg feSelf) fe₂ feSelf _
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2)
          fun rules' hrules' => ?_
        refine Yields.pure ?_
        simpa [ciSkel, provSkel, hrules'] using hacc.push
          (.recInfo c.1 c.2.1 c.2.2.1 rules')
      refine Yields.mono
        (Yields.foldlM_rel (R := SkelIs) hstep checked fe₂ sk h)
        fun fe' hfe' => ?_
      rw [foldl_recMemberSkels]
      simp only [foldl_cons_map] at hfe' 
      simp only [show checked.map provSkel = recs.map recMemberSkel from hq] at hfe'
      exact hfe'
    · exact Yields.ofThrowBind

theorem checkProjFnS_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjFnS cfg fe T ctorName lps nP nF i)
      (fun fe' => SkelIs fe' (.recr (projFnName T i) nP nP [ctorName] :: sk)) := by
  unfold checkProjFnS
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem installProjFnStepS_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (installProjFnStepS cfg T ctorName lps nP nF fe i)
      (fun fe' => SkelIs fe' (projFnStepSkels T ctorName nP sk i)) := by
  unfold installProjFnStepS projFnStepSkels
  rw [h.isSome (projModelName T i)]
  split <;> rename_i hb
  · ybind
    exact checkProjFnS_skels cfg h T ctorName lps nP nF i
  · exact Yields.pure h

/-! ## The direct simple-structure install's skeleton (task #175 W4c)

Every stage's install decision is the block's own or a freshness
check; the stored constants' names are the block's (`checkConstantValF`
keeps the name). -/

theorem checkDirectIndF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ops : CheckerOps CheckCM) (p : DirectParts) :
    Yields (checkDirectIndF ops fe p)
      (fun r => SkelIs r.1 (.ind p.cvT.name :: sk)) := by
  unfold checkDirectIndF
  refine Yields.bind' (checkConstantValF_name ops fe p.cvT) fun cvTa hn => ?_
  yields
  all_goals
    (refine Yields.pure ?_
     have := h.push (.indInfo cvTa (directCaps p))
     simpa [ciSkel, hn] using this)

theorem checkDirectCtorF_skels {fe₀ fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ops : CheckerOps CheckCM) (p : DirectParts)
    (cvTa : ConstantVal) :
    Yields (checkDirectCtorF ops fe₀ fe p cvTa)
      (fun r => SkelIs r.1 (.ctor p.cvC.name p.nP p.nF :: sk)) := by
  unfold checkDirectCtorF
  refine Yields.bind' (checkConstantValF_name ops fe p.cvC) fun cvCa hn => ?_
  yields
  all_goals
    (refine Yields.pure ?_
     have := h.push (.ctorInfo cvCa p.nP p.nF)
     simpa [ciSkel, hn] using this)

theorem checkDirectProjTableF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (cvCa : ConstantVal) :
    Yields (checkDirectProjTableF (m := CheckCM) T C lps nP nF resSort guards
        cvCa fe)
      (fun fe' => SkelIs fe' (.proj (projTableName T) :: sk)) := by
  unfold checkDirectProjTableF
  yields
  all_goals (refine Yields.pure ?_; exact h.push _)

theorem checkDirectStructS_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (p : DirectParts) :
    Yields (checkDirectStructS cfg fe p)
      (fun fe' => SkelIs fe' (directSkels p sk)) := by
  unfold checkDirectStructS
  ybind
  refine Yields.bind' (checkDirectIndF_skels h _ p) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTa⟩ := r₁
  simp only []
  ybind
  refine Yields.bind' (checkDirectCtorF_skels h₁ _ p cvTa) fun r₂ h₂ => ?_
  obtain ⟨fe₂, cvCa, sorts⟩ := r₂
  simp only []
  ybind
  refine Yields.bind' (checkDirectRecF_name _ fe₂ p cvTa cvCa) fun r₃ hnR => ?_
  obtain ⟨cvRa, rhsA⟩ := r₃
  simp only [] at hnR
  try simp only []
  generalize (if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
      RecRuleFire.plain else RecRuleFire.inert) = fire
  have h₃ : SkelIs (fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]))
      (.recr p.cvR.name (p.nP + 2) (p.nP + 2) [p.cvC.name] ::
        .ctor p.cvC.name p.nP p.nF :: .ind p.cvT.name :: sk) := by
    have := h₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩])
    simpa [ciSkel, hnR] using this
  exact checkDirectProjTableF_skels h₃ p.cvT.name p.cvC.name p.cvT.levelParams
    p.nP p.nF p.resSort (directProjGuards cvCa.type p.nP p.nF sorts) cvCa

/-- The members-then-recursors phase, shared by both arms of
`checkIndDeclSF`'s block match. -/
theorem indBase_skels (cfg : CoreCfg) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberS cfg blockNames caps) fe
        checkIndRecsS cfg blockNames fe₂ recs)
      (fun fe' => SkelIs fe'
        (recs.foldl recMemberSkels (nonrecs.foldl indMemberSkels sk))) := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
      (fun acc ci sk' hacc => checkIndMemberS_skels cfg blockNames caps hacc ci)
      nonrecs fe sk h) fun fe₂ h₂ => ?_
  exact checkIndRecsS_skels cfg blockNames h₂ recs

theorem checkIndDeclSF_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (block : List ConstantInfo) :
    Yields (checkIndDeclSF cfg fe block)
      (fun fe' => SkelIs fe' (indDeclSkelsModeled block sk)) := by
  unfold checkIndDeclSF indDeclSkelsModeled
  simp only []
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
    split
    case h_1 cvT capsT cvC nP nF hI hC =>
      have hI' : block.filter isIndCI = [ConstantInfo.indInfo cvT capsT] := hI
      have hC' : block.filter isCtorCI = [ConstantInfo.ctorInfo cvC nP nF] := hC
      rw [hI', hC']
      simp only []
      ybind
      refine Yields.bind'
        (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
          (fun acc ci sk' hacc =>
            checkIndMemberS_skels cfg _ _ hacc ci) _ fe sk h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsS_skels cfg _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          -- the projection phase runs on structure-like blocks only
          -- (task #175 SigmaHom): a decision of the block's own
          -- constructor type, so the skeleton spec computes it
          by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams
              nP nF = true
          · simp only [if_pos hsl]
            exact Yields.foldlM_rel (R := SkelIs)
              (g := projFnStepSkels cvT.name cvC.name nP)
              (fun acc i sk' hacc =>
                installProjFnStepS_skels cfg hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ _ h₃
          · simp only [if_neg hsl]
            exact Yields.pure (P := fun fe' => SkelIs fe' _) h₃
    case h_2 hne =>
      split
      case h_1 cvT capsT cvC nP nF hI hC =>
        exact absurd hC (hne cvT capsT cvC nP nF hI)
      case h_2 => exact indBase_skels cfg _ _ h _ _

/-! ### The tolerated-axiom branch

`toleratedAxiomNames` is exactly `[sorryAx]`, and none of the pinned
axiom guards can fire on it — so at `.axiomDecl` the *push-or-not*
decision is a function of the header name alone, in both drivers. -/

theorem tolerated_eq {n : Name} (ht : toleratedAxiomNames.contains n = true) :
    n = Name.anonymous.str "sorryAx" := by
  simpa [toleratedAxiomNames] using ht

theorem tolerated_not_std (fe : FEnv) (cvA : ConstantVal)
    (ht : toleratedAxiomNames.contains cvA.name = true) :
    stdAxiomOkF fe cvA = false := by
  rw [stdAxiomOkF, if_neg, if_neg] <;> rw [tolerated_eq ht] <;> decide

theorem tolerated_ne_trust {n : Name}
    (ht : toleratedAxiomNames.contains n = true) : n ≠ trustCompilerName := by
  rw [tolerated_eq ht]; decide

theorem tolerated_ne_ofReduce {n : Name}
    (ht : toleratedAxiomNames.contains n = true) :
    ¬(n = ofReduceNatName ∨ n = ofReduceBoolName) := by
  rw [tolerated_eq ht]; decide

theorem tolerated_ne_std {n : Name}
    (ht : toleratedAxiomNames.contains n = true) :
    ¬(n = propextName ∨ n = choiceName) := by
  rw [tolerated_eq ht]; decide

/-! ### The cached certified declaration clause -/

theorem checkDeclSPC_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPC cfg fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPC declCSkels
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_name cfg fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkDefnValC cfg fe cvA jty value hint)
        (fun fe' => SkelIs fe' (.defn cv.name :: sk)) := by
      rw [← hp]; exact checkDefnValC_skels cfg h cvA jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name cfg fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    rw [← hp]
    exact checkThmValC_skels cfg h cvA jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name cfg fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkOpaqueValC cfg fe cvA jty value)
        (fun fe' => SkelIs fe' (.ax cv.name :: sk)) := by
      rw [← hp]; exact checkOpaqueValC_skels cfg h cvA jty value
    refine Yields.bind' key fun fe2 h2 => ?_
    yields
    all_goals (apply Yields.pure; exact h2)
  | axiomDecl cv =>
    simp only []
    refine Yields.bind' (checkConstantValC_name cfg fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    rw [← hp]
    by_cases ht : toleratedAxiomNames.contains cvA.name = true
    · rw [if_pos ht,
        if_neg (by rw [tolerated_not_std fe cvA ht]; exact Bool.false_ne_true),
        if_neg (tolerated_ne_trust ht), if_neg (tolerated_ne_ofReduce ht),
        if_neg (tolerated_ne_std ht), if_pos ht]
      exact Yields.pure h
    · rw [if_neg ht]
      yields
      all_goals first
        | (apply Yields.pure; exact h.push _)
        | exact absurd (by assumption) ht
  | basisDecl kind =>
    have hfold : ∀ (fe' : FEnv) (sk' : List InstallSkel), SkelIs fe' sk' →
        Yields (kind.declsA.foldlM installBasisDeclF fe')
          (fun x => SkelIs x
            (kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk')) :=
      fun fe' sk' h' =>
        Yields.foldlM_rel (R := SkelIs) (g := fun acc ci => ciSkel ci :: acc)
          (fun acc ci sk'' hacc => installBasisDeclF_skels hacc ci)
          kind.declsA fe' sk' h'
    simp only []
    yields
    all_goals exact hfold fe sk h
  | indDecl block =>
    simp only []
    unfold directPartsF? indDeclSkels
    cases directPartsCore? block with
    | none => exact checkIndDeclSF_skels cfg h block
    | some p =>
      simp only []
      rw [directNonRecF_skel h]
      by_cases hnr : directNonRecSk sk p = true
      · simp only [if_pos hnr]
        exact checkDirectStructS_skels cfg h p
      · simp only [if_neg hnr]
        exact checkIndDeclSF_skels cfg h block

theorem checkDeclSPStepC_skels (cfg : CoreCfg) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPStepC cfg fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPStepC
  ybind
  exact checkDeclSPC_skels cfg h pd

/-! ## The floor

The driver is one fold over the converted declaration list at any
config, so the skeleton spec `declCSkels` computes the installed
environment at *every* config.  Hence: whenever two configs both
**accept**, they installed the same constants, in the same order, with
the same skeletons — and in particular the same names and the same
count.

Scope, stated exactly: these are **accept-verdict** statements.  The
trusted config's purpose is to reject less, and the recorded
trusted-mode divergences are decline/accept divergences, untouched
here. -/

theorem Yields.run' {α : Type} {m : CheckCM α} {P : α → Prop}
    (h : Yields m P) {s : CState} {a : α} (hr : StateT.run' m s = .ok a) :
    P a := by
  have hs : StateT.run' m s = (m s).bind (fun p => .ok p.1) := rfl
  rw [hs] at hr
  cases hm : m s with
  | error e => rw [hm] at hr; cases hr
  | ok b => rw [hm] at hr; cases hr; exact h s b.1 b.2 hm

theorem env_of_run {X : CheckM FEnv} {env : Env}
    (h : (do let fe ← X; pure fe.env) = .ok env) :
    ∃ fe, X = .ok fe ∧ fe.env = env := by
  cases hx : X with
  | error e => rw [hx] at h; cases h
  | ok fe => rw [hx] at h; cases h; exact ⟨fe, rfl, rfl⟩

theorem skelIs_empty : SkelIs (mkFEnv Env.empty) [] := ⟨⟨_, rfl⟩, rfl⟩

/-- The declaration-stream specification: the skeletons a stream
installs, newest first. -/
def streamSkels (ds : List DeclC) : List InstallSkel :=
  ds.foldl (fun sk pd => declCSkels pd sk) []

/-! ### The direct-parse entry points (task #171's route) -/

/-- **The skeleton spec, at every config.**  This is the floor's whole
content since the twin's retirement: one driver, one proof. -/
theorem checkDeclsSPCachedD_skels {cfg : CoreCfg} {ds : List DeclC}
    {env : Env} (h : checkDeclsSPCachedD cfg ds = .ok env) :
    envSkels env = streamSkels ds := by
  unfold checkDeclsSPCachedD at h
  obtain ⟨fe, hx, rfl⟩ := env_of_run h
  exact ((Yields.foldlM_rel (R := SkelIs)
    (g := fun sk (pc : DeclC) => declCSkels pc sk)
    (fun b a c hb => checkDeclSPStepC_skels cfg hb a) ds
    (mkFEnv Env.empty) [] skelIs_empty).run' hx).2

/-- **The floor, direct-parse route.**  Whenever the cached driver at
two configs — in particular the trusted (`cfgT`) and the verified
(`cfgP`) config the binary ships — both accept the same stream, the two
installed environments carry the same install skeletons.  Stated for
any two configs: the old two-driver statement is the instance `cfgT` /
`cfgOf mode`. -/
theorem trusted_agrees_P_skels_D {cfgP' cfgT' : CoreCfg} {ds : List DeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD cfgP' ds = .ok envP)
    (hN : checkDeclsSPCachedD cfgT' ds = .ok envN) :
    envSkels envN = envSkels envP :=
  (checkDeclsSPCachedD_skels hN).trans (checkDeclsSPCachedD_skels hP).symm

/-- The census's sentence: the accepted declaration **names** agree. -/
theorem trusted_agrees_P_names_D {cfgP' cfgT' : CoreCfg} {ds : List DeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD cfgP' ds = .ok envP)
    (hN : checkDeclsSPCachedD cfgT' ds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (trusted_agrees_P_skels_D hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

/-- … and so do the accepted declaration **counts**. -/
theorem trusted_agrees_P_count_D {cfgP' cfgT' : CoreCfg} {ds : List DeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD cfgP' ds = .ok envP)
    (hN : checkDeclsSPCachedD cfgT' ds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (trusted_agrees_P_skels_D hP hN)
  simpa [envSkels] using h

/-- The shipped pair, spelled out: `--trusted` and `--verified` agree on
the install skeletons whenever both accept. -/
theorem trusted_agrees_P_skels_shipped {ds : List DeclC} {envP envT : Env}
    (hP : checkDeclsSPCachedD cfgP ds = .ok envP)
    (hT : checkDeclsSPCachedD cfgT ds = .ok envT) :
    envSkels envT = envSkels envP :=
  trusted_agrees_P_skels_D hP hT

end Setlec.Cached
