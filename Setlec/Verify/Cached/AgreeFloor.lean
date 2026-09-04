import Setlec.Cached.ParsedNC
import Setlec.Verify.EnvBound

/-!
# The parity↔P agreement floor (task #172, batch B7)

The *cheap floor* of census part 4 §3: whenever the cached parity
driver (`Setlec/Cached/ParsedNC.lean`) and the cached certified driver
(`Setlec/Cached/ParsedC.lean`) both **accept** a stream, the two
installed environments carry the same constants, in the same order,
with the same install skeletons — and in particular the same names and
the same count.

Nothing here reasons about the cores.  The floor's whole content is
that the two drivers are *the same fold*, and the only work is that
this is not quite true on the nose: the inductive-block clause installs
constants under **environment-dependent guards**
(`installProjFnStep*`'s model lookup; `installProjTemplateStepS`'s
recursor lookup, which reads a stored recursor's `majorIdx`,
`rulePrefix` and its single rule's `ctor`).  So the induction runs on
the *install skeleton* — exactly the data those guards read, and
nothing a core computes — and the names corollary falls out.

Two facts close the remaining branches without core reasoning:

* `directStructsEnabled = false` (`Kernel/Direct.lean`), so
  `directPartsF?` is constantly `none` and the direct simple-structure
  clause is unreachable in **both** drivers (`directPartsF?_eq_none`);
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
  | .projInfo e => .proj (projFnName e.structName e.idx)

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

/-- The skeleton `checkIndMemberS`/`checkIndMemberNC` installs (junk off
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

/-- `installProjTemplateStepS`'s specification: the stored recursor's
`majorIdx`, `rulePrefix` and single rule's `ctor` decide. -/
def projTemplateStepSkels (T ctorName : Name) (nP nF : Nat)
    (sk : List InstallSkel) (i : Nat) : List InstallSkel :=
  if (skFind? sk (projFnName T i)).isNone then
    match skFind? sk (T.str "rec") with
    | some (.recr _ mI rP [c]) =>
      if mI = rP ∧ rP = nP + 2 ∧ c = ctorName ∧ i < nF then
        .proj (projFnName T i) :: sk
      else sk
    | _ => sk
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

/-- The inductive-block clause's specification. -/
def indDeclSkels (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  let base := (block.filter isRecCI).foldl recMemberSkels
    ((block.filter isNonRecCI).foldl indMemberSkels sk)
  match block.filter isIndCI, block.filter isCtorCI with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    (List.range nF).foldl (projTemplateStepSkels cvT.name cvC.name nP nF)
      ((List.range nF).foldl (projFnStepSkels cvT.name cvC.name nP) base)
  | _, _ => base

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





/-! ## The unreachable direct clause

`directStructsEnabled` is a compile-time `false`, so the direct
simple-structure recogniser never fires — in **either** driver.  The
floor proves this rather than assuming it. -/

theorem directPartsF?_eq_none (fe : FEnv) (block : List ConstantInfo) :
    directPartsF? fe block = none := by
  unfold directPartsF?
  cases directPartsCore? block <;> simp [directStructsEnabled]

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

theorem checkConstantValC_name (mode : CheckMode) (fe : FEnv)
    (cv : ConstantValC) :
    Yields (checkConstantValC mode fe cv) (fun p => p.1.name = cv.name) := by
  unfold checkConstantValC
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkDefnValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) (hint : ReducibilityHint) :
    Yields (checkDefnValC mode fe cvA jty value hint)
      (fun fe' => SkelIs fe' (.defn cvA.name :: sk)) := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkThmValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) :
    Yields (checkThmValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.thm cvA.name :: sk)) := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkOpaqueValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : ExprC) :
    Yields (checkOpaqueValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.ax cvA.name :: sk)) := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkIndMemberS_skels (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) :
    Yields (checkIndMemberS mode blockNames caps fe ci)
      (fun fe' => SkelIs fe' (indMemberSkel ci :: sk)) := by
  unfold checkIndMemberS
  ybind
  refine Yields.bind'
    (checkMemberValF_name (sharedOpsC mode fe) blockNames fe ci.toConstantVal)
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

theorem provisionRecsS_spec (mode : CheckMode) (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) (feAcc : FEnv),
      Yields (provisionRecsS mode blockNames feAcc recs)
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
        (checkMemberValF_name (sharedOpsC mode feAcc) blockNames feAcc _)
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

theorem checkIndRecsS_skels (mode : CheckMode) (blockNames : List Name)
    {fe₂ : FEnv} {sk : List InstallSkel} (h : SkelIs fe₂ sk)
    (recs : List ConstantInfo) :
    Yields (checkIndRecsS mode blockNames fe₂ recs)
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
        (provisionRecsS_spec mode blockNames recs fe₂) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      have hstep : ∀ (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule)
          (sk' : List InstallSkel), SkelIs acc sk' →
          Yields (do
            let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
              (fun n => if blockNames.contains n then n.str "_model" else n)
              c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
            pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
            (fun acc' => SkelIs acc' (provSkel c :: sk')) := by
        intro acc c sk' hacc
        refine Yields.bind'
          (checkIotaRulesF_ctors mode (sharedOpsC mode feSelf) fe₂ feSelf _
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

theorem checkProjFnS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjFnS mode fe T ctorName lps nP nF i)
      (fun fe' => SkelIs fe' (.recr (projFnName T i) nP nP [ctorName] :: sk)) := by
  unfold checkProjFnS
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem installProjFnStepS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (installProjFnStepS mode T ctorName lps nP nF fe i)
      (fun fe' => SkelIs fe' (projFnStepSkels T ctorName nP sk i)) := by
  unfold installProjFnStepS projFnStepSkels
  rw [h.isSome (projModelName T i)]
  split <;> rename_i hb
  · ybind
    exact checkProjFnS_skels mode h T ctorName lps nP nF i
  · exact Yields.pure h

theorem installProjTemplateStepS_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    Yields (installProjTemplateStepS T ctorName lps nP nF fe i)
      (fun fe' => SkelIs fe' (projTemplateStepSkels T ctorName nP nF sk i)) := by
  unfold installProjTemplateStepS projTemplateStepSkels
  rw [h.isNone (projFnName T i)]
  split <;> rename_i hb
  · unfold installProjTemplateS
    rw [← h.find? (T.str "rec")]
    cases hfe : fe.find? (T.str "rec") with
    | none => exact Yields.pure h
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules =>
        cases rules with
        | nil => exact Yields.pure h
        | cons r rest =>
          cases rest with
          | cons _ _ => exact Yields.pure h
          | nil =>
            simp only [ciSkel, List.map_cons, List.map_nil, Option.map]
            split <;> rename_i hcond
            · rw [if_pos (And.intro hcond.2.1 (And.intro hcond.2.2.1 hcond.2.2.2))]
              exact Yields.pure (h.push _)
            · rw [if_neg (fun hc => hcond ⟨hb, hc.1, hc.2.1, hc.2.2⟩)]
              exact Yields.pure h
      | _ => exact Yields.pure h
  · exact Yields.pure h

/-- The members-then-recursors phase, shared by both arms of
`checkIndDeclSF`'s block match. -/
theorem indBase_skels (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
        checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => SkelIs fe'
        (recs.foldl recMemberSkels (nonrecs.foldl indMemberSkels sk))) := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
      (fun acc ci sk' hacc => checkIndMemberS_skels mode blockNames caps hacc ci)
      nonrecs fe sk h) fun fe₂ h₂ => ?_
  exact checkIndRecsS_skels mode blockNames h₂ recs

theorem checkIndDeclSF_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (block : List ConstantInfo) :
    Yields (checkIndDeclSF mode fe block)
      (fun fe' => SkelIs fe' (indDeclSkels block sk)) := by
  unfold checkIndDeclSF indDeclSkels
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
            checkIndMemberS_skels mode _ _ hacc ci) _ fe sk h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsS_skels mode _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          refine Yields.bind'
            (Yields.foldlM_rel (R := SkelIs)
              (g := projFnStepSkels cvT.name cvC.name nP)
              (fun acc i sk' hacc =>
                installProjFnStepS_skels mode hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ _ h₃)
            fun fe₄ h₄ => ?_
          exact Yields.foldlM_rel (R := SkelIs)
            (g := projTemplateStepSkels cvT.name cvC.name nP nF)
            (fun acc i sk' hacc =>
              installProjTemplateStepS_skels hacc cvT.name cvC.name
                cvT.levelParams nP nF i) (List.range nF) fe₄ _ h₄
    case h_2 hne =>
      split
      case h_1 cvT capsT cvC nP nF hI hC =>
        exact absurd hC (hne cvT capsT cvC nP nF hI)
      case h_2 => exact indBase_skels mode _ _ h _ _

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

theorem checkDeclSPC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPC mode fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPC declCSkels
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkDefnValC mode fe cvA jty value hint)
        (fun fe' => SkelIs fe' (.defn cv.name :: sk)) := by
      rw [← hp]; exact checkDefnValC_skels mode h cvA jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    rw [← hp]
    exact checkThmValC_skels mode h cvA jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkOpaqueValC mode fe cvA jty value)
        (fun fe' => SkelIs fe' (.ax cv.name :: sk)) := by
      rw [← hp]; exact checkOpaqueValC_skels mode h cvA jty value
    refine Yields.bind' key fun fe2 h2 => ?_
    yields
    all_goals (apply Yields.pure; exact h2)
  | axiomDecl cv =>
    simp only []
    refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
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
    rw [directPartsF?_eq_none]
    exact checkIndDeclSF_skels mode h block

theorem checkDeclSPStepC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPStepC mode fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPStepC
  ybind
  exact checkDeclSPC_skels mode h pd

/-! ## The cached parity driver's install stages

`Setlec/Cached/ParsedNC.lean` duplicates its certified counterpart
definition by definition with `sharedOpsC mode` replaced by
`sharedOpsCNC` and the front-door knot on `coreKnotFNC`.  The
skeleton facts therefore mirror the certified ones line for line, and
land on **the same specification functions** — which is the whole
content of the floor.  Note `installProjTemplateStepS` is *shared*
between the two drivers, so its lemma is reused rather than mirrored. -/

theorem checkConstantValCNC_name (fe : FEnv) (cv : ConstantValC) :
    Yields (checkConstantValCNC fe cv) (fun p => p.1.name = cv.name) := by
  unfold checkConstantValCNC
  yields
  all_goals (apply Yields.pure; rfl)

theorem checkDefnValCNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (cvA : ConstantVal) (jty value : ExprC)
    (hint : ReducibilityHint) :
    Yields (checkDefnValCNC fe cvA jty value hint)
      (fun fe' => SkelIs fe' (.defn cvA.name :: sk)) := by
  unfold checkDefnValCNC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkThmValCNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (cvA : ConstantVal) (jty value : ExprC) :
    Yields (checkThmValCNC fe cvA jty value)
      (fun fe' => SkelIs fe' (.thm cvA.name :: sk)) := by
  unfold checkThmValCNC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkOpaqueValCNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (cvA : ConstantVal) (jty value : ExprC) :
    Yields (checkOpaqueValCNC fe cvA jty value)
      (fun fe' => SkelIs fe' (.ax cvA.name :: sk)) := by
  unfold checkOpaqueValCNC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkIndMemberNC_skels (blockNames : List Name) (caps : IndCaps)
    {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) :
    Yields (checkIndMemberNC blockNames caps fe ci)
      (fun fe' => SkelIs fe' (indMemberSkel ci :: sk)) := by
  unfold checkIndMemberNC
  ybind
  refine Yields.bind'
    (checkMemberValF_name (sharedOpsCNC fe) blockNames fe ci.toConstantVal)
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

theorem provisionRecsNC_spec (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) (feAcc : FEnv),
      Yields (provisionRecsNC blockNames feAcc recs)
        (fun p => p.2.map provSkel = recs.map recMemberSkel) := by
  intro recs
  induction recs with
  | nil => intro feAcc; unfold provisionRecsNC; exact Yields.pure rfl
  | cons ci rest ih =>
    intro feAcc
    unfold provisionRecsNC
    cases ci with
    | recInfo cv mI rP rules =>
      ybind
      refine Yields.bind'
        (checkMemberValF_name (sharedOpsCNC feAcc) blockNames feAcc _)
        fun cvA hcvA => ?_
      refine Yields.bind' (ih _) fun q hq => ?_
      obtain ⟨feSelf, others⟩ := q
      refine Yields.pure ?_
      simp only [List.map_cons, provSkel, recMemberSkel, hcvA,
        ConstantInfo.toConstantVal] at hq ⊢
      rw [hq]
    | _ => exact Yields.ofThrow

theorem checkIndRecsNC_skels (blockNames : List Name) {fe₂ : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe₂ sk) (recs : List ConstantInfo) :
    Yields (checkIndRecsNC blockNames fe₂ recs)
      (fun fe' => SkelIs fe' (recs.foldl recMemberSkels sk)) := by
  unfold checkIndRecsNC
  simp only []
  split
  · rename_i hemp
    have hr : recs = [] := by cases recs <;> simp_all
    subst hr
    exact Yields.pure h
  · split
    · refine Yields.bind'
        (provisionRecsNC_spec blockNames recs fe₂) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      have hstep : ∀ (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule)
          (sk' : List InstallSkel), SkelIs acc sk' →
          Yields (do
            let rules' ← checkIotaRulesF .noModel (sharedOpsCNC feSelf) fe₂ feSelf
              (fun n => if blockNames.contains n then n.str "_model" else n)
              c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
            pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
            (fun acc' => SkelIs acc' (provSkel c :: sk')) := by
        intro acc c sk' hacc
        refine Yields.bind'
          (checkIotaRulesF_ctors .noModel (sharedOpsCNC feSelf) fe₂ feSelf _
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

theorem checkProjFnNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjFnNC fe T ctorName lps nP nF i)
      (fun fe' => SkelIs fe' (.recr (projFnName T i) nP nP [ctorName] :: sk)) := by
  unfold checkProjFnNC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem installProjFnStepNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    Yields (installProjFnStepNC T ctorName lps nP nF fe i)
      (fun fe' => SkelIs fe' (projFnStepSkels T ctorName nP sk i)) := by
  unfold installProjFnStepNC projFnStepSkels
  rw [h.isSome (projModelName T i)]
  split <;> rename_i hb
  · ybind
    exact checkProjFnNC_skels h T ctorName lps nP nF i
  · exact Yields.pure h

theorem indBaseNC_skels (blockNames : List Name) (caps : IndCaps)
    {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberNC blockNames caps) fe
        checkIndRecsNC blockNames fe₂ recs)
      (fun fe' => SkelIs fe'
        (recs.foldl recMemberSkels (nonrecs.foldl indMemberSkels sk))) := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := SkelIs) (g := indMemberSkels)
      (fun acc ci sk' hacc => checkIndMemberNC_skels blockNames caps hacc ci)
      nonrecs fe sk h) fun fe₂ h₂ => ?_
  exact checkIndRecsNC_skels blockNames h₂ recs

theorem checkIndDeclNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (block : List ConstantInfo) :
    Yields (checkIndDeclNC fe block)
      (fun fe' => SkelIs fe' (indDeclSkels block sk)) := by
  unfold checkIndDeclNC indDeclSkels
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
            checkIndMemberNC_skels _ _ hacc ci) _ fe sk h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsNC_skels _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          refine Yields.bind'
            (Yields.foldlM_rel (R := SkelIs)
              (g := projFnStepSkels cvT.name cvC.name nP)
              (fun acc i sk' hacc =>
                installProjFnStepNC_skels hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ _ h₃)
            fun fe₄ h₄ => ?_
          exact Yields.foldlM_rel (R := SkelIs)
            (g := projTemplateStepSkels cvT.name cvC.name nP nF)
            (fun acc i sk' hacc =>
              installProjTemplateStepS_skels hacc cvT.name cvC.name
                cvT.levelParams nP nF i) (List.range nF) fe₄ _ h₄
    case h_2 hne =>
      split
      case h_1 cvT capsT cvC nP nF hI hC =>
        exact absurd hC (hne cvT capsT cvC nP nF hI)
      case h_2 => exact indBaseNC_skels _ _ h _ _

theorem checkDeclSPCNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPCNC fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPCNC declCSkels
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValCNC_name fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkDefnValCNC fe cvA jty value hint)
        (fun fe' => SkelIs fe' (.defn cv.name :: sk)) := by
      rw [← hp]; exact checkDefnValCNC_skels h cvA jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValCNC_name fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    rw [← hp]
    exact checkThmValCNC_skels h cvA jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValCNC_name fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    simp only []
    have key : Yields (checkOpaqueValCNC fe cvA jty value)
        (fun fe' => SkelIs fe' (.ax cv.name :: sk)) := by
      rw [← hp]; exact checkOpaqueValCNC_skels h cvA jty value
    refine Yields.bind' key fun fe2 h2 => ?_
    yields
    all_goals (apply Yields.pure; exact h2)
  | axiomDecl cv =>
    simp only []
    refine Yields.bind' (checkConstantValCNC_name fe cv) fun p hp => ?_
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
    rw [directPartsF?_eq_none]
    exact checkIndDeclNC_skels h block

theorem checkDeclSPStepCNC_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (pd : DeclC) :
    Yields (checkDeclSPStepCNC fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclSPStepCNC
  ybind
  ybind
  exact checkDeclSPCNC_skels h pd

/-! ## The floor

Both drivers are the same fold over the same converted declaration
list, so the skeleton spec `declCSkels` computes *both* installed
environments.  Hence: whenever both **accept**, they installed the same
constants, in the same order, with the same skeletons — and in
particular the same names and the same count.

Scope, stated exactly: these are **accept-verdict** statements.  The
parity core's purpose is to reject less, and the recorded no-model
divergences are decline/accept divergences, untouched here. -/

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

theorem streamSkels_map (ds : List WDeclC) :
    streamSkels (ds.map (·.1))
      = ds.foldl (fun sk pc => declCSkels pc.1 sk) [] := by
  unfold streamSkels
  rw [List.foldl_map]

/-! ### The direct-parse entry points (task #171's route) -/

theorem checkDeclsSPCachedD_skels {mode : CheckMode} {ds : List WDeclC}
    {env : Env} (h : checkDeclsSPCachedD mode ds = .ok env) :
    envSkels env = streamSkels (ds.map (·.1)) := by
  unfold checkDeclsSPCachedD at h
  obtain ⟨fe, hx, rfl⟩ := env_of_run h
  have := (Yields.foldlM_rel (R := SkelIs)
    (g := fun sk (pc : WDeclC) => declCSkels pc.1 sk)
    (fun b a c hb => checkDeclSPStepC_skels mode hb a.1) ds
    (mkFEnv Env.empty) [] skelIs_empty).run' hx
  exact this.2.trans (streamSkels_map ds).symm

theorem checkDeclsSPCachedDNM_skels {ds : List WDeclC} {env : Env}
    (h : checkDeclsSPCachedDNM ds = .ok env) :
    envSkels env = streamSkels (ds.map (·.1)) := by
  unfold checkDeclsSPCachedDNM at h
  obtain ⟨fe, hx, rfl⟩ := env_of_run h
  have := (Yields.foldlM_rel (R := SkelIs)
    (g := fun sk (pc : WDeclC) => declCSkels pc.1 sk)
    (fun b a c hb => checkDeclSPStepCNC_skels hb a.1) ds
    (mkFEnv Env.empty) [] skelIs_empty).run' hx
  exact this.2.trans (streamSkels_map ds).symm

/-- **The floor, direct-parse route.**  Whenever the cached parity
driver and the cached certified driver both accept the same stream,
the two installed environments carry the same install skeletons. -/
theorem parity_agrees_P_skels_D {mode : CheckMode} {ds : List WDeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD mode ds = .ok envP)
    (hN : checkDeclsSPCachedDNM ds = .ok envN) :
    envSkels envN = envSkels envP :=
  (checkDeclsSPCachedDNM_skels hN).trans (checkDeclsSPCachedD_skels hP).symm

/-- The census's sentence: the accepted declaration **names** agree. -/
theorem parity_agrees_P_names_D {mode : CheckMode} {ds : List WDeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD mode ds = .ok envP)
    (hN : checkDeclsSPCachedDNM ds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (parity_agrees_P_skels_D hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

/-- … and so do the accepted declaration **counts**. -/
theorem parity_agrees_P_count_D {mode : CheckMode} {ds : List WDeclC}
    {envP envN : Env}
    (hP : checkDeclsSPCachedD mode ds = .ok envP)
    (hN : checkDeclsSPCachedDNM ds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (parity_agrees_P_skels_D hP hN)
  simpa [envSkels] using h

/-! ### The arena-parse entry points

The two drivers run `declsCOfP` — the same conversion, on the same
arena — before the fold, so they fold the same `DeclC` list. -/

theorem checkDeclsSPCached_skels {mode : CheckMode} {st : WFStore}
    {pds : List DeclP} {ds : List DeclC} {env : Env}
    (hds : declsCOfP st.raw {} pds = .ok ds)
    (h : checkDeclsSPCached mode st pds = .ok env) :
    envSkels env = streamSkels ds := by
  unfold checkDeclsSPCached at h
  rw [hds] at h
  obtain ⟨fe, hx, rfl⟩ := env_of_run h
  exact ((Yields.foldlM_rel (R := SkelIs)
    (g := fun sk (pd : DeclC) => declCSkels pd sk)
    (fun b a c hb => checkDeclSPStepC_skels mode hb a) ds
    (mkFEnv Env.empty) [] skelIs_empty).run' hx).2

theorem checkDeclsSPCachedNM_skels {st : WFStore} {pds : List DeclP}
    {ds : List DeclC} {env : Env}
    (hds : declsCOfP st.raw {} pds = .ok ds)
    (h : checkDeclsSPCachedNM st pds = .ok env) :
    envSkels env = streamSkels ds := by
  unfold checkDeclsSPCachedNM at h
  rw [hds] at h
  obtain ⟨fe, hx, rfl⟩ := env_of_run h
  exact ((Yields.foldlM_rel (R := SkelIs)
    (g := fun sk (pd : DeclC) => declCSkels pd sk)
    (fun b a c hb => checkDeclSPStepCNC_skels hb a) ds
    (mkFEnv Env.empty) [] skelIs_empty).run' hx).2

/-- **The floor, arena-parse route.** -/
theorem parity_agrees_P_skels {mode : CheckMode} {st : WFStore}
    {pds : List DeclP} {envP envN : Env}
    (hP : checkDeclsSPCached mode st pds = .ok envP)
    (hN : checkDeclsSPCachedNM st pds = .ok envN) :
    envSkels envN = envSkels envP := by
  cases hds : declsCOfP st.raw {} pds with
  | error e =>
    unfold checkDeclsSPCached at hP
    rw [hds] at hP
    cases hP
  | ok ds =>
    exact (checkDeclsSPCachedNM_skels hds hN).trans
      (checkDeclsSPCached_skels hds hP).symm

theorem parity_agrees_P_names {mode : CheckMode} {st : WFStore}
    {pds : List DeclP} {envP envN : Env}
    (hP : checkDeclsSPCached mode st pds = .ok envP)
    (hN : checkDeclsSPCachedNM st pds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (parity_agrees_P_skels hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

theorem parity_agrees_P_count {mode : CheckMode} {st : WFStore}
    {pds : List DeclP} {envP envN : Env}
    (hP : checkDeclsSPCached mode st pds = .ok envP)
    (hN : checkDeclsSPCachedNM st pds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (parity_agrees_P_skels hP hN)
  simpa [envSkels] using h

end Setlec.Cached
