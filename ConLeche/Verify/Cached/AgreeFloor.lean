module

public import ConLeche.Cached.Installed
import ConLeche.Verify.EnvBound

public section

/-!
# The trusted↔P agreement floor (task #172, batch B7; restated at the
twin's retirement, 2026-09-06)

The *cheap floor* of census part 4 §3: whenever the cached driver
(`ConLeche/Cached/ParsedC.lean`) at the trusted config and at the
verified config both **accept** a stream, the two installed
environments carry the same constants, in the same order, with the same
install skeletons — and in particular the same names and the same
count.

**What the retirement did to the statement.**  Until 2026-09-06 the
trusted lane was a separate driver (`checkDeclsT`,
`ConLeche/Cached/ParsedT.lean`) over a hand-written cert-skipping core,
and the floor had to prove the skeleton spec for *both* drivers, stage
by stage — the second half of this file was a clause-by-clause
duplicate of the first.  Now there is one driver, `checkDecls
mode`, and the floor is the skeleton spec proved **once, for every
`mode : CheckMode`** (`checkDecls_skels`); the agreement of
two modes is its two instances glued by `Eq.trans`.  That is strictly
stronger than the frozen B7 statement: the old theorem is the new one
at `μP := .verified`, `μT := .trusted`, and the new one covers any two
modes (task #185: "any two configs" until the configuration record
retired).  The certification-only work the trusted mode omits
(`mode.verifiedChecks`, group A, and `mode.certs`) is invisible to the
skeleton by construction — the spec forgets everything a core computes
— which is exactly why the proof is mode-generic without a case
split.

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
  (`structPartsF?`) reads the index only through name lookups
  (`structNonRecF_skel`), so it runs on the skeleton too;
* at `.axiomDecl` the push-or-not decision is a function of the header
  name alone — the `sorryAx` record installs nothing in
  both drivers, and `stdAxiomOkF` is `false` off `propext`/`choice`, so
  every other accepted axiom installs exactly one `.axiomInfo`.

See DESIGN.md, "TASK #172 — BATCH B7: THE AGREEMENT FLOOR — STATEMENT
FREEZE" for the frozen statements and the scope (accept verdicts only;
T2c untouched).
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## The kit: final-value reasoning for `CheckCM`

`CheckCM = StateT CState (Except CheckError)`.  The floor reads only
the *returned* environment, never the state, so the whole monadic
discipline it needs is: "`P` holds of every value this action can
return".  The bind rule then carries **no** hypothesis on the bound
action — which is what makes the long `do` blocks of the drivers
collapse to their final `pure`. -/

/-- `P` holds of every value the action can return. -/
@[expose] def Yields {α : Type} (m : CheckCM α) (P : α → Prop) : Prop :=
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
  | recr (n : Name) (majorIdx rulePrefix : Nat)
  | proj (n : Name)
  deriving DecidableEq, Repr, Inhabited

/-- The declared name of a skeleton. -/
def skelName : InstallSkel → Name
  | .ax n | .defn n | .thm n | .ind n => n
  | .ctor n _ _ | .recr n _ _ | .proj n => n

/-- The skeleton of an installed constant. -/
def ciSkel : ConstantInfo → InstallSkel
  | .axiomInfo cv => .ax cv.name
  | .defnInfo cv _ _ => .defn cv.name
  | .thmInfo cv _ => .thm cv.name
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | .recInfo cv mI rP _ => .recr cv.name mI rP
  | .projInfo tbl => .proj (projTableName tbl.structName)

@[simp] theorem skelName_ciSkel (ci : ConstantInfo) :
    skelName (ciSkel ci) = ci.name := by
  cases ci <;> rfl

/-- The skeleton list of an environment (newest first, as `consts`). -/
def envSkels (env : Env) : List InstallSkel := env.consts.map ciSkel

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

theorem canon_empty : Canon (mkFEnv Env.empty) := ⟨_, rfl⟩

/-- The floor's induction hypothesis: a canonical index whose
environment has the given skeleton list. -/
def SkelIs (fe : FEnv) (sk : List InstallSkel) : Prop :=
  Canon fe ∧ envSkels fe.env = sk

theorem SkelIs.push {fe : FEnv} {sk : List InstallSkel} (h : SkelIs fe sk)
    (ci : ConstantInfo) : SkelIs (fe.push ci) (ciSkel ci :: sk) :=
  ⟨canon_push h.1 ci, by
    show (ci :: fe.env.consts).map ciSkel = _
    rw [List.map_cons]
    exact congrArg (ciSkel ci :: ·) h.2⟩

/-! ## The specification fold

One pure function per driver clause, computing the skeletons the clause
installs from the declaration and the skeletons already installed.  It
is **total**: on inputs the drivers reject it is junk, and `Yields`
makes junk vacuous. -/

/-! The block's member classifiers.  They are *named* (rather than
inlined `match` lambdas as in the driver) for one reason: the driver's
own lambdas compile to per-declaration matcher constants, so a rewrite
with the block-shape equation `split` hands back needs a rigid head to
aim at.  Each is definitionally the driver's lambda, so the bridge is
`exact`. -/

/-! ### The direct sum clause (task #175 sum-types)

The second gate reads the index exactly as the first does — `constsResolveF`
on the raw constructor domains — and its install decisions are the block's
own; only the *number* of constants it pushes varies with the block (one
per constructor). -/

/-- The constructors' conses at the skeleton level (the first
constructor deepest, as `consSumCtors`). -/
def sumCtorSkels (nP : Nat) (cs : List (Name × Nat)) (sk : List InstallSkel) :
    List InstallSkel :=
  cs.foldl (fun acc c => .ctor c.1 nP c.2 :: acc) sk

/-! ### The uniform route's skeleton (milestone M1)

The INSTALL ORDER at k members (the floor's agreement is positional):
the k type formers, then every constructor of every member in block
order, then the k recursors, then one projection table per
structure-like member. -/

/-- The k type formers (member 0 deepest, as `consBlockInds`). -/
def blockIndSkels : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk => blockIndSkels rest (.ind ms.cvT.name :: sk)

/-- Every member's constructors, in block order. -/
def blockCtorSkels (nP : Nat) : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk =>
    blockCtorSkels nP rest (sumCtorSkels nP (ms.ctors.map fun c => (c.1.name, c.2)) sk)

/-- The block's recursors, each with its TARGET member's rules and its
OWN argument sums (`BlockShape.rulePrefixAt`/`recTgtAt`: the recursor
record's — the install conses exactly these). -/
def blockRecSkels (q : BlockShape) : Nat → List RecShape → List InstallSkel →
    List InstallSkel
  | _, [], sk => sk
  | r, rc :: rest, sk =>
    blockRecSkels q (r + 1) rest
      (.recr rc.cvR.name (q.majorIdxAt r) (q.rulePrefixAt r) :: sk)

/-- The projection table of every structure-like member. -/
def blockTableSkels : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk =>
    blockTableSkels rest
      (if ms.ctors.length == 1 && ms.nIdx == 0 then
        .proj (projTableName ms.cvT.name) :: sk else sk)

/-- The uniform install's skeleton. -/
def blockSkels (p : BlockParts) (sk : List InstallSkel) : List InstallSkel :=
  blockTableSkels p.members
    (blockRecSkels p.toBlockShape 0 p.recs
      (blockCtorSkels p.nP p.members (blockIndSkels p.members sk)))

/-- The inductive dispatch: the uniform route (the k-ary skeleton); a
block the recogniser does not read installs nothing (it declines).  The
RECOGNISER decides, and nothing else (task #219), so the skeleton list
needs no environment at all. -/
def indDeclSkels (nP : Nat) (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  match blockParts? nP block with
  | some p => blockSkels p sk
  | none => sk

/-- The skeletons one declaration installs. -/
def declCSkels : Declaration → List InstallSkel → List InstallSkel
  | .defnDecl cv _ _, sk => .defn cv.name :: sk
  | .thmDecl cv _, sk => .thm cv.name :: sk
  | .opaqueDecl cv _, sk => .ax cv.name :: sk
  | .axiomDecl cv, sk =>
    -- task #293: `Quot.sound` is the pinned quotient block's own
    -- record and installs nothing of its own, like `sorryAx`
    if cv.name = sorryAxName ∨ cv.name = quotSoundName then sk
    else .ax cv.name :: sk
  | .basisDecl kind, sk =>
    kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
  -- task #293: the quotient package's `type` record installs the
  -- pinned block; its other records are members of that block
  | .quotDecl k _, sk =>
    match k with
    | .type => BasisKind.quotK.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | _ => sk
  | .indDecl block nP, sk =>
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin
    match basisPinHit block with
    | some kind => kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | none => indDeclSkels nP block sk

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

theorem installBasisDeclF_skels {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => SkelIs fe' (ciSkel ci :: sk)) := by
  unfold installBasisDeclF
  yields
  all_goals (apply Yields.pure; exact h.push ci)

/-! ## The cached certified driver's install stages -/

theorem checkConstantValC_name (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValC mode fe cv) (fun p => p.1.name = cv.name) := by
  unfold checkConstantValC
  yields
  all_goals (apply Yields.pure; rfl)

theorem annotConstantValC_fresh (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (annotConstantValC mode fe cv)
      (fun p => p.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold annotConstantValC
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

theorem annotValueC_fresh (mode : CheckMode) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (record : Bool) :
    Yields (annotValueC mode fe cv value record)
      (fun r => r.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold annotValueC
  ybind
  refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hp => ?_
  obtain ⟨cvA, jty⟩ := p
  ybind
  exact Yields.pure hp

theorem checkDefnValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) (hint : ReducibilityHint) :
    Yields (checkDefnValC mode fe cvA jty value hint)
      (fun fe' => SkelIs fe' (.defn cvA.name :: sk)) := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkThmValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) :
    Yields (checkThmValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.thm cvA.name :: sk)) := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

theorem checkOpaqueValC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (cvA : ConstantVal)
    (jty value : Expr) :
    Yields (checkOpaqueValC mode fe cvA jty value)
      (fun fe' => SkelIs fe' (.ax cvA.name :: sk)) := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push _)

/-! ## The direct simple-structure install's skeleton (task #175 W4c)

Every stage's install decision is the block's own or a freshness
check; the stored constants' names are the block's (`checkConstantValF`
keeps the name). -/

theorem checkStructProjTableF_skels {w : StructWalkers} {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa fe)
      (fun fe' => SkelIs fe' (.proj (projTableName T) :: sk)) := by
  unfold checkStructProjTableF
  yields
  all_goals (refine Yields.pure ?_; exact h.push _)

/-! ## The direct sum install's skeleton (task #175 sum-types, indexed)

Same shape as the structure route's, with the constructor stage run
over a list: the stored constructors' names and field counts are the
block's (`checkConstantValF` keeps the name, the stage keeps the
count), and the generated recursor's rules are one per constructor, so
the rule-name list the skeleton records is the block's own. -/

/-- The former's telescope stage keeps the block's name (task #195):
the checked constant is the input or a re-check at the block's own
header. -/
theorem checkSumTeleF_name (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    Yields (checkSumTeleF ops fe cv n cvTa₀)
      (fun r => r.1.name = cvTa₀.name ∨ r.1.name = cv.name) := by
  unfold checkSumTeleF
  split
  · exact Yields.pure (Or.inl rfl)
  · ybind
    refine Yields.bind' (checkConstantValF_name ops fe _) fun cvTa hn => ?_
    exact Yields.pure (Or.inr hn)

theorem checkSumCtorF_name (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_name ops fe cvC) fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact hn)

/-- The constructor list's names and field counts are the block's, and
the field-sort lists come one per constructor (task #210 Part A). -/
theorem checkSumCtorsF_names (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun r => r.1.map (fun c => (c.1.name, c.2))
          = cs.map (fun c => (c.1.name, c.2)) ∧ r.2.length = cs.length)
  | [] => Yields.pure ⟨rfl, rfl⟩
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_name ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun q hn => ?_
    obtain ⟨cvCa, sorts⟩ := q
    refine Yields.bind' (checkSumCtorsF_names ops fe₀ fe T lps nP nIdx rs isProp
      large cvTa cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    have hn' : cvCa.name = c.1.name := hn
    exact Yields.pure ⟨by simp [hn', hrest.1], by simpa using hrest.2⟩

/-- The constructors' conses at the skeleton level. -/
theorem consSumCtorsF_skels (nP : Nat) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {fe : FEnv} {sk : List InstallSkel},
      SkelIs fe sk →
      SkelIs (consSumCtorsF nP ctorsA fe)
        (sumCtorSkels nP (ctorsA.map fun c => (c.1.name, c.2)) sk)
  | [], _, _, h => h
  | c :: cs, fe, sk, h => by
    have hstep := consSumCtorsF_skels nP (ctorsA := cs)
      (h.push (.ctorInfo c.1 nP c.2))
    simpa [consSumCtorsF, sumCtorSkels, ciSkel] using hstep

/-- The stored rules are one per constructor, in constructor order. -/
theorem sumRules_map_ctor (find? : Name → Option ConstantInfo)
    (recName : Name) (nP mI rP : Nat) (recTy : Expr) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr},
      rhss.length = ctorsA.length →
      (sumRules find? recName nP mI rP recTy ctorsA rhss).map (·.ctor)
        = ctorsA.map (·.1.name)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, rhs :: rhss, h => by
    simp only [sumRules, List.map_cons, List.cons.injEq, true_and,
      recRuleBits_ctor]
    exact sumRules_map_ctor find? recName nP mI rP recTy (by simpa using h)

/-- The rules the uniform route stores at a major are one per
constructor of the major, in its order (the firing mode aside). -/
theorem tgtStoredRules_map_ctor (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (cv : ConstantVal) (mI rP : Nat) (M : TargetMajor) {rhss : List Expr}
    (h : rhss.length = M.ctors.length) :
    (tgtStoredRules find? resolves cv mI rP M rhss).map (·.ctor) = M.ctors.map (·.1.name) := by
  unfold tgtStoredRules
  cases M.member with
  | none => simp only [List.map_map, Function.comp_def]; exact sumRules_map_ctor _ _ _ _ _ _ h
  | some _ => exact sumRules_map_ctor _ _ _ _ _ _ h

/-! ### The direct recursive install (task #188) -/

theorem checkNativeRulesF_len {w : StructWalkers} (fe : FEnv)
    (rlps : List Name) (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) :
    ∀ (k j : Nat),
      Yields (checkNativeRulesF (m := CheckCM) w fe rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j)
        (fun rhss => rhss.length = k)
  | 0, _ => Yields.pure rfl
  | k + 1, j => by
    unfold checkNativeRulesF
    refine Yields.bind fun rhs => ?_
    try ylet
    split
    case isTrue =>
      refine Yields.bind' (checkNativeRulesF_len fe rlps T lps elim large
        nP nIdx tty ctors recC rlvls k (j + 1)) fun rest hrest => ?_
      exact Yields.pure (by simp [hrest])
    case isFalse => exact Yields.ofThrowBind

/-! ### Freshness of the stored names (moved from `PushChain.lean`,
lane FLIP1, so that the uniform route's skeleton and chain lemmas share
them) -/

theorem checkConstantValF_fresh (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv)
      (fun cvA => cvA.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkConstantValF
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

theorem checkSumCtorF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name ∧ fe.find? cvC.name = none) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_fresh ops fe cvC) fun cvCa h₀ => ?_
  obtain ⟨hn, hfr⟩ := h₀
  yields
  all_goals (apply Yields.pure; exact ⟨hn, hfr⟩)

theorem checkSumCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun r => r.1.map (·.1.name) = cs.map (·.1.name) ∧
          ∀ c ∈ r.1, fe.find? c.1.name = none)
  | [] => Yields.pure ⟨rfl, fun _ hc => nomatch hc⟩
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun q hq => ?_
    obtain ⟨cvCa, sorts⟩ := q
    obtain ⟨hn, hfr⟩ := hq
    refine Yields.bind' (checkSumCtorsF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large cvTa cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    obtain ⟨hrest, hfrs⟩ := hrest
    have hn' : cvCa.name = c.1.name := hn
    have hrest' : rest.map (·.1.name) = cs.map (·.1.name) := hrest
    refine Yields.pure ⟨by simp [hn', hrest'], ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · show fe.find? cvCa.name = none
      rw [hn]; exact hfr
    · exact hfrs d hd

/-! ### The uniform route at k members (lane FLIP1)

The k-ary install's skeleton is `blockSkels` of the RECOGNISED record,
read off the stages' names and counts: the formers keep their names,
the constructors theirs and their field counts, every recursor its
record's name with its TARGET member's constructors as its rules, and
a structure-like member its table.  The recursor stage is read at its
CHECK. -/

theorem Yields.and {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (hP : Yields m P) (hQ : Yields m Q) : Yields m (fun a => P a ∧ Q a) :=
  fun s a s' hr => ⟨hP s a s' hr, hQ s a s' hr⟩

theorem checkBlockTeleF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (nP : Nat)
    (ms : MemberShape) :
    Yields (checkBlockTeleF ops fe nP ms)
      (fun r => r.1.name = ms.cvT.name ∧ fe.find? ms.cvT.name = none) := by
  unfold checkBlockTeleF
  refine Yields.bind' (checkConstantValF_fresh ops fe ms.cvT) fun cvTa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (checkSumTeleF_name ops fe ms.cvT _ cvTa₀) fun r hn => ?_
  obtain ⟨cvTa, s⟩ := r
  have hn' : cvTa.name = ms.cvT.name := by
    rcases hn with h1 | h1
    · exact h1.trans hn₀
    · exact h1
  yields
  all_goals exact Yields.pure ⟨hn', hfr⟩

theorem checkBlockTelesF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (nP : Nat) :
    ∀ mss : List MemberShape,
      Yields (checkBlockTelesF ops fe nP mss)
        (fun rs => rs.map (·.1.name) = mss.map (·.cvT.name) ∧
          ∀ ms ∈ mss, fe.find? ms.cvT.name = none)
  | [] => Yields.pure ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest => by
    unfold checkBlockTelesF
    refine Yields.bind' (checkBlockTeleF_fresh ops fe nP ms) fun r hr => ?_
    refine Yields.bind' (checkBlockTelesF_fresh ops fe nP rest) fun rs hrs => ?_
    refine Yields.pure ⟨by simp [hr.1, hrs.1], ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hr.2
    · exact hrs.2 m hm

/-- The formers' stage: the record the shape completed (the sort read),
the environment the formers' conses build, the formers' names, and
their freshness at the block's own index. -/
theorem checkBlockIndsF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockParts)
    (isRec : Bool) :
    Yields (checkBlockIndsF ops fe p isRec)
      (fun r => (∃ s, r.2.2 = p.toBlockShape.withSort s) ∧
        r.1 = consBlockIndsF r.2.2 isRec r.2.1 0 fe ∧
        r.2.1.map (·.name) = p.members.map (·.cvT.name) ∧
        ∀ ms ∈ p.members, fe.find? ms.cvT.name = none) := by
  unfold checkBlockIndsF
  split
  · exact Yields.ofThrow
  · next ms0 rest hm =>
    refine Yields.bind' (checkBlockTeleF_fresh ops fe p.nP ms0) fun r0 h0 => ?_
    obtain ⟨cvTa0, s0⟩ := r0
    refine Yields.bind' (checkBlockTelesF_fresh ops fe p.nP rest) fun cvs hcvs => ?_
    refine Yields.bind fun _ => ?_
    refine Yields.pure ⟨⟨s0, rfl⟩, rfl, ?_, ?_⟩
    · rw [hm]
      simp only [List.map_cons, List.map_map, List.cons.injEq]
      exact ⟨h0.1, by rw [← hcvs.1]; rfl⟩
    · rw [hm]
      intro m hmm
      rcases List.mem_cons.mp hmm with rfl | hmm
      · exact h0.2
      · exact hcvs.2 m hmm

/-- The formers' conses at the skeleton level (member 0 deepest). -/
theorem consBlockIndsF_skels (p₁ : BlockShape) (isRec : Bool) :
    ∀ {cvTas : List ConstantVal} {mss : List MemberShape} {i : Nat} {fe : FEnv}
      {sk : List InstallSkel},
      cvTas.map (·.name) = mss.map (·.cvT.name) → SkelIs fe sk →
      SkelIs (consBlockIndsF p₁ isRec cvTas i fe) (blockIndSkels mss sk)
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, _, hn, _ => by simp at hn
  | _ :: _, [], _, _, _, hn, _ => by simp at hn
  | cvTa :: rest, ms :: mss, i, fe, sk, hn, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    have hstep := consBlockIndsF_skels p₁ isRec (i := i + 1) hn.2
      (h.push (.indInfo cvTa (blockCapsAt p₁ i isRec)))
    simpa [consBlockIndsF, blockIndSkels, ciSkel, hn.1] using hstep

/-- `consSumCtorsF` is a left fold: over an append it is the two conses
in turn. -/
theorem consSumCtorsF_append (nP : Nat) :
    ∀ (a b : List (ConstantVal × Nat)) (fe : FEnv),
      consSumCtorsF nP (a ++ b) fe = consSumCtorsF nP b (consSumCtorsF nP a fe)
  | [], _, _ => rfl
  | _ :: a, b, _ => consSumCtorsF_append nP a b _

/-- The members' constructors, consed member by member, are the
whole block's constructors consed in block order. -/
theorem consBlockCtorsF_flatten (nP : Nat) :
    ∀ (ctorsAs : List (List (ConstantVal × Nat))) (fe : FEnv),
      consBlockCtorsF nP ctorsAs fe = consSumCtorsF nP ctorsAs.flatten fe
  | [], _ => rfl
  | ctorsA :: rest, fe => by
    rw [consBlockCtorsF, List.flatten_cons, consSumCtorsF_append]
    exact consBlockCtorsF_flatten nP rest _

theorem sumCtorSkels_append (nP : Nat) (a b : List (Name × Nat)) (sk : List InstallSkel) :
    sumCtorSkels nP (a ++ b) sk = sumCtorSkels nP b (sumCtorSkels nP a sk) := by
  simp only [sumCtorSkels, List.foldl_append]

/-- The members' constructors at the skeleton level. -/
theorem consBlockCtorsF_skels (nP : Nat) :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {mss : List MemberShape} {fe : FEnv}
      {sk : List InstallSkel},
      ctorsAs.map (List.map fun c => (c.1.name, c.2))
          = mss.map (fun ms => ms.ctors.map fun c => (c.1.name, c.2)) →
      SkelIs fe sk →
      SkelIs (consBlockCtorsF nP ctorsAs fe) (blockCtorSkels nP mss sk)
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, hn, _ => by simp at hn
  | _ :: _, [], _, _, hn, _ => by simp at hn
  | ctorsA :: rest, ms :: mss, fe, sk, hn, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    have h1 := consSumCtorsF_skels nP (ctorsA := ctorsA) h
    rw [hn.1] at h1
    rw [consBlockCtorsF, blockCtorSkels]
    exact consBlockCtorsF_skels nP hn.2 h1

/-- The constructors' stage: names and field counts per member, one
field-sort list per constructor, and every stored name fresh at the
environment the stage runs at. -/
theorem checkBlockCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      Yields (checkBlockCtorsF ops fe₀ fe p l)
        (fun r => r.1.map (List.map fun c => (c.1.name, c.2))
            = l.map (fun x => x.1.ctors.map fun c => (c.1.name, c.2)) ∧
          r.2.map List.length = l.map (fun x => x.1.ctors.length) ∧
          ∀ cs ∈ r.1, ∀ c ∈ cs, fe.find? c.1.name = none)
  | [] => Yields.pure ⟨rfl, rfl, fun _ h => nomatch h⟩
  | (ms, cvTa) :: rest => by
    unfold checkBlockCtorsF
    refine Yields.bind' (Yields.and
      (checkSumCtorsF_names ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort p.isProp
        p.large cvTa ms.ctors)
      (checkSumCtorsF_fresh ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort p.isProp
        p.large cvTa ms.ctors)) fun q hq => ?_
    obtain ⟨ctorsA, sortss⟩ := q
    obtain ⟨⟨hn, hlS⟩, -, hfr⟩ := hq
    refine Yields.bind' (checkBlockCtorsF_fresh ops fe₀ fe p rest) fun r hr => ?_
    obtain ⟨restC, restS⟩ := r
    obtain ⟨hn', hlS', hfr'⟩ := hr
    refine Yields.pure ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.cons.injEq]
      exact ⟨hn, hn'⟩
    · simp only [List.map_cons, List.cons.injEq]
      exact ⟨hlS, hlS'⟩
    · intro cs hcs
      rcases List.mem_cons.mp hcs with rfl | hcs
      · exact hfr
      · exact hfr' cs hcs

/-- A stage followed by a reject-only check (`thenConform`, lane CONF1)
returns the stage's value: whatever the stage yields, the composite
does. -/
theorem Yields.thenConform {α : Type} {stage : CheckCM α} {conform : CheckCM Unit}
    {P : α → Prop} (h : Yields stage P) : Yields (ConLeche.thenConform stage conform) P := by
  unfold ConLeche.thenConform
  exact Yields.bind' h fun a ha => Yields.bind fun _ => Yields.pure ha

theorem Yields.unwrapOr {α : Type} {o : Option α} {e : CheckError} :
    Yields (unwrapOr o e : CheckCM α) (fun a => o = some a) := by
  cases o with
  | none => exact Yields.ofThrow
  | some a => exact Yields.pure rfl

/-! ### The TARGET recursor check at the skeleton level (lane RECLIB, B1)

The recursor stage is `targetRecCheck` (`ConLeche/Kernel/Inductives/RecCheck.lean`);
on the uniform route (`outside = false`) every major is a member, and it
is the member the record names (K7). -/

/-- The major on the uniform route: a member, with its stored
constructors. -/
theorem targetMajorOf_member {aux : NestNodes} (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (fvs : List Expr) (mty : Expr) :
    Yields (targetMajorOf (m := CheckCM) fe p false aux ctorsAs fvs mty)
      (fun M => ∃ t, M.member = some t ∧ t < p.k ∧ ctorsAs[t]? = some M.ctors) := by
  unfold targetMajorOf
  dsimp only
  split
  · split
    · refine Yields.bind' Yields.unwrapOr fun ms hms => ?_
      refine Yields.bind' Yields.unwrapOr fun ctorsA hctorsA => ?_
      split
      · exact Yields.pure ⟨_, rfl, (List.getElem?_eq_some_iff.mp hms).1, hctorsA⟩
      · exact Yields.ofThrowBind
    · yields
      all_goals first | exact Yields.ofThrow | (exfalso; simp_all)
  · exact Yields.ofThrow

/-- One recursor's type on the uniform route: the record's name, fresh,
and its major the member the record names, with that member's stored
constructors. -/
theorem targetRecTy_member {aux : NestNodes} (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rc : RecShape) :
    Yields (targetRecTy ops fe p false nested aux cvTas ctorsAs rc)
      (fun t => t.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none ∧
        t.2.1.member = some rc.tgt ∧ rc.tgt < p.k ∧ ctorsAs[rc.tgt]? = some t.2.1.ctors) := by
  unfold targetRecTy
  refine Yields.bind' (checkConstantValF_fresh ops fe rc.cvR) fun cvRi hcv => ?_
  dsimp only
  by_cases h1 : p.nP ≤ rc.rP
  case neg => rw [if_neg h1]; exact Yields.ofThrowBind
  rw [if_pos h1]
  by_cases h2 : rc.rP ≤ rc.mI
  case neg => rw [if_neg h2]; exact Yields.ofThrowBind
  rw [if_pos h2]
  refine Yields.bind fun x => ?_
  refine Yields.bind fun maj => ?_
  refine Yields.bind' (targetMajorOf_member fe p ctorsAs _ _) fun M hM => ?_
  obtain ⟨t, hmt, htk, hct⟩ := hM
  by_cases hK7 : Option.all (fun x => x == rc.tgt) M.member = true
  case neg => rw [if_neg hK7]; exact Yields.ofThrowBind
  rw [if_pos hK7]
  obtain rfl : t = rc.tgt := by rw [hmt] at hK7; simpa using hK7
  yields
  all_goals first | exact Yields.ofThrow | exact Yields.pure ⟨hcv.1, hcv.2, hmt, htk, hct⟩

/-- What one checked recursor of the uniform route stores, against its
record: its name, fresh at the stage's index, and its major the member
the record names, with that member's stored constructors. -/
@[expose] def TargetTyOk (fe : FEnv) (p : BlockShape) (ctorsAs : List (List (ConstantVal × Nat)))
    (rc : RecShape) (t : ConstantVal × TargetMajor × Level) : Prop :=
  t.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none ∧
    t.2.1.member = some rc.tgt ∧ rc.tgt < p.k ∧ ctorsAs[rc.tgt]? = some t.2.1.ctors

/-- Every recursor's type on the uniform route, against the records. -/
theorem targetRecTys_member {aux : NestNodes} (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    ∀ (recs : List RecShape),
      Yields (targetRecTys ops fe p false nested aux cvTas ctorsAs recs)
        (fun tys => tys.length = recs.length ∧
          ∀ (j : Nat) (rc : RecShape), recs[j]? = some rc →
            ∃ t, tys[j]? = some t ∧ TargetTyOk fe p ctorsAs rc t)
  | [] => Yields.pure ⟨rfl, fun _ _ h => nomatch h⟩
  | rc :: rcs => by
    unfold targetRecTys
    refine Yields.bind' (targetRecTy_member ops fe p nested cvTas ctorsAs rc) fun t ht => ?_
    refine Yields.bind' (targetRecTys_member ops fe p nested cvTas ctorsAs rcs) fun ts hts => ?_
    refine Yields.pure ⟨by simp [hts.1], fun j rc' hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hj
      exact ⟨t, rfl, ht⟩
    | succ j => exact hts.2 j rc' (by simpa using hj)

/-- One recursor's rules: one right-hand side per constructor. -/
theorem targetRules_len (opsR : CheckerOps CheckCM) (w : StructWalkers) (feR : FEnv)
    (opsT : CheckerOps CheckCM) (feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (cvRi : ConstantVal) (rP : Nat) (M : TargetMajor) :
    ∀ (cs : List (ConstantVal × Nat)) (rhss : List Expr),
      Yields (targetRules opsR w feR opsT feT p formerTys fam cvRi rP M cs rhss)
        (fun rs => rs.length = cs.length)
  | [], [] => Yields.pure rfl
  | [], _ :: _ => Yields.ofThrow
  | _ :: _, [] => Yields.ofThrow
  | cA :: cs, rhs :: rhss => by
    unfold targetRules
    refine Yields.bind fun _ => ?_
    refine Yields.bind' (targetRules_len opsR w feR opsT feT p formerTys fam cvRi rP M cs rhss)
      fun rs hrs => ?_
    exact Yields.pure (by simp [hrs])

/-- Every recursor's rules: the checked recursor and its major kept,
one right-hand side per constructor of the major. -/
theorem targetRecsRules_len (opsR : CheckerOps CheckCM) (w : StructWalkers) (feR : FEnv)
    (opsT : CheckerOps CheckCM) (feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) :
    ∀ (recs : List RecShape) (tys : List (ConstantVal × TargetMajor × Level)),
      recs.length = tys.length →
      Yields (targetRecsRules opsR w feR opsT feT p formerTys fam recs tys)
        (fun out => out.length = tys.length ∧
          ∀ (j : Nat) (t : ConstantVal × TargetMajor × Level), tys[j]? = some t →
            ∃ rh, out[j]? = some (t.1, t.2.1, rh) ∧ rh.length = t.2.1.ctors.length)
  | [], [], _ => Yields.pure ⟨rfl, fun _ _ h => nomatch h⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | rc :: rcs, (cvRi, M, u) :: ts, h => by
    unfold targetRecsRules
    dsimp only
    split
    case isFalse => exact Yields.ofThrowBind
    refine Yields.bind' (targetRules_len opsR w feR opsT feT p formerTys fam cvRi rc.rP M _ _)
      fun rh hrh => ?_
    refine Yields.bind' (targetRecsRules_len opsR w feR opsT feT p formerTys fam rcs ts
      (by simpa using h)) fun rest hrest => ?_
    refine Yields.pure ⟨by simp [hrest.1], fun j t hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : (cvRi, M, u) = t := by simpa using hj
      exact ⟨rh, rfl, hrh⟩
    | succ j =>
      obtain ⟨rh', h1, h2⟩ := hrest.2 j t (by simpa using hj)
      exact ⟨rh', by simpa using h1, h2⟩

/-- One recursor's type at ANY majors (the route switch on): the
record's name, fresh at the check's index. -/
theorem targetRecTy_name {aux : NestNodes} (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape)
    (outside nested : Bool) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (rc : RecShape) :
    Yields (targetRecTy ops fe p outside nested aux cvTas ctorsAs rc)
      (fun t => t.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none) := by
  unfold targetRecTy
  refine Yields.bind' (checkConstantValF_fresh ops fe rc.cvR) fun cvRi hcv => ?_
  dsimp only
  by_cases h1 : p.nP ≤ rc.rP
  case neg => rw [if_neg h1]; exact Yields.ofThrowBind
  rw [if_pos h1]
  by_cases h2 : rc.rP ≤ rc.mI
  case neg => rw [if_neg h2]; exact Yields.ofThrowBind
  rw [if_pos h2]
  refine Yields.bind fun x => ?_
  refine Yields.bind fun maj => ?_
  refine Yields.bind fun M => ?_
  by_cases hK7 : Option.all (fun x => x == rc.tgt) M.member = true
  case neg => rw [if_neg hK7]; exact Yields.ofThrowBind
  rw [if_pos hK7]
  yields
  all_goals first | exact Yields.ofThrow | exact Yields.pure ⟨hcv.1, hcv.2⟩

/-- Every recursor's type at ANY majors, against the records. -/
theorem targetRecTys_names {aux : NestNodes} (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape)
    (outside nested : Bool) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    ∀ (recs : List RecShape),
      Yields (targetRecTys ops fe p outside nested aux cvTas ctorsAs recs)
        (fun tys => tys.length = recs.length ∧
          ∀ (j : Nat) (rc : RecShape), recs[j]? = some rc →
            ∃ t, tys[j]? = some t ∧ t.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none)
  | [] => Yields.pure ⟨rfl, fun _ _ h => nomatch h⟩
  | rc :: rcs => by
    unfold targetRecTys
    refine Yields.bind' (targetRecTy_name (aux := aux) ops fe p outside nested cvTas ctorsAs rc)
      fun t ht => ?_
    refine Yields.bind' (targetRecTys_names (aux := aux) ops fe p outside nested cvTas ctorsAs rcs)
      fun ts hts => ?_
    refine Yields.pure ⟨by simp [hts.1], fun j rc' hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hj
      exact ⟨t, rfl, ht⟩
    | succ j => exact hts.2 j rc' (by simpa using hj)

/-- **The target check at ANY majors, at the skeleton level** (the
route switch on, lane FLIPPREP): one stored recursor per record, in
order, under the record's name (fresh at the check's index), the
family's names distinct. -/
theorem targetRecCheck_names {aux : NestNodes} (so : ShadowOps CheckCM) (fe : FEnv) (p : BlockShape)
    (outside nested : Bool) (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    Yields (targetRecCheck so fe p outside nested aux block cvTas ctorsAs)
      (fun out => (p.recs.map (·.cvR.name)).Nodup ∧ out.length = p.recs.length ∧
        ∀ (j : Nat) (rc : RecShape), p.recs[j]? = some rc →
          ∃ o, out[j]? = some o ∧ o.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none) := by
  unfold targetRecCheck
  refine Yields.bind' (Q := fun _ => (p.recs.map (·.cvR.name)).Nodup) ?_ fun _ hnd => ?_
  · unfold targetRecPins
    dsimp only
    by_cases h1 : blockRecLpsOk p = true
    case neg => rw [if_neg h1]; exact Yields.ofThrow
    rw [if_pos h1]
    by_cases h2 : blockRecNamesUnreserved p = true
    case neg => rw [if_neg h2]; exact Yields.ofThrow
    rw [if_pos h2]
    split
    case isFalse => exact Yields.ofThrow
    split
    case isFalse => exact Yields.ofThrow
    by_cases h5 : (p.recs.map (·.cvR.name)).Nodup
    case neg => rw [if_neg h5]; exact Yields.ofThrow
    rw [if_pos h5]
    split
    · split
      · exact Yields.pure h5
      · exact Yields.ofThrow
    · exact Yields.ofThrow
  refine Yields.bind' (targetRecTys_names (aux := aux) (so.opsAt fe) fe p outside nested cvTas ctorsAs p.recs)
    fun tys htys => ?_
  dsimp only
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind' (targetRecsRules_len _ _ _ _ _ p _ _ p.recs tys htys.1.symm)
    fun out hout => ?_
  refine Yields.bind fun _ => Yields.pure ?_
  refine ⟨hnd, by rw [hout.1, htys.1], fun j rc hj => ?_⟩
  obtain ⟨t, htj, hname, hfr⟩ := htys.2 j rc hj
  obtain ⟨rh, hoj, -⟩ := hout.2 j t htj
  exact ⟨_, hoj, hname, hfr⟩

/-- The recursors' conses AT THEIR MAJORS (`consBlockRecsTF`) at the
skeleton level, from the target check's output: each record's name. -/
theorem consBlockRecsTF_skelsT (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (p : BlockShape) :
    ∀ (l : List RecShape) (ri : Nat)
      (out : List (ConstantVal × TargetMajor × List Expr))
      (fe : FEnv) (sk : List InstallSkel), l = p.recs.drop ri → out.length = l.length →
      (∀ (j : Nat) o (rc : RecShape), out[j]? = some o → l[j]? = some rc →
        o.1.name = rc.cvR.name) →
      SkelIs fe sk →
      SkelIs (consBlockRecsTF find? resolves p ri out fe) (blockRecSkels p ri l sk)
  | [], _, [], _, _, _, _, _, h => h
  | [], _, _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, [], _, _, _, hlen, _, _ => by simp at hlen
  | rc :: rest, ri, (cv, M, rhss) :: out, fe, sk, hl, hlen, hall, h => by
    have hrest : rest = p.recs.drop (ri + 1) := by
      rw [← List.drop_drop, ← hl]; rfl
    have hname := hall 0 _ rc rfl rfl
    dsimp only at hname
    let ci : ConstantInfo := .recInfo cv (p.majorIdxAt ri) (p.rulePrefixAt ri)
      (tgtStoredRules find? resolves cv (p.majorIdxAt ri) (p.rulePrefixAt ri) M rhss)
    have hci : ciSkel ci = .recr rc.cvR.name (p.majorIdxAt ri) (p.rulePrefixAt ri) := by
      simp only [ci, ciSkel, hname]
    have h' := consBlockRecsTF_skelsT find? resolves p rest (ri + 1) out
      (fe.push ci) (ciSkel ci :: sk) hrest (by simpa using hlen)
      (fun j r rc' hj hj' => hall (j + 1) r rc' (by simpa using hj) (by simpa using hj'))
      (h.push ci)
    rw [hci] at h'
    exact h'

/-- The projection tables at the skeleton level: one per
structure-like member, read off the member's own counts (the stored
constructor and field-sort lists are one per constructor). -/
theorem checkBlockTablesF_skels {w : StructWalkers} (p : BlockShape) :
    ∀ (mss : List MemberShape) (ctorsAs : List (List (ConstantVal × Nat)))
      (sortsss : List (List (List Level))) {fe : FEnv} {sk : List InstallSkel},
      ctorsAs.map List.length = mss.map (·.ctors.length) →
      sortsss.map List.length = mss.map (·.ctors.length) →
      SkelIs fe sk →
      Yields (checkBlockTablesF (m := CheckCM) w p (mss.zip (ctorsAs.zip sortsss)) fe)
        (fun fe' => SkelIs fe' (blockTableSkels mss sk))
  | [], _, _, _, _, _, _, h => Yields.pure h
  | _ :: _, [], _, _, _, hc, _, _ => by simp at hc
  | _ :: _, _ :: _, [], _, _, _, hs, _ => by simp at hs
  | ms :: mss, ctorsA :: ctorsAs, sortss :: sortsss, fe, sk, hc, hs, h => by
    simp only [List.map_cons, List.cons.injEq] at hc hs
    simp only [List.zip_cons_cons]
    unfold checkBlockTablesF
    have key : Yields
        (match ctorsA, sortss with
         | [cA], [sorts] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) w ms.cvT.name cA.1.name p.lps p.nP cA.2
               p.resSort (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe
           else pure fe
         | _, _ => pure fe)
        (fun fe' => SkelIs fe' (if ms.ctors.length == 1 && ms.nIdx == 0 then
          .proj (projTableName ms.cvT.name) :: sk else sk)) := by
      match ctorsA, sortss, hc.1, hs.1 with
      | [cA], [sorts], hc1, _ =>
        have h1 : (ms.ctors.length == 1) = true := by simp [← hc1]
        simp only [h1, Bool.true_and]
        by_cases hi : (ms.nIdx == 0) = true
        · rw [if_pos hi, if_pos hi]
          exact checkStructProjTableF_skels h _ _ _ _ _ _ _ _ _
        · rw [if_neg hi, if_neg hi]
          exact Yields.pure h
      | [], _, hc1, _ =>
        have h1 : (ms.ctors.length == 1) = false := by simp [← hc1]
        simp only [h1, Bool.false_and]
        exact Yields.pure h
      | _ :: _ :: _, _, hc1, _ =>
        have h1 : (ms.ctors.length == 1) = false := by simp [← hc1]
        simp only [h1, Bool.false_and]
        exact Yields.pure h
      | [_], [], hc1, hs1 => simp at hc1 hs1; omega
      | [_], _ :: _ :: _, hc1, hs1 => simp at hc1 hs1; omega
    refine Yields.bind' key fun fe' h' => ?_
    exact checkBlockTablesF_skels p mss ctorsAs sortsss hc.2 hs.2 h'

/-- The completed record's recursor skeleton is the recognised one's:
the sort the formers read is not in it. -/
theorem blockRecSkels_withSort (q : BlockShape) (s : Level) :
    ∀ (r : Nat) (l : List RecShape) (sk : List InstallSkel),
      blockRecSkels (q.withSort s) r l sk = blockRecSkels q r l sk
  | _, [], _ => rfl
  | r, rc :: rest, sk => by
    simp only [blockRecSkels]
    exact blockRecSkels_withSort q s (r + 1) rest _

/-- The install after the pass: the k-ary skeleton of the completed
record. -/
theorem checkBlockTailS_skels (mode : CheckMode) {block : List ConstantInfo}
    {sk : List InstallSkel} {q : BlockPass FEnv} (nst : Bool)
    (h₁ : SkelIs q.env₁ (blockIndSkels q.p.members sk))
    (hns : q.ctorsAs.map (List.map fun c => (c.1.name, c.2))
      = q.p.members.map (fun ms => ms.ctors.map fun c => (c.1.name, c.2)))
    (hlenS : q.sortsss.map List.length = q.p.members.map (·.ctors.length)) :
    Yields (checkBlockTailS mode block q nst) (fun fe' => SkelIs fe' (blockSkels q.p sk)) := by
  unfold checkBlockTailS
  dsimp only
  split
  · exact Yields.ofThrowBind
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  unfold checkBlockRecS
  have hlenC : q.ctorsAs.map List.length = q.p.members.map (·.ctors.length) := by
    have := congrArg (List.map List.length) hns
    simpa [List.map_map, Function.comp_def] using this
  have h₂ := consBlockCtorsF_skels q.p.nP hns h₁
  refine Yields.bind' (Yields.thenConform
    (targetRecCheck_names (shadowOpsC mode) _ q.p.toBlockShape nst _ block q.cvTas q.ctorsAs))
    fun out hout => ?_
  have hrs := consBlockRecsTF_skelsT
      (consBlockCtorsF q.p.nP q.ctorsAs q.env₁).find?
      (·.constsResolveF (consBlockCtorsF q.p.nP q.ctorsAs q.env₁)) q.p.toBlockShape
      q.p.recs 0 out _ _ (List.drop_zero (l := q.p.recs)).symm hout.2.1
      (fun j o rc hoj hrc => by
        obtain ⟨o', hoj', hname, -⟩ := hout.2.2 j rc hrc
        rw [hoj] at hoj'
        obtain rfl := Option.some.inj hoj'
        exact hname) h₂
  exact checkBlockTablesF_skels q.p.toBlockShape q.p.members q.ctorsAs q.sortsss hlenC hlenS hrs


/-- One pass at k members (task #268): the formers' skeleton, the
record's shape (the sort read), the constructors by name and field
count, one field-sort list per constructor. -/
theorem checkBlockPassS_skels (mode : CheckMode) {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (p₀ : BlockParts) (isRec : Bool) (nst : Bool) :
    Yields (checkBlockPassS mode fe p₀ isRec nst)
      (fun r => SkelIs r.env₁ (blockIndSkels p₀.members sk) ∧
        (∃ s, r.p.toBlockShape = p₀.toBlockShape.withSort s) ∧
        r.ctorsAs.map (List.map fun c => (c.1.name, c.2))
          = r.p.members.map (fun ms => ms.ctors.map fun c => (c.1.name, c.2)) ∧
        r.sortsss.map List.length = r.p.members.map (·.ctors.length)) := by
  unfold checkBlockPassS
  refine Yields.bind' (checkBlockIndsF_fresh _ fe p₀ isRec) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTas, p₁⟩ := r₁
  obtain ⟨⟨s, hps⟩, hfe₁, hn, -⟩ := h₁
  try simp only [] at hps hfe₁ hn
  subst hps
  try simp only []
  ybind
  have hlen : (p₀.members.zip cvTas).map (fun x => x.1) = p₀.members := by
    have := congrArg List.length hn
    simp only [List.length_map] at this
    rw [List.map_fst_zip (by omega)]
  refine Yields.bind' (checkBlockCtorsF_fresh _ fe₁ fe₁ _ _) fun r hr => ?_
  obtain ⟨ctorsAs, sortsss⟩ := r
  obtain ⟨hns, hlS, -⟩ := hr
  try simp only []
  refine Yields.bind fun kinds => ?_
  refine Yields.pure ⟨?_, ⟨s, rfl⟩, ?_, ?_⟩
  · rw [hfe₁]
    exact consBlockIndsF_skels _ isRec hn h
  · simp only [BlockParts.complete_members,
      BlockShape.withSort_members] at hns ⊢
    rw [hns]
    conv => rhs; rw [← hlen]
    rw [List.map_map]
    rfl
  · simp only [BlockParts.complete_members,
      BlockShape.withSort_members] at hlS ⊢
    rw [hlS]
    conv => rhs; rw [← hlen]
    rw [List.map_map]
    rfl

/-- The completed record's skeleton is the recognised one's. -/
theorem blockSkels_withSort {p q : BlockParts} {s : Level}
    (hq : q.toBlockShape = p.toBlockShape.withSort s) (sk : List InstallSkel) :
    blockSkels q sk = blockSkels p sk := by
  have hm : q.members = p.members := by
    show q.toBlockShape.members = p.toBlockShape.members
    rw [hq]; rfl
  have hr : q.recs = p.recs := by
    show q.toBlockShape.recs = p.toBlockShape.recs
    rw [hq]; rfl
  have hn : q.nP = p.nP := by
    show q.toBlockShape.nP = p.toBlockShape.nP
    rw [hq]; rfl
  unfold blockSkels
  rw [hm, hr, hn, hq, blockRecSkels_withSort]

/-- **The uniform install at k members, at the skeleton level**: the
pass at official's `is_rec` and the install after it. -/
theorem checkBlockKS_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (block : List ConstantInfo) (p : BlockParts)
    (nst : Bool) :
    Yields (checkBlockKS mode fe block p nst) (fun fe' => SkelIs fe' (blockSkels p sk)) := by
  unfold checkBlockKS
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => ?dupBad) (fun _ => ?main)
  case dupBad => exact Yields.ofThrowBind
  case main =>
  ybind
  refine Yields.bind' (checkBlockPassS_skels mode h p (blockRawRec p) nst) fun q hr => ?_
  obtain ⟨h₁, ⟨s, hq⟩, hns, hlenS⟩ := hr
  try simp only [] at h₁ hq hns hlenS
  try simp only []
  have hm : q.p.members = p.members := by
    show q.p.toBlockShape.members = p.toBlockShape.members
    rw [hq]; rfl
  refine Yields.mono (checkBlockTailS_skels mode nst (by rw [hm]; exact h₁) hns hlenS) ?_
  intro fe' h'
  rwa [blockSkels_withSort hq] at h'


/-! ### The tolerated-axiom branch

`sorryAx` is the one axiom the checker tolerates as a declaration, and
none of the pinned axiom guards can fire on it — so at `.axiomDecl` the
*push-or-not* decision is a function of the header name alone, in both
drivers. -/

theorem tolerated_not_std (fe : FEnv) (cvA : ConstantVal)
    (ht : cvA.name = sorryAxName) :
    stdAxiomOkF fe cvA = false := by
  rw [stdAxiomOkF, if_neg, if_neg] <;> rw [ht] <;> decide

theorem tolerated_ne_trust {n : Name}
    (ht : n = sorryAxName) : n ≠ trustCompilerName := by
  rw [ht]; decide

theorem tolerated_ne_ofReduce {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = ofReduceNatName ∨ n = ofReduceBoolName) := by
  rw [ht]; decide

theorem tolerated_ne_std {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = propextName ∨ n = choiceName) := by
  rw [ht]; decide

/-! ### The cached certified declaration clause -/

/-- The pinned-block install's skeleton reading, shared by the three
arms that install one (task #293). -/
theorem checkBasisDeclC_skels {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (kind : BasisKind) :
    Yields (checkBasisDeclC fe kind)
      (fun fe' => SkelIs fe'
        (kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk)) := by
  have hfold : ∀ (fe' : FEnv) (sk' : List InstallSkel), SkelIs fe' sk' →
      Yields (kind.declsA.foldlM installBasisDeclF fe')
        (fun x => SkelIs x
          (kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk')) :=
    fun fe' sk' h' =>
      Yields.foldlM_rel (R := SkelIs) (g := fun acc ci => ciSkel ci :: acc)
        (fun acc ci sk'' hacc => installBasisDeclF_skels hacc ci)
        kind.declsA fe' sk' h'
  unfold checkBasisDeclC
  yields
  all_goals exact hfold fe sk h

theorem checkDeclC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclC declCSkels
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
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | axiomDecl cv =>
    simp only []
    -- task #293: `Quot.sound` is compared with the pin and installs
    -- nothing of its own
    by_cases hqs : cv.name = quotSoundName
    · rw [if_pos hqs, if_pos (Or.inr hqs)]
      split
      · exact Yields.pure h
      · exact Yields.ofThrow
    · rw [if_neg hqs]
      refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
      obtain ⟨cvA, jty⟩ := p
      simp only []
      rw [← hp]
      by_cases ht : cvA.name = sorryAxName
      · rw [if_pos (Or.inl ht),
          if_neg (by rw [tolerated_not_std fe cvA ht]; exact Bool.false_ne_true),
          if_neg (tolerated_ne_trust ht), if_neg (tolerated_ne_ofReduce ht),
          if_neg (tolerated_ne_std ht), if_pos ht]
        exact Yields.pure h
      · have hne : ¬(cvA.name = sorryAxName ∨ cvA.name = quotSoundName) := by
          rintro (h' | h')
          · exact ht h'
          · exact hqs (hp ▸ h')
        rw [if_neg hne]
        yields
        all_goals first
          | (apply Yields.pure; exact h.push _)
          | exact absurd (by assumption) ht
  | basisDecl kind => exact checkBasisDeclC_skels h kind
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the
    -- other members install nothing, a mismatch throws
    simp only []
    cases k <;>
      (split
       · first
         | exact checkBasisDeclC_skels h .quotK
         | exact Yields.pure h
       · exact Yields.ofThrow)
  | indDecl block nP =>
    simp only []
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin; the declared parameter count (task #228) below it is a
    -- guard whose `throw` installs nothing
    split
    next kind hk => rw [hk]; exact checkBasisDeclC_skels h kind
    next hk =>
      rw [hk]
      split
      · unfold indDeclSkels
        cases hbp : blockParts? nP block with
        | none => exact Yields.bind fun _ => Yields.ofThrow
        | some p =>
          -- the uniform route, at any number of members, nested
          -- blocks included
          exact checkBlockKS_skels mode h block p true
      · exact Yields.ofThrow

theorem checkDeclStepC_skels (mode : CheckMode) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd)
      (fun fe' => SkelIs fe' (declCSkels pd sk)) := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_skels mode h pd

/-! ## The floor

The fold installs every record by `annotStepC` (`checkDecls`,
`ConLeche/Cached/Installed.lean`) — a separable value declaration by
the install halves, everything else by `checkDeclStepC` — and its
phase B pushes nothing, so the skeleton spec `declCSkels` computes the
installed environment at *every* mode.  Hence: whenever two modes both
**accept**, they installed the same constants, in the same order, with
the same skeletons — and in particular the same names and the same
count.

Scope, stated exactly: these are **accept-verdict** statements.  The
trusted config's purpose is to reject less, and the recorded
trusted-mode divergences are decline/accept divergences, untouched
here. -/

theorem skelIs_empty : SkelIs (mkFEnv Env.empty) [] := ⟨⟨_, rfl⟩, rfl⟩

/-- The declaration-stream specification: the skeletons a stream
installs, newest first. -/
def streamSkels (ds : List Declaration) : List InstallSkel :=
  ds.foldl (fun sk pd => declCSkels pd sk) []

/-! ### The direct-parse entry points (task #171's route) -/

/-- Phase A's step body installs the declaration's skeletons: the value
kinds push the one constant the fold's value checkers push, everything
else runs `checkDeclStepC`. -/
theorem annotStepC_skels (mode : CheckMode) (i : Nat) {fe : FEnv}
    {sk : List InstallSkel} (h : SkelIs fe sk) (pend : Array PendingCheck) (pd : Declaration) :
    Yields (annotStepC mode pins i fe pend pd) (fun r => SkelIs r.1 (declCSkels pd sk)) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode pins fe pd', pend) :
      CheckCM (FEnv × Array PendingCheck)) (fun r => SkelIs r.1 (declCSkels pd' sk)) :=
    fun pd' => Yields.bind' (checkDeclStepC_skels mode h pd') fun fe' h' => Yields.pure h'
  unfold annotStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value true) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      apply Yields.pure
      show SkelIs (fe.push (.defnInfo cvA jv hint)) (.defn cv.name :: sk)
      rw [← hr.1]; exact h.push _
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hr => ?_
    obtain ⟨cvA, jty⟩ := p
    ybind
    apply Yields.pure
    show SkelIs (fe.push (.thmInfo cvA value)) (.thm cv.name :: sk)
    rw [← hr.1]; exact h.push _
  | opaqueDecl cv value =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value false) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      apply Yields.pure
      show SkelIs (fe.push (.axiomInfo cvA)) (.ax cv.name :: sk)
      rw [← hr.1]; exact h.push _
  | axiomDecl cv => exact hord _
  | basisDecl kind => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- Phase A's accepting run installs the stream's skeletons. -/
theorem installRun_skels (mode : CheckMode) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (h : InstallRun mode pins ds p s q s') {sk : List InstallSkel} (hp : SkelIs p.2.1 sk) :
    SkelIs q.2.1 (ds.foldl (fun sk pd => declCSkels pd sk) sk) := by
  induction h generalizing sk with
  | nil p s => exact hp
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    rw [List.foldl_cons]
    exact ih (annotStepC_skels mode p.1 hp p.2.2 pd s (fe₁, pend₁) s₁ hstepC)

/-- **The skeleton spec, at every mode.**  This is the floor's whole
content since the twin's retirement: one fold, one proof. -/
theorem checkDecls_skels {mode : CheckMode} {ds : Array Declaration}
    {env : Env} (h : checkDecls mode pins ds = .ok env) :
    envSkels env = streamSkels ds.toList := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
  obtain ⟨n, s, r⟩ := fc.1.run
  exact (installRun_skels mode r skelIs_empty).2

/-- **The floor, direct-parse route.**  Whenever the cached driver at
two modes — in particular the trusted (`.trusted`) and the verified
(`.verified`) mode the binary ships — both accept the same stream, the
two installed environments carry the same install skeletons.  Stated
for any two modes: the old two-driver statement is the instance
`.trusted` / `.verified` (`trusted_agrees_skels_shipped`). -/
theorem trusted_agrees_skels_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envSkels envN = envSkels envP :=
  (checkDecls_skels hN).trans (checkDecls_skels hP).symm

/-- The census's sentence: the accepted declaration **names** agree. -/
theorem trusted_agrees_names_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (trusted_agrees_skels_D hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

/-- … and so do the accepted declaration **counts**. -/
theorem trusted_agrees_count_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (trusted_agrees_skels_D hP hN)
  simpa [envSkels] using h

/-- The shipped pair, spelled out: `--trusted` and `--verified` agree on
the install skeletons whenever both accept. -/
theorem trusted_agrees_skels_shipped {ds : Array Declaration} {envP envT : Env}
    (hP : checkDecls .verified pins ds = .ok envP)
    (hT : checkDecls .trusted pins ds = .ok envT) :
    envSkels envT = envSkels envP :=
  trusted_agrees_skels_D hP hT

end ConLeche.Cached
