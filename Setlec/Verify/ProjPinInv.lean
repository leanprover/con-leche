import Setlec.Verify.EnvWF
import Setlec.Kernel.Checker

/-!
# `NativeProjPinned` — the projection table's pin, as an install-time invariant

The `.proj` inference clause computes its residual from the pinned
two-parameter basis shape instead of walking the stored entry type
(task #161 item B2).  What licenses that is the fact that a `native`
projection-table entry is one of the two basis pair entries — consumed
so far only through `ProjOkT` (`Verify/EnvPreds.lean:106`), a field of
the verification tiers' environment records.

`ProjOkT` was always *syntactic* (no values, no interpretation, no
`V`); what it lacked was a **standalone route** — a way to reach the
pin without holding an `EnvR`/`EnvS` for the environment.  This module
supplies one, and the reason it is cheap is worth stating:

> **The invariant below is a closed induction.**  Every environment
> extension the checker performs either conses a non-`projInfo`
> constant, or conses an elimination-template entry whose `native`
> flag is a literal `false` at the construction site, or conses a
> member of the closed literal list `BasisKind.declsA`.  No auxiliary
> invariant is needed — unlike every field of the tower's environment
> records, which are inductive only together.

Tree-wide there are **five** `ProjEntry` construction sites: the two
pinned pair entries (`Kernel/Basis/PSigma.lean:310,318`, native slot a
literal `true`) and the three lanes' elimination-template installs
(`Kernel/Modeled.lean:689`, `Kernel/CheckerS.lean:1197`,
`Cached/CheckerC.lean:147`, native slot a literal `false`).  Table
entries never occur in parsed input (`Frontend/Export.lean:104`), so
the native pair is *injected* by `installBasisDecl` and never supplied
by a stream.  Task #107's audit rules both restrictions permanent, so
this is ratified design and not an accident; see DESIGN.md, "The
`.proj` pin is an install-time invariant, not a model licence".

The statement is proved for the `Env` presentation only.  The interned
and cached lanes install through the same functions and are bridged to
this one by `mkFEnv_push` (`Verify/SimS.lean:39`), so the invariant
transports without restatement.
-/

namespace Setlec

/-! ## The invariant -/

/-- **Every stored `native` projection-table entry is one of the two
pinned pair entries.**

Stated over the raw constant list — no `find?`, no freshness, no
valuation, no `V`.  This is the fragment of `projEntry_pins`
(`SetBase/ProjPins.lean:41`) that the `.proj` inference clause
consumes; the two stored-block conjuncts of that theorem are read only
by the certified tiers' denotation lemmas and stay in the tower. -/
def NativeProjPinned (env : Env) : Prop :=
  ∀ e : ProjEntry, (ConstantInfo.projInfo e) ∈ env.consts →
    e.native = true → e = pairFstEntry ∨ e = pairSndEntry

theorem NativeProjPinned.empty : NativeProjPinned Env.empty := by
  intro e h; simp [Env.empty] at h

/-- A one-constant extension whose head is not a table entry — the
shape of every install site but two. -/
def ConsedNonProj (env env' : Env) : Prop :=
  ∃ ci : ConstantInfo, (∀ e, ci ≠ .projInfo e) ∧ env' = ⟨ci :: env.consts⟩

theorem NativeProjPinned.consed {env env' : Env} (h : NativeProjPinned env)
    (hc : ConsedNonProj env env') : NativeProjPinned env' := by
  obtain ⟨ci, hci, rfl⟩ := hc
  intro e hmem hnat
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact absurd rfl (hci e)
  · exact h e hmem' hnat

/-- The elimination-template extension: the `native` flag is a literal
`false` at the construction site, so the head is vacuous. -/
theorem NativeProjPinned.cons_template {env : Env} {e₀ : ProjEntry}
    (h : NativeProjPinned env) (hn : e₀.native = false) :
    NativeProjPinned ⟨.projInfo e₀ :: env.consts⟩ := by
  intro e hmem hnat
  rcases List.mem_cons.mp hmem with heq | hmem'
  · cases ConstantInfo.projInfo.inj heq.symm
    exact absurd (hn.symm.trans hnat) (by decide)
  · exact h e hmem' hnat

/-! ## The basis census — the only producer of a `native` entry

`BasisKind.declsA` is a closed literal list, so this is a `decide`. -/

/-- Every `projInfo` member of a basis block that is `native` is one of
the two pinned pair entries. -/
def declsANativeOk (k : BasisKind) : Bool :=
  k.declsA.all fun ci => match ci with
    | .projInfo e => !e.native || (e == pairFstEntry || e == pairSndEntry)
    | _ => true

theorem declsANativeOk_all : ∀ k : BasisKind, declsANativeOk k = true := by
  intro k; cases k <;> decide

theorem basis_native_pinned {k : BasisKind} {e : ProjEntry}
    (hci : (ConstantInfo.projInfo e) ∈ k.declsA) (hnat : e.native = true) :
    e = pairFstEntry ∨ e = pairSndEntry := by
  have h := declsANativeOk_all k
  simp only [declsANativeOk, List.all_eq_true] at h
  have := h _ (by simpa using hci)
  simp only [hnat, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at this
  exact this

/-! ## The install sites, inverted

Fourteen environment-extension sites in the spec lane
(`Kernel/Checker.lean` nine, `Kernel/Modeled.lean` five).  Twelve of
them cons a constant that is visibly not a table entry; the thirteenth
(`installBasisDecl`) conses a member of `declsA`; the fourteenth
(`installProjTemplate`) is the only one that conses a `projInfo`, with
`native` a literal `false`.

Every inversion is the same two lines — split the `Except` do-block,
then read off the head — so they are written with one local tactic. -/

section Inversions

variable {ops : CheckerOps CheckM} {env env' : Env}

/-- Peel one `Except` bind.  Peeling rather than inlining the whole
do-block is what keeps these inversions cheap: `simp only [bind,
Except.bind]` materialises the entire nested block and `split`'s
internal `simp` then exceeds its step budget on the larger checkers. -/
theorem exceptBind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- Walk a checker do-block in the `Except` monad — peel binds, split
guards — and read the extension off the surviving `pure`. -/
local syntax "install_shape" ident : tactic
local macro_rules
  | `(tactic| install_shape $h:ident) =>
    `(tactic|
      (repeat' first
         | (obtain ⟨_, -, $h:ident⟩ := exceptBind_ok $h)
         | split at $h:ident
       all_goals first
         | exact ⟨_, (fun e => by simp), (Except.ok.inj $h:ident).symm⟩
         | exact ⟨_, (fun e => by simp),
             (Prod.mk.inj (Except.ok.inj $h:ident)).1.symm⟩
         | exact absurd $h:ident (by simp)))

theorem checkDefnVal_consed {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (h : checkDefnVal (m := CheckM) ops env cv value hint = .ok env') :
    ConsedNonProj env env' := by
  unfold checkDefnVal at h; install_shape h

theorem checkThmVal_consed {cv : ConstantVal} {value : Expr}
    (h : checkThmVal (m := CheckM) ops env cv value = .ok env') :
    ConsedNonProj env env' := by
  unfold checkThmVal at h; install_shape h

theorem checkOpaqueVal_consed {cv : ConstantVal} {value : Expr}
    (h : checkOpaqueVal (m := CheckM) ops env cv value = .ok env') :
    ConsedNonProj env env' := by
  unfold checkOpaqueVal at h; install_shape h

theorem checkDirectInd_consed {p : DirectParts} {cvTa : ConstantVal}
    (h : checkDirectInd (m := CheckM) ops env p = .ok (env', cvTa)) :
    ConsedNonProj env env' := by
  unfold checkDirectInd at h; install_shape h

theorem checkDirectCtor_consed {env₀ : Env} {p : DirectParts}
    {cvTa cvCa : ConstantVal}
    (h : checkDirectCtor (m := CheckM) ops env₀ env p cvTa = .ok (env', cvCa)) :
    ConsedNonProj env env' := by
  unfold checkDirectCtor at h; install_shape h

theorem checkIndMember_consed {blockNames : List Name} {caps : IndCaps}
    {ci : ConstantInfo}
    (h : checkIndMember (m := CheckM) ops blockNames caps env ci = .ok env') :
    ConsedNonProj env env' := by
  unfold checkIndMember at h; install_shape h

theorem checkProjFn_consed {mode : CheckMode} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn (m := CheckM) mode ops env T ctorName lps nP nF i
      = .ok env') : ConsedNonProj env env' := by
  unfold checkProjFn at h; install_shape h

/-! ### The two sites that install a table entry -/

theorem installBasisDecl_shape {ci : ConstantInfo}
    (h : installBasisDecl (m := CheckM) env ci = .ok env') :
    env' = ⟨ci :: env.consts⟩ := by
  simp only [installBasisDecl, bind, Except.bind] at h
  split at h
  · simp only [pure, Except.pure] at h
    first | exact Except.ok.inj h | exact (Except.ok.inj h).symm
  · simp at h

theorem installProjTemplate_shape {T c : Name} {lps : List Name}
    {nP nF i : Nat}
    (h : installProjTemplate (m := CheckM) env T c lps nP nF i = .ok env') :
    env' = env ∨ ∃ e : ProjEntry, e.native = false ∧
      env' = ⟨.projInfo e :: env.consts⟩ := by
  unfold installProjTemplate at h
  split at h
  · split at h
    · exact Or.inr ⟨_, rfl, (Except.ok.inj h).symm⟩
    · exact Or.inl (Except.ok.inj h).symm
  · exact Or.inl (Except.ok.inj h).symm

end Inversions

/-! ## Preservation, site by site

Each step is `NativeProjPinned`-in, `NativeProjPinned`-out, and — the
point of the module — **none of them needs a further hypothesis**. -/

section Preservation

variable {mode : CheckMode} {ops : CheckerOps CheckM} {env env' : Env}

/-- A `foldlM` of preserving steps preserves. -/
theorem foldlM_preserves {α : Type} {f : Env → α → CheckM Env} {l : List α}
    (hstep : ∀ (e e' : Env) (a : α), NativeProjPinned e → f e a = .ok e' →
      NativeProjPinned e') :
    ∀ {env env' : Env}, NativeProjPinned env →
      l.foldlM f env = .ok env' → NativeProjPinned env' := by
  induction l with
  | nil => intro env env' hI h; exact (Except.ok.inj h) ▸ hI
  | cons a as ih =>
    intro env env' hI h
    rw [List.foldlM_cons] at h
    obtain ⟨e₁, h₁, h₂⟩ := exceptBind_ok h
    exact ih (hstep _ _ _ hI h₁) h₂

theorem installBasisDecl_preserves {ci : ConstantInfo} {k : BasisKind}
    (hI : NativeProjPinned env) (hmem : ci ∈ k.declsA)
    (h : installBasisDecl (m := CheckM) env ci = .ok env') :
    NativeProjPinned env' := by
  have hE := installBasisDecl_shape h
  subst hE
  intro e hmemc hnat
  rcases List.mem_cons.mp hmemc with rfl | hmem'
  · exact basis_native_pinned hmem hnat
  · exact hI e hmem' hnat

theorem installProjTemplate_preserves {T c : Name} {lps : List Name}
    {nP nF i : Nat} (hI : NativeProjPinned env)
    (h : installProjTemplate (m := CheckM) env T c lps nP nF i = .ok env') :
    NativeProjPinned env' := by
  rcases installProjTemplate_shape h with rfl | ⟨e₀, hn, rfl⟩
  · exact hI
  · exact hI.cons_template hn

/-! ### The block folds -/

theorem provisionRecs_preserves {blockNames : List Name} :
    ∀ {recs : List ConstantInfo} {envAcc envSelf : Env}
      {cs : List (ConstantVal × Nat × Nat × List RecRule)},
      NativeProjPinned envAcc →
      provisionRecs (m := CheckM) ops blockNames envAcc recs = .ok (envSelf, cs) →
      NativeProjPinned envSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf cs hI h
    exact (Prod.mk.inj (Except.ok.inj h)).1 ▸ hI
  | cons ci rest ih =>
    intro envAcc envSelf cs hI h
    unfold provisionRecs at h
    split at h
    · obtain ⟨cvA, -, h⟩ := exceptBind_ok h
      obtain ⟨q, hq, h⟩ := exceptBind_ok h
      obtain ⟨qe, qcs⟩ := q
      have hIq : NativeProjPinned qe := by
        refine ih ?_ hq
        intro e hmem hnat
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact nomatch heq
        · exact hI e hmem' hnat
      exact (Prod.mk.inj (Except.ok.inj h)).1 ▸ hIq
    · exact absurd h (by simp)

theorem checkIndRecs_preserves {blockNames : List Name}
    {recs : List ConstantInfo} (hI : NativeProjPinned env)
    (h : checkIndRecs (m := CheckM) mode ops blockNames env recs = .ok env') :
    NativeProjPinned env' := by
  unfold checkIndRecs at h
  split at h
  · exact (Except.ok.inj h) ▸ hI
  · repeat' first
      | (obtain ⟨_, -, h⟩ := exceptBind_ok h)
      | split at h
    all_goals first
      | (refine foldlM_preserves ?_ hI h
         intro e e' a hIe hs
         obtain ⟨_, -, hs⟩ := exceptBind_ok hs
         exact hIe.consed ⟨_, (fun e => by simp), (Except.ok.inj hs).symm⟩)
      | exact absurd h (by simp)

/-! ### The projection passes -/

theorem installProjFnStep_preserves {T ctorName : Name} {lps : List Name}
    {nP nF i : Nat} (hI : NativeProjPinned env)
    (h : installProjFnStep (m := CheckM) mode ops T ctorName lps nP nF env i
      = .ok env') : NativeProjPinned env' := by
  unfold installProjFnStep at h
  split at h
  · exact hI.consed (checkProjFn_consed h)
  · exact (Except.ok.inj h) ▸ hI

theorem installProjTemplateStep_preserves {T ctorName : Name} {lps : List Name}
    {nP nF i : Nat} (hI : NativeProjPinned env)
    (h : installProjTemplateStep (m := CheckM) T ctorName lps nP nF env i
      = .ok env') : NativeProjPinned env' := by
  unfold installProjTemplateStep at h
  split at h
  · exact installProjTemplate_preserves hI h
  · exact (Except.ok.inj h) ▸ hI

/-! ### The modeled block -/

/-- The member fold: `checkIndMember` conses an `indInfo` or a
`ctorInfo`, or throws. -/
theorem indMembers_preserves {blockNames : List Name} {caps : IndCaps}
    {nonrecs : List ConstantInfo} (hI : NativeProjPinned env)
    (h : nonrecs.foldlM (checkIndMember (m := CheckM) ops blockNames caps) env
      = .ok env') : NativeProjPinned env' := by
  refine foldlM_preserves ?_ hI h
  intro e e' a hIe hs
  exact hIe.consed (checkIndMember_consed hs)

theorem checkIndDecl_preserves {block : List ConstantInfo}
    (hI : NativeProjPinned env)
    (h : checkIndDecl (m := CheckM) mode ops env block = .ok env') :
    NativeProjPinned env' := by
  unfold checkIndDecl at h
  repeat' first
    | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
    | (obtain ⟨(_ : IndCaps), -, h⟩ := exceptBind_ok h)
    | (dsimp only at h)
    | split at h
  all_goals first
    -- the single-constructor arm: member fold, recursor group, the two
    -- guards, then the two projection passes
    | (obtain ⟨(envM : Env), hM, h⟩ := exceptBind_ok h
       obtain ⟨(envR : Env), hR, h⟩ := exceptBind_ok h
       have hIR : NativeProjPinned envR :=
         checkIndRecs_preserves (indMembers_preserves hI hM) hR
       repeat' first
         | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
         | (dsimp only at h)
         | split at h
       all_goals first
         | (obtain ⟨(envP : Env), hP, h⟩ := exceptBind_ok h
            have hIP : NativeProjPinned envP := by
              refine foldlM_preserves ?_ hIR hP
              intro e e' a hIe hs
              exact installProjFnStep_preserves hIe hs
            refine foldlM_preserves ?_ hIP h
            intro e e' a hIe hs
            exact installProjTemplateStep_preserves hIe hs)
         | exact absurd h (by simp))
    -- the general arm: member fold, then the recursor group
    | (obtain ⟨(envM : Env), hM, h⟩ := exceptBind_ok h
       exact checkIndRecs_preserves (indMembers_preserves hI hM) h)
    | exact absurd h (by simp)

/-! ### The direct structure (task #175 wiring: unreachable pre-flip)

`checkDirectProj` now installs **native tower-backed** projection
entries (`tower := true`), which the pin as stated excludes — the
post-flip invariant is the frozen disjunction (DESIGN, task #175
wiring, §2: `native → pair ∨ tower`), landing together with the infer
clause's `¬ tower` guard at the flip stage.  Pre-flip the arm is
unreachable — `directStructsEnabled = false` makes `directParts?`
return `none` on every input — and the walk discharges it by
computation, not by a preserved shape. -/

private theorem directParts?_none (env : Env) (block : List ConstantInfo) :
    directParts? env block = none := by
  unfold directParts?
  split
  · simp [directStructsEnabled]
  · rfl

/-! ### The declaration, and the stream -/

/-- A `foldlM` of steps that preserve *for the elements of the list*. -/
theorem foldlM_preserves_mem {α : Type} {f : Env → α → CheckM Env} :
    ∀ {l : List α},
      (∀ (e e' : Env) (a : α), a ∈ l → NativeProjPinned e → f e a = .ok e' →
        NativeProjPinned e') →
      ∀ {env env' : Env}, NativeProjPinned env →
        l.foldlM f env = .ok env' → NativeProjPinned env' := by
  intro l
  induction l with
  | nil => intro _ env env' hI h; exact (Except.ok.inj h) ▸ hI
  | cons a as ih =>
    intro hstep env env' hI h
    rw [List.foldlM_cons] at h
    obtain ⟨e₁, h₁, h₂⟩ := exceptBind_ok h
    exact ih (fun e e' b hb => hstep e e' b (List.mem_cons_of_mem _ hb))
      (hstep _ _ _ (List.mem_cons_self ..) hI h₁) h₂

/-- **One declaration preserves the pin.**  Six kinds, fourteen
extension sites, and not one of them needs a hypothesis beyond the
invariant itself. -/
theorem checkDecl_preserves {d : Declaration} (hI : NativeProjPinned env)
    (h : checkDecl (m := CheckM) mode ops env d = .ok env') :
    NativeProjPinned env' := by
  unfold checkDecl at h
  cases d with
  | defnDecl cv value hint =>
    dsimp only at h
    obtain ⟨(_ : ConstantVal), -, h⟩ := exceptBind_ok h
    obtain ⟨(env₂ : Env), h₂, h⟩ := exceptBind_ok h
    have hI₂ : NativeProjPinned env₂ := hI.consed (checkDefnVal_consed h₂)
    repeat' first
      | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
      | (obtain ⟨(_ : Bool), -, h⟩ := exceptBind_ok h)
      | (dsimp only at h)
      | split at h
    all_goals first
      | exact (Except.ok.inj h) ▸ hI₂
      | exact absurd h (by simp)
  | thmDecl cv value =>
    dsimp only at h
    obtain ⟨(_ : ConstantVal), -, h⟩ := exceptBind_ok h
    exact hI.consed (checkThmVal_consed h)
  | opaqueDecl cv value =>
    dsimp only at h
    obtain ⟨(_ : ConstantVal), -, h⟩ := exceptBind_ok h
    obtain ⟨(env₂ : Env), h₂, h⟩ := exceptBind_ok h
    have hI₂ : NativeProjPinned env₂ := hI.consed (checkOpaqueVal_consed h₂)
    repeat' first
      | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
      | (dsimp only at h)
      | split at h
    all_goals first
      | exact (Except.ok.inj h) ▸ hI₂
      | exact absurd h (by simp)
  | axiomDecl cv =>
    dsimp only at h
    obtain ⟨(_ : ConstantVal), -, h⟩ := exceptBind_ok h
    repeat' first
      | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
      | (dsimp only at h)
      | split at h
    all_goals first
      | exact (Except.ok.inj h) ▸ hI
      | exact hI.consed ⟨_, (fun e => by simp), (Except.ok.inj h).symm⟩
      | exact absurd h (by simp)
  | basisDecl kind =>
    dsimp only at h
    repeat' first
      | (obtain ⟨(_ : Unit), -, h⟩ := exceptBind_ok h)
      | (dsimp only at h)
      | split at h
    all_goals first
      | (refine foldlM_preserves_mem ?_ hI h
         intro e e' a ha hIe hs
         exact installBasisDecl_preserves hIe ha hs)
      | exact absurd h (by simp)
  | indDecl block =>
    dsimp only at h
    rw [directParts?_none] at h
    exact checkIndDecl_preserves hI h

/-- **The stream preserves the pin**, from the empty environment. -/
theorem checkDecls_nativeProjPinned {ds : List Declaration}
    (h : checkDecls (m := CheckM) mode ops ds = .ok env') :
    NativeProjPinned env' := by
  refine foldlM_preserves ?_ NativeProjPinned.empty h
  intro e e' a hIe hs
  exact checkDecl_preserves hIe hs


end Preservation

/-! ## The consumer-facing form

What the `.proj` inference clause needs, read off the invariant: the
entry's identity, and — from the lookup alone, no environment predicate
involved — the structure name and the index. -/

section Consumers

variable {env : Env} {sn : Name} {i : Nat} {entry : ProjEntry}

/-- A pinned entry's stored name pins the structure name and the index.
**This half needs no environment predicate at all** — only that the
lookup succeeded, since a table entry is stored under
`projFnName entry.structName entry.idx`. -/
theorem projEntry_names (hf : env.findProj? sn i = some entry)
    (hpin : entry = pairFstEntry ∨ entry = pairSndEntry) :
    sn = psigmaName ∧ entry.idx = i := by
  have h1 := List.find?_some (Env.findProj?_some hf)
  have h2 : (ConstantInfo.projInfo entry).name = projFnName sn i :=
    eq_of_beq (by simpa using h1)
  simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
  refine ⟨?_, (projFnName_inj h2).2⟩
  have hsn : entry.structName = sn := (projFnName_inj h2).1
  rw [← hsn]
  rcases hpin with rfl | rfl <;> rfl

/-- **The pin, from the install-time invariant.**  The premise-free
counterpart of `projEntry_pins`' first three conjuncts
(`SetBase/ProjPins.lean:41`): no `ProjOkT`, no environment record, no
tower.  The two stored-block conjuncts of that theorem are not here —
they are read only by the certified tiers' denotation lemmas and stay
where they are. -/
theorem NativeProjPinned.pinned (hI : NativeProjPinned env)
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      sn = psigmaName ∧ entry.idx = i :=
  let hpin := hI entry (List.mem_of_find?_eq_some (Env.findProj?_some hf)) hnat
  ⟨hpin, projEntry_names hf hpin⟩

/-- A pinned (pair-backed) entry is not tower-backed — what the
task-#175 tower branches guard on. -/
theorem NativeProjPinned.not_tower (hI : NativeProjPinned env)
    {sn : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    entry.tower = false := by
  obtain ⟨hpin, -, -⟩ := hI.pinned hf hnat
  rcases hpin with rfl | rfl <;> rfl

/-- The clause-level consequence, spelled out: at a `native` entry the
parameter spine has exactly two members and the index is `0` or `1`, so
the `.proj` inference clause's `.internal "malformed projection entry"`
branch is **unreachable** on any environment the checker builds. -/
theorem NativeProjPinned.spineShape (hI : NativeProjPinned env)
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    entry.numParams = 2 ∧ entry.levelParams.length = 2 ∧ i < 2 := by
  obtain ⟨hpin, -, hidx⟩ := hI.pinned hf hnat
  refine ⟨?_, ?_, ?_⟩ <;>
    rcases hpin with rfl | rfl <;>
      first
        | rfl
        | (rw [← hidx]; decide)

end Consumers

end Setlec
