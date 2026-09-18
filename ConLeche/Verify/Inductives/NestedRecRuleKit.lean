module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Denote.Install

public section

/-!
# The restored rules, positionally, and the auxiliary fire shape
(task #315 M7, item 5 step 2)

`NestedInv.lean` reads two facts off a `restoreRules` run — the
right-hand side is the restore of the auxiliary one
(`restoreRules_id`) and every stored constructor is a `ctorInfo`
(`restoreRules_ctorStored`).  The rule LAW (`RecRuleLaw`,
`Model/Annot/EnvModelM.lean`) needs the whole row, so this module adds

* `restoreRules_at` — the twin of `restoreRecTys_at` at the rules:
  rule `i` of the output is rule `i` of the input with the walk's
  right-hand side, the five scope guards the run checked, the
  `inferType` run that VALIDATES its binder data, the constructor's
  stored record (whose parameter count IS the stored `ctorParams`),
  the field count unchanged, `paramsBlind = !isMimic`, and the firing
  mode the run computed — `.plain`-or-`.inert` at a member's own
  recursor, the certified `.nested` shape at a mimic's;
* `nestedFireShape_inv` — the certificate itself, inverted: the
  recursor type's major domain is a constant-headed spine whose first
  `cnP` arguments are the pins lifted past the index binders and whose
  remaining `mI - rP` arguments are exactly those binders, with the
  pins scoped at the rule prefix and resolving at the environment.

Both are pure run inversions: no model, no reading.
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## A thrown step never succeeds -/

/-- A thrown step never succeeds (`NestedInv.lean`'s `nestThrow_ne_ok`,
whose `close_throw` is `local` to that module). -/
private theorem rkThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact rkThrow_ne_ok (by assumption))
        | (exfalso; exact rkThrow_ne_ok h)
        | (simp at h))

/-! ## The auxiliary fire shape, inverted -/

/-- **THE MIMIC RULE'S FIRE SHAPE** (`nestedFireShape`, the kernel's
certificate), inverted.  At a mimic recursor the stored fire is
`.nested lvls pins`, and this is everything the run checked to
produce it: the recursor type's major domain (the binder after the
`mI` recursor arguments) is an application of a CONSTANT at the
levels `lvls`, its `cnP + (mI - rP)` arguments split as the pins
lifted past the `mI - rP` index binders followed by those binders in
reverse, and each pin is fvar-free, scoped at the rule prefix `rP`,
resolves at the environment and mentions only the block's level
parameters. -/
theorem nestedFireShape_inv {envSelf : Env} {lps : List Name} {tyA : Expr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr}
    (h : nestedFireShape envSelf lps tyA mI rP cnP = some (lvls, pins)) :
    rP ≤ mI ∧
      ∃ (bs : List (Expr × BinderMeta)) (dom body : Expr) (bm : BinderMeta) (D : Name),
        tyA.stripPis mI = some (bs, .forallE dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs.length = cnP + (mI - rP) ∧
        pins = (dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0) ∧
        dom.getAppArgs.take cnP = pins.map (Expr.liftLooseBVars (mI - rP) 0) ∧
        dom.getAppArgs.drop cnP
          = (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)) ∧
        (∀ q ∈ pins, q.hasFvar = false ∧ q.looseBVarsBounded rP = true ∧
          q.constsResolve envSelf = true ∧ q.allLevelParamsDefined lps = true) ∧
        ∀ u ∈ lvls, Level.allParamsDefined lps u = true := by
  unfold nestedFireShape at h
  split at h
  case isFalse => exact nomatch h
  split at h
  case h_2 => exact nomatch h
  split at h
  case h_2 => exact nomatch h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hle _ bs dom body bm hsp _ D us hhd hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hlen, hlift, hdrop, hpins, hlvls⟩ := hcond
  refine ⟨hle, bs, dom, body, bm, D, hsp, hhd, hlen, rfl, eq_of_beq hlift,
    eq_of_beq hdrop, ?_, ?_⟩
  · intro q hq
    have hq' := List.all_eq_true.mp hpins q hq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq'
    exact ⟨hq'.1.1.1, hq'.1.1.2, hq'.1.2, hq'.2⟩
  · intro u hu
    exact List.all_eq_true.mp hlvls u hu

/-! ## The restored rules, positionally and in full -/

/-- **THE RESTORED RULES, IN FULL** (`restoreRecTys_at`'s twin at the
rules).  Rule `i` of the output is rule `i` of the input with

* the right-hand side the restore's (`restoreNested`), scoped at the
  block's level parameters, resolving at the environment, closed and
  fvar-free, its projection nodes naming the stored structures, and
  `inferType`-validated;
* the constructor a STORED constructor, whose stored parameter count
  IS the rule's `ctorParams` (K.24);
* the field count and `paramsBlind = !isMimic`;
* the firing mode the run computed. -/
theorem restoreRules_at {envR : Env} {R : RestoreTbl} {lps : List Name} {recName : Name}
    {isMimic : Bool} {recTy : Expr} {mI rP F : Nat} :
    ∀ {rules out : List RecRule},
      restoreRules (m := CheckM) (fueledOps mode F) envR R lps recName isMimic recTy mI rP
          rules = .ok out →
      out.length = rules.length ∧
      ∀ (i : Nat) (rl o : RecRule), rules[i]? = some rl → out[i]? = some o →
        restoreNested R rl.rhs = .ok o.rhs ∧
        o.rhs.allLevelParamsDefined lps = true ∧ o.rhs.constsResolve envR = true ∧
        o.rhs.looseBVarsBounded 0 = true ∧ o.rhs.hasFvar = false ∧
        o.rhs.projTablesOk envR = true ∧
        (∃ ty : Expr, inferTypeCore mode envR F 0 o.rhs = .ok ty) ∧
        (∃ (cvj : ConstantVal) (cnF : Nat),
          envR.find? o.ctor = some (.ctorInfo cvj o.ctorParams cnF)) ∧
        o.nfields = rl.nfields ∧ o.paramsBlind = !isMimic ∧
        (isMimic = false → o.ctor = rl.ctor ∧
          o.fire = (if Expr.recRulePlain recTy mI rP o.ctorParams then .plain else .inert)) ∧
        (isMimic = true →
          (∃ pn : Expr, R.ctorPins.find? (fun q => q.1 == rl.ctor)
            = some (rl.ctor, pn, o.ctor)) ∧
          o.fire = (match nestedFireShape envR lps recTy mI rP o.ctorParams with
            | some (lvls, pins) => .nested lvls pins
            | none => .inert)) := by
  intro rules
  induction rules with
  | nil =>
    intro out h
    simp only [restoreRules, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨by rw [← h], fun i rl o hr _ => by simp at hr⟩
  | cons rl rest ih =>
    intro out h
    unfold restoreRules at h
    obtain ⟨rhsA, hrhs, h⟩ := exceptBind_ok h
    have hrhs' := nestedLift_ok hrhs
    by_cases h1 : (rhsA.allLevelParamsDefined lps && rhsA.constsResolve envR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar) = true
    case neg => rw [if_neg h1] at h; close_throw
    rw [if_pos h1] at h
    try simp only [bind, Except.bind] at h
    by_cases h2 : rhsA.projTablesOk envR = true
    case neg => rw [if_neg h2] at h; close_throw
    rw [if_pos h2] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    try simp only at h
    by_cases h3 : (!isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor)) = true
    case neg => rw [if_neg h3] at h; close_throw
    rw [if_pos h3] at h
    try simp only [bind, Except.bind] at h
    split at h
    case h_2 => close_throw
    rename_i cvj cnP cnF hfind
    try simp only [pure, Except.pure] at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [Except.ok.injEq] at h
    obtain rfl := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i rl' o hr ho
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr ho
      obtain rfl := hr
      obtain rfl := ho
      cases isMimic with
      | false =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        simp only [recRuleBits_rhs, recRuleBits_ctor, recRuleBits_ctorParams,
          recRuleBits_nfields, recRuleBits_fire, recRuleBits_paramsBlind,
          Bool.false_eq_true, if_false]
        exact ⟨hrhs', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, h2, ⟨ty, hty⟩,
          ⟨cvj, cnF, hfind⟩, trivial, trivial, fun _ => ⟨trivial, trivial⟩, fun hc => hc.elim⟩
      | true =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        have hany : ∃ x, x ∈ R.ctorPins ∧ (x.1 == rl.ctor) = true := by
          simpa using h3
        obtain ⟨⟨c0, pn, nm⟩, hf⟩ :=
          Option.isSome_iff_exists.mp (List.find?_isSome.mpr hany)
        have hp : ((c0, pn, nm).1 == rl.ctor) = true :=
          List.find?_some (p := fun q : Name × Expr × Name => q.1 == rl.ctor) hf
        have hc0 : c0 = rl.ctor := beq_iff_eq.mp hp
        subst hc0
        simp only [recRuleBits_rhs, recRuleBits_ctor, recRuleBits_ctorParams,
          recRuleBits_nfields, recRuleBits_fire, recRuleBits_paramsBlind, if_true]
        refine ⟨hrhs', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, h2, ⟨ty, hty⟩,
          ⟨cvj, cnF, hfind⟩, trivial, trivial, fun hc => absurd hc (by simp),
          fun _ => ⟨⟨pn, ?_⟩, rfl⟩⟩
        rw [hf]
    | succ n =>
      simp only [List.getElem?_cons_succ] at hr ho
      exact hall n rl' o hr ho

/-! ## The rule-less provision's lookups (`provisionNestedRecs`)

The mutual route's four lookup facts about `provisionMutualRecs`
(`MutualRecsSwap.lean`, `MutualRecsStore.lean`, `BlockRepCross.lean`)
at the NESTED route's loop, whose list is one of TRIPLES
`(cvRa, mI, rP)`: the read-back supplies each recursor's argument sums
per entry where the mutual route computes them from the block, so the
consed head is `recInfo x.1 x.2.1 x.2.2 []` and nothing else differs.
-/

/-- The provision's lookups, at a name none of the provisioned
recursors carries: the base environment's
(`provisionMutualRecs_find?_of_ne`'s twin). -/
theorem provisionNestedRecs_find?_of_ne :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (provisionNestedRecs l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mI, rP) :: rest, env, n, hne => by
    show (provisionNestedRecs rest ⟨.recInfo cvRa mI rP [] :: env.consts⟩).find? n = env.find? n
    rw [provisionNestedRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons, if_neg (fun hh => hne (cvRa, mI, rP) List.mem_cons_self hh.symm)]

/-- The provision stores every entry rule-less under its own name
(`provisionMutualRecs_find?_mem`'s twin). -/
theorem provisionNestedRecs_find?_mem :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} {x : ConstantVal × Nat × Nat},
      (l.map (·.1.name)).Nodup → x ∈ l →
      (provisionNestedRecs l env).find? x.1.name
        = some (.recInfo x.1 x.2.1 x.2.2 [])
  | [], _, _, _, hx => absurd hx (by simp)
  | (cvRa, mI, rP) :: rest, env, x, hnd, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show (provisionNestedRecs rest ⟨.recInfo cvRa mI rP [] :: env.consts⟩).find? x.1.name = _
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [provisionNestedRecs_find?_of_ne (fun y hy heq => hnd.1 (by
        rw [heq]; exact List.mem_map_of_mem hy))]
      exact Env.find?_cons_self _ _
    · exact provisionNestedRecs_find?_mem hnd.2 hx'

/-- **The provision's stored entries survive its own conses**: a name
the restored constructors' environment already carries is found
unchanged past the `k + nPins` fresh recursors
(`provisionMutualRecs_findPreserved`'s twin). -/
theorem provisionNestedRecs_findPreserved {l : List (ConstantVal × Nat × Nat)} {env : Env}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none) :
    ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      (provisionNestedRecs l env).find? n = some ci := by
  intro n ci hf
  rw [provisionNestedRecs_find?_of_ne ?ne]
  · exact hf
  case ne =>
    intro x hx hn
    have := hfresh x hx
    rw [← hn, hf] at this
    exact nomatch this

/-- **NO PROJECTION TABLE APPEARS**: every cons of the provision is a
RECURSOR, so where the base environment has no table neither does the
provisioned one (`findProj?_cons_of_base_none`, the third component of
`provisionMutualRecs_extend`). -/
theorem provisionNestedRecs_findProj?_none :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} (sn : Name) (i : Nat),
      env.findProj? sn i = none → (provisionNestedRecs l env).findProj? sn i = none
  | [], _, _, _, h => h
  | (cvRa, mI, rP) :: rest, env, sn, i, h => by
    show (provisionNestedRecs rest ⟨.recInfo cvRa mI rP [] :: env.consts⟩).findProj? sn i = none
    exact provisionNestedRecs_findProj?_none sn i
      (Verify.findProj?_cons_of_base_none (c₀ := .recInfo cvRa mI rP [])
        (fun _ hh => nomatch hh) sn i h)

/-- **NO PROJECTION TABLE MOVES ACROSS THE PROVISION**: the conses are
recursors at names the environment does not carry, so a table lookup is
answered the same below and above them.  Stated through the tree's
`findProj?` API (`Env.findProj?_some`/`_of_table`) — never by unfolding
`Env.findProj?`. -/
theorem provisionNestedRecs_findProj?_eq {l : List (ConstantVal × Nat × Nat)} {env : Env}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none) :
    ∀ (sn : Name) (i : Nat), (provisionNestedRecs l env).findProj? sn i = env.findProj? sn i := by
  intro sn i
  cases h : env.findProj? sn i with
  | none => exact provisionNestedRecs_findProj?_none sn i h
  | some entry =>
    obtain ⟨tbl, h0, hi, rfl⟩ := Env.findProj?_some h
    exact Env.findProj?_of_table (provisionNestedRecs_findPreserved hfresh _ _ h0) hi

end ConLeche
