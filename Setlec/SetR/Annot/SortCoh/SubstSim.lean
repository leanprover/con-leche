import Setlec.SetR.Annot.SortCoh.Theta

/-!
# Run-level sort coherence — the substitution simulation (map, helpers, induction)

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-! ### The substitution simulation (the Θ push's engine): map seal

The det-sync break one push in (the run processes *opened* cores, the
loops *substituted* ones) is answered by a forward-only simulation:
the substituted image of an opened core/loop run is itself reachable
by GATE-FREE reduction steps.  `RawReach` is that image trace — it
mirrors the kernel's clause structure (head congruence, β/ζ at the
node, the two literal conversions, δ, the nat rows, the three iota
rows, the projection fire) but carries **no certificate gates**
(infer/defeq/level checks): the walk re-decomposes the loops' actual
runs from the image point by determinism, and a sort-successful run
*forces* every gate along the trace (a stuck non-sort endpoint
contradicts the success).  The relation is budget-indexed (`G`
ceilings the one carried run — the string-literal expansion's closed
whnf — honoring the both-fuel-bounds design axiom; consumption is
det-only, so a ceiling plus weakening suffices).  The rescue rows
(K/eta) carry their fabrication data existentially (`ust`, `targs`
are infer-derived on the opened side — "only eta carries
infer-lockstep"; the sort-level seam is `EtaRescueSortAgree`'s).
There is deliberately NO free argument-position congruence: a
gratuitous argument step would break the endpoint's syntactic
agreement with the actual run — majors reach only *inside* the iota
rows, where the fire consumes them. -/
inductive RawReach (μ : CheckMode) (env : Env) (d G : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : RawReach μ env d G e e
  | appL {f f' : Expr} (x : Expr) {w : Expr}
      (h : RawReach μ env d G f f')
      (rest : RawReach μ env d G (.app f' x) w) :
      RawReach μ env d G (.app f x) w
  | projC (sn : Name) (i : Nat) {pe pe' w : Expr}
      (h : RawReach μ env d G pe pe')
      (rest : RawReach μ env d G (.proj sn i pe') w) :
      RawReach μ env d G (.proj sn i pe) w
  | beta (n : Name) (ty b x : Expr) (m : Setlec.BinderMeta)
      {w : Expr}
      (rest : RawReach μ env d G (b.instantiate1 x) w) :
      RawReach μ env d G (.app (.lam n ty b m) x) w
  | zeta (n : Name) (ty v b : Expr) {w : Expr}
      (rest : RawReach μ env d G (b.instantiate1 v) w) :
      RawReach μ env d G (.letE n ty v b) w
  | litNat (e : Expr) {w : Expr}
      (rest : RawReach μ env d G (Setlec.litToCtorIfNat env e) w) :
      RawReach μ env d G e w
  | litStr (s : String) (g : Nat) {t w : Expr}
      (hg : g ≤ G)
      (hs : Setlec.strLitSupported env = true)
      (hr : whnf μ env g d (Setlec.strLitToConstructor s) = .ok t)
      (rest : RawReach μ env d G t w) :
      RawReach μ env d G (.lit (.strVal s)) w
  | delta {e e' w : Expr}
      (h : unfoldDefinition env e = some e')
      (rest : RawReach μ env d G e' w) : RawReach μ env d G e w
  | natSucc (x : Expr) {ax : Expr} (n : Nat) {w : Expr}
      (hs : Setlec.natLitSupported env = true)
      (hx : RawReach μ env d G x ax)
      (hnl : Setlec.rawNatLit? ax = some n)
      (rest : RawReach μ env d G (.lit (.natVal (n + 1))) w) :
      RawReach μ env d G (.app (.const Setlec.natSuccName []) x) w
  | natU1 (c : Name) (x : Expr) {ax : Expr} (n : Nat) {res w : Expr}
      (hc : c = Setlec.natPredName ∨ c = Setlec.natLog2Name)
      (hg : Setlec.natOpGuard env c = true)
      (hx : RawReach μ env d G x ax)
      (hnl : Setlec.rawNatLit? ax = some n)
      (hres : Setlec.natOpResult c n 0 = some res)
      (rest : RawReach μ env d G res w) :
      RawReach μ env d G (.app (.const c []) x) w
  | natB (c : Name) (x y : Expr) {ax ay : Expr} (n₁ n₂ : Nat)
      {res w : Expr}
      (hc : c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName)
      (hg : Setlec.natOpGuard env c = true)
      (hx : RawReach μ env d G x ax)
      (hy : RawReach μ env d G y ay)
      (hnx : Setlec.rawNatLit? ax = some n₁)
      (hny : Setlec.rawNatLit? ay = some n₂)
      (hres : Setlec.natOpResult c n₁ n₂ = some res)
      (rest : RawReach μ env d G res w) :
      RawReach μ env d G (.app (.app (.const c []) x) y) w
  | iotaPlain (c : Name) (us : List Level) {e : Expr}
      (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rules : List Setlec.RecRule) (rl : Setlec.RecRule)
      (cj : Name) (usj : List Level) {M w : Expr}
      (hfn : e.getAppFn = .const c us)
      (hc : env.find? c = some (.recInfo cv mI rP rules))
      (hlen : e.getAppArgs.length = mI + 1)
      (hM : RawReach μ env d G (e.getAppArgs.getD mI (.bvar 0)) M)
      (hMfn : M.getAppFn = .const cj usj)
      (hrl : rules.find? (fun r' => r'.ctor == cj) = some rl)
      (hml : M.getAppArgs.length = rl.ctorParams + rl.nfields)
      (hnin : rl.fire ≠ .inert)
      (rest : RawReach μ env d G
        (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP
            ++ M.getAppArgs.drop rl.ctorParams)) w) :
      RawReach μ env d G e w
  | iotaK (c : Name) (us : List Level) {e : Expr}
      (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rl : Setlec.RecRule)
      (cvj : Setlec.ConstantVal) (cnP : Nat)
      (T : Name) (usT : List Level)
      (cvT : Setlec.ConstantVal) (caps : Setlec.IndCaps)
      (targs : List Expr) {M w : Expr}
      (hfn : e.getAppFn = .const c us)
      (hc : env.find? c = some (.recInfo cv mI rP [rl]))
      (hlen : e.getAppArgs.length = mI + 1)
      (hM : RawReach μ env d G (e.getAppArgs.getD mI (.bvar 0)) M)
      (hcj : env.find? rl.ctor = some (.ctorInfo cvj cnP 0))
      (hT : cvj.type.piResult.getAppFn = .const T usT)
      (hTi : env.find? T = some (.indInfo cvT caps))
      (hK : caps.ruleK = true)
      (hml : (targs.take cnP).length = rl.ctorParams + rl.nfields)
      (rest : RawReach μ env d G
        (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP
            ++ (targs.take cnP).drop rl.ctorParams)) w) :
      RawReach μ env d G e w
  | iotaEta (c : Name) (us ust : List Level) {e : Expr}
      (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rl : Setlec.RecRule)
      (cvj : Setlec.ConstantVal) (cnP cnF : Nat)
      (T : Name) (usT : List Level)
      (cvT : Setlec.ConstantVal) (caps : Setlec.IndCaps)
      (targs : List Expr) {M w : Expr}
      (hfn : e.getAppFn = .const c us)
      (hc : env.find? c = some (.recInfo cv mI rP [rl]))
      (hlen : e.getAppArgs.length = mI + 1)
      (hM : RawReach μ env d G (e.getAppArgs.getD mI (.bvar 0)) M)
      (hcj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
      (hT : cvj.type.piResult.getAppFn = .const T usT)
      (hTi : env.find? T = some (.indInfo cvT caps))
      (heta : caps.eta = true)
      (hec : rl.ctor = caps.etaCtor)
      (hml : (Setlec.etaFabArgs T ust targs M caps.etaFields).length
        = rl.ctorParams + rl.nfields)
      (rest : RawReach μ env d G
        (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP
            ++ (Setlec.etaFabArgs T ust targs M caps.etaFields).drop
              rl.ctorParams)) w) :
      RawReach μ env d G e w
  | projFire (sn : Name) (i : Nat) {E w : Expr}
      (entry : Setlec.ProjEntry) (us : List Level)
      (hf : env.findProj? sn i = some entry)
      (hfn : E.getAppFn = .const entry.ctor us)
      (hnat : entry.native = true)
      (hi : i < entry.numFields)
      (hlenE : E.getAppArgs.length
        = entry.numParams + entry.numFields)
      (rest : RawReach μ env d G
        (E.getAppArgs.getD (entry.numParams + i) (.bvar 0)) w) :
      RawReach μ env d G (.proj sn i E) w

/-- The image trace composes. -/
theorem RawReach.trans {μ : CheckMode} {env : Env} {d G : Nat}
    {u v x : Expr} (h₁ : RawReach μ env d G u v)
    (h₂ : RawReach μ env d G v x) : RawReach μ env d G u x := by
  revert h₂
  induction h₁ with
  | refl e => exact fun h₂ => h₂
  | appL xa h rest ihh ihr =>
    exact fun h₂ => .appL xa h (ihr h₂)
  | projC sn i h rest ihh ihr =>
    exact fun h₂ => .projC sn i h (ihr h₂)
  | beta n ty b xa m rest ih =>
    exact fun h₂ => .beta n ty b xa m (ih h₂)
  | zeta n ty v' b rest ih =>
    exact fun h₂ => .zeta n ty v' b (ih h₂)
  | litNat e rest ih => exact fun h₂ => .litNat e (ih h₂)
  | litStr s g hg hs hr rest ih =>
    exact fun h₂ => .litStr s g hg hs hr (ih h₂)
  | delta h rest ih => exact fun h₂ => .delta h (ih h₂)
  | natSucc xa n hs hx hnl rest ihx ihr =>
    exact fun h₂ => .natSucc xa n hs hx hnl (ihr h₂)
  | natU1 c xa n hc hg hx hnl hres rest ihx ihr =>
    exact fun h₂ => .natU1 c xa n hc hg hx hnl hres (ihr h₂)
  | natB c xa ya n₁ n₂ hc hg hx hy hnx hny hres rest ihx ihy ihr =>
    exact fun h₂ => .natB c xa ya n₁ n₂ hc hg hx hy hnx hny hres
      (ihr h₂)
  | iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen hM hMfn hrl
      hml hnin rest ihM ihr =>
    exact fun h₂ => .iotaPlain c us cv mI rP rules rl cj usj hfn hc
      hlen hM hMfn hrl hml hnin (ihr h₂)
  | iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn hc hlen
      hM hcj hT hTi hK hml rest ihM ihr =>
    exact fun h₂ => .iotaK c us cv mI rP rl cvj cnP T usT cvT caps
      targs hfn hc hlen hM hcj hT hTi hK hml (ihr h₂)
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml rest ihM ihr =>
    exact fun h₂ => .iotaEta c us ust cv mI rP rl cvj cnP cnF T usT
      cvT caps targs hfn hc hlen hM hcj hT hTi heta hec hml (ihr h₂)
  | projFire sn i entry us hf hfn hnat hi hlenE rest ih =>
    exact fun h₂ => .projFire sn i entry us hf hfn hnat hi hlenE
      (ih h₂)

/-- The budget ceiling weakens. -/
theorem RawReach.mono_budget {μ : CheckMode} {env : Env}
    {d G G' : Nat} (hG : G ≤ G') {u v : Expr}
    (h : RawReach μ env d G u v) : RawReach μ env d G' u v := by
  induction h with
  | refl e => exact .refl e
  | appL x h rest ih₁ ih₂ => exact .appL x ih₁ ih₂
  | projC sn i h rest ih₁ ih₂ => exact .projC sn i ih₁ ih₂
  | beta n ty b x m rest ih => exact .beta n ty b x m ih
  | zeta n ty v b rest ih => exact .zeta n ty v b ih
  | litNat e rest ih => exact .litNat e ih
  | litStr s g hg hs hr rest ih =>
    exact .litStr s g (Nat.le_trans hg hG) hs hr ih
  | delta h rest ih => exact .delta h ih
  | natSucc x n hs hx hnl rest ih₁ ih₂ =>
    exact .natSucc x n hs ih₁ hnl ih₂
  | natU1 c x n hc hg hx hnl hres rest ih₁ ih₂ =>
    exact .natU1 c x n hc hg ih₁ hnl hres ih₂
  | natB c x y n₁ n₂ hc hg hx hy hnx hny hres rest ih₁ ih₂ ih₃ =>
    exact .natB c x y n₁ n₂ hc hg ih₁ ih₂ hnx hny hres ih₃
  | iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen hM hMfn hrl
      hml hnin rest ih₁ ih₂ =>
    exact .iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen ih₁
      hMfn hrl hml hnin ih₂
  | iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn hc hlen
      hM hcj hT hTi hK hml rest ih₁ ih₂ =>
    exact .iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn
      hc hlen ih₁ hcj hT hTi hK hml ih₂
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml rest ih₁ ih₂ =>
    exact .iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps
      targs hfn hc hlen ih₁ hcj hT hTi heta hec hml ih₂
  | projFire sn i entry us hf hfn hnat hi hlenE rest ih =>
    exact .projFire sn i entry us hf hfn hnat hi hlenE ih

/-- **The core simulation claim** at one knot fuel: a depth-`(d+1)`
`whnfCore` run on an opened, locally closed subject maps — under the
one-binder telescope substitution at cursor 0 — to a gate-free image
trace at depth `d`, ceilinged by the run's own knot fuel. -/
def WhnfCoreSubstSimF (μ : CheckMode) (env : Env)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a e e' : Expr},
    a.looseBVarsBounded 0 = true → Expr.WScoped d a →
    e.looseBVarsBounded 0 = true → Expr.WScoped (d + 1) e →
    whnfCore μ env fuel (d + 1) e = .ok e' →
    RawReach μ env d fuel (substAK d 0 a e) (substAK d 0 a e')

/-- **The loop simulation claim** at one knot fuel (any loop
budget): a depth-`(d+1)` `whnfLoop` run maps to the gate-free image
trace at depth `d`. -/
def WhnfLoopSubstSimF (μ : CheckMode) (env : Env)
    (fuel : Nat) : Prop :=
  ∀ {d l : Nat} {a e e' : Expr},
    a.looseBVarsBounded 0 = true → Expr.WScoped d a →
    e.looseBVarsBounded 0 = true → Expr.WScoped (d + 1) e →
    Setlec.whnfLoop (Setlec.pureFns μ env fuel) env (d + 1) l e
      = .ok e' →
    RawReach μ env d fuel (substAK d 0 a e) (substAK d 0 a e')

/-- **The entry-point simulation claim** at one knot fuel (map
amendment at the induction's pre-build: the knot's bodies see the
predecessor record, so the core body's internal `r.whnf` runs are
`whnf`-at-`fuel` — the loop claim alone does not cover them). -/
def WhnfSubstSimF (μ : CheckMode) (env : Env)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a e e' : Expr},
    a.looseBVarsBounded 0 = true → Expr.WScoped d a →
    e.looseBVarsBounded 0 = true → Expr.WScoped (d + 1) e →
    whnf μ env fuel (d + 1) e = .ok e' →
    RawReach μ env d fuel (substAK d 0 a e) (substAK d 0 a e')

/-- The substitution simulation, all tiers at one knot fuel (the
`ShiftClaims` pattern; the mutual induction discharges the three in
order — `whnf` from the predecessor's loop, `core` from the body,
`loop` from `core` and `whnf` at the same fuel). -/
structure SubstSimClaims (μ : CheckMode) (env : Env)
    (fuel : Nat) : Prop where
  core : WhnfCoreSubstSimF μ env fuel
  whnf : WhnfSubstSimF μ env fuel
  loop : WhnfLoopSubstSimF μ env fuel

/-! #### The sim's helper kit (spine images, unfolding, closed-run
depth transport) -/

/-- A term with no reachable `fvar` leaves has no `fvar` at all. -/
theorem not_hasFvar_of_fvarLeaves_nil :
    ∀ {e : Expr}, e.fvarLeaves = [] → e.hasFvar = false := by
  intro e
  induction e <;>
    simp_all [Setlec.Expr.fvarLeaves, Setlec.Expr.hasFvar,
      List.append_eq_nil_iff]

/-- The telescope substitution on a const-headed spine: same head,
mapped arguments. -/
theorem substAK_of_const_head {d k : Nat} {a e : Expr} {c : Name}
    {us : List Level} (hfn : e.getAppFn = .const c us) :
    substAK d k a e
      = Setlec.Expr.mkAppN (.const c us)
          (e.getAppArgs.map (substAK d k a)) := by
  have he := (Setlec.Expr.mkAppN_getApp e).symm
  rw [hfn] at he
  rw [he, substAK_mkAppN, Setlec.Expr.getAppArgs_mkAppN]
  rfl

/-- The image spine's head. -/
theorem substAK_getAppFn_const {d k : Nat} {a e : Expr} {c : Name}
    {us : List Level} (hfn : e.getAppFn = .const c us) :
    (substAK d k a e).getAppFn = .const c us := by
  rw [substAK_of_const_head hfn, Setlec.Expr.getAppFn_mkAppN]
  rfl

/-- The image spine's arguments. -/
theorem substAK_getAppArgs_const {d k : Nat} {a e : Expr} {c : Name}
    {us : List Level} (hfn : e.getAppFn = .const c us) :
    (substAK d k a e).getAppArgs
      = e.getAppArgs.map (substAK d k a) := by
  rw [substAK_of_const_head hfn, Setlec.Expr.getAppArgs_mkAppN]
  rfl

/-- Delta commutes with the telescope substitution: the head constant
and the stored (closed) value are invariant, the spine maps. -/
theorem substAK_unfoldDefinition {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} {d k : Nat} {a : Expr}
    (h : unfoldDefinition env e = some e₂) :
    unfoldDefinition env (substAK d k a e)
      = some (substAK d k a e₂) := by
  unfold Setlec.unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  have himg : unfoldDefinition env (substAK d k a e)
      = match env.find? n with
        | some (.defnInfo cv value _) =>
          if us.length = cv.levelParams.length then
            some (Setlec.Expr.mkAppN
              (value.instantiateLevelParams cv.levelParams us)
              (substAK d k a e).getAppArgs)
          else none
        | some (.thmInfo cv value) =>
          if us.length = cv.levelParams.length then
            some (Setlec.Expr.mkAppN
              (value.instantiateLevelParams cv.levelParams us)
              (substAK d k a e).getAppArgs)
          else none
        | _ => none := by
    unfold Setlec.unfoldDefinition
    rw [substAK_getAppFn_const hfn]
    rfl
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    dsimp only at h
    revert h
    split
    next hlen =>
      intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, -, -, hval⟩ :=
        henv _ (Setlec.find?_mem hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
      rw [himg, hf]
      dsimp only
      rw [if_pos hlen, substAK_getAppArgs_const hfn, substAK_mkAppN]
      rw [substAK_eq_self
        (by
          rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hvc)]
          exact fun l hl => absurd hl List.not_mem_nil)
        (by
          rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
          exact looseBVarsBounded_mono (Nat.zero_le _) hvb)]
    next => intro h; exact nomatch h
  | some (.defnInfo cv value hint) =>
    intro h
    dsimp only at h
    revert h
    split
    next hlen =>
      intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, hval, -⟩ :=
        henv _ (Setlec.find?_mem hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value hint rfl
      rw [himg, hf]
      dsimp only
      rw [if_pos hlen, substAK_getAppArgs_const hfn, substAK_mkAppN]
      rw [substAK_eq_self
        (by
          rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hvc)]
          exact fun l hl => absurd hl List.not_mem_nil)
        (by
          rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
          exact looseBVarsBounded_mono (Nat.zero_le _) hvb)]
    next => intro h; exact nomatch h

/-- The eta fabrication maps componentwise under the substitution. -/
theorem substAK_etaFabArgs {d k : Nat} {a : Expr} (T : Name)
    (ust : List Level) (targs : List Expr) (M : Expr) (nF : Nat) :
    (Setlec.etaFabArgs T ust targs M nF).map (substAK d k a)
      = Setlec.etaFabArgs T ust (targs.map (substAK d k a))
          (substAK d k a M) nF := by
  unfold Setlec.etaFabArgs
  rw [List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  show substAK d k a
      (Setlec.Expr.mkAppN (.const (Setlec.projFnName T j) ust)
        (targs ++ [M])) = _
  rw [substAK_mkAppN, List.map_append]
  rfl

/-- A closed run transports one depth down (the discharged
`ShiftClaims` battery at `shiftFrom 0` = identity on `fvar`-free
terms). -/
theorem whnf_closed_depth_down {env : Env} (henv : EnvWF env)
    {g d : Nat} {e t : Expr} (hfv : e.hasFvar = false)
    (h : whnf μ env g (d + 1) e = .ok t) :
    whnf μ env g d e = .ok t := by
  have hsc := (Setlec.shiftClaims (mode := μ) (env := env) henv
    g).whnf (p := 0) (Nat.zero_le d) (e := e)
    (Setlec.Expr.WScoped.of_not_hasFvar hfv)
  rw [Setlec.Expr.shiftFrom_eq_self_of_not_hasFvar hfv, h] at hsc
  cases hw : whnf μ env g d e with
  | error err =>
    rw [hw] at hsc
    exact nomatch hsc
  | ok t' =>
    rw [hw] at hsc
    simp only [Except.map, Except.ok.injEq] at hsc
    have hfv' : t'.hasFvar = false := by
      apply not_hasFvar_of_fvarLeaves_nil
      have hsub := Setlec.whnf_leaves (mode := μ) henv g hw
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv] at hsub
      cases hl : t'.fvarLeaves with
      | nil => rfl
      | cons x xs =>
        exact absurd (hsub x (by rw [hl]; exact List.mem_cons_self))
          List.not_mem_nil
    rw [Setlec.Expr.shiftFrom_eq_self_of_not_hasFvar hfv'] at hsc
    rw [hsc]

/-! #### The substitution simulation: the induction -/

/-- `Nat`-literal constructor forms are closed. -/
theorem natLitToConstructor_closed (n : Nat) :
    (Setlec.natLitToConstructor n).hasFvar = false ∧
    (Setlec.natLitToConstructor n).looseBVarsBounded 0 = true := by
  cases n <;>
    simp [Setlec.natLitToConstructor, Setlec.Expr.hasFvar,
      Setlec.Expr.looseBVarsBounded]

/-- The string-literal expansion is `fvar`-free. -/
theorem strLitToConstructor_not_hasFvar (s : String) :
    (Setlec.strLitToConstructor s).hasFvar = false :=
  not_hasFvar_of_fvarLeaves_nil
    (Setlec.strLitToConstructor_leaves_nil s)

/-- The string-literal expansion is locally closed. -/
theorem strLitToConstructor_bounded (s : String) :
    (Setlec.strLitToConstructor s).looseBVarsBounded 0 = true := by
  unfold Setlec.strLitToConstructor
  simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
  refine ⟨trivial, ?_⟩
  induction s.toList with
  | nil => rfl
  | cons c cs ih =>
    simp [Setlec.Expr.looseBVarsBounded, ih]

/-- `getD` under `map`, inside the bound. -/
theorem getD_map_lt {f : Expr → Expr} {l : List Expr} {i : Nat}
    (h : i < l.length) :
    (l.map f).getD i (.bvar 0) = f (l.getD i (.bvar 0)) := by
  rw [getD_eq_getElem' (by simpa using h), getD_eq_getElem' h,
    List.getElem_map]

/-- A `rawNatLit?` reading survives the substitution (the readable
forms are closed). -/
theorem substAK_of_rawNatLit {w : Expr} {n : Nat}
    (h : Setlec.rawNatLit? w = some n) {d k : Nat} {a : Expr} :
    substAK d k a w = w := by
  match w, h with
  | .lit (.natVal _), _ => rfl
  | .const c [], _ => rfl

/-- Decomposition of a fired `reduceNat`: the row, its argument
runs, the literal readings and the computed result. -/
theorem reduceNat_decompose {env : Env} {fuel d : Nat} {e e₂ : Expr}
    (h : Setlec.reduceNatP μ env fuel d e = .ok (some e₂)) :
    (∃ x wx n, e = .app (.const Setlec.natSuccName []) x ∧
      Setlec.natLitSupported env = true ∧
      whnf μ env fuel d x = .ok wx ∧
      Setlec.rawNatLit? wx = some n ∧
      e₂ = .lit (.natVal (n + 1))) ∨
    (∃ c x wx n, e = .app (.const c []) x ∧
      (c = Setlec.natPredName ∨ c = Setlec.natLog2Name) ∧
      Setlec.natOpGuard env c = true ∧
      whnf μ env fuel d x = .ok wx ∧
      Setlec.rawNatLit? wx = some n ∧
      Setlec.natOpResult c n 0 = some e₂) ∨
    (∃ c x y wx wy n₁ n₂, e = .app (.app (.const c []) x) y ∧
      (c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨
        c = Setlec.natShiftRightName) ∧
      Setlec.natOpGuard env c = true ∧
      whnf μ env fuel d x = .ok wx ∧
      Setlec.rawNatLit? wx = some n₁ ∧
      whnf μ env fuel d y = .ok wy ∧
      Setlec.rawNatLit? wy = some n₂ ∧
      Setlec.natOpResult c n₁ n₂ = some e₂) := by
  dsimp only [Setlec.reduceNatP] at h
  revert h
  match e with
  | .app (.const c []) a => ?_
  | .app (.app (.const c []) a) b => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
  | .const _ _ =>
    intro h; simp [Setlec.reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _ | .app (.fvar _ _ _) _ | .app (.sort _) _
  | .app (.lam _ _ _ _) _ | .app (.forallE _ _ _ _) _
  | .app (.letE _ _ _ _) _ | .app (.lit _) _
  | .app (.proj _ _ _) _ =>
    intro h; simp [Setlec.reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _ =>
    intro h; simp [Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _ | .app (.app (.fvar _ _ _) _) _
  | .app (.app (.sort _) _) _ | .app (.app (.app _ _) _) _
  | .app (.app (.lam _ _ _ _) _) _
  | .app (.app (.forallE _ _ _ _) _) _
  | .app (.app (.letE _ _ _ _) _) _ | .app (.app (.lit _) _) _
  | .app (.app (.proj _ _ _) _) _ =>
    intro h; simp [Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _ =>
    intro h; simp [Setlec.reduceNat, pure, Except.pure] at h
  · -- unary rows
    intro h
    simp only [Setlec.reduceNat, Bind.bind, Except.bind,
      Setlec.whnf_def] at h
    revert h
    split
    next hrow =>
      intro h
      cases hwa : whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        dsimp only at h
        revert h
        cases hnl : Setlec.rawNatLit? wa with
        | none => intro h; simp [pure, Except.pure] at h
        | some n =>
          intro h
          simp only [pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h
          exact Or.inl ⟨a, wa, n, by rw [hrow.1], hrow.2, hwa,
            hnl, h.symm⟩
    next hrow =>
      split
      next hrow2 =>
        intro h
        cases hwa : whnf μ env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          dsimp only at h
          revert h
          cases hnl : Setlec.rawNatLit? wa with
          | none => intro h; simp [pure, Except.pure] at h
          | some n =>
            intro h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            exact Or.inr (Or.inl ⟨c, a, wa, n, rfl, .inl hrow2.1,
              hrow2.2, hwa, hnl, h⟩)
      next hrow2 =>
        split
        next hrow3 =>
          intro h
          cases hwa : whnf μ env fuel d a with
          | error err => rw [hwa] at h; exact nomatch h
          | ok wa =>
            rw [hwa] at h
            dsimp only at h
            revert h
            cases hnl : Setlec.rawNatLit? wa with
            | none => intro h; simp [pure, Except.pure] at h
            | some n =>
              intro h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              exact Or.inr (Or.inl ⟨c, a, wa, n, rfl, .inr hrow3.1,
                hrow3.2, hwa, hnl, h⟩)
        next hrow3 =>
          split
          next hrow4 =>
            intro h
            cases hwa : whnf μ env fuel d a with
            | error err => rw [hwa] at h; exact nomatch h
            | ok wa =>
              rw [hwa] at h
              dsimp only at h
              revert h
              cases hnl : Setlec.rawNatLit? wa with
              | none => intro h; simp [pure, Except.pure] at h
              | some n =>
                intro h
                simp [throw, throwThe, MonadExceptOf.throw] at h
          next hrow4 =>
            intro h
            simp [pure, Except.pure] at h
  · -- binary rows
    intro h
    simp only [Setlec.reduceNat, Bind.bind, Except.bind,
      Setlec.whnf_def] at h
    revert h
    split
    next hrow =>
      intro h
      cases hwa : whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        dsimp only at h
        cases hwb : whnf μ env fuel d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok wb =>
          rw [hwb] at h
          dsimp only at h
          revert h
          cases hnla : Setlec.rawNatLit? wa with
          | none =>
            cases hnlb : Setlec.rawNatLit? wb <;>
              (intro h; simp [pure, Except.pure] at h)
          | some n₁ =>
            cases hnlb : Setlec.rawNatLit? wb with
            | none => intro h; simp [pure, Except.pure] at h
            | some n₂ =>
              intro h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              exact Or.inr (Or.inr ⟨c, a, b, wa, wb, n₁, n₂, rfl,
                hrow.1, hrow.2, hwa, hnla, hwb, hnlb, h⟩)
    next hrow =>
      split
      next hrow2 =>
        intro h
        cases hwa : whnf μ env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          dsimp only at h
          cases hwb : whnf μ env fuel d b with
          | error err => rw [hwb] at h; exact nomatch h
          | ok wb =>
            rw [hwb] at h
            dsimp only at h
            revert h
            cases hnla : Setlec.rawNatLit? wa with
            | none =>
              cases hnlb : Setlec.rawNatLit? wb <;>
                (intro h; simp [pure, Except.pure] at h)
            | some n₁ =>
              cases hnlb : Setlec.rawNatLit? wb with
              | none => intro h; simp [pure, Except.pure] at h
              | some n₂ =>
                intro h
                simp [throw, throwThe, MonadExceptOf.throw] at h
      next hrow2 =>
        intro h
        simp [pure, Except.pure] at h

/-- The zero tier: no fuel, no runs. -/
theorem substSim_zero {env : Env} : SubstSimClaims μ env 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro d a e e' _ _ _ _ h; exact nomatch h
  · intro d a e e' _ _ _ _ h; exact nomatch h
  · intro d l a e e' _ _ _ _ h
    cases l with
    | zero => exact nomatch h
    | succ l =>
      unfold Setlec.whnfLoop Setlec.whnfStep at h
      simp only [Bind.bind, Except.bind] at h
      exact nomatch h

/-- The `whnf` tier at `fuel + 1` (the predecessor loop's instance
at the fixed budget). -/
theorem substSim_whnf_succ {env : Env} {fuel : Nat}
    (ih : SubstSimClaims μ env fuel) :
    WhnfSubstSimF μ env (fuel + 1) := by
  intro d a e e' hab hwa heb hwe h
  rw [Setlec.whnf_succ] at h
  exact (ih.loop hab hwa heb hwe h).mono_budget (Nat.le_succ fuel)

/-- Unfolding preserves closedness and scoping (stored values are
closed; the spine is the subject's). -/
theorem unfoldDefinition_pres {env : Env} (henv : EnvWF env)
    {d : Nat} {e e₂ : Expr}
    (h : unfoldDefinition env e = some e₂)
    (heb : e.looseBVarsBounded 0 = true)
    (hwe : Expr.WScoped d e) :
    e₂.looseBVarsBounded 0 = true ∧ Expr.WScoped d e₂ := by
  unfold Setlec.unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    dsimp only at h
    revert h
    split
    next hlen =>
      intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, -, -, hval⟩ :=
        henv _ (Setlec.find?_mem hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
      constructor
      · exact Setlec.looseBVarsBounded_mkAppN
          (by
            rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hvb)
          (fun x hx => Setlec.looseBVarsBounded_getAppArgs heb x hx)
      · exact Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hvc))
          (fun x hx => Setlec.Expr.WScoped.getAppArgs hwe x hx)
    next => intro h; exact nomatch h
  | some (.defnInfo cv value hint) =>
    intro h
    dsimp only at h
    revert h
    split
    next hlen =>
      intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, hval, -⟩ :=
        henv _ (Setlec.find?_mem hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value hint rfl
      constructor
      · exact Setlec.looseBVarsBounded_mkAppN
          (by
            rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hvb)
          (fun x hx => Setlec.looseBVarsBounded_getAppArgs heb x hx)
      · exact Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hvc))
          (fun x hx => Setlec.Expr.WScoped.getAppArgs hwe x hx)
    next => intro h; exact nomatch h

/-- The loop tier at `fuel + 1`: budget induction over `whnfStep`,
the core and entry tiers at the same fuel feeding the head run and
the nat rows' argument runs. -/
theorem substSim_loop_succ {env : Env} {fuel : Nat}
    (henv : EnvWF env)
    (hcore : WhnfCoreSubstSimF μ env (fuel + 1))
    (hwhnf : WhnfSubstSimF μ env (fuel + 1)) :
    WhnfLoopSubstSimF μ env (fuel + 1) := by
  intro d l
  induction l with
  | zero => intro a e e' _ _ _ _ h; exact nomatch h
  | succ l ihl =>
    intro a e e' hab hwa heb hwe h
    obtain ⟨e₁, hwc, hcase⟩ := whnfStep_decompose h
    rw [Setlec.whnfCore_def] at hwc
    have heb₁ : e₁.looseBVarsBounded 0 = true :=
      Setlec.whnfCore_looseBVars (mode := μ) henv (fuel + 1) hwc heb
    have hwe₁ : Expr.WScoped (d + 1) e₁ :=
      Setlec.whnfCore_WScoped (mode := μ) henv (fuel + 1) hwc hwe
    have htr₁ := hcore hab hwa heb hwe hwc
    rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hud, hcont⟩ |
      ⟨-, -, rfl⟩
    · -- the nat row
      rw [Setlec.reduceNat_fold] at hrn
      have he₂ := Setlec.reduceNat_inv (mode := μ) hrn
      have heb₂ : e₂.looseBVarsBounded 0 = true := by
        rcases he₂ with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
      have hwe₂ : Expr.WScoped (d + 1) e₂ :=
        Setlec.Expr.WScoped.of_not_hasFvar (by
          rcases he₂ with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl)
      have hsA₂ : substAK d 0 a e₂ = e₂ := by
        rcases he₂ with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
      have hrest := ihl hab hwa heb₂ hwe₂ hcont
      rw [hsA₂] at hrest
      refine htr₁.trans ?_
      rcases reduceNat_decompose hrn with
        ⟨x, wx, n, rfl, hs, hwx, hnl, rfl⟩ |
        ⟨c, x, wx, n, rfl, hc, hg, hwx, hnl, hres⟩ |
        ⟨c, x, y, wx, wy, n₁, n₂, rfl, hc, hg, hwx, hnlx, hwy,
          hnly, hres⟩
      · have hxb : x.looseBVarsBounded 0 = true := by
          simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true] at heb₁
          exact heb₁.2
        have hxw : Expr.WScoped (d + 1) x := by
          simp only [Expr.WScoped] at hwe₁
          exact hwe₁.2
        have htrx := hwhnf hab hwa hxb hxw hwx
        exact RawReach.natSucc _ n hs htrx
          (by rw [substAK_of_rawNatLit hnl]; exact hnl) hrest
      · have hxb : x.looseBVarsBounded 0 = true := by
          simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true] at heb₁
          exact heb₁.2
        have hxw : Expr.WScoped (d + 1) x := by
          simp only [Expr.WScoped] at hwe₁
          exact hwe₁.2
        have htrx := hwhnf hab hwa hxb hxw hwx
        exact RawReach.natU1 c _ n hc hg htrx
          (by rw [substAK_of_rawNatLit hnl]; exact hnl) hres hrest
      · have hxyb : x.looseBVarsBounded 0 = true ∧
            y.looseBVarsBounded 0 = true := by
          simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true] at heb₁
          exact ⟨heb₁.1.2, heb₁.2⟩
        have hxyw : Expr.WScoped (d + 1) x ∧
            Expr.WScoped (d + 1) y := by
          simp only [Expr.WScoped] at hwe₁
          exact ⟨hwe₁.1.2, hwe₁.2⟩
        have htrx := hwhnf hab hwa hxyb.1 hxyw.1 hwx
        have htry := hwhnf hab hwa hxyb.2 hxyw.2 hwy
        exact RawReach.natB c _ _ n₁ n₂ hc hg htrx htry
          (by rw [substAK_of_rawNatLit hnlx]; exact hnlx)
          (by rw [substAK_of_rawNatLit hnly]; exact hnly) hres hrest
    · -- the delta row
      obtain ⟨heb₂, hwe₂⟩ := unfoldDefinition_pres henv hud heb₁ hwe₁
      exact htr₁.trans (.delta (substAK_unfoldDefinition henv hud)
        (ihl hab hwa heb₂ hwe₂ hcont))
    · exact htr₁

/-- `substAK` is the identity on closed, `fvar`-free terms. -/
theorem substAK_eq_self_of_closed {d k : Nat} {a e : Expr}
    (hfv : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    substAK d k a e = e :=
  substAK_eq_self
    (by
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv]
      exact fun l hl => absurd hl List.not_mem_nil)
    (looseBVarsBounded_mono (Nat.zero_le _) hb)

/-- The `Nat` layer's outcome shapes. -/
theorem litToCtorIfNat_cases (env : Env) (e : Expr) :
    Setlec.litToCtorIfNat env e = e ∨
    ∃ n, e = .lit (.natVal n) ∧
      Setlec.litToCtorIfNat env e = Setlec.natLitToConstructor n := by
  match e with
  | .lit (.natVal n) =>
    by_cases hns : Setlec.natLitSupported env
    · exact Or.inr ⟨n, rfl, by
        show (if Setlec.natLitSupported env
            then Setlec.natLitToConstructor n
            else Expr.lit (.natVal n)) = _
        rw [if_pos hns]⟩
    · exact Or.inl (by
        show (if Setlec.natLitSupported env
            then Setlec.natLitToConstructor n
            else Expr.lit (.natVal n)) = _
        rw [if_neg hns])
  | .lit (.strVal s) => exact Or.inl rfl
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
  | .proj _ _ _ => exact Or.inl rfl

/-- The literal conversion preserves closedness and scoping. -/
theorem litMajor_pres {env : Env} (henv : EnvWF env)
    {fuel dd : Nat} {m₀ m₁ : Expr}
    (hlit : Setlec.litMajorToCtorP μ env fuel dd m₀ = .ok m₁)
    (hb : m₀.looseBVarsBounded 0 = true)
    (hw : Expr.WScoped dd m₀) :
    m₁.looseBVarsBounded 0 = true ∧ Expr.WScoped dd m₁ := by
  rcases Setlec.litMajorToCtorP_inv (mode := μ) hlit with
    heq | ⟨str, rfl, hsupp, hred⟩
  · rcases litToCtorIfNat_cases env m₀ with hid | ⟨n, rfl, hconv⟩
    · rw [hid] at heq
      exact heq ▸ ⟨hb, hw⟩
    · rw [hconv] at heq
      subst heq
      exact ⟨(natLitToConstructor_closed n).2,
        Setlec.Expr.WScoped.of_not_hasFvar
          (natLitToConstructor_closed n).1⟩
  · have hb₁ : m₁.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars (mode := μ) henv fuel hred
        (strLitToConstructor_bounded str)
    have hfv₁ : m₁.hasFvar = false := by
      apply not_hasFvar_of_fvarLeaves_nil
      have hsub := Setlec.whnf_leaves (mode := μ) henv fuel hred
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (strLitToConstructor_not_hasFvar str)] at hsub
      cases hl : m₁.fvarLeaves with
      | nil => rfl
      | cons z zs =>
        exact absurd (hsub z (by rw [hl]; exact List.mem_cons_self))
          List.not_mem_nil
    exact ⟨hb₁, Setlec.Expr.WScoped.of_not_hasFvar hfv₁⟩

/-- The major's image trace: the slot's loop run, then the literal
conversion — both mapped (the closed string expansion transports one
depth down through the shift battery). -/
theorem substSim_major_trace {env : Env} {fuel : Nat}
    (henv : EnvWF env) (ih : SubstSimClaims μ env fuel)
    {d : Nat} {a slot major₀ major₁ : Expr}
    (hab : a.looseBVarsBounded 0 = true) (hwa : Expr.WScoped d a)
    (hsb : slot.looseBVarsBounded 0 = true)
    (hsw : Expr.WScoped (d + 1) slot)
    (hmaj : whnf μ env fuel (d + 1) slot = .ok major₀)
    (hlit : Setlec.litMajorToCtorP μ env fuel (d + 1) major₀
      = .ok major₁) :
    RawReach μ env d (fuel + 1) (substAK d 0 a slot)
      (substAK d 0 a major₁) := by
  have htr₀ := (ih.whnf hab hwa hsb hsw hmaj).mono_budget
    (Nat.le_succ fuel)
  have hb₀ : major₀.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars (mode := μ) henv fuel hmaj hsb
  refine htr₀.trans ?_
  rcases Setlec.litMajorToCtorP_inv (mode := μ) hlit with
    heq | ⟨str, rfl, hsupp, hred⟩
  · -- the Nat layer (or the identity)
    have hclosed : ∀ n : Nat,
        (Setlec.litToCtorIfNat env (.lit (.natVal n))).hasFvar
          = false ∧
        (Setlec.litToCtorIfNat env
          (.lit (.natVal n))).looseBVarsBounded 0 = true := by
      intro n
      constructor
      · show (if Setlec.natLitSupported env
            then Setlec.natLitToConstructor n
            else Expr.lit (.natVal n)).hasFvar = false
        by_cases hns : Setlec.natLitSupported env
        · rw [if_pos hns]; exact (natLitToConstructor_closed n).1
        · rw [if_neg hns]; rfl
      · show Setlec.Expr.looseBVarsBounded 0
            (if Setlec.natLitSupported env
              then Setlec.natLitToConstructor n
              else Expr.lit (.natVal n)) = true
        by_cases hns : Setlec.natLitSupported env
        · rw [if_pos hns]; exact (natLitToConstructor_closed n).2
        · rw [if_neg hns]; rfl
    match major₀, heq with
    | .lit (.natVal n), heq =>
      refine RawReach.litNat (.lit (.natVal n)) ?_
      rw [heq, substAK_eq_self_of_closed (hclosed n).1 (hclosed n).2]
      exact .refl _
    | .bvar i, heq => rw [heq]; exact .refl _
    | .fvar idx nm ty, heq => rw [heq]; exact .refl _
    | .sort u, heq => rw [heq]; exact .refl _
    | .const c' us', heq => rw [heq]; exact .refl _
    | .app f' x', heq => rw [heq]; exact .refl _
    | .lam n' t' b' m', heq => rw [heq]; exact .refl _
    | .forallE n' t' b' m', heq => rw [heq]; exact .refl _
    | .letE n' t' v' b', heq => rw [heq]; exact .refl _
    | .proj s' i' e₀, heq => rw [heq]; exact .refl _
    | .lit (.strVal str), heq => rw [heq]; exact .refl _
  · -- the String layer
    have hfv₁ : major₁.hasFvar = false := by
      apply not_hasFvar_of_fvarLeaves_nil
      have hsub := Setlec.whnf_leaves (mode := μ) henv fuel hred
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (strLitToConstructor_not_hasFvar str)] at hsub
      cases hl : major₁.fvarLeaves with
      | nil => rfl
      | cons z zs =>
        exact absurd (hsub z (by rw [hl]; exact List.mem_cons_self))
          List.not_mem_nil
    have hb₁ : major₁.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars (mode := μ) henv fuel hred
        (strLitToConstructor_bounded str)
    refine RawReach.litStr str fuel (Nat.le_succ fuel) hsupp
      (whnf_closed_depth_down henv
        (strLitToConstructor_not_hasFvar str) hred) ?_
    rw [substAK_eq_self_of_closed hfv₁ hb₁]
    exact .refl _

/-- The core tier at `fuel + 1` (the body's clause walk; internal
runs at `fuel` through the predecessor claims). -/
theorem substSim_core_succ {env : Env} {fuel : Nat}
    (henv : EnvWF env) (ih : SubstSimClaims μ env fuel) :
    WhnfCoreSubstSimF μ env (fuel + 1) := by
  intro d a e e' hab hwa heb hwe h
  cases e with
  | sort u =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | fvar idx n ty =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | forallE n ty body bi =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | lam n ty body bi =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | const n us =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | lit l =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, pure, Except.pure,
      Except.ok.injEq] at h
    exact h ▸ .refl _
  | bvar i =>
    rw [Setlec.whnfCore_succ] at h
    simp [Setlec.whnfCoreBody, throw, throwThe,
      MonadExceptOf.throw] at h
  | letE nn tt vv bb =>
    rw [Setlec.whnfCore_succ] at h
    simp only [Setlec.whnfCoreBody, Setlec.whnfCore_def] at h
    have hparts : (tt.looseBVarsBounded 0 = true ∧
        vv.looseBVarsBounded 0 = true) ∧
        bb.looseBVarsBounded 1 = true := by
      simp only [Setlec.Expr.looseBVarsBounded,
        Bool.and_eq_true] at heb
      exact heb
    have hwparts : Expr.WScoped (d + 1) tt ∧
        Expr.WScoped (d + 1) vv ∧ Expr.WScoped (d + 1) bb := by
      simp only [Expr.WScoped] at hwe
      exact hwe
    have hcb : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
      Setlec.Expr.looseBVarsBounded_instantiate1_gen hparts.1.2
        hparts.2
    have hwcb : Expr.WScoped (d + 1) (bb.instantiate1 vv) :=
      Setlec.Expr.WScoped.instantiate1_gen hwparts.2.1 0 hwparts.2.2
    have htr := ih.core hab hwa hcb hwcb h
    show RawReach μ env d (fuel + 1)
      (.letE nn (substAK d 0 a tt) (substAK d 0 a vv)
        (substAK d 1 a bb)) (substAK d 0 a e')
    refine RawReach.zeta _ _ _ _ ?_
    rw [show (substAK d 1 a bb).instantiate1 (substAK d 0 a vv)
        = substAK d 0 a (bb.instantiate1 vv) from
      substAK_instantiate1 hab hparts.1.2 bb 0]
    exact htr.mono_budget (Nat.le_succ fuel)
  | app f x =>
    obtain ⟨f', hwf, hcase⟩ := Setlec.whnf_app_inv (mode := μ) h
    have hfxb : f.looseBVarsBounded 0 = true ∧
        x.looseBVarsBounded 0 = true := by
      simp only [Setlec.Expr.looseBVarsBounded,
        Bool.and_eq_true] at heb
      exact heb
    have hfxw : Expr.WScoped (d + 1) f ∧
        Expr.WScoped (d + 1) x := by
      simp only [Expr.WScoped] at hwe
      exact hwe
    have hfb' : f'.looseBVarsBounded 0 = true :=
      Setlec.whnfCore_looseBVars (mode := μ) henv fuel hwf hfxb.1
    have hfw' : Expr.WScoped (d + 1) f' :=
      Setlec.whnfCore_WScoped (mode := μ) henv fuel hwf hfxw.1
    have htrf := (ih.core hab hwa hfxb.1 hfxw.1 hwf).mono_budget
      (Nat.le_succ fuel)
    show RawReach μ env d (fuel + 1)
      (.app (substAK d 0 a f) (substAK d 0 a x)) (substAK d 0 a e')
    rcases hcase with ⟨n, ty, body, m, rfl, hbeta, -⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- fired β
      have hbb : body.looseBVarsBounded 1 = true := by
        simp only [Setlec.Expr.looseBVarsBounded,
          Bool.and_eq_true] at hfb'
        exact hfb'.2
      have hbw : Expr.WScoped (d + 1) body := by
        simp only [Expr.WScoped] at hfw'
        exact hfw'.2
      have hcb : (body.instantiate1 x).looseBVarsBounded 0 = true :=
        Setlec.Expr.looseBVarsBounded_instantiate1_gen hfxb.2 hbb
      have hwcb : Expr.WScoped (d + 1) (body.instantiate1 x) :=
        Setlec.Expr.WScoped.instantiate1_gen hfxw.2 0 hbw
      have htrc := ih.core hab hwa hcb hwcb hbeta
      refine RawReach.appL _ htrf ?_
      show RawReach μ env d (fuel + 1)
        (.app (.lam n (substAK d 0 a ty) (substAK d 1 a body) m)
          (substAK d 0 a x)) (substAK d 0 a e')
      refine RawReach.beta _ _ _ _ _ ?_
      rw [show (substAK d 1 a body).instantiate1 (substAK d 0 a x)
          = substAK d 0 a (body.instantiate1 x) from
        substAK_instantiate1 hab hfxb.2 body 0]
      exact htrc.mono_budget (Nat.le_succ fuel)
    · -- fired iota
      obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj,
        usj, cvj, cnP, cnF, rl, cbinders, cbody, residual, cr, usr,
        hifn, hifc, hilen, himaj, hilit, hisub, himfn, hifj, hirule,
        himl, -, -, hinin, -, -, -, -, -, -, -, -, rfl⟩ :=
        Setlec.iotaRec_inv (mode := μ) hio
      have hSb : (Expr.app f' x).looseBVarsBounded 0 = true := by
        simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hfb', hfxb.2⟩
      have hSw : Expr.WScoped (d + 1) (Expr.app f' x) := by
        simp only [Expr.WScoped]
        exact ⟨hfw', hfxw.2⟩
      have hslot : mI < (Expr.app f' x).getAppArgs.length := by
        omega
      have hslotb : ((Expr.app f' x).getAppArgs.getD mI
          (.bvar 0)).looseBVarsBounded 0 = true :=
        Setlec.looseBVarsBounded_getAppArgs hSb _
          (Setlec.getD_mem hslot)
      have hslotw : Expr.WScoped (d + 1)
          ((Expr.app f' x).getAppArgs.getD mI (.bvar 0)) :=
        Setlec.Expr.WScoped.getAppArgs hSw _
          (Setlec.getD_mem hslot)
      have htrM := substSim_major_trace henv ih hab hwa hslotb
        hslotw himaj hilit
      have hm₀b : major₀.looseBVarsBounded 0 = true :=
        Setlec.whnf_looseBVars (mode := μ) henv fuel himaj hslotb
      have hm₀w : Expr.WScoped (d + 1) major₀ :=
        Setlec.whnf_WScoped (mode := μ) henv fuel himaj hslotw
      obtain ⟨hm₁b, hm₁w⟩ := litMajor_pres henv hilit hm₀b hm₀w
      obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hifc)
      obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP rules rfl rl
        (List.mem_of_find?_eq_some hirule)
      have hrIb : (rl.rhs.instantiateLevelParams cv.levelParams
          us).looseBVarsBounded 0 = true := by
        rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
        exact hrb
      have hrIfv : (rl.rhs.instantiateLevelParams cv.levelParams
          us).hasFvar = false := by
        rw [Setlec.Expr.hasFvar_instantiateLevelParams]
        exact hrfv
      have hmajf : major.looseBVarsBounded 0 = true ∧
          Expr.WScoped (d + 1) major := by
        rcases Setlec.majorToCtor_inv (mode := μ) hisub with
          rfl | ⟨hwsc, hbnd, -, -⟩
        · exact ⟨hm₁b, hm₁w⟩
        · exact ⟨hbnd, Setlec.Expr.WScoped.of_wscopedB hwsc⟩
      have he''b : (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          ((Expr.app f' x).getAppArgs.take rP
            ++ major.getAppArgs.drop
              rl.ctorParams)).looseBVarsBounded 0 = true := by
        refine Setlec.looseBVarsBounded_mkAppN hrIb ?_
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.looseBVarsBounded_getAppArgs hSb _
            (List.take_subset _ _ hz)
        · exact Setlec.looseBVarsBounded_getAppArgs hmajf.1 _
            (List.drop_subset _ _ hz)
      have he''w : Expr.WScoped (d + 1) (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          ((Expr.app f' x).getAppArgs.take rP
            ++ major.getAppArgs.drop rl.ctorParams)) := by
        refine Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar hrIfv) ?_
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.Expr.WScoped.getAppArgs hSw _
            (List.take_subset _ _ hz)
        · exact Setlec.Expr.WScoped.getAppArgs hmajf.2 _
            (List.drop_subset _ _ hz)
      have htrE := (ih.core hab hwa he''b he''w hwe'').mono_budget
        (Nat.le_succ fuel)
      rw [show substAK d 0 a (Setlec.Expr.mkAppN
          (rl.rhs.instantiateLevelParams cv.levelParams us)
          ((Expr.app f' x).getAppArgs.take rP
            ++ major.getAppArgs.drop rl.ctorParams))
          = Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            (((Expr.app f' x).getAppArgs.map
                (substAK d 0 a)).take rP
              ++ (major.getAppArgs.map
                (substAK d 0 a)).drop rl.ctorParams) from by
        rw [substAK_mkAppN, substAK_eq_self_of_closed hrIfv hrIb,
          List.map_append, List.map_take, List.map_drop]] at htrE
      refine RawReach.appL _ htrf ?_
      rcases Setlec.majorToCtor_inv (mode := μ) hisub with heqM |
        ⟨hwsc, hbnd, hlv, rl', cvj', cnP', cnF', tmaj₀, tmaj, T,
          us₀, ust, cvT, caps, hrules, hcj', hT', hTi', -, -, htfn,
          hKor⟩
      · -- the plain row
        subst heqM
        refine RawReach.iotaPlain c us cv mI rP rules rl cj usj
          (M := substAK d 0 a major) (w := substAK d 0 a e')
          (substAK_getAppFn_const hifn) hifc ?_ ?_
          (substAK_getAppFn_const himfn) hirule ?_ hinin ?_
        · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, List.length_map]
          exact hilen
        · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, getD_map_lt hslot]
          exact htrM
        · rw [substAK_getAppArgs_const himfn, List.length_map]
          exact himl
        · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn,
            substAK_getAppArgs_const himfn]
          exact htrE
      · -- the rescue rows
        subst hrules
        have hrl_eq : rl' = rl := by
          simp only [List.find?] at hirule
          split at hirule
          · exact Option.some.inj hirule
          · exact nomatch hirule
        rcases hKor with
          ⟨hK, hcnF, -, -, -, hfab, -, -, -⟩ |
          ⟨heta, hec, -, -, hlenT, -, -, -, hfab, -, -⟩
        · -- the K row
          rw [hrl_eq] at hfab hcj' hifc
          rw [hcnF] at hcj'
          have hma : major.getAppArgs
              = tmaj.getAppArgs.take cnP' := by
            rw [hfab, Setlec.Expr.getAppArgs_mkAppN]
            rfl
          refine RawReach.iotaK c us cv mI rP rl cvj' cnP' T us₀
            cvT caps (tmaj.getAppArgs.map (substAK d 0 a))
            (M := substAK d 0 a major₁) (w := substAK d 0 a e')
            (substAK_getAppFn_const hifn) hifc ?_ ?_ hcj' hT' hTi'
            hK ?_ ?_
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, List.length_map]
            exact hilen
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, getD_map_lt hslot]
            exact htrM
          · rw [← List.map_take, List.length_map, ← hma]
            exact himl
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn]
            rw [hma, List.map_take] at htrE
            exact htrE
        · -- the eta row
          rw [hrl_eq] at hcj' hec hifc
          have hma : major.getAppArgs
              = Setlec.etaFabArgs T ust tmaj.getAppArgs major₁
                caps.etaFields := by
            rw [hfab, Setlec.Expr.getAppArgs_mkAppN]
            rfl
          refine RawReach.iotaEta c us ust cv mI rP rl cvj' cnP'
            cnF' T us₀ cvT caps
            (tmaj.getAppArgs.map (substAK d 0 a))
            (M := substAK d 0 a major₁) (w := substAK d 0 a e')
            (substAK_getAppFn_const hifn) hifc ?_ ?_ hcj' hT' hTi'
            heta hec ?_ ?_
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, List.length_map]
            exact hilen
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn, getD_map_lt hslot]
            exact htrM
          · rw [← substAK_etaFabArgs, List.length_map, ← hma]
            exact himl
          · rw [show ((substAK d 0 a f').app
                (substAK d 0 a x)).getAppArgs
              = (Expr.app f' x).getAppArgs.map (substAK d 0 a) from
            substAK_getAppArgs_const hifn,
              ← substAK_etaFabArgs, ← hma]
            exact htrE
    · -- stuck
      exact RawReach.appL _ htrf (.refl _)
  | proj sn i pe =>
    obtain ⟨e₂, e₃, hw, hlitp, hcase⟩ :=
      Setlec.whnf_proj_inv (mode := μ) h
    have hpb : pe.looseBVarsBounded 0 = true := by
      simp only [Setlec.Expr.looseBVarsBounded] at heb
      exact heb
    have hpw : Expr.WScoped (d + 1) pe := by
      simp only [Expr.WScoped] at hwe
      exact hwe
    have htrPe := (ih.whnf hab hwa hpb hpw hw).mono_budget
      (Nat.le_succ fuel)
    have heb₂ : e₂.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars (mode := μ) henv fuel hw hpb
    have hwe₂ : Expr.WScoped (d + 1) e₂ :=
      Setlec.whnf_WScoped (mode := μ) henv fuel hw hpw
    have hstep : RawReach μ env d (fuel + 1) (substAK d 0 a e₂)
        (substAK d 0 a e₃) ∧
        e₃.looseBVarsBounded 0 = true ∧
        Expr.WScoped (d + 1) e₃ := by
      rcases Setlec.projLitToCtorP_inv (mode := μ) hlitp with
        rfl | ⟨str, rfl, hsupp, hred⟩
      · exact ⟨.refl _, heb₂, hwe₂⟩
      · have hfv₃ : e₃.hasFvar = false := by
          apply not_hasFvar_of_fvarLeaves_nil
          have hsub := Setlec.whnf_leaves (mode := μ) henv fuel hred
          rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar
            (strLitToConstructor_not_hasFvar str)] at hsub
          cases hl : e₃.fvarLeaves with
          | nil => rfl
          | cons z zs =>
            exact absurd
              (hsub z (by rw [hl]; exact List.mem_cons_self))
              List.not_mem_nil
        have hb₃ : e₃.looseBVarsBounded 0 = true :=
          Setlec.whnf_looseBVars (mode := μ) henv fuel hred
            (strLitToConstructor_bounded str)
        refine ⟨RawReach.litStr str fuel (Nat.le_succ fuel) hsupp
          (whnf_closed_depth_down henv
            (strLitToConstructor_not_hasFvar str) hred) ?_, hb₃,
          Setlec.Expr.WScoped.of_not_hasFvar hfv₃⟩
        rw [substAK_eq_self_of_closed hfv₃ hb₃]
        exact .refl _
    show RawReach μ env d (fuel + 1)
      (.proj sn i (substAK d 0 a pe)) (substAK d 0 a e')
    refine RawReach.projC sn i (htrPe.trans hstep.1) ?_
    rcases hcase with rfl |
      ⟨us, entry, hfn2, hf2, hnat, hi, hlen2, hus, hred2, -, -⟩
    · exact .refl _
    · have hilt : entry.numParams + i < e₃.getAppArgs.length := by
        omega
      have hargb : (e₃.getAppArgs.getD (entry.numParams + i)
          (.bvar 0)).looseBVarsBounded 0 = true :=
        Setlec.looseBVarsBounded_getAppArgs hstep.2.1 _
          (Setlec.getD_mem hilt)
      have hargw : Expr.WScoped (d + 1)
          (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) :=
        Setlec.Expr.WScoped.getAppArgs hstep.2.2 _
          (Setlec.getD_mem hilt)
      have htrF := ih.core hab hwa hargb hargw hred2
      refine RawReach.projFire sn i entry us hf2
        (substAK_getAppFn_const hfn2) hnat hi ?_ ?_
      · rw [substAK_getAppArgs_const hfn2, List.length_map]
        exact hlen2
      · rw [substAK_getAppArgs_const hfn2, getD_map_lt hilt]
        exact htrF.mono_budget (Nat.le_succ fuel)

/-- **The substitution simulation DISCHARGED** (the Θ push's
engine): every tier at every knot fuel — a depth-`(d+1)` run on an
opened, locally closed subject maps under the cursor-0 telescope
substitution to a gate-free image trace at depth `d`. -/
theorem substSimClaims {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat), SubstSimClaims μ env fuel := by
  intro fuel
  induction fuel with
  | zero => exact substSim_zero
  | succ fuel ih =>
    have hwhnf : WhnfSubstSimF μ env (fuel + 1) :=
      substSim_whnf_succ ih
    have hcore : WhnfCoreSubstSimF μ env (fuel + 1) :=
      substSim_core_succ henv ih
    exact ⟨hcore, hwhnf, substSim_loop_succ henv hcore hwhnf⟩

/-- **The λ-head case DISCHARGED**: build the spine zip from the
congruent λ components and dispatch. -/
theorem zipLamHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipLamHeadCase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ b₁ b₂ m as bs ℓa ℓb below hty
    hbody hlen hargs hIs hIt hp hQ ha hb
  exact zipHeadDispatch (φ := φ) (Q := Q) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.lam n ty₁ ty₂ b₁ b₂ m hty hbody)
      hlen hargs) hIs hIt hp hQ ha hb

/-- **The letE-head case DISCHARGED**: same dispatch, letE-node
head zip. -/
theorem zipLetEHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipLetEHeadCase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ v₁ v₂ b₁ b₂ as bs ℓa ℓb below
    hty hval hbody hlen hargs hIs hIt hp hQ ha hb
  exact zipHeadDispatch (φ := φ) (Q := Q) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval
      hbody) hlen hargs) hIs hIt hp hQ ha hb

end Discharge

end Setlec.SetR.Interp2
