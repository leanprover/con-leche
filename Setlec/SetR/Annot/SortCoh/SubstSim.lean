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
      (hg : Setlec.natOpStored env c = true)
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
      (hg : Setlec.natOpStored env c = true)
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
      (htb : ∀ z ∈ targs.take cnP, z.looseBVarsBounded 0 = true)
      (htw : ∀ z ∈ targs.take cnP, Expr.WScoped d z)
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
      (htb : ∀ z ∈ targs, z.looseBVarsBounded 0 = true)
      (htw : ∀ z ∈ targs, Expr.WScoped d z)
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
      hM hcj hT hTi hK hml htb htw rest ihM ihr =>
    exact fun h₂ => .iotaK c us cv mI rP rl cvj cnP T usT cvT caps
      targs hfn hc hlen hM hcj hT hTi hK hml htb htw (ihr h₂)
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml htb htw rest ihM ihr =>
    exact fun h₂ => .iotaEta c us ust cv mI rP rl cvj cnP cnF T usT
      cvT caps targs hfn hc hlen hM hcj hT hTi heta hec hml htb htw
      (ihr h₂)
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
      hM hcj hT hTi hK hml htb htw rest ih₁ ih₂ =>
    exact .iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn
      hc hlen ih₁ hcj hT hTi hK hml htb htw ih₂
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml htb htw rest ih₁ ih₂ =>
    exact .iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps
      targs hfn hc hlen ih₁ hcj hT hTi heta hec hml htb htw ih₂
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
      Setlec.natOpStored env c = true ∧
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
      Setlec.natOpStored env c = true ∧
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

/-- The telescope substitution preserves the loose-bvar bound. -/
theorem substAK_bounded {d k : Nat} {a e : Expr}
    (hab : a.looseBVarsBounded 0 = true)
    (he : e.looseBVarsBounded k = true) :
    (substAK d k a e).looseBVarsBounded k = true :=
  Setlec.Expr.looseBVarsBounded_instantiate1_gen hab
    (Setlec.looseBVarsBounded_abstract1 e k he)

/-- The telescope substitution lands one scope down. -/
theorem substAK_WScoped {d k : Nat} {a e : Expr}
    (hwa : Expr.WScoped d a) (hwe : Expr.WScoped (d + 1) e) :
    Expr.WScoped d (substAK d k a e) :=
  Setlec.Expr.WScoped.instantiate1_gen hwa k
    (Setlec.WScoped.abstract1 k hwe)

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
        hifn, hifc, hilen, -, himaj, hilit, hisub, himfn, hifj, hirule,
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
            hK ?_ ?_ ?_ ?_
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
          · intro z hz
            rw [← List.map_take, ← hma] at hz
            obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
            exact substAK_bounded hab
              (Setlec.looseBVarsBounded_getAppArgs hbnd z₀ hz₀)
          · intro z hz
            rw [← List.map_take, ← hma] at hz
            obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
            exact substAK_WScoped hwa
              (Setlec.Expr.WScoped.getAppArgs
                (Setlec.Expr.WScoped.of_wscopedB hwsc) z₀ hz₀)
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
            heta hec ?_ ?_ ?_ ?_
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
          · intro z hz
            obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
            have hz₀' : z₀ ∈ major.getAppArgs := by
              rw [hma]
              unfold Setlec.etaFabArgs
              exact List.mem_append_left _ hz₀
            exact substAK_bounded hab
              (Setlec.looseBVarsBounded_getAppArgs hbnd z₀ hz₀')
          · intro z hz
            obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
            have hz₀' : z₀ ∈ major.getAppArgs := by
              rw [hma]
              unfold Setlec.etaFabArgs
              exact List.mem_append_left _ hz₀
            exact substAK_WScoped hwa
              (Setlec.Expr.WScoped.getAppArgs
                (Setlec.Expr.WScoped.of_wscopedB hwsc) z₀ hz₀')
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
      ⟨us, entry, hfn2, hf2, hnat, hi, hlen2, hus, hred2, -⟩
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
    {Q : Nat → Expr → Expr → Prop} (hgOff : μ.betaGate = false)
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
  intro fc d ga la gb lb n ty₁ ty₂ b₁ b₂ m₁ m₂ as bs ℓa ℓb below hty
    hbody hlen hargs hIs hIt hp hQ ha hb
  exact zipHeadDispatch (φ := φ) (Q := Q) (hg := hgOff) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.lam n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody)
      hlen hargs) hIs hIt hp hQ ha hb

/-- **The letE-head case DISCHARGED**: same dispatch, letE-node
head zip. -/
theorem zipLetEHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop} (hgOff : μ.betaGate = false)
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
  exact zipHeadDispatch (φ := φ) (Q := Q) (hg := hgOff) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval
      hbody) hlen hargs) hIs hIt hp hQ ha hb

/-! #### The identity embeddings (runs as gate-free traces)

A depth-`d` run on a well-scoped subject embeds as a `RawReach`
trace at the SAME depth with zero new inductions: shift the run one
depth up (the discharged `ShiftClaims` battery; `shiftFrom d` is the
identity on `WScoped d` material), apply the simulation with a dummy
closed argument, and collapse both `substAK`s by `substAK_eq_self`
(the subject is `d`-fresh).  The push's telescope trace is these
embeddings composed with `RawReach.image` over `Γ`. -/

/-- Explicit-budget loops preserve the closedness package. -/
theorem whnfLoop_pres {env : Env} (henv : EnvWF env) {g : Nat} :
    ∀ (l : Nat) {d : Nat} {e e' : Expr},
      Setlec.whnfLoop (Setlec.pureFns μ env g) env d l e = .ok e' →
      e.looseBVarsBounded 0 = true → Expr.WScoped d e →
      e'.looseBVarsBounded 0 = true ∧ Expr.WScoped d e' := by
  intro l
  induction l with
  | zero => intro d e e' h; exact nomatch h
  | succ l ih =>
    intro d e e' h heb hwe
    obtain ⟨e₁, hwc, hcase⟩ := whnfStep_decompose h
    rw [Setlec.whnfCore_def] at hwc
    have heb₁ : e₁.looseBVarsBounded 0 = true :=
      Setlec.whnfCore_looseBVars (mode := μ) henv g hwc heb
    have hwe₁ : Expr.WScoped d e₁ :=
      Setlec.whnfCore_WScoped (mode := μ) henv g hwc hwe
    rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hud, hcont⟩ |
      ⟨-, -, rfl⟩
    · rw [Setlec.reduceNat_fold] at hrn
      have he₂ := Setlec.reduceNat_inv (mode := μ) hrn
      refine ih hcont ?_ ?_
      · rcases he₂ with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
      · exact Setlec.Expr.WScoped.of_not_hasFvar (by
          rcases he₂ with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl)
    · obtain ⟨heb₂, hwe₂⟩ := unfoldDefinition_pres henv hud heb₁ hwe₁
      exact ih hcont heb₂ hwe₂
    · exact ⟨heb₁, hwe₁⟩

/-- A `whnfCore` run embeds as a trace at its own depth. -/
theorem whnfCore_toRawReach {env : Env} (henv : EnvWF env)
    {g d : Nat} {e e' : Expr}
    (heb : e.looseBVarsBounded 0 = true) (hwe : Expr.WScoped d e)
    (h : whnfCore μ env g d e = .ok e') :
    RawReach μ env d g e e' := by
  have hwe' : Expr.WScoped d e' :=
    Setlec.whnfCore_WScoped (mode := μ) henv g h hwe
  have heb' : e'.looseBVarsBounded 0 = true :=
    Setlec.whnfCore_looseBVars (mode := μ) henv g h heb
  have hup : whnfCore μ env g (d + 1) e = .ok e' := by
    have hsc := (Setlec.shiftClaims (mode := μ) (env := env) henv
      g).whnfCore (p := d) (Nat.le_refl d) hwe
    rw [Setlec.Expr.shiftFrom_eq_self
      (Setlec.Expr.WScoped.fvarsBelow hwe), h] at hsc
    simpa [Except.map, Setlec.Expr.shiftFrom_eq_self
      (Setlec.Expr.WScoped.fvarsBelow hwe')] using hsc
  have hsim := (substSimClaims henv g).core (d := d)
    (a := Expr.sort .zero) rfl
    (Setlec.Expr.WScoped.of_not_hasFvar rfl) heb
    (Setlec.Expr.WScoped.mono (Nat.le_succ d) hwe) hup
  rwa [substAK_eq_self (fun l hl => Nat.ne_of_lt
      (Setlec.Expr.fvarLeaves_lt_of_wscoped hwe l hl)) heb,
    substAK_eq_self (fun l hl => Nat.ne_of_lt
      (Setlec.Expr.fvarLeaves_lt_of_wscoped hwe' l hl)) heb']
    at hsim

/-- An explicit-budget loop run embeds as a trace at its own depth. -/
theorem whnfLoop_toRawReach {env : Env} (henv : EnvWF env)
    {g l d : Nat} {e e' : Expr}
    (heb : e.looseBVarsBounded 0 = true) (hwe : Expr.WScoped d e)
    (h : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l e
      = .ok e') :
    RawReach μ env d g e e' := by
  obtain ⟨heb', hwe'⟩ := whnfLoop_pres henv l h heb hwe
  have hup : Setlec.whnfLoop (Setlec.pureFns μ env g) env (d + 1) l
      e = .ok e' := by
    have hsc := Setlec.whnfLoop_shift (mode := μ) henv
      (Setlec.shiftClaims henv g) l (Nat.le_refl d) hwe
    rw [Setlec.Expr.shiftFrom_eq_self
      (Setlec.Expr.WScoped.fvarsBelow hwe), h] at hsc
    simpa [Except.map, Setlec.Expr.shiftFrom_eq_self
      (Setlec.Expr.WScoped.fvarsBelow hwe')] using hsc
  have hsim := (substSimClaims henv g).loop (d := d)
    (a := Expr.sort .zero) rfl
    (Setlec.Expr.WScoped.of_not_hasFvar rfl) heb
    (Setlec.Expr.WScoped.mono (Nat.le_succ d) hwe) hup
  rwa [substAK_eq_self (fun l' hl => Nat.ne_of_lt
      (Setlec.Expr.fvarLeaves_lt_of_wscoped hwe l' hl)) heb,
    substAK_eq_self (fun l' hl => Nat.ne_of_lt
      (Setlec.Expr.fvarLeaves_lt_of_wscoped hwe' l' hl)) heb']
    at hsim

/-! #### The trace-preservation and trace-image tier (E2) -/

/-- A closed whnf input yields a closed output (leaves route). -/
theorem whnf_closed_out_fvarfree {env : Env} (henv : EnvWF env)
    {g dd : Nat} {e t : Expr} (hfv : e.hasFvar = false)
    (h : whnf μ env g dd e = .ok t) : t.hasFvar = false := by
  apply not_hasFvar_of_fvarLeaves_nil
  have hsub := Setlec.whnf_leaves (mode := μ) henv g h
  rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv] at hsub
  cases hl : t.fvarLeaves with
  | nil => rfl
  | cons z zs =>
    exact absurd (hsub z (by rw [hl]; exact List.mem_cons_self))
      List.not_mem_nil

/-- `natOpResult` reducts are literals or `Bool` constructors. -/
theorem natOpResult_closed {c : Name} {n₁ n₂ : Nat} {res : Expr}
    (h : Setlec.natOpResult c n₁ n₂ = some res) :
    res.hasFvar = false ∧ res.looseBVarsBounded 0 = true := by
  delta Setlec.natOpResult at h
  by_cases h0 : c = Setlec.natPredName
  · rw [if_pos h0] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · rw [if_neg h0] at h
    by_cases h1 : c = Setlec.natAddName
    · rw [if_pos h1] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl⟩
    · rw [if_neg h1] at h
      by_cases h2 : c = Setlec.natSubName
      · rw [if_pos h2] at h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl⟩
      · rw [if_neg h2] at h
        by_cases h3 : c = Setlec.natMulName
        · rw [if_pos h3] at h
          obtain rfl := Option.some.inj h
          exact ⟨rfl, rfl⟩
        · rw [if_neg h3] at h
          by_cases h4 : c = Setlec.natPowName
          · rw [if_pos h4] at h
            obtain rfl := Option.some.inj h
            exact ⟨rfl, rfl⟩
          · rw [if_neg h4] at h
            by_cases h5 : c = Setlec.natDivName
            · rw [if_pos h5] at h
              obtain rfl := Option.some.inj h
              exact ⟨rfl, rfl⟩
            · rw [if_neg h5] at h
              by_cases h6 : c = Setlec.natModName
              · rw [if_pos h6] at h
                obtain rfl := Option.some.inj h
                exact ⟨rfl, rfl⟩
              · rw [if_neg h6] at h
                by_cases h7 : c = Setlec.natGcdName
                · rw [if_pos h7] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨rfl, rfl⟩
                · rw [if_neg h7] at h
                  by_cases h8 : c = Setlec.natLandName
                  · rw [if_pos h8] at h
                    obtain rfl := Option.some.inj h
                    exact ⟨rfl, rfl⟩
                  · rw [if_neg h8] at h
                    by_cases h9 : c = Setlec.natLorName
                    · rw [if_pos h9] at h
                      obtain rfl := Option.some.inj h
                      exact ⟨rfl, rfl⟩
                    · rw [if_neg h9] at h
                      by_cases h10 : c = Setlec.natXorName
                      · rw [if_pos h10] at h
                        obtain rfl := Option.some.inj h
                        exact ⟨rfl, rfl⟩
                      · rw [if_neg h10] at h
                        by_cases h11 : c = Setlec.natShiftLeftName
                        · rw [if_pos h11] at h
                          obtain rfl := Option.some.inj h
                          exact ⟨rfl, rfl⟩
                        · rw [if_neg h11] at h
                          by_cases h12 : c = Setlec.natShiftRightName
                          · rw [if_pos h12] at h
                            obtain rfl := Option.some.inj h
                            exact ⟨rfl, rfl⟩
                          · rw [if_neg h12] at h
                            by_cases h13 : c = Setlec.natLog2Name
                            · rw [if_pos h13] at h
                              obtain rfl := Option.some.inj h
                              exact ⟨rfl, rfl⟩
                            · rw [if_neg h13] at h
                              by_cases h14 : c = Setlec.natBeqName
                              · rw [if_pos h14] at h
                                obtain rfl := Option.some.inj h
                                exact ⟨rfl, rfl⟩
                              · rw [if_neg h14] at h
                                by_cases h15 : c = Setlec.natBleName
                                · rw [if_pos h15] at h
                                  obtain rfl := Option.some.inj h
                                  exact ⟨rfl, rfl⟩
                                · rw [if_neg h15] at h
                                  simp at h

/-- The closedness package travels along a gate-free trace. -/
theorem RawReach.pres {env : Env} (henv : EnvWF env)
    {d G : Nat} {X Y : Expr} (h : RawReach μ env d G X Y) :
    X.looseBVarsBounded 0 = true → Expr.WScoped d X →
    Y.looseBVarsBounded 0 = true ∧ Expr.WScoped d Y := by
  induction h with
  | refl e => exact fun hb hw => ⟨hb, hw⟩
  | appL x h rest ihh ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    obtain ⟨hfb', hfw'⟩ := ihh hb.1 hw.1
    refine ihr ?_ ?_
    · simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hfb', hb.2⟩
    · simp only [Expr.WScoped]
      exact ⟨hfw', hw.2⟩
  | projC sn i h rest ihh ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Expr.WScoped] at hw
    obtain ⟨hb', hw'⟩ := ihh hb hw
    refine ihr ?_ ?_
    · simpa only [Setlec.Expr.looseBVarsBounded] using hb'
    · simpa only [Expr.WScoped] using hw'
  | beta n ty b x m rest ih =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    exact ih
      (Setlec.Expr.looseBVarsBounded_instantiate1_gen hb.2
        hb.1.2)
      (Setlec.Expr.WScoped.instantiate1_gen hw.2 0 hw.1.2)
  | zeta n ty v b rest ih =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    exact ih
      (Setlec.Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
      (Setlec.Expr.WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
  | litNat e rest ih =>
    intro hb hw
    rcases litToCtorIfNat_cases env e with hid | ⟨n, rfl, hconv⟩
    · refine ih ?_ ?_
      · rw [hid]; exact hb
      · rw [hid]; exact hw
    · refine ih ?_ ?_
      · rw [hconv]; exact (natLitToConstructor_closed n).2
      · rw [hconv]
        exact Setlec.Expr.WScoped.of_not_hasFvar
          (natLitToConstructor_closed n).1
  | litStr s g hg hs hr rest ih =>
    intro hb hw
    exact ih
      (Setlec.whnf_looseBVars (mode := μ) henv g hr
        (strLitToConstructor_bounded s))
      (Setlec.Expr.WScoped.of_not_hasFvar
        (whnf_closed_out_fvarfree henv
          (strLitToConstructor_not_hasFvar s) hr))
  | delta hu rest ih =>
    intro hb hw
    obtain ⟨hb', hw'⟩ := unfoldDefinition_pres henv hu hb hw
    exact ih hb' hw'
  | natSucc x n hs hx hnl rest ihx ihr =>
    intro hb hw
    exact ihr rfl (Setlec.Expr.WScoped.of_not_hasFvar rfl)
  | natU1 c x n hc hg hx hnl hres rest ihx ihr =>
    intro hb hw
    exact ihr (natOpResult_closed hres).2
      (Setlec.Expr.WScoped.of_not_hasFvar (natOpResult_closed hres).1)
  | natB c x y n₁ n₂ hc hg hx hy hnx hny hres rest ihx ihy ihr =>
    intro hb hw
    exact ihr (natOpResult_closed hres).2
      (Setlec.Expr.WScoped.of_not_hasFvar (natOpResult_closed hres).1)
  | iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen hM hMfn hrl
      hml hnin rest ihM ihr =>
    intro hb hw
    obtain ⟨hMb, hMw⟩ := ihM
      (Setlec.looseBVarsBounded_getAppArgs hb _
        (Setlec.getD_mem (by rw [hlen]; omega)))
      (Setlec.Expr.WScoped.getAppArgs hw _
        (Setlec.getD_mem (by rw [hlen]; omega)))
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP rules rfl rl
      (List.mem_of_find?_eq_some hrl)
    refine ihr (Setlec.looseBVarsBounded_mkAppN
      (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
          exact hrb) ?_)
      (Setlec.Expr.WScoped.mkAppN
        (Setlec.Expr.WScoped.of_not_hasFvar (by
          rw [Setlec.Expr.hasFvar_instantiateLevelParams]
          exact hrfv)) ?_)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.looseBVarsBounded_getAppArgs hb _
          (List.take_subset _ _ hz)
      · exact Setlec.looseBVarsBounded_getAppArgs hMb _
          (List.drop_subset _ _ hz)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.Expr.WScoped.getAppArgs hw _
          (List.take_subset _ _ hz)
      · exact Setlec.Expr.WScoped.getAppArgs hMw _
          (List.drop_subset _ _ hz)
  | iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn hc hlen
      hM hcj hT hTi hK hml htb htw rest ihM ihr =>
    intro hb hw
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP [rl] rfl rl
      List.mem_cons_self
    refine ihr (Setlec.looseBVarsBounded_mkAppN
      (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
          exact hrb) ?_)
      (Setlec.Expr.WScoped.mkAppN
        (Setlec.Expr.WScoped.of_not_hasFvar (by
          rw [Setlec.Expr.hasFvar_instantiateLevelParams]
          exact hrfv)) ?_)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.looseBVarsBounded_getAppArgs hb _
          (List.take_subset _ _ hz)
      · exact htb _ (List.drop_subset _ _ hz)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.Expr.WScoped.getAppArgs hw _
          (List.take_subset _ _ hz)
      · exact htw _ (List.drop_subset _ _ hz)
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml htb htw rest ihM ihr =>
    intro hb hw
    obtain ⟨hMb, hMw⟩ := ihM
      (Setlec.looseBVarsBounded_getAppArgs hb _
        (Setlec.getD_mem (by rw [hlen]; omega)))
      (Setlec.Expr.WScoped.getAppArgs hw _
        (Setlec.getD_mem (by rw [hlen]; omega)))
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP [rl] rfl rl
      List.mem_cons_self
    refine ihr (Setlec.looseBVarsBounded_mkAppN
      (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
          exact hrb) ?_)
      (Setlec.Expr.WScoped.mkAppN
        (Setlec.Expr.WScoped.of_not_hasFvar (by
          rw [Setlec.Expr.hasFvar_instantiateLevelParams]
          exact hrfv)) ?_)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.looseBVarsBounded_getAppArgs hb _
          (List.take_subset _ _ hz)
      · have hz' := List.drop_subset _ _ hz
        unfold Setlec.etaFabArgs at hz'
        rcases List.mem_append.mp hz' with hz' | hz'
        · exact htb z hz'
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz'
          refine Setlec.looseBVarsBounded_mkAppN rfl ?_
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact htb y hy
          · rw [List.mem_singleton] at hy
            exact hy ▸ hMb
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Setlec.Expr.WScoped.getAppArgs hw _
          (List.take_subset _ _ hz)
      · have hz' := List.drop_subset _ _ hz
        unfold Setlec.etaFabArgs at hz'
        rcases List.mem_append.mp hz' with hz' | hz'
        · exact htw z hz'
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz'
          refine Setlec.Expr.WScoped.mkAppN
            (Setlec.Expr.WScoped.of_not_hasFvar rfl) ?_
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact htw y hy
          · rw [List.mem_singleton] at hy
            exact hy ▸ hMw
  | projFire sn i entry us hf hfn hnat hi hlenE rest ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Expr.WScoped] at hw
    exact ihr
      (Setlec.looseBVarsBounded_getAppArgs hb _
        (Setlec.getD_mem (by rw [hlenE]; omega)))
      (Setlec.Expr.WScoped.getAppArgs hw _
        (Setlec.getD_mem (by rw [hlenE]; omega)))

set_option maxHeartbeats 1600000 in
/-- **The trace image**: a gate-free trace at depth `d + 1` maps
under the one-binder telescope substitution to a trace at depth `d`
— the lemma that iterates the simulation over the Θ telescope. -/
theorem RawReach.image {env : Env} (henv : EnvWF env)
    {d G : Nat} {X Y : Expr} (h : RawReach μ env (d + 1) G X Y)
    {a : Expr} (hab : a.looseBVarsBounded 0 = true)
    (hwa : Expr.WScoped d a) :
    X.looseBVarsBounded 0 = true → Expr.WScoped (d + 1) X →
    RawReach μ env d G (substAK d 0 a X) (substAK d 0 a Y) := by
  induction h with
  | refl e => exact fun _ _ => .refl _
  | appL x h rest ihh ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    obtain ⟨hfb', hfw'⟩ := RawReach.pres henv h hb.1 hw.1
    show RawReach μ env d G
      (.app (substAK d 0 a _) (substAK d 0 a x)) _
    refine RawReach.appL _ (ihh hb.1 hw.1) ?_
    exact ihr
      (by simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true]
          exact ⟨hfb', hb.2⟩)
      (by simp only [Expr.WScoped]
          exact ⟨hfw', hw.2⟩)
  | projC sn i h rest ihh ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Expr.WScoped] at hw
    obtain ⟨hb', hw'⟩ := RawReach.pres henv h hb hw
    show RawReach μ env d G (.proj sn i (substAK d 0 a _)) _
    refine RawReach.projC sn i (ihh hb hw) ?_
    exact ihr
      (by simpa only [Setlec.Expr.looseBVarsBounded] using hb')
      (by simpa only [Expr.WScoped] using hw')
  | beta n ty b x m rest ih =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G
      (.app (.lam n (substAK d 0 a ty) (substAK d 1 a b) m)
        (substAK d 0 a x)) _
    refine RawReach.beta _ _ _ _ _ ?_
    rw [show (substAK d 1 a b).instantiate1 (substAK d 0 a x)
        = substAK d 0 a (b.instantiate1 x) from
      substAK_instantiate1 hab hb.2 b 0]
    exact ih
      (Setlec.Expr.looseBVarsBounded_instantiate1_gen hb.2 hb.1.2)
      (Setlec.Expr.WScoped.instantiate1_gen hw.2 0 hw.1.2)
  | zeta n ty v b rest ih =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G
      (.letE n (substAK d 0 a ty) (substAK d 0 a v)
        (substAK d 1 a b)) _
    refine RawReach.zeta _ _ _ _ ?_
    rw [show (substAK d 1 a b).instantiate1 (substAK d 0 a v)
        = substAK d 0 a (b.instantiate1 v) from
      substAK_instantiate1 hab hb.1.2 b 0]
    exact ih
      (Setlec.Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
      (Setlec.Expr.WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
  | litNat e rest ih =>
    intro hb hw
    rcases litToCtorIfNat_cases env e with hid | ⟨n, rfl, hconv⟩
    · rw [show Setlec.litToCtorIfNat env e = e from hid] at ih
      exact ih hb hw
    · refine RawReach.litNat (.lit (.natVal n)) ?_
      rw [show substAK d 0 a (Setlec.litToCtorIfNat env
            (.lit (.natVal n)))
          = Setlec.litToCtorIfNat env (.lit (.natVal n)) from
        substAK_eq_self_of_closed
          (by rw [hconv]; exact (natLitToConstructor_closed n).1)
          (by rw [hconv]
              exact (natLitToConstructor_closed n).2)] at ih
      exact ih
        (by rw [hconv]; exact (natLitToConstructor_closed n).2)
        (by rw [hconv]
            exact Setlec.Expr.WScoped.of_not_hasFvar
              (natLitToConstructor_closed n).1)
  | litStr s g hg hs hr rest ih =>
    intro hb hw
    have hbt := Setlec.whnf_looseBVars (mode := μ) henv g hr
      (strLitToConstructor_bounded s)
    have hft := whnf_closed_out_fvarfree henv
      (strLitToConstructor_not_hasFvar s) hr
    refine RawReach.litStr s g hg hs
      (whnf_closed_depth_down henv
        (strLitToConstructor_not_hasFvar s) hr) ?_
    rw [show substAK d 0 a _ = _ from
      substAK_eq_self_of_closed hft hbt] at ih
    exact ih hbt (Setlec.Expr.WScoped.of_not_hasFvar hft)
  | delta hu rest ih =>
    intro hb hw
    obtain ⟨hb', hw'⟩ := unfoldDefinition_pres henv hu hb hw
    exact RawReach.delta (substAK_unfoldDefinition henv hu)
      (ih hb' hw')
  | natSucc x n hs hx hnl rest ihx ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G
      (.app (.const Setlec.natSuccName []) (substAK d 0 a x)) _
    refine RawReach.natSucc _ n hs (ihx hb.2 hw.2)
      (by rw [substAK_of_rawNatLit hnl]; exact hnl) ?_
    rw [show substAK d 0 a (Expr.lit (.natVal (n + 1)))
        = Expr.lit (.natVal (n + 1)) from rfl] at ihr
    exact ihr rfl (Setlec.Expr.WScoped.of_not_hasFvar rfl)
  | natU1 c x n hc hg hx hnl hres rest ihx ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G
      (.app (.const c []) (substAK d 0 a x)) _
    refine RawReach.natU1 c _ n hc hg (ihx hb.2 hw.2)
      (by rw [substAK_of_rawNatLit hnl]; exact hnl) hres ?_
    rw [show substAK d 0 a _ = _ from
      substAK_eq_self_of_closed (natOpResult_closed hres).1
        (natOpResult_closed hres).2] at ihr
    exact ihr (natOpResult_closed hres).2
      (Setlec.Expr.WScoped.of_not_hasFvar
        (natOpResult_closed hres).1)
  | natB c x y n₁ n₂ hc hg hx hy hnx hny hres rest ihx ihy ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G
      (.app (.app (.const c []) (substAK d 0 a x))
        (substAK d 0 a y)) _
    refine RawReach.natB c _ _ n₁ n₂ hc hg
      (ihx hb.1.2 hw.1.2) (ihy hb.2 hw.2)
      (by rw [substAK_of_rawNatLit hnx]; exact hnx)
      (by rw [substAK_of_rawNatLit hny]; exact hny) hres ?_
    rw [show substAK d 0 a _ = _ from
      substAK_eq_self_of_closed (natOpResult_closed hres).1
        (natOpResult_closed hres).2] at ihr
    exact ihr (natOpResult_closed hres).2
      (Setlec.Expr.WScoped.of_not_hasFvar
        (natOpResult_closed hres).1)
  | iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen hM hMfn hrl
      hml hnin rest ihM ihr =>
    intro hb hw
    obtain ⟨hMb, hMw⟩ := RawReach.pres henv hM
      (Setlec.looseBVarsBounded_getAppArgs hb _
        (Setlec.getD_mem (by rw [hlen]; omega)))
      (Setlec.Expr.WScoped.getAppArgs hw _
        (Setlec.getD_mem (by rw [hlen]; omega)))
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP rules rfl rl
      (List.mem_of_find?_eq_some hrl)
    rename_i e' M' w'
    refine RawReach.iotaPlain c us cv mI rP rules rl cj usj
      (M := substAK d 0 a M') (w := substAK d 0 a w')
      (substAK_getAppFn_const hfn) hc ?_ ?_
      (substAK_getAppFn_const hMfn) hrl ?_ hnin ?_
    · rw [substAK_getAppArgs_const hfn, List.length_map]
      exact hlen
    · rw [substAK_getAppArgs_const hfn,
        getD_map_lt (by rw [hlen]; omega)]
      exact ihM
        (Setlec.looseBVarsBounded_getAppArgs hb _
          (Setlec.getD_mem (by rw [hlen]; omega)))
        (Setlec.Expr.WScoped.getAppArgs hw _
          (Setlec.getD_mem (by rw [hlen]; omega)))
    · rw [substAK_getAppArgs_const hMfn, List.length_map]
      exact hml
    · rw [substAK_getAppArgs_const hfn,
        substAK_getAppArgs_const hMfn]
      rw [substAK_mkAppN,
        substAK_eq_self_of_closed
          (e := rl.rhs.instantiateLevelParams cv.levelParams us)
          (by rw [Setlec.Expr.hasFvar_instantiateLevelParams]
              exact hrfv)
          (by
            rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb)] at ihr
      simp only [List.map_append, List.map_take, List.map_drop]
        at ihr
      refine ihr (Setlec.looseBVarsBounded_mkAppN
        (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb) ?_)
        (Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hrfv)) ?_)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.looseBVarsBounded_getAppArgs hb _
            (List.take_subset _ _ hz)
        · exact Setlec.looseBVarsBounded_getAppArgs hMb _
            (List.drop_subset _ _ hz)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.Expr.WScoped.getAppArgs hw _
            (List.take_subset _ _ hz)
        · exact Setlec.Expr.WScoped.getAppArgs hMw _
            (List.drop_subset _ _ hz)
  | iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn hc hlen
      hM hcj hT hTi hK hml htb htw rest ihM ihr =>
    intro hb hw
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP [rl] rfl rl
      List.mem_cons_self
    rename_i e' M' w'
    refine RawReach.iotaK c us cv mI rP rl cvj cnP T usT cvT caps
      (targs.map (substAK d 0 a))
      (M := substAK d 0 a M') (w := substAK d 0 a w')
      (substAK_getAppFn_const hfn) hc ?_ ?_ hcj hT hTi hK ?_ ?_ ?_
      ?_
    · rw [substAK_getAppArgs_const hfn, List.length_map]
      exact hlen
    · rw [substAK_getAppArgs_const hfn,
        getD_map_lt (by rw [hlen]; omega)]
      exact ihM
        (Setlec.looseBVarsBounded_getAppArgs hb _
          (Setlec.getD_mem (by rw [hlen]; omega)))
        (Setlec.Expr.WScoped.getAppArgs hw _
          (Setlec.getD_mem (by rw [hlen]; omega)))
    · rw [← List.map_take, List.length_map]
      exact hml
    · intro z hz
      rw [← List.map_take] at hz
      obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
      exact substAK_bounded hab (htb z₀ hz₀)
    · intro z hz
      rw [← List.map_take] at hz
      obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
      exact substAK_WScoped hwa (htw z₀ hz₀)
    · rw [substAK_getAppArgs_const hfn]
      rw [substAK_mkAppN,
        substAK_eq_self_of_closed
          (e := rl.rhs.instantiateLevelParams cv.levelParams us)
          (by rw [Setlec.Expr.hasFvar_instantiateLevelParams]
              exact hrfv)
          (by
            rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb)] at ihr
      simp only [List.map_append, List.map_take, List.map_drop]
        at ihr
      refine ihr (Setlec.looseBVarsBounded_mkAppN
        (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb) ?_)
        (Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hrfv)) ?_)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.looseBVarsBounded_getAppArgs hb _
            (List.take_subset _ _ hz)
        · exact htb _ (List.drop_subset _ _ hz)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.Expr.WScoped.getAppArgs hw _
            (List.take_subset _ _ hz)
        · exact htw _ (List.drop_subset _ _ hz)
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml htb htw rest ihM ihr =>
    intro hb hw
    rename_i e' M' w'
    obtain ⟨hMb, hMw⟩ := RawReach.pres henv hM
      (Setlec.looseBVarsBounded_getAppArgs hb _
        (Setlec.getD_mem (by rw [hlen]; omega)))
      (Setlec.Expr.WScoped.getAppArgs hw _
        (Setlec.getD_mem (by rw [hlen]; omega)))
    obtain ⟨-, -, -, -, -, hrec, -⟩ := henv _ (Setlec.find?_mem hc)
    obtain ⟨hrfv, -, -, hrb, -⟩ := hrec cv mI rP [rl] rfl rl
      List.mem_cons_self
    have hfabB : ∀ z ∈ Setlec.etaFabArgs T ust targs M'
        caps.etaFields, z.looseBVarsBounded 0 = true := by
      intro z hz
      unfold Setlec.etaFabArgs at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact htb z hz
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
        refine Setlec.looseBVarsBounded_mkAppN rfl ?_
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact htb y hy
        · rw [List.mem_singleton] at hy
          exact hy ▸ hMb
    have hfabW : ∀ z ∈ Setlec.etaFabArgs T ust targs M'
        caps.etaFields, Expr.WScoped (d + 1) z := by
      intro z hz
      unfold Setlec.etaFabArgs at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact htw z hz
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
        refine Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar rfl) ?_
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact htw y hy
        · rw [List.mem_singleton] at hy
          exact hy ▸ hMw
    refine RawReach.iotaEta c us ust cv mI rP rl cvj cnP cnF T usT
      cvT caps (targs.map (substAK d 0 a))
      (M := substAK d 0 a M') (w := substAK d 0 a w')
      (substAK_getAppFn_const hfn) hc ?_ ?_ hcj hT hTi heta hec ?_
      ?_ ?_ ?_
    · rw [substAK_getAppArgs_const hfn, List.length_map]
      exact hlen
    · rw [substAK_getAppArgs_const hfn,
        getD_map_lt (by rw [hlen]; omega)]
      exact ihM
        (Setlec.looseBVarsBounded_getAppArgs hb _
          (Setlec.getD_mem (by rw [hlen]; omega)))
        (Setlec.Expr.WScoped.getAppArgs hw _
          (Setlec.getD_mem (by rw [hlen]; omega)))
    · rw [← substAK_etaFabArgs, List.length_map]
      exact hml
    · intro z hz
      obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
      exact substAK_bounded hab (htb z₀ hz₀)
    · intro z hz
      obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
      exact substAK_WScoped hwa (htw z₀ hz₀)
    · rw [substAK_getAppArgs_const hfn, ← substAK_etaFabArgs]
      rw [substAK_mkAppN,
        substAK_eq_self_of_closed
          (e := rl.rhs.instantiateLevelParams cv.levelParams us)
          (by rw [Setlec.Expr.hasFvar_instantiateLevelParams]
              exact hrfv)
          (by
            rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb)] at ihr
      simp only [List.map_append, List.map_take, List.map_drop]
        at ihr
      refine ihr (Setlec.looseBVarsBounded_mkAppN
        (by rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hrb) ?_)
        (Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar (by
            rw [Setlec.Expr.hasFvar_instantiateLevelParams]
            exact hrfv)) ?_)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.looseBVarsBounded_getAppArgs hb _
            (List.take_subset _ _ hz)
        · exact hfabB _ (List.drop_subset _ _ hz)
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Setlec.Expr.WScoped.getAppArgs hw _
            (List.take_subset _ _ hz)
        · exact hfabW _ (List.drop_subset _ _ hz)
  | projFire sn i entry us hf hfn hnat hi hlenE rest ihr =>
    intro hb hw
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Expr.WScoped] at hw
    show RawReach μ env d G (.proj sn i (substAK d 0 a _)) _
    refine RawReach.projFire sn i entry us hf
      (substAK_getAppFn_const hfn) hnat hi ?_ ?_
    · rw [substAK_getAppArgs_const hfn, List.length_map]
      exact hlenE
    · rw [substAK_getAppArgs_const hfn,
        getD_map_lt (by rw [hlenE]; omega)]
      exact ihr
        (Setlec.looseBVarsBounded_getAppArgs hb _
          (Setlec.getD_mem (by rw [hlenE]; omega)))
        (Setlec.Expr.WScoped.getAppArgs hw _
          (Setlec.getD_mem (by rw [hlenE]; omega)))

/-- The LEFT telescope substitution preserves local closedness. -/
theorem thetaSubst_bounded₁ {μ : CheckMode} {env : Env} {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeOk μ env fcK d Γ →
      X.looseBVarsBounded 0 = true →
      (thetaSubst₁ d Γ X).looseBVarsBounded 0 = true
  | [], d, X => fun _ hb => hb
  | t :: Γ', d, X => fun hΓ hb => by
    obtain ⟨-, -, hI₁, -, -, hΓ'⟩ := hΓ
    exact substAK_bounded hI₁.2.1 (thetaSubst_bounded₁ hΓ' hb)

/-- The RIGHT telescope substitution preserves local closedness. -/
theorem thetaSubst_bounded₂ {μ : CheckMode} {env : Env} {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeOk μ env fcK d Γ →
      X.looseBVarsBounded 0 = true →
      (thetaSubst₂ d Γ X).looseBVarsBounded 0 = true
  | [], d, X => fun _ hb => hb
  | t :: Γ', d, X => fun hΓ hb => by
    obtain ⟨-, -, -, hI₂, -, hΓ'⟩ := hΓ
    exact substAK_bounded hI₂.2.1 (thetaSubst_bounded₂ hΓ' hb)

/-- The LEFT telescope substitution lands at the outer scope. -/
theorem thetaSubst_WScoped₁ {μ : CheckMode} {env : Env} {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeOk μ env fcK d Γ →
      Expr.WScoped (d + Γ.length) X →
      Expr.WScoped d (thetaSubst₁ d Γ X)
  | [], d, X => fun _ hw => hw
  | t :: Γ', d, X => fun hΓ hw => by
    obtain ⟨-, -, hI₁, -, -, hΓ'⟩ := hΓ
    refine substAK_WScoped hI₁.1 ?_
    refine thetaSubst_WScoped₁ hΓ' ?_
    have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
      simp [List.length_cons]
      omega
    rw [heq]
    exact hw

/-- The RIGHT telescope substitution lands at the outer scope. -/
theorem thetaSubst_WScoped₂ {μ : CheckMode} {env : Env} {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d : Nat} {X : Expr},
      TelescopeOk μ env fcK d Γ →
      Expr.WScoped (d + Γ.length) X →
      Expr.WScoped d (thetaSubst₂ d Γ X)
  | [], d, X => fun _ hw => hw
  | t :: Γ', d, X => fun hΓ hw => by
    obtain ⟨-, -, -, hI₂, -, hΓ'⟩ := hΓ
    refine substAK_WScoped hI₂.1 ?_
    refine thetaSubst_WScoped₂ hΓ' ?_
    have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
      simp [List.length_cons]
      omega
    rw [heq]
    exact hw

/-! #### The telescope trace (E3): traces map down the Θ telescope -/

/-- A trace at the telescope's inner depth maps under the LEFT
telescope substitution to a trace at the outer depth (fold of
`RawReach.image` over `Γ`; the arguments' packages come from
`TelescopeOk`). -/
theorem thetaSubst₁_trace {env : Env} (henv : EnvWF env)
    {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d G : Nat} {X Y : Expr},
      TelescopeOk μ env fcK d Γ →
      RawReach μ env (d + Γ.length) G X Y →
      X.looseBVarsBounded 0 = true →
      Expr.WScoped (d + Γ.length) X →
      RawReach μ env d G (thetaSubst₁ d Γ X) (thetaSubst₁ d Γ Y)
  | [], d, G, X, Y => fun _ h _ _ => h
  | t :: Γ', d, G, X, Y => fun hΓ h hb hw => by
    obtain ⟨-, -, hI₁, -, -, hΓ'⟩ := hΓ
    have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
      simp [List.length_cons]
      omega
    have h' : RawReach μ env ((d + 1) + Γ'.length) G X Y := by
      rw [heq]
      exact h
    have hw' : Expr.WScoped ((d + 1) + Γ'.length) X := by
      rw [heq]
      exact hw
    have hin := thetaSubst₁_trace henv hΓ' h' hb hw'
    show RawReach μ env d G
      (substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' X))
      (substAK d 0 t.a₁ (thetaSubst₁ (d + 1) Γ' Y))
    refine RawReach.image henv hin hI₁.2.1 hI₁.1 ?_ ?_
    · exact thetaSubst_bounded₁ hΓ' hb
    · exact thetaSubst_WScoped₁ hΓ' hw'

/-- The RIGHT-side telescope trace. -/
theorem thetaSubst₂_trace {env : Env} (henv : EnvWF env)
    {fcK : Nat} :
    ∀ {Γ : List ThetaEntry} {d G : Nat} {X Y : Expr},
      TelescopeOk μ env fcK d Γ →
      RawReach μ env (d + Γ.length) G X Y →
      X.looseBVarsBounded 0 = true →
      Expr.WScoped (d + Γ.length) X →
      RawReach μ env d G (thetaSubst₂ d Γ X) (thetaSubst₂ d Γ Y)
  | [], d, G, X, Y => fun _ h _ _ => h
  | t :: Γ', d, G, X, Y => fun hΓ h hb hw => by
    obtain ⟨-, -, -, hI₂, -, hΓ'⟩ := hΓ
    have heq : (d + 1) + Γ'.length = d + (t :: Γ').length := by
      simp [List.length_cons]
      omega
    have h' : RawReach μ env ((d + 1) + Γ'.length) G X Y := by
      rw [heq]
      exact h
    have hw' : Expr.WScoped ((d + 1) + Γ'.length) X := by
      rw [heq]
      exact hw
    have hin := thetaSubst₂_trace henv hΓ' h' hb hw'
    show RawReach μ env d G
      (substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' X))
      (substAK d 0 t.a₂ (thetaSubst₂ (d + 1) Γ' Y))
    refine RawReach.image henv hin hI₂.2.1 hI₂.1 ?_ ?_
    · exact thetaSubst_bounded₂ hΓ' hb
    · exact thetaSubst_WScoped₂ hΓ' hw'

end Discharge

end Setlec.SetR.Interp2
