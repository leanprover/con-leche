import Setlec.SetR.Interp2.Step2.Routed
import Setlec.SetR.Interp2.Step2.Fuel
import Setlec.SetR.Bridge.InferStruct

/-!
# `InferStep2` — the inference quarter, discharged and routed

`inferBody`'s eleven clauses against `InferClaims2`, and the assembly
`inferStep2_of`.  The ledger, clause by clause:

| clause | status |
|---|---|
| `.sort`, `.bvar` | closed (`Step2/Dispatch.lean`) |
| `.forallE` | **closed here**, outright |
| `.lam` | closed here modulo `LamCodSort2` |
| `.app`, `.letE` | closed here modulo `BetaCross2` |
| `.const` | closed here modulo `ConstType2` |
| `.lit (.natVal _)` | closed here modulo `NatHeads2` |
| `.fvar` | routed — the seal-3 STOP (`FvarCtx2`) |
| `.lit (.strVal _)`, `.proj` | routed, clause-granular |

Every residue is stated at the smallest granularity the clause's own
proof exposes: where a clause closes *except* for one missing fact,
the fact is the residue and the clause is a theorem, so the ledger
records what is missing rather than what is unfinished.

## Three things this quarter learned

* **STOP — `InferClaims2` is refuted at low fuel**, and the routing
  is what found it.  The claim asks the *returned type* to have a
  `denote2` at the claim's own fuel; `.const` and `.fvar` recurse
  into nothing, so nothing pays for it, and at fuel `1` no `whnf`
  succeeds at all.  `inferClaims2_one_refuted` is the mechanized
  witness, and `CheckStep2` falls with it.  See the STOP section.
* **`denote2` fuel-monotonicity is a theorem, not an input**
  (`Step2/Fuel.lean`).  `Claims2`'s ledger scheduled it and
  `Step2Inputs` carries `InferFuelDet` for it; `knotFuelMono` has
  landed since, and the monotone form — which is what the clauses
  consume — follows outright.  It is also the natural repair
  material for the STOP.
* **`denote2`'s λ clause is finer-grained than the checker's λ
  check** (the `LamCodSort2` section).  The task-#152 codomain-sort
  computation runs once per λ *chain* and only at the verified modes;
  `denote2` asks for it at every λ *node*.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level BinderMeta inferTypeCore
  whnf)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## Two readings of a run -/

/-- The checker's own sort computation, read off a run: infer, then
whnf to a sort.  Every binder clause of `denote2` wants one of these
and every binder clause of `inferBody` produces one. -/
theorem sortOfE_of_run {f d : Nat} {e t : Expr} {u : Level}
    (hi : inferTypeCore μ env f d e = .ok t)
    (hw : whnf μ env f d t = .ok (.sort u)) :
    sortOfE μ env φ f d e = some (u.eval φ) := by
  unfold sortOfE
  rw [hi]
  simp only [Except.toOption]
  rw [hw]

/-- The converse reading: a successful `sortOfE` *is* a pair of runs.
`denote2` stores the checker's numerals, so a clause that receives an
annotation receives the runs that produced it — this is how the
application clause recovers the ∀'s codomain-sort fact, which its own
`inferBody` branch never computes. -/
theorem sortOfE_runs {f d : Nat} {e : Expr} {k : Nat}
    (h : sortOfE μ env φ f d e = some k) :
    ∃ t l, inferTypeCore μ env f d e = .ok t ∧
      whnf μ env f d t = .ok (.sort l) ∧ l.eval φ = k := by
  unfold sortOfE at h
  cases hi : inferTypeCore μ env f d e with
  | error err => rw [hi] at h; exact nomatch h
  | ok t =>
    rw [hi] at h
    simp only [Except.toOption] at h
    cases hw : whnf μ env f d t with
    | error err => rw [hw] at h; exact nomatch h
    | ok w =>
      rw [hw] at h
      revert h
      match w with
      | .sort l => intro h; exact ⟨t, l, rfl, hw, Option.some.inj h⟩
      | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _
      | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _
      | .proj _ _ _ => intro h; exact nomatch h

/-- `denote2` at a sort. -/
theorem denote2_sort {acval : Name → (Name → Nat) → AVExpr} {f d : Nat}
    {u : Level} :
    denote2 μ acval env φ f d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denote2]

/-- **A subject whose inferred type whnfs to a sort interprets into
that universe.**  The `interp2` transpose of `inferSortR`: the
inference claim gives the membership at the *inferred* type's
annotation, the reduction claim moves it to the sort's, and
`interp2_sort` reads the result.  Every binder clause runs this
twice. -/
theorem inferSort2 (m : EnvS2 V env) {d : Nat}
    {Δa : List AVExpr} {e t : Expr} {u : Level}
    (ihw : WhnfClaims2 μ m φ fuel) (ihi : InferClaims2 μ m φ fuel)
    (hi : inferTypeCore μ env fuel d e = .ok t)
    (hw : whnf μ env fuel d t = .ok (.sort u))
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e)
    {ea : AVExpr} (hea : denote2 μ m.acval env φ fuel d e = some ea) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ (univ (u.eval φ) : V) := by
  obtain ⟨ea', ta, hea', hta, hrow⟩ := ihi hi hws hb hLb hC
  obtain rfl : ea' = ea := by
    rw [hea'] at hea; exact Option.some.inj hea
  obtain ⟨htw, htb, htL, htC⟩ :=
    frame_inferR m.base.wf hi hws hb hLb hC
  obtain ⟨sa, hsa, hred⟩ := ihw hw htw htb htL htC hta
  rw [denote2_sort] at hsa
  obtain rfl : sa = AVExpr.sort (u.eval φ) := (Option.some.inj hsa).symm
  intro ρ hρ
  obtain ⟨hok, hmem⟩ := hrow ρ hρ
  refine ⟨hok, ?_⟩
  rw [← interp2_sort (V := V) (ρ := ρ) (u := u.eval φ)]
  exact (hred ρ hρ).1 ▸ hmem

/-! ## I6: the `∀` clause -/

/-- **`.forallE`.**  The clause `denote2`'s own `pi` former was built
for: the checker's two sort runs *are* the two `sortOfE` calls the
annotation makes, the opened body is the same opened body on both
sides, and the returned type is a sort — so nothing crosses a
substitution and the row is `sound_pi` on the nose. -/
theorem infer_forallE_claim2 (m : EnvS2 V env) {d : Nat} {n : Name}
    {ty body t : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    (ihw : WhnfClaims2 μ m φ fuel) (ihi : InferClaims2 μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hb : (Expr.forallE n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE n ty body mb))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.forallE n ty body mb)) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.forallE n ty body mb)
        = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, vv, hty, hwu, hbt, hens, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody :
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) body :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the domain: its annotation, and its erasure for the opening
  obtain ⟨ta, tta, hta, htta, -⟩ := ihi hty hws.1 hb.1 hLty hCty
  have htaE : Setlec.TTVerify.denote m.base.cval env φ d ty
      = some ta.erase := denote2_erase m.acval_erase d ty hta
  obtain ⟨hwopen, hbopen, hLopen, hCopen⟩ :=
    frame_openR (n := n) m.base.cval_closed hws.1 hb.1 hws.2 hb.2 hLty
      hLbody hCty hCbody htaE
  have hCopen' : CtxOkR μ m.base.cval env φ (d + 1)
      ((ta :: Δa).map AVExpr.erase)
      (body.instantiate1 (.fvar d n ty)) := by
    simpa using hCopen
  -- the codomain, in the extended context
  obtain ⟨ba, tbt, hba, -, -⟩ := ihi hbt hwopen hbopen hLopen hCopen'
  -- the two sort facts
  have hdomS := inferSort2 m ihw ihi hty hwu hws.1 hb.1 hLty hCty hta
  have hcodS :=
    inferSort2 m ihw ihi hbt (Setlec.ensureSortCore_inv hens)
      hwopen hbopen hLopen hCopen' hba
  refine ⟨.pi (u.eval φ) (vv.eval φ) ta ba,
    .sort (Setlec.TT.imax (u.eval φ) (vv.eval φ)), ?_, ?_, ?_⟩
  · rw [denote2, denote2_fuelMono (Nat.le_succ fuel) d ty hta,
      denote2_fuelMono (Nat.le_succ fuel) (d + 1) _ hba,
      sortOfE_fuelMono (φ := φ) (Nat.le_succ fuel)
        (sortOfE_of_run hty hwu),
      sortOfE_fuelMono (φ := φ) (Nat.le_succ fuel)
        (sortOfE_of_run hbt (Setlec.ensureSortCore_inv hens))]
    rfl
  · rw [denote2_sort]
    rfl
  · intro ρ hρ
    refine sound_pi V (hdomS ρ hρ).1 (fun x hx => ?_) (hdomS ρ hρ).2
      (fun x hx => ?_)
    · exact (hcodS (cons x ρ) (Sat2_cons V hρ hx)).1
    · exact (hcodS (cons x ρ) (Sat2_cons V hρ hx)).2

/-! ## I3: the `const` clause, and its routed half

`EnvS2.mem_type2` is stated **conditionally on** a `denote2` of the
stored type at depth `0` and the substituted assignment; the clause
needs one at the *ambient* depth `d` and the *instantiated* type, and
it needs it to **exist**.  Neither crossing has a lemma:
`denote_instLevels`/`denote_lift` are `denote`-side, and their
`denote2` analogues are false-to-hard — `sortOfE` runs the checker on
the expression, so the level-instantiated and the uninstantiated runs
are different runs, and no level-substitution commutation for the knot
exists.  So the crossing is bundled with the definedness into one
honest residue, in exactly the shape the clause consumes.

**And the residue is false at `fuel = 1`** — which is not a defect of
the residue but the statement's, and is where this quarter's STOP was
found.  See `inferClaims2_one_refuted` below. -/

/-- **The `const` clause's residue**: a stored constant's *instantiated*
type has a canonical annotation at every depth, and the constant
inhabits it.  `EnvS2.mem_type2` is the depth-`0`, uninstantiated
half. -/
def ConstType2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : Setlec.ConstantInfo) (us : List Level),
    env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta, denote2 μ m.acval env φ fuel d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp2 V ρ ta

/-- **`.const`.**  Truthfulness is `acval_ok2`; the membership and the
returned type's definedness are the residue above. -/
theorem infer_const_claim2 (m : EnvS2 V env) (hct : ConstType2 m μ φ
      (fuel + 1)) {d : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.const n us) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  cases hf : env.find? n with
  | none =>
    rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨ta, hta, hmem⟩ := hct d n ci us hf hlen
      refine ⟨m.acval n
        (Level.substFn φ ci.toConstantVal.levelParams us), ta, ?_, hta,
        fun ρ _ => ⟨m.acval_ok2 n _ ρ, hmem ρ⟩⟩
      rw [denote2, hf]
      dsimp only
      rw [if_pos hlen]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## I4: the `Nat`-literal clause, and its routed half

`natLit_facts2` takes the two head facts as explicit arguments and
`Claims2`'s ledger points at `mem_type2` for them.  **They do not come
from there at this claim's fuel.**  `mem_type2` is conditional on a
`denote2` of the stored type; `Nat.succ`'s stored type is `Nat → Nat`,
so that `denote2` runs `denote2`'s `pi` clause, so it wants two
`sortOfE`s — two *knot runs at the claim's own fuel*, and the `.lit`
clause of `inferBody` runs nothing at all (it is a guard and a stored
name).  At `fuel + 1 = 1` the runs throw outright.  So the head facts
are not derivable here at any fuel the clause controls, and they are
routed. -/

/-- **The `Nat`-literal clause's residue**: the zero's membership and
the successor's, at the annotated valuation's own `Nat` leaf. -/
def NatHeads2 {env : Env} (m : EnvS2 V env) (φ : Name → Nat) : Prop :=
  Setlec.natLitSupported env = true →
  ∀ ρ : Nat → V,
    interp2 V ρ (m.acval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp2 V ρ (m.acval natName (Level.substFn φ [] [])) ∧
    interp2 V ρ (m.acval natSuccName (Level.substFn φ [] []))
      ∈ˢ piR 1 (interp2 V ρ (m.acval natName (Level.substFn φ [] [])))
        (fun _ => interp2 V ρ
          (m.acval natName (Level.substFn φ [] [])))

/-- **`.lit (.natVal k)`.**  The numeral induction is
`natLit_facts2`; the head facts are the residue, and the returned
`.const natName []` denotes because the support guard pins the stored
declaration's level parameters empty. -/
theorem infer_natLit_claim2 (m : EnvS2 V env) (hnh : NatHeads2 m φ)
    {d k : Nat} {t : Expr} {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.lit (.natVal k))
        = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : Setlec.natLitSupported env = true := by simpa using hg
    cases hf : env.find? natName with
    | none =>
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        natName_levelParams_nil hgt hf
      refine ⟨natLitT2 (m.acval natZeroName (Level.substFn φ [] []))
          (m.acval natSuccName (Level.substFn φ [] [])) k,
        m.acval natName (Level.substFn φ [] []), ?_, ?_, ?_⟩
      · rw [denote2, if_pos hgt]
      · rw [denote2, hf]
        dsimp only
        rw [if_pos (by simp [hlp]), hlp]
      · intro ρ _
        exact natLit_facts2 (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ)
          (hnh hgt ρ).1 (hnh hgt ρ).2 k
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The residues

Two clauses are routed whole (`.lit (.strVal _)`, `.proj`), named at
**clause granularity** — `inferBody` restricted to one `Expr` shape,
the only legitimate boundary (the `InferPiStepR` pattern of
`Bridge/Infer.lean`).  Three more are routed at a *sub-clause*
granularity: the clause is proved, one named fact is missing.

**I2 (`.fvar`)** is the seal-3 STOP, unchanged: `Claims2`'s hypothesis
side carries `CtxOkR` at the *erasures*, which states the leaf package
in the relational currency; the clause reads it in the annotated one.
`Dispatch.lean`'s `CtxOk2` is the proposed repair and
`CtxOk2.fvar_leaf` checks that it supplies exactly this residue. -/

/-- The `.fvar` clause's residue — `CtxOk2.fvar_leaf`'s conclusion,
conditioned on the claim's own hypothesis. -/
def FvarCtx2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d idx : Nat} {n : Name} {ty : Expr} {Δa : List AVExpr},
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.fvar idx n ty) →
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d ty = some tya ∧
      Δa[d - 1 - idx]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa

/-! ### I5 (`.lit (.strVal _)`)

The transposition of `Sound/Lit.lean`'s `strLit_facts` (394 lines)
onto `charListT2`.  Volume, mostly — but it also inherits
`NatHeads2`'s obstruction several times over: the head facts it needs
are for `String.ofList`, `List.nil`/`List.cons`, `Char.ofNat` and the
two `Nat` constructors, and every one of those stored types is a `pi`,
whose `denote2` wants `sortOfE` runs the `.lit` branch of `inferBody`
never makes.  Routed whole rather than to seven head facts, since the
numeral induction is not written either. -/

/-- The `String`-literal clause. -/
def InferStrLitStep2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {s : String} {t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t →
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.lit (.strVal s))
        = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-! ### I7 (`.lam`) — the chain-granularity mismatch

**The third finding.**  `denote2`'s `lam` clause calls
`lamSortE` at **every** λ node.  `inferBody` runs that computation at
**one node per λ chain** — the `!body.isLam` guard of task #152 — and
only when `mode.verified`.  So the clause's own run does not supply
`denote2`'s own λ clause, and the claim's `∃ ea` conclusion has no
witness at this node.

Two regimes, and they differ:

* at `.noModel` (`CheckMode.verified = false`, the official-parity
  lane, which the reference kernel's `infer_lambda` matches) the check
  runs at **no** λ node at all.  `denote2` of any λ may then be
  `none`, and the claim as stated is not merely unproved here — it has
  no supplier anywhere in the lane;
* at the verified modes the check runs at the innermost binder, and an
  outer binder's `lamSortE` unfolds into the *inner* λ's runs
  (`sortOfE` of the inner λ's inferred `∀`-type is the inner domain
  check plus the inner codomain check), so it is reachable — by an
  induction **down the λ chain**, at descending fuels lifted back by
  `knotFuelMono`.  That induction is not the clause's; `inferBody`'s
  case split gives one node.

The checker's own comment argues no *fact* is lost ("the codomain is
the inner λ's own `∀`-type, whose sort is `imax` of …").  True of the
sorts' **values**; `denote2` additionally needs the computation to
*succeed at this node*, which is what the per-node clause does not
give.  Three exits, and the choice is a junction decision: weaken
`denote2`'s λ clause to default the numeral where the check is
skipped; run the check at every λ node; or land the chain induction
(and, for `.noModel`, decide whether `Claims2` is claimed there at
all).  Routed to the residue below. -/

/-- **The λ clause's residue**, and it is exactly the missing run:
the task-#152 codomain-sort check's output at **every** λ node, not
only at the chain's innermost one.  `inferTypeCore_lam_inv` delivers
this same pair under `mode.verified = true → body.isLam = false`;
strike those two side conditions and the clause below closes.

Deliberately *not* stated as the general "an inferred type is itself
sorted" — that is validity for `Infer`, refuted at the application
clause (`Setlec/SetR/DESIGN.md`, findings A3/B5/A5).  The λ-node run
is in the premises, so the residue claims nothing outside the sites
the checker already visits. -/
def LamCodSort2 (μ : CheckMode) (env : Env) : Prop :=
  ∀ {fuel d : Nat} {n : Name} {ty body bt t : Expr} {mb : BinderMeta},
    inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t →
    inferTypeCore μ env fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) = .ok bt →
    ∃ btt v, inferTypeCore μ env fuel (d + 1) bt = .ok btt ∧
      whnf μ env fuel (d + 1) btt = .ok (.sort v)

/-- **`.lam`, modulo the codomain-sort run.**  Everything else in the
clause closes: the abstraction round trip is `abstract1_instantiate1`
(the leaf discipline supplies its side condition), the domain sort is
the clause's own `whnf`, and the row is `sound_lam` — whose kind-`0`
fibre premise is *also* the residue's sort fact, read through
`inferSort2`. -/
theorem infer_lam_claim2 (m : EnvS2 V env) (hcod : LamCodSort2 μ env)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : BinderMeta}
    {Δa : List AVExpr}
    (ihw : WhnfClaims2 μ m φ fuel) (ihi : InferClaims2 μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.lam n ty body mb)) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.lam n ty body mb)
        = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, -, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  obtain ⟨btt, v, hbtt, hwv⟩ := hcod h hbt
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody :
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) body :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  obtain ⟨ta, tta, hta, -, -⟩ := ihi hty hws.1 hb.1 hLty hCty
  have htaE : Setlec.TTVerify.denote m.base.cval env φ d ty
      = some ta.erase := denote2_erase m.acval_erase d ty hta
  obtain ⟨hwopen, hbopen, hLopen, hCopen⟩ :=
    frame_openR (n := n) m.base.cval_closed hws.1 hb.1 hws.2 hb.2 hLty
      hLbody hCty hCbody htaE
  have hCopen' : CtxOkR μ m.base.cval env φ (d + 1)
      ((ta :: Δa).map AVExpr.erase)
      (body.instantiate1 (.fvar d n ty)) := by
    simpa using hCopen
  obtain ⟨ba, tbt, hba, htbt, hrow⟩ :=
    ihi hbt hwopen hbopen hLopen hCopen'
  -- the abstraction round trip, verbatim from the `denote` lane
  have hleaf :
      Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact ⟨rfl, rfl⟩
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d n ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl =>
      hleaf l (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen l hl))
  have hbtb : bt.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.base.wf fuel hbt hwopen hbopen hLopen
  have hround : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
    abstract1_instantiate1 bt 0 hcons hbtb
  -- the residue's sort fact, read semantically
  obtain ⟨hwsbt, -, hLbt, hCbt⟩ :=
    frame_inferR m.base.wf hbt hwopen hbopen hLopen hCopen'
  have hcodS := inferSort2 m ihw ihi hbtt hwv hwsbt hbtb hLbt hCbt htbt
  have hlamS : lamSortE μ env φ (fuel + 1) (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some (v.eval φ) := by
    unfold lamSortE
    rw [(knotFuelMono μ env).1 (Nat.le_succ fuel) hbt]
    simp only [Except.toOption]
    exact sortOfE_fuelMono (Nat.le_succ fuel) (sortOfE_of_run hbtt hwv)
  refine ⟨.lam (v.eval φ) ta ba,
    .pi (u.eval φ) (v.eval φ) ta tbt, ?_, ?_, ?_⟩
  · rw [denote2, denote2_fuelMono (Nat.le_succ fuel) d ty hta,
      denote2_fuelMono (Nat.le_succ fuel) (d + 1) _ hba, hlamS]
    rfl
  · rw [denote2, denote2_fuelMono (Nat.le_succ fuel) d ty hta, hround,
      denote2_fuelMono (Nat.le_succ fuel) (d + 1) bt htbt,
      sortOfE_fuelMono (φ := φ) (Nat.le_succ fuel)
        (sortOfE_of_run hty hwu),
      sortOfE_fuelMono (φ := φ) (Nat.le_succ fuel)
        (sortOfE_of_run hbtt hwv)]
    rfl
  · intro ρ hρ
    have hdomS := inferSort2 m ihw ihi hty hwu hws.1 hb.1 hLty hCty hta
    refine sound_lam V (hdomS ρ hρ).1 (fun x hx => ?_) (fun x hx => ?_)
      (fun h0 x hx => ?_)
    · exact (hrow (cons x ρ) (Sat2_cons V hρ hx)).1
    · exact (hrow (cons x ρ) (Sat2_cons V hρ hx)).2
    · exact univ_zero (V := V) ▸ h0 ▸
        (hcodS (cons x ρ) (Sat2_cons V hρ hx)).2

/-! ### I8 (`.app`) and I10 (`.letE`) — the β crossing

Both close here; what they are short of is one named crossing.

Both return a *substituted* expression (`body'.instantiate1 a`;
`inferTypeCore` on `b.instantiate1 v`) while `sound_app`/`sound_letE`
conclude at the *descended* annotation (`Ba.inst aa`; the opened body's
`ba`).  The `denote` lane crosses this with `denote_beta`
(`Verify/Denote/Inst.lean`).  Its `denote2` analogue does not exist and
is not a transposition: `denote2`'s binder clauses carry the checker's
own sort numerals, so the crossing needs the numerals to survive the
substitution — which is exactly `SortSubstStable`
(`Annot/SimSubst.lean`, frozen, carried by `Step2Inputs`).

And `SortSubstStable` **is not enough**: it is stated for `lamSortE`
only, while `denote2`'s `pi` clause under a substituted body wants the
same stability for `sortOfE`.  The `sortOfE` twin has no statement
anywhere.  That is the second finding: the commutation kit the β
crossing needs is one lemma wider than the frozen premise. -/

/-- **The β crossing**, named once and shared by both clauses: the
canonical annotation of a substituted body is, at every satisfying
valuation, the descended annotation of the opened one.

This is `denote_beta`'s slot, and the `denote2` statement is
*semantic* rather than syntactic on purpose — `denote2`'s binder
clauses carry the checker's own numerals, and the opened and the
substituted runs can branch differently (`Annot/SimSubst.lean`'s
second trap), so an equation between the two annotations is not what
holds.  What holds is agreement of the interpretations under `Sat2`,
which is exactly `SortSubstStable`'s conclusion shape. -/
def BetaCross2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty b a : Expr} {Δa : List AVExpr}
    {aa : AVExpr},
    denote2 μ m.acval env φ fuel d a = some aa →
    (∀ {ba : AVExpr},
      denote2 μ m.acval env φ fuel (d + 1)
        (b.instantiate1 (.fvar d n ty)) = some ba →
      ∃ ra,
        denote2 μ m.acval env φ fuel d (b.instantiate1 a) = some ra ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ra = interp2 V ρ (ba.inst aa) ∧
          (AnnotOk2 V ρ ra → AnnotOk2 V ρ (ba.inst aa))) ∧
    (∀ {ra : AVExpr},
      denote2 μ m.acval env φ fuel d (b.instantiate1 a) = some ra →
      ∃ ba,
        denote2 μ m.acval env φ fuel (d + 1)
          (b.instantiate1 (.fvar d n ty)) = some ba ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ra = interp2 V ρ (ba.inst aa) ∧
          (AnnotOk2 V ρ ra → AnnotOk2 V ρ (ba.inst aa)))

/-- **`.app`, modulo the β crossing.**  The four premises of
`sound_app` are the clause's four moves: the head's inference plus the
reduction claim put it at the ∀'s *annotation*; the argument's
inference plus the defeq claim put it in the domain's; and the kind-`0`
fibre premise — which `inferBody`'s app branch never computes — is
recovered from the annotation itself, because the ∀'s `denote2` stored
the codomain `sortOfE`, and `sortOfE_runs` reads the runs back out. -/
theorem infer_app_claim2 (m : EnvS2 V env)
    (hbeta : BetaCross2 m μ φ (fuel + 1))
    {d : Nat} {f a t : Expr} {Δa : List AVExpr}
    (ihw : WhnfClaims2 μ m φ fuel) (ihd : DefEqClaims2 μ m φ fuel)
    (ihi : InferClaims2 μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.app f a)) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.app f a) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tf, n', ty', body', mb', htf, hwf, rfl, tya, hta, hde⟩ :=
    Setlec.inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) f :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  obtain ⟨fa, tfa, hfa, htfa, hrowf⟩ := ihi htf hws.1 hb.1 hLf hCf
  obtain ⟨htfw, htfb, htfL, htfC⟩ :=
    frame_inferR m.base.wf htf hws.1 hb.1 hLf hCf
  obtain ⟨pa, hpa, hredf⟩ := ihw hwf htfw htfb htfL htfC htfa
  -- the ∀'s own frame conditions
  have hwfe : Expr.WScoped d (Expr.forallE n' ty' body' mb') :=
    whnf_WScoped m.base.wf fuel hwf htfw
  have hbfe : (Expr.forallE n' ty' body' mb').looseBVarsBounded 0
      = true := whnf_looseBVars m.base.wf fuel hwf htfb
  have hLfe : Expr.LeavesBounded (.forallE n' ty' body' mb') :=
    fun l hl => htfL l (whnf_fvarLeaves m.base.wf fuel hwf l hl)
  have hCfe : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.forallE n' ty' body' mb') :=
    CtxOkR.of_subset (whnf_fvarLeaves m.base.wf fuel hwf) htfC
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty' := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hLbody' : Expr.LeavesBounded body' := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCty' : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty' :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
  have hCbody' :
      CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) body' :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
  -- decompose the ∀'s annotation into the four things `denote2` put
  -- in it
  rw [denote2] at hpa
  rcases hAa : denote2 μ m.acval env φ fuel d ty' with _ | Aa
  · rw [hAa] at hpa; exact nomatch hpa
  rw [hAa] at hpa
  rcases hBa : denote2 μ m.acval env φ fuel (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | Ba
  · rw [hBa] at hpa; exact nomatch hpa
  rw [hBa] at hpa
  rcases hu' : sortOfE μ env φ fuel d ty' with _ | u'
  · rw [hu'] at hpa; exact nomatch hpa
  rw [hu'] at hpa
  rcases hv' : sortOfE μ env φ fuel (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | v'
  · rw [hv'] at hpa; exact nomatch hpa
  rw [hv'] at hpa
  obtain rfl : pa = .pi u' v' Aa Ba := (Option.some.inj hpa).symm
  -- the argument, and its certificate against the domain
  obtain ⟨aa, taa, haa, htaa, hrowa⟩ := ihi hta hws.2 hb.2 hLa hCa
  obtain ⟨htaw, htab, htaL, htaC⟩ :=
    frame_inferR m.base.wf hta hws.2 hb.2 hLa hCa
  have hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ taa = interp2 V ρ Aa :=
    ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC hCty' htaa hAa
  -- the codomain's sort, read back out of the annotation
  obtain ⟨X, l, hX, hwX, hlv⟩ := sortOfE_runs hv'
  have hAaE : Setlec.TTVerify.denote m.base.cval env φ d ty'
      = some Aa.erase := denote2_erase m.acval_erase d ty' hAa
  obtain ⟨hwo, hbo, hLo, hCo⟩ :=
    frame_openR (n := n') m.base.cval_closed hwfe.1 hbfe.1 hwfe.2
      hbfe.2 hLty' hLbody' hCty' hCbody' hAaE
  have hCo' : CtxOkR μ m.base.cval env φ (d + 1)
      ((Aa :: Δa).map AVExpr.erase)
      (body'.instantiate1 (.fvar d n' ty')) := by simpa using hCo
  have hcodS := inferSort2 m ihw ihi hX hwX hwo hbo hLo hCo' hBa
  -- the crossing
  obtain ⟨ra, hra, hcross⟩ :=
    (hbeta (Δa := Δa)
      (denote2_fuelMono (Nat.le_succ fuel) d a haa)).1
      (denote2_fuelMono (Nat.le_succ fuel) (d + 1) _ hBa)
  refine ⟨.app fa aa, ra, ?_, hra, ?_⟩
  · rw [denote2, denote2_fuelMono (Nat.le_succ fuel) d f hfa,
      denote2_fuelMono (Nat.le_succ fuel) d a haa]
    rfl
  · intro ρ hρ
    obtain ⟨hokf, hmemf⟩ := hrowf ρ hρ
    obtain ⟨hoka, hmema⟩ := hrowa ρ hρ
    have hf2 : interp2 V ρ fa ∈ˢ interp2 V ρ (.pi u' v' Aa Ba) := by
      rw [← (hredf ρ hρ).1]; exact hmemf
    have ha2 : interp2 V ρ aa ∈ˢ interp2 V ρ Aa := by
      rw [← hdom ρ hρ]; exact hmema
    have hcod0 : v' = 0 → ∀ x, x ∈ˢ interp2 V ρ Aa →
        interp2 V (cons x ρ) Ba ∈ˢ (univZero : V) := by
      intro h0 x hx
      have hmem := (hcodS (cons x ρ) (Sat2_cons V hρ hx)).2
      rw [hlv, h0] at hmem
      exact univ_zero (V := V) ▸ hmem
    have hrow := sound_app V hokf hoka hf2 ha2 hcod0
    exact ⟨hrow.1, by rw [(hcross ρ hρ).1]; exact hrow.2⟩

/-- **`.letE`, modulo the β crossing.**  ζ is annotation-free, so the
clause is an identity once the crossing supplies the *opened* body's
annotation — which is what the second direction of `BetaCross2` is
for: the checker infers the **substituted** body (`infer_let`'s order),
while `denote2`'s `letE` clause is structural and reads the opened one,
so the definedness travels backwards here and forwards in `.app`. -/
theorem infer_letE_claim2 (m : EnvS2 V env)
    (hbeta : BetaCross2 m μ φ (fuel + 1))
    {d : Nat} {n : Name} {ty val b t : Expr} {Δa : List AVExpr}
    (ihi : InferClaims2 μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.letE n ty val b)) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.letE n ty val b)
        = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, sv, tvv, hty, -, hvv, -, hbody⟩ :=
    Setlec.inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLval : Expr.LeavesBounded val := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCval : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) val :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) := fun l hl => by
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hLb l (by simp [Expr.fvarLeaves, h2])
    · exact hLval l h2
  have hCred : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (b.instantiate1 val) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hCval.2 l h2
  obtain ⟨ta, tta, hta, -, hrowT⟩ := ihi hty hws.1 hb.1.1 hLty hCty
  obtain ⟨va, tva, hva, -, hrowV⟩ :=
    ihi hvv hws.2.1 hb.1.2 hLval hCval
  obtain ⟨bva, tbv, hbva, htbv, hrowB⟩ :=
    ihi hbody hwred hbred hLred hCred
  obtain ⟨ba, hba, hcross⟩ :=
    (hbeta (Δa := Δa) (ty := ty) (n := n)
      (denote2_fuelMono (Nat.le_succ fuel) d val hva)).2
      (denote2_fuelMono (Nat.le_succ fuel) d _ hbva)
  refine ⟨.letE ta va ba, tbv, ?_,
    denote2_fuelMono (Nat.le_succ fuel) d t htbv, ?_⟩
  · rw [denote2, denote2_fuelMono (Nat.le_succ fuel) d ty hta,
      denote2_fuelMono (Nat.le_succ fuel) d val hva, hba]
    rfl
  · intro ρ hρ
    obtain ⟨hokv, -⟩ := hrowV ρ hρ
    obtain ⟨hokb, hmemb⟩ := hrowB ρ hρ
    obtain ⟨heq, hok⟩ := hcross ρ hρ
    have hokba : AnnotOk2 V (cons (interp2 V ρ va) ρ) ba :=
      (AnnotOk2_inst0 V hokv).mp (hok hokb)
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_letE]
      exact ⟨(hrowT ρ hρ).1, hokv, hokba⟩
    · rw [interp2_letE, ← interp2_inst0, ← heq]
      exact hmemb

/-! ### I9 (`.proj`)

Undischarged in the `denote` lane too (`Bridge/InferStruct.lean` closes
I6/I7/I8/I10 and stops), and here it is short of two further things.
The returned type is `piResidual` of the projection table's stored
entry, and no invariant relates that expression to `sound_proj_*`'s
semantic `A`/`Bf` — `EnvS2` carries no projection-table field at all.
And `denote2`'s `proj` clause is defined only for `i < 2`, while
`inferBody` accepts any index with a `native` entry, so the claim's
`∃ ea` additionally needs `ProjOkT`'s pair-entry pin read at the field
index. -/

/-- The projection clause. -/
def InferProjStep2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i : Nat} {sn : Name} {pe t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase)
      (.proj sn i pe) →
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.proj sn i pe) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-! ## STOP — `InferClaims2` is refuted at low fuel

**The quarter's second finding, and it is about the sealed statement,
not about a supplier.**  `InferClaims2 μ m φ f` demands that the
checker's *returned type* have a `denote2` **at the claim's own fuel
`f`**.  For the clauses that recurse this is affordable — the run at
`f` paid for the subterms — and for `.sort` and the literals the
returned type is a shape `denote2` handles with no run at all.  Two
clauses are in neither position: `.const` and `.fvar` recurse into
nothing, and both return a type `inferBody` merely *reads* (the stored
declaration; the leaf's annotation).  `denote2` of that type is a knot
computation at `f`, and nothing in the clause bought it.

At `f = 1` the gap is total: `whnf` at fuel `1` runs `whnfCore` at
fuel `0`, which throws, so **no** `whnf` at fuel `1` succeeds, so no
`sortOfE` at fuel `1` does, so `denote2` at fuel `1` is `none` on
every `∀`.  Meanwhile `inferTypeCore μ env 1 d (.const n us)`
succeeds outright.  So for any environment storing a constant whose
instantiated type is a `∀` — every realistic environment —
`InferClaims2 μ m φ 1` **has no witness** — mechanized below as
`inferClaims2_one_refuted`.

Consequences, stated plainly:

* `CheckStep2` is false as sealed: at `fuel = 0` its four hypotheses
  are the vacuous fuel-zero claims (`checkSound2`'s `zero` case
  proves them), and its conclusion contains `InferClaims2 μ m φ 1`;
* so is `InferStep2`, and `inferStep2_of` below is *not* thereby
  vacuous-but-wrong — it is exactly right, and it localises the
  falsity: `ConstType2 m μ φ 1` asks for the impossible `denote2`, so
  `InferInputs2` is where the statement's own defect sits.  A residue
  that turns out to be false is a residue that has done its job;
* `.fvar` is an *independent* second witness — its returned type is
  the leaf's own annotation, so no change to `EnvS2` can repair it.
  The defect is the claim's fuel discipline, not a missing field.

The repair is a junction decision on `Claims2`, and there are two
obvious shapes: quantify the conclusion's `denote2` at *some* fuel
(with `denote2_fuelMono`, `Step2/Fuel.lean`, making the choice
harmless downstream), or condition the claim on the returned type
denoting.  Both are statement changes; neither is a consumer's to
make. -/

/-- No `whnf` succeeds at fuel `1`: the loop's first act is `whnfCore`
at fuel `0`. -/
theorem whnf_one_not_ok {d : Nat} {e t : Expr} :
    whnf μ env 1 d e ≠ .ok t := by
  obtain ⟨k, hk⟩ := Setlec.whnfLoopFuel_succ
  rw [Setlec.whnf_succ]
  show Setlec.whnfBody (Setlec.pureFns μ env 0) env d e ≠ _
  rw [Setlec.whnfBody, hk, Setlec.whnfLoop, Setlec.whnfStep]
  simp only [Bind.bind, Except.bind]
  rw [show (Setlec.pureFns μ env 0).whnfCore d e
      = Setlec.whnfCore μ env 0 d e from rfl, Setlec.whnfCore_zero]
  simp [throw, throwThe, MonadExceptOf.throw]

/-- Hence no sort computation succeeds at fuel `1`. -/
theorem sortOfE_one {d : Nat} {e : Expr} :
    sortOfE μ env φ 1 d e = none := by
  unfold sortOfE
  cases hi : inferTypeCore μ env 1 d e with
  | error err => rfl
  | ok t =>
    simp only [Except.toOption]
    cases hw : whnf μ env 1 d t with
    | error err => rfl
    | ok w => exact absurd hw whnf_one_not_ok

/-- Hence no `∀` has a canonical annotation at fuel `1`. -/
theorem denote2_one_forallE {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {n : Name} {ty body : Expr} {mb : BinderMeta} :
    denote2 μ acval env φ 1 d (.forallE n ty body mb) = none := by
  rw [denote2]
  rcases hta : denote2 μ acval env φ 1 d ty with _ | ta
  · rfl
  rcases hba : denote2 μ acval env φ 1 (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rfl
  rw [sortOfE_one]
  rfl

/-- **The refutation.**  One stored constant with a `∀` type is
enough: the `.const` clause succeeds at fuel `1` and its returned type
cannot be annotated there. -/
theorem inferClaims2_one_refuted {env : Env} (m : EnvS2 V env)
    {n : Name} {us : List Level} {ci : Setlec.ConstantInfo}
    {n' : Name} {ty' body' : Expr} {mb' : BinderMeta}
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpi : ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us = .forallE n' ty' body' mb') :
    ¬ InferClaims2 μ m φ 1 := by
  intro hclaim
  have hrun : inferTypeCore μ env 1 0 (.const n us)
      = .ok (.forallE n' ty' body' mb') := by
    rw [Setlec.inferTypeCore_succ]
    simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
      Except.pure, Bind.bind, Except.bind, hf]
    rw [if_pos hlen, hpi]
  obtain ⟨ea, ta, -, hta, -⟩ := hclaim (Δa := []) hrun
    (by simp [Expr.WScoped]) (by simp [Expr.looseBVarsBounded])
    (by intro l hl; simp [Expr.fvarLeaves] at hl)
    (CtxOkR.nil (by simp [Expr.fvarLeaves]))
  rw [denote2_one_forallE] at hta
  exact nomatch hta

/-! ## The assembly -/

/-- **The quarter's routed inputs**, bundled: the seven residues,
quantified over everything `InferStep2` quantifies over. -/
structure InferInputs2 (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- I2: the context correspondence in the annotated currency -/
  fvar_ctx : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), FvarCtx2 m μ φ fuel
  /-- I3: the stored type's annotation, instantiated and at depth -/
  const_ty : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), ConstType2 m μ φ fuel
  /-- I4: the two numeral head facts -/
  nat_heads : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    NatHeads2 m φ
  /-- I5: the `String`-literal clause -/
  str_lit : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferStrLitStep2 m μ φ fuel
  /-- I7: the codomain-sort run at every λ node (the
  chain-granularity finding) -/
  lam_cod : ∀ {env : Env}, LamCodSort2 μ env
  /-- I8/I10: the β crossing -/
  beta : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), BetaCross2 m μ φ fuel
  /-- I9: the projection clause -/
  proj : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    InferProjStep2 m μ φ fuel

/-- **`InferStep2`, modulo the routed inputs.**  The dispatch is the
`infer_claimsR` one: eleven `Expr` shapes, one line each, because each
one *is* a clause.  Three close outright (`.sort`, `.bvar`,
`.forallE`), five more against a sub-clause residue (`.fvar`,
`.const`, `.lit (.natVal _)`, `.lam`, and `.app`/`.letE` sharing
one), and two are routed whole. -/
theorem inferStep2_of (h : InferInputs2 V μ) : InferStep2 μ V := by
  intro env m φ fuel _ihwc ihw ihd ihi
  intro d e t Δa hrun hws hb hLb hC
  match e, hrun, hws, hb, hLb, hC with
  | .sort u, hrun, _, _, _, _ => exact infer_sort_claim2 m hrun
  | .bvar i, hrun, _, _, _, _ => exact infer_bvar_claim2 m hrun
  | .fvar idx nm ty, hrun, _, _, _, hC =>
    obtain ⟨tya, Aa, hden, hidx, hlink⟩ := h.fvar_ctx m φ (fuel + 1) hC
    exact infer_fvar_claim2 m hidx hrun hden hlink
  | .const nm us, hrun, _, _, _, _ =>
    exact infer_const_claim2 m (h.const_ty m φ (fuel + 1)) hrun
  | .lit (.natVal k), hrun, _, _, _, _ =>
    exact infer_natLit_claim2 m (h.nat_heads m φ) hrun
  | .lit (.strVal s), hrun, _, _, _, _ =>
    exact h.str_lit m φ fuel hrun
  | .forallE nm ty body mb, hrun, hws, hb, hLb, hC =>
    exact infer_forallE_claim2 m ihw ihi hrun hws hb hLb hC
  | .lam nm ty body mb, hrun, hws, hb, hLb, hC =>
    exact infer_lam_claim2 m h.lam_cod ihw ihi hrun hws hb hLb hC
  | .app f a, hrun, hws, hb, hLb, hC =>
    exact infer_app_claim2 m (h.beta m φ (fuel + 1)) ihw ihd ihi hrun
      hws hb hLb hC
  | .letE nm ty val b, hrun, hws, hb, hLb, hC =>
    exact infer_letE_claim2 m (h.beta m φ (fuel + 1)) ihi hrun hws hb
      hLb hC
  | .proj sn i pe, hrun, hws, hb, hLb, hC =>
    exact h.proj m φ fuel hrun hws hb hLb hC

end Setlec.SetR.Interp2
