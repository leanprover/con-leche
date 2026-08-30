import Setlec.SetR.Interp2.Step2.Routed
import Setlec.SetR.Interp2.Step2.Fuel
import Setlec.SetR.Interp2.Claims2B
import Setlec.SetR.Interp2.Claims2C
import Setlec.SetR.Interp2.Claims2D
import Setlec.SetR.Bridge.InferStruct

/-!
# `InferStep2` — the inference quarter, discharged and routed

**Read the second half first.**  Everything down to
`inferClaims2_one_refuted` is against the **refuted** `InferClaims2`
and stays as the tombstone; the live quarter is the seal-6/7 section
at the end of this file (`inferStep2B_of : InferInputs2A V μ →
InferStep2B μ V`), against `Claims2A`'s `InferClaims2A` and
`Claims2B`'s corrected reduction claims.

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

/-- `denote2` at a sort.  (Named `…Q` at seal 7: `Step2/DefEqRun.lean`
carries the same lemma and the two files land in one import closure at
the fold-in.) -/
theorem denote2_sortQ {acval : Name → (Name → Nat) → AVExpr} {f d : Nat}
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
  rw [denote2_sortQ] at hsa
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
  · rw [denote2_sortQ]
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

/-- Hence no sort computation succeeds at fuel `1`.  (Renamed at
seal 7: `Step2/Whnf.lean` found the same lemma independently and this
file now imports it — the duplicate is kept rather than deleted, so
the tombstone below stays self-contained.) -/
theorem sortOfE_at_one {d : Nat} {e : Expr} :
    sortOfE μ env φ 1 d e = none := by
  unfold sortOfE
  cases hi : inferTypeCore μ env 1 d e with
  | error err => rfl
  | ok t =>
    simp only [Except.toOption]
    cases hw : whnf μ env 1 d t with
    | error err => rfl
    | ok w => exact absurd hw whnf_one_not_ok

/-- Hence no `∀` has a canonical annotation at fuel `1`.  (Renamed at
seal 7 for the same reason as `sortOfE_at_one`.) -/
theorem denote2_at_one_forallE {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {n : Name} {ty body : Expr} {mb : BinderMeta} :
    denote2 μ acval env φ 1 d (.forallE n ty body mb) = none := by
  rw [denote2]
  rcases hta : denote2 μ acval env φ 1 d ty with _ | ta
  · rfl
  rcases hba : denote2 μ acval env φ 1 (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rfl
  rw [sortOfE_at_one]
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
  rw [denote2_at_one_forallE] at hta
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

/-! # Seal 6 — the quarter re-pointed onto `Claims2A`

Everything above stays as the tombstone of the sealed shape
(`inferClaims2_one_refuted` included; it does **not** hold of
`InferClaims2A` and is not re-proved there).  What follows is the same
eleven clauses against the amended claim.

**The shape change that does the work is not R3's `F' ≥ F` slack but
its other half: the subject's annotation moved to the *hypothesis*
side.**  A clause no longer has to *produce* `denote2` of its own
node, only to invert one it is handed.  Three consequences, all of
them ledger entries:

* the λ chain-granularity finding **dissolves** — `denote2`'s per-node
  `lamSortE` is now a hypothesis, so a node where the checker skipped
  the #152 run makes the claim vacuous rather than false.
  `LamCodSort2` is retired, and `μ.verified = true` (R4) is *not* what
  retired it;
* `.forallE` needs no induction hypothesis at all: the two `sortOfE`s
  it used to recover from its own runs are stored in the annotation it
  is given;
* and the *cost*: runs read back out of a hypothesis annotation live
  at the caller's fuel `F`, which is unrelated to the induction's
  `fuel`.  `inferSort2` — infer, reduce, read the sort — is therefore
  no longer available at those sites, and its content becomes the
  residue `SortSem2`.  This is R1/R3's price and it is paid once.
-/

/-! ### The corrected reduction claim

`WhnfClaims2A` was refuted in turn (`Interp2/EnvS2Refute.lean`) and
seal 7's `WhnfClaims2B` (`Interp2/Claims2B.lean`) is what this quarter
consumes: the reduct's annotation at some `F' ≥ F`.  The quarter
consumes a reduction claim at **exactly one site** — the `.app`
clause's head — so the correction cost this file one `obtain` pattern
and one extra `denote2_fuelMono`. -/

/-! ### Fuel plumbing

`denote2_fuelMono` is a theorem, so two annotations are always
available at a common fuel; the two lemmas below are its `sortOfE`
twins in the form the clauses read runs back with. -/

/-- The checker's sort computation is fuel-*determined* where it is
defined at all: `sortOfE_fuelMono` in both directions. -/
theorem sortOfE_crossFuel {F G d : Nat} {e : Expr} {a b : Nat}
    (h1 : sortOfE μ env φ F d e = some a)
    (h2 : sortOfE μ env φ G d e = some b) : a = b := by
  have h1' := sortOfE_fuelMono (Nat.le_add_right F G) h1
  have h2' := sortOfE_fuelMono (Nat.le_add_left G F) h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

/-- Ditto for the inference run itself. -/
theorem infer_crossFuel {F G d : Nat} {e : Expr} {a b : Expr}
    (h1 : inferTypeCore μ env F d e = .ok a)
    (h2 : inferTypeCore μ env G d e = .ok b) : a = b := by
  have h1' := (knotFuelMono μ env).1 (Nat.le_add_right F G) h1
  have h2' := (knotFuelMono μ env).1 (Nat.le_add_left G F) h2
  rw [h1'] at h2'
  exact Except.ok.inj h2'

/-- A successful `lamSortE` **is** an inference run plus a `sortOfE`;
this is how the λ clause recovers the #152 codomain fact from the
annotation it is handed rather than from a run it does not have. -/
theorem lamSortE_runs {F d : Nat} {e : Expr} {v : Nat}
    (h : lamSortE μ env φ F d e = some v) :
    ∃ bt, inferTypeCore μ env F d e = .ok bt ∧
      sortOfE μ env φ F d bt = some v := by
  unfold lamSortE at h
  cases hi : inferTypeCore μ env F d e with
  | error err => rw [hi] at h; exact nomatch h
  | ok bt =>
    rw [hi] at h
    simp only [Except.toOption] at h
    exact ⟨bt, rfl, h⟩

/-- The frame conditions of an opened binder, *without* the context —
`frame_openR`'s first three components, which need no correspondence in
either currency. -/
theorem frame_open2 {d : Nat} {n : Name} {ty body : Expr}
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hwb : Expr.WScoped d body)
    (hbb : body.looseBVarsBounded 1 = true)
    (hLty : Expr.LeavesBounded ty)
    (hLbody : Expr.LeavesBounded body) :
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) ∧
      (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
  refine ⟨Expr.WScoped.instantiate1 hwty 0 hwb,
    Setlec.looseBVarsBounded_instantiate1 body 0 hbb, fun l hl => ?_⟩
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
  · exact hLbody l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbty
    · exact hLty l h3

/-! ### The re-pointed residues

Five of the seven sealed inputs survive the re-pointing, three of them
with their fuel re-quantified; two are **retired** (`FvarCtx2`,
`LamCodSort2`); three are **new**, and all three are the price of the
amendment rather than of the checker:

| residue | status at seal 7 |
|---|---|
| `ConstType2A` | `ConstType2` + R3's slack — the refuted slot |
| `BetaCross2A` | `BetaCross2`, one direction only, with slack |
| `NatHeads2` | unchanged (fuel-free already) |
| `InferStrLitStep2A`, `InferProjStep2A` | the two whole clauses |
| `FvarCtx2` | **retired** — `CtxOk2.fvar_leaf` supplies it |
| `LamCodSort2` | **retired** — the per-node run is now a hypothesis |
| `SortSem2` | **new** — `inferSort2` at a fuel off the induction |
| `TypeOk2` | **new** — R2's grading, at the one site that consumes it |
| `CtxOk2R`, `CtxOk2Open` | **new** — the context in two currencies |
-/

/-- **The `const` clause's residue, re-pointed.**  `ConstType2`
verbatim except that the annotation's fuel is the *prover's*: given any
`F`, the stored constant's instantiated type annotates at some
`F' ≥ F`.  This is the exact slot `inferClaims2_one_refuted` shot
through — at `F = 1` the sealed form demanded a `denote2` that provably
does not exist, and here the residue may answer at a larger fuel. -/
def ConstType2A {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (n : Name) (ci : Setlec.ConstantInfo) (us : List Level),
    env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp2 V ρ ta

/-- **The sort fact at an annotation fuel the clause does not
control.**  This is `inferSort2`'s statement with the run's fuel and
the annotation's fuel identified and *free*: infer, reduce to a sort,
conclude the subject lands in that universe.

It is new at seal 7 and it is the amendment's own cost.  Under the
sealed claims a binder clause recovered this from its own runs at
`fuel` through `ihi`/`ihw`; under R1/R3 the numerals a clause must
justify are the ones stored in the annotation it is *handed*, whose
runs happened at the caller's `F` — a fuel the induction has not
reached.  So the content is unchanged and the *fuel* is what routes
it: `SortSem2` is `inferSort2` for all fuels at once, and the top-level
induction (`checkSound2B`) is where it becomes available. -/
def SortSem2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d u : Nat} {e : Expr} {Δa : List AVExpr} {ea : AVExpr},
    CtxOk2 m μ φ F d Δa e →
    sortOfE μ env φ F d e = some u →
    denote2 μ m.acval env φ F d e = some ea →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ (univ u : V)

/-- **What R2's grading costs, isolated.**  `WhnfClaims2B`'s conclusion
is under `AnnotOk2` of the *subject*, and the one site in this quarter
that reduces (`.app`, the head's type) has no such fact: the inference
claim concludes truthfulness of the term it typed, never of the type it
returned.  So the grading premise is a residue, and it is exactly
"an inferred type's annotation is truthful".

Deliberately **not** "an inferred type is itself sorted" — that is
validity, refuted at this very clause (`Setlec/SetR/DESIGN.md`,
findings A3/B5/A5).  Truthfulness is the weaker, hereditary statement
`AnnotOk2` names, and it is all the grading asks for. -/
def TypeOk2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F f d : Nat} {e t : Expr} {Δa : List AVExpr} {ta : AVExpr},
    inferTypeCore μ env f d e = .ok t →
    CtxOk2 m μ φ F d Δa e →
    denote2 μ m.acval env φ F d t = some ta →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta

/-- **The context in the other currency.**  `InferClaims2A` takes
`CtxOk2`; `WhnfClaims2B` and `DefEqClaims2A` still take
`CtxOkR`-on-erasures, and the `.app` clause consumes all three.  So a
clause that threads the context between the quarters needs the bridge,
and it does not exist: `CtxOkR`'s leaf package is
`∃ T', Infer … ∧ DefEq … T' T`, a *derivation*, while `CtxOk2`'s is an
`interp2` equation, and semantic agreement is not `DefEq` (the step-3
map's "no `VExpr → AVExpr`" wall, in the direction seal 3 did not
test).

**This residue is therefore not merely unproved — it is very probably
false**, and it is stated to make that visible rather than to be
discharged.  The honest repair is at the *statement* level: the
claim family should take the context in both currencies (a
`CtxOk2 ∧ CtxOkR` conjunction), or `WhnfClaims2B`/`DefEqClaims2A`
should move to `CtxOk2` as `InferClaims2A` did.  Seal 6 recorded the
asymmetry as evidence; this is the first consumer to *pay* for it, and
the finding is that the asymmetry is not payable.

**Settled: refuted** (`Step2/CtxOk2RRefute.lean`, `not_ctxOk2R` —
`¬ CtxOk2R m μ φ` at *every* `m`, `μ`, `φ`, on the three standard
axioms).  The mechanized reason is cheaper than the relational one
above and does not need it: `CtxOk2` guards its leaf agreement by
`Sat2`, satisfaction in the **annotated** currency, while `CtxOkR` is
a derivation whose only semantic reading is `Sat` in the **collapse**
currency — and the two currencies disagree about inhabitation at an
empty-domain λ (`lamR_pos_empty` gives `∅`, `lamC_empty` gives `pt`;
the #100 countermodel).  At `Δa = [⟪fun (_ : Empty) => Prop⟫]` the
`CtxOk2` hypothesis is free and `CtxOkR` still owes an
`Infer`/`DefEq` pair, which `Infer.sound`/`DefEq.sound` turn into
`ptTag ∈ˢ univ 0`.  `ctxOk2R_refuted_nonvacuous` repeats it with the
`interp2` agreement holding for every `ρ`, so vacuity is not the
whole story: `⟪Empty⟫` and `⟪fun (_ : Empty) => Prop⟫` are equal over
`interp2` and different over `interp`.

The trap-checks do **not** fire here: `CtxOkR` mentions `denote`, not
`denote2`, so the smallest-fuel test has nothing to bite on, and the
refutation is uniform in `F`. -/
def CtxOk2R {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {Δa : List AVExpr} {e : Expr},
    CtxOk2 m μ φ F d Δa e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e

/-- **`CtxOk2.open`** — the one threading move the supplier's kit
(`Step2/Dispatch.lean`) does not have, and the only one that is not a
projection: opening a binder extends the annotated context by the
domain's annotation, which needs the leaf package to survive a depth
increase (`denote_weaken_top`'s `denote2` twin, which does not exist).
Named here at the granularity `CtxOkR.open` has, so that it can be
moved to the supplier verbatim. -/
def CtxOk2Open {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {Δa : List AVExpr} {n : Name} {ty body : Expr}
    {ta : AVExpr},
    CtxOk2 m μ φ F d Δa ty → CtxOk2 m μ φ F d Δa body →
    denote2 μ m.acval env φ F d ty = some ta →
    Expr.fvarsBelow d ty →
    CtxOk2 m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty))

/-- **The β crossing, re-pointed.**  `BetaCross2` with R3's slack and
**one direction only**: the sealed statement needed the backward
direction for `.letE` (whose `denote2` the clause had to *produce*),
and R1 removed that obligation — the `letE`'s annotation is now a
hypothesis and the crossing is used forwards at both sites. -/
def BetaCross2A {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {n : Name} {ty b a : Expr} {Δa : List AVExpr}
    {aa ba : AVExpr},
    denote2 μ m.acval env φ F d a = some aa →
    denote2 μ m.acval env φ F (d + 1)
      (b.instantiate1 (.fvar d n ty)) = some ba →
    ∃ F' ra, F ≤ F' ∧
      denote2 μ m.acval env φ F' d (b.instantiate1 a) = some ra ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ra = interp2 V ρ (ba.inst aa) ∧
        (AnnotOk2 V ρ ra → AnnotOk2 V ρ (ba.inst aa))

/-- The `String`-literal clause, re-pointed. -/
def InferStrLitStep2A {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d F : Nat} {s : String} {t : Expr} {Δa : List AVExpr}
    {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t →
    denote2 μ m.acval env φ F d (.lit (.strVal s)) = some ea →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The projection clause, re-pointed. -/
def InferProjStep2A {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i F : Nat} {sn : Name} {pe t : Expr} {Δa : List AVExpr}
    {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOk2 m μ φ F d Δa (.proj sn i pe) →
    denote2 μ m.acval env φ F d (.proj sn i pe) = some ea →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-! ### The two constant-shaped clauses -/

/-- **`.const`, amended — and this is R3's whole point.**  The clause
is the sealed one with the residue answering at its own fuel: the
subject's annotation is the valuation's leaf (`denote2`'s `const`
equation, now a hypothesis), truthfulness is `acval_ok2`, and the
returned type's annotation is `ConstType2A`'s `F'`. -/
theorem infer_const_claim2A (m : EnvS2 V env) (hct : ConstType2A m μ φ)
    {d F : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AVExpr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.const n us) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
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
      rw [denote2, hf] at hea
      dsimp only at hea
      rw [if_pos hlen] at hea
      obtain rfl : ea = m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us) :=
        (Option.some.inj hea).symm
      obtain ⟨F', ta, hle, hta, hmem⟩ := hct F d n ci us hf hlen
      exact ⟨F', ta, hle, hta, fun ρ _ => ⟨m.acval_ok2 n _ ρ, hmem ρ⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.lit (.natVal k)`, amended.**  The numeral induction is
`natLit_facts2` and the head facts are `NatHeads2`, both unchanged;
`F' = F` because the returned `.const natName []` denotes without a
run (the support guard pins the stored level parameters empty). -/
theorem infer_natLit_claim2A (m : EnvS2 V env) (hnh : NatHeads2 m φ)
    {d k F : Nat} {t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.lit (.natVal k)) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
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
    rw [denote2, if_pos hgt] at hea
    obtain rfl : ea = natLitT2
        (m.acval natZeroName (Level.substFn φ [] []))
        (m.acval natSuccName (Level.substFn φ [] [])) k :=
      (Option.some.inj hea).symm
    cases hf : env.find? natName with
    | none =>
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        natName_levelParams_nil hgt hf
      refine ⟨F, m.acval natName (Level.substFn φ [] []),
        Nat.le_refl F, ?_, ?_⟩
      · rw [denote2, hf]
        dsimp only
        rw [if_pos (by simp [hlp]), hlp]
      · intro ρ _
        exact natLit_facts2 (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ)
          (hnh hgt ρ).1 (hnh hgt ρ).2 k
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### `.forallE` — the clause the amendment made *free*

Under the sealed claim this clause had to exhibit `denote2` of its own
`∀`, which meant producing both `sortOfE`s; it got them from its own
runs through `inferSort2`, i.e. through two induction hypotheses.
Under R1 the annotation is handed over, so the two `sortOfE`s are
*hypotheses*, and the clause consumes **no induction hypothesis at
all** — only the semantic reading of the two numerals it is given.
`F' = F`: the returned type is a sort. -/

theorem infer_forallE_claim2A (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) {d F : Nat} {n : Name}
    {ty body t : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hC : CtxOk2 m μ φ F d Δa (.forallE n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.forallE n ty body mb)
      = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, vv, hty, hwu, hbt, hens, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  simp only [Expr.WScoped] at hws
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hu : sortOfE μ env φ F d ty with _ | u0
  · rw [hu] at hea; exact nomatch hea
  rw [hu] at hea
  rcases hv : sortOfE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .pi u0 v0 ta ba := (Option.some.inj hea).symm
  obtain rfl : u0 = u.eval φ :=
    sortOfE_crossFuel hu (sortOfE_of_run hty hwu)
  obtain rfl : v0 = vv.eval φ :=
    sortOfE_crossFuel hv
      (sortOfE_of_run hbt (Setlec.ensureSortCore_inv hens))
  refine ⟨F, .sort (Setlec.TT.imax (u.eval φ) (vv.eval φ)),
    Nat.le_refl F, by rw [denote2_sortQ]; rfl, ?_⟩
  intro ρ hρ
  have hCop := hop (n := n) hC.forallE_ty hC.forallE_body hta
    hws.1.fvarsBelow
  have hdom := hss hC.forallE_ty hu hta ρ hρ
  have hcod : ∀ x, x ∈ˢ interp2 V ρ ta →
      AnnotOk2 V (cons x ρ) ba ∧
        interp2 V (cons x ρ) ba ∈ˢ (univ (vv.eval φ) : V) :=
    fun x hx => hss hCop hv hba (cons x ρ) (Sat2_cons V hρ hx)
  exact sound_pi V hdom.1 (fun x hx => (hcod x hx).1) hdom.2
    (fun x hx => (hcod x hx).2)

/-! ### `.lam` — the chain-granularity finding, dissolved

The sealed clause was short of `LamCodSort2`: `denote2` asks for the
#152 codomain-sort run at **every** λ node and `inferBody` makes it at
one node per chain, so the clause could not *produce* its own
annotation.  Under R1 it does not have to.  The `lamSortE` is a
hypothesis, and `lamSortE_runs` reads the inference run and the
`sortOfE` back out of it — which is exactly the pair `LamCodSort2`
was invented to supply.  The residue is **retired**, and the regime
split it recorded (`.noModel` vs verified) is answered too: at a mode
or a node where the checker skips the run, `denote2` returns `none`
and the claim is vacuous there.

Worth stating plainly because seal 6 attributed this repair to R4:
**`μ.verified = true` is not what fixed the λ clause.**  It was
consumed here only to pass on to the induction hypothesis, and the R4
spike therefore deleted it from the claims and from this signature.
`lamSortE` is `denote2`'s **own** `inferTypeCore`/`sortOfE` pair, not
a readback of the checker's #152 run, so the clause never depended on
the mode having made that check. -/

theorem infer_lam_claim2A (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) {d F : Nat} {n : Name}
    {ty body t : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    {ea : AVExpr} (ihi : InferClaims2A μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOk2 m μ φ F d Δa (.lam n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.lam n ty body mb) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, -, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's annotation, inverted
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hv : lamSortE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .lam v0 ta ba := (Option.some.inj hea).symm
  -- the run the sealed clause was missing, read out of the annotation
  have hsv : sortOfE μ env φ F (d + 1) bt = some v0 := by
    obtain ⟨bt0, hbt0, hs0⟩ := lamSortE_runs hv
    rwa [infer_crossFuel hbt0 hbt] at hs0
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hCop := hop (n := n) hC.lam_ty hC.lam_body hta hws.1.fvarsBelow
  obtain ⟨F1, tbt, hle1, htbt, hrow⟩ :=
    ihi hbt hwopen hbopen hLopen hCop hba
  -- the abstraction round trip, verbatim from the sealed clause
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
  -- the common fuel: the body's, raised past the clause's own runs
  have hF1 : F1 ≤ F1 + fuel := Nat.le_add_right F1 fuel
  have hFF : F ≤ F1 + fuel := Nat.le_trans hle1 hF1
  have hfl : fuel ≤ F1 + fuel := Nat.le_add_left fuel F1
  refine ⟨F1 + fuel, .pi (u.eval φ) v0 ta tbt, hFF, ?_, ?_⟩
  · rw [denote2, denote2_fuelMono hFF d ty hta, hround,
      denote2_fuelMono hF1 (d + 1) bt htbt,
      sortOfE_fuelMono (φ := φ) hfl (sortOfE_of_run hty hwu),
      sortOfE_fuelMono (φ := φ) hFF hsv]
    rfl
  · intro ρ hρ
    have hdomS := hss (Δa := Δa)
      (CtxOk2.fuelMono (Nat.le_add_right F fuel) hC.lam_ty)
      (sortOfE_fuelMono (φ := φ) (Nat.le_add_left fuel F)
        (sortOfE_of_run hty hwu))
      (denote2_fuelMono (Nat.le_add_right F fuel) d ty hta) ρ hρ
    have hCbt : CtxOk2 m μ φ (F1 + fuel) (d + 1) (ta :: Δa) bt :=
      (CtxOk2.fuelMono hFF hCop).of_subset
        (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen)
    have hcodS : ∀ x, x ∈ˢ interp2 V ρ ta →
        interp2 V (cons x ρ) tbt ∈ˢ (univ v0 : V) :=
      fun x hx => (hss hCbt (sortOfE_fuelMono (φ := φ) hFF hsv)
        (denote2_fuelMono hF1 (d + 1) bt htbt) (cons x ρ)
        (Sat2_cons V hρ hx)).2
    refine sound_lam V hdomS.1 (fun x hx => ?_) (fun x hx => ?_)
      (fun h0 x hx => ?_)
    · exact (hrow (cons x ρ) (Sat2_cons V hρ hx)).1
    · exact (hrow (cons x ρ) (Sat2_cons V hρ hx)).2
    · exact univ_zero (V := V) ▸ h0 ▸ hcodS x hx

/-! ### `.letE` — the β crossing, now needed in one direction only

The sealed clause used `BetaCross2` **backwards** (substituted ⟶
opened), because it had to exhibit the `letE`'s own annotation and
`denote2`'s `letE` clause is structural in the *opened* body while the
checker infers the *substituted* one.  R1 hands the annotation over,
so the opened body's `ba` is a hypothesis and the crossing is used
forwards, as in `.app`.  One direction of the residue is therefore
dead. -/

theorem infer_letE_claim2A (m : EnvS2 V env)
    (hbeta : BetaCross2A m μ φ) {d F : Nat} {n : Name}
    {ty val b t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihi : InferClaims2A μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOk2 m μ φ F d Δa (.letE n ty val b))
    (hea : denote2 μ m.acval env φ F d (.letE n ty val b) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
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
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) := fun l hl => by
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hLb l (by simp [Expr.fvarLeaves, h2])
    · exact hLval l h2
  have hCred : CtxOk2 m μ φ F d Δa (b.instantiate1 val) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hC.letE_body.2 l h2
    · exact hC.letE_val.2 l h2
  -- the subject's annotation, inverted
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d val with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (b.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  -- the three sub-inferences
  obtain ⟨Ft, tta, -, -, hrowT⟩ :=
    ihi hty hws.1 hb.1.1 hLty hC.letE_ty hta
  obtain ⟨Fv, tva, -, -, hrowV⟩ :=
    ihi hvv hws.2.1 hb.1.2 hLval hC.letE_val hva
  obtain ⟨F2, ra, hle2, hra, hcross⟩ := hbeta (Δa := Δa) hva hba
  obtain ⟨F3, tbv, hle3, htbv, hrowB⟩ :=
    ihi hbody hwred hbred hLred
      (CtxOk2.fuelMono hle2 hCred) hra
  refine ⟨F3, tbv, Nat.le_trans hle2 hle3, htbv, ?_⟩
  intro ρ hρ
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

/-! ### `.app` — the one site that consumes a reduction claim

Three things this clause, and only this clause, pays for.

* **R2's grading.**  `WhnfClaims2B` concludes under `AnnotOk2` of its
  *subject*, and the subject here is the head's **inferred type**.  The
  inference claim concludes truthfulness of the term it typed, never of
  the type it returned, so the premise is not in hand and `TypeOk2` is
  the residue.  (Answering the junction's question directly: **no**, the
  grading is not free at this site, and it is free at every other site
  in the quarter only because no other clause reduces.)
* **The two currencies.**  `ihd` and `ihw` take `CtxOkR`-on-erasures
  while the claim supplies `CtxOk2`; `CtxOk2R` is the bridge and it is
  the residue this quarter believes to be *false* (see its docstring).
* **The kind-`0` fibre**, which `inferBody`'s app branch never
  computes.  The sealed clause recovered it with `sortOfE_runs` and
  `inferSort2` — a run at `fuel`, inside the induction.  Under R1 the
  ∀'s annotation was produced at a fuel the reduction claim chose, so
  the runs inside it are off the induction and `SortSem2` is what reads
  them. -/

theorem infer_app_claim2A (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) (hcr : CtxOk2R m μ φ)
    (htok : TypeOk2 m μ φ) (hbeta : BetaCross2A m μ φ)
    {d F : Nat} {f a t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihw : WhnfClaims2B μ m φ fuel)
    (ihd : DefEqClaims2B μ m φ fuel) (ihi : InferClaims2A μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk2 m μ φ F d Δa (.app f a))
    (hea : denote2 μ m.acval env φ F d (.app f a) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
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
  -- the subject's annotation, inverted
  rw [denote2] at hea
  rcases hfa : denote2 μ m.acval env φ F d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote2 μ m.acval env φ F d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- the head, and its type reduced to the `∀`
  obtain ⟨F1, tfa, hle1, htfa, hrowf⟩ :=
    ihi htf hws.1 hb.1 hLf hC.app_fn hfa
  obtain ⟨htfw, htfb, htfL, htfC⟩ :=
    frame_inferR m.base.wf htf hws.1 hb.1 hLf (hcr hC.app_fn)
  obtain ⟨G, pa, hleG, hpa, hredf⟩ :=
    ihw hwf htfw htfb htfL htfC htfa
  have hle1G : F ≤ G := Nat.le_trans hle1 hleG
  -- the `∀`'s frame conditions
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
  have hCty' : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty' :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
  -- the `∀`'s annotation, decomposed into the four things `denote2`
  -- put in it
  rw [denote2] at hpa
  rcases hAa : denote2 μ m.acval env φ G d ty' with _ | Aa
  · rw [hAa] at hpa; exact nomatch hpa
  rw [hAa] at hpa
  rcases hBa : denote2 μ m.acval env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | Ba
  · rw [hBa] at hpa; exact nomatch hpa
  rw [hBa] at hpa
  rcases hu' : sortOfE μ env φ G d ty' with _ | u'
  · rw [hu'] at hpa; exact nomatch hpa
  rw [hu'] at hpa
  rcases hv' : sortOfE μ env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | v'
  · rw [hv'] at hpa; exact nomatch hpa
  rw [hv'] at hpa
  obtain rfl : pa = .pi u' v' Aa Ba := (Option.some.inj hpa).symm
  -- the argument, and its certificate against the domain
  obtain ⟨F2, taa, hle2, htaa, hrowa⟩ :=
    ihi hta hws.2 hb.2 hLa hC.app_arg haa
  obtain ⟨htaw, htab, htaL, htaC⟩ :=
    frame_inferR m.base.wf hta hws.2 hb.2 hLa (hcr hC.app_arg)
  -- STOP 3: the defeq claim is graded, so its two `AnnotOk2`
  -- premises are paid here.  This is `app_defeq_premises2A` below,
  -- inlined only because it is stated after this clause: the
  -- argument type's from `TypeOk2`, the domain's free from R2's own
  -- grading via `AnnotOk2_pi`.  Cost to this quarter: nothing new.
  have hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ taa = interp2 V ρ Aa := by
    intro ρ hρ
    have htfaOk : AnnotOk2 V ρ tfa :=
      htok htf (CtxOk2.fuelMono hle1 hC.app_fn) htfa ρ hρ
    have hpiOk : AnnotOk2 V ρ (.pi u' v' Aa Ba) :=
      (hredf ρ hρ htfaOk).2
    have hokta : AnnotOk2 V ρ taa :=
      htok hta (CtxOk2.fuelMono hle2 hC.app_arg) htaa ρ hρ
    have hokA : AnnotOk2 V ρ Aa := by
      rw [AnnotOk2_pi] at hpiOk; exact hpiOk.1
    exact ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC hCty'
      (denote2_fuelMono (Nat.le_add_right F2 G) d tya htaa)
      (denote2_fuelMono (Nat.le_add_left G F2) d ty' hAa) ρ hρ
      hokta hokA
  -- the annotated context, carried up to the `∀`'s own fuel
  have hCf : CtxOk2 m μ φ G d Δa f := CtxOk2.fuelMono hle1G hC.app_fn
  have hCpi : CtxOk2 m μ φ G d Δa (.forallE n' ty' body' mb') :=
    (hCf.of_subset
      (inferTypeCore_fvarLeaves m.base.wf fuel htf hws.1)).of_subset
      (whnf_fvarLeaves m.base.wf fuel hwf)
  have hCop := hop (n := n') hCpi.forallE_ty hCpi.forallE_body hAa
    hwfe.1.fvarsBelow
  -- the crossing, at the `∀`'s fuel
  obtain ⟨F3, ra, hle3, hra, hcross⟩ :=
    hbeta (Δa := Δa) (denote2_fuelMono hle1G d a haa) hBa
  refine ⟨F3, ra, Nat.le_trans hle1G hle3, hra, ?_⟩
  intro ρ hρ
  obtain ⟨hokf, hmemf⟩ := hrowf ρ hρ
  obtain ⟨hoka, hmema⟩ := hrowa ρ hρ
  have hoktf : AnnotOk2 V ρ tfa :=
    htok htf (CtxOk2.fuelMono hle1 hC.app_fn) htfa ρ hρ
  have hf2 : interp2 V ρ fa ∈ˢ interp2 V ρ (.pi u' v' Aa Ba) := by
    rw [← (hredf ρ hρ hoktf).1]; exact hmemf
  have ha2 : interp2 V ρ aa ∈ˢ interp2 V ρ Aa := by
    rw [← hdom ρ hρ]; exact hmema
  have hcod0 : v' = 0 → ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro h0 x hx
    have hmem := (hss hCop hv' hBa (cons x ρ) (Sat2_cons V hρ hx)).2
    rw [h0] at hmem
    exact univ_zero (V := V) ▸ hmem
  have hrow := sound_app V hokf hoka hf2 ha2 hcod0
  exact ⟨hrow.1, by rw [(hcross ρ hρ).1]; exact hrow.2⟩

/-! ### The assembly

`InferInputs2` had seven fields.  Two are gone (`fvar_ctx`,
`lam_cod` — both *retired*, not merely renamed: the `.fvar` clause now
reads the claim's own `CtxOk2`, and the λ clause reads its own
hypothesis annotation), three are re-pointed (`const_ty`, `beta`,
`proj`), two are unchanged (`nat_heads`, `str_lit`), and **four are
new**, all four charged to the amendment rather than to the checker:
`sort_sem` and `type_ok` to R1/R3's decoupling of the annotation fuel
from the run's, `ctx_R` and `ctx_open` to the context hypothesis being
`CtxOk2` in one claim and `CtxOkR` in two others.
-/

/-- **The quarter's routed inputs**, re-pointed. -/
structure InferInputs2A (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- I3: the stored type's annotation, at a fuel of its own choosing
  (R3's slot — the sealed `const_ty` is refuted at `fuel = 1`) -/
  const_ty : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    ConstType2A m μ φ
  /-- I4: the two numeral head facts (unchanged) -/
  nat_heads : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    NatHeads2 m φ
  /-- I5: the `String`-literal clause -/
  str_lit : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferStrLitStep2A m μ φ fuel
  /-- I8/I10: the β crossing, forwards only -/
  beta : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    BetaCross2A m μ φ
  /-- I9: the projection clause -/
  proj : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStep2A m μ φ fuel
  /-- **new**: the sort fact at an annotation fuel off the induction -/
  sort_sem : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    SortSem2 m μ φ
  /-- **new**: R2's grading premise at the one site that reduces -/
  type_ok : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    TypeOk2 m μ φ
  /-- **new, and believed false**: the context in the other currency -/
  ctx_R : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    CtxOk2R m μ φ
  /-- **new**: `CtxOkR.open`'s missing twin -/
  ctx_open : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    CtxOk2Open m μ φ

/-- **`InferStep2B`, modulo the routed inputs.**  The dispatch is
unchanged in shape — eleven `Expr` shapes, one line each — with the
subject's annotation threaded alongside the run and the context.

Four clauses close with **no residue of their own**: `.sort`, `.bvar`,
`.fvar` (the seal-3 STOP, discharged by `CtxOk2`) and `.forallE`
(which now needs no induction hypothesis either). -/
theorem inferStep2B_of (h : InferInputs2A V μ) : InferStep2B μ V := by
  intro env m φ fuel _ihwc ihw ihd ihi
  intro d e t Δa hrun hws hb hLb F ea hC hea
  match e, hrun, hws, hb, hLb, hC, hea with
  | .sort u, hrun, _, _, _, _, hea => exact infer_sort_claim2A hrun hea
  | .bvar i, hrun, _, _, _, _, hea => exact infer_bvar_claim2A hrun hea
  | .fvar idx nm ty, hrun, _, _, _, hC, hea =>
    exact infer_fvar_claim2A hC hrun hea
  | .const nm us, hrun, _, _, _, _, hea =>
    exact infer_const_claim2A m (h.const_ty m φ) hrun hea
  | .lit (.natVal k), hrun, _, _, _, _, hea =>
    exact infer_natLit_claim2A m (h.nat_heads m φ) hrun hea
  | .lit (.strVal s), hrun, _, _, _, _, hea =>
    exact h.str_lit m φ fuel hrun hea
  | .forallE nm ty body mb, hrun, hws, _, _, hC, hea =>
    exact infer_forallE_claim2A m (h.sort_sem m φ) (h.ctx_open m φ)
      hrun hws hC hea
  | .lam nm ty body mb, hrun, hws, hb, hLb, hC, hea =>
    exact infer_lam_claim2A m (h.sort_sem m φ) (h.ctx_open m φ) ihi
      hrun hws hb hLb hC hea
  | .app f a, hrun, hws, hb, hLb, hC, hea =>
    exact infer_app_claim2A m (h.sort_sem m φ) (h.ctx_open m φ)
      (h.ctx_R m φ) (h.type_ok m φ) (h.beta m φ) ihw ihd ihi hrun
      hws hb hLb hC hea
  | .letE nm ty val b, hrun, hws, hb, hLb, hC, hea =>
    exact infer_letE_claim2A m (h.beta m φ) ihi hrun hws hb hLb hC
      hea
  | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
    exact h.proj m φ fuel hrun hws hb hLb hC hea

/-! ### The defeq quarter's premises, answered at the site

`DefEqClaims2A` left ungraded turned out to be unprovable in its own
quarter (its first move is a `whnfCore`, whose claim is graded), and
the repair `DefEqClaims2AP` takes the two subjects' `AnnotOk2` as
premises.  The question back to this quarter was whether its one
consuming site can pay.

**It can, and it costs nothing new.**  The `.app` clause compares the
argument's inferred type with the ∀'s domain, and:

* `AnnotOk2` of the **domain** is *free from R2 itself* — the graded
  reduction claim hands back `AnnotOk2` of the reduct, the reduct's
  annotation is the `∀`'s `.pi`, and `AnnotOk2_pi` splits it;
* `AnnotOk2` of the **argument's inferred type** is `TypeOk2`, which
  this clause already had to assume for R2's *other* premise, at the
  same site, about the same kind of object.

So the defeq repair adds **no residue** to this quarter.  Checked
rather than argued: -/

theorem app_defeq_premises2A (m : EnvS2 V env) (htok : TypeOk2 m μ φ)
    {F f d u' v' : Nat} {a tya : Expr} {Δa : List AVExpr}
    {taa Aa Ba : AVExpr} {ρ : Nat → V}
    (hrun : inferTypeCore μ env f d a = .ok tya)
    (hCa : CtxOk2 m μ φ F d Δa a)
    (htaa : denote2 μ m.acval env φ F d tya = some taa)
    (hpi : AnnotOk2 V ρ (.pi u' v' Aa Ba))
    (hρ : Sat2 V Δa ρ) :
    AnnotOk2 V ρ taa ∧ AnnotOk2 V ρ Aa := by
  refine ⟨htok hrun hCa htaa ρ hρ, ?_⟩
  rw [AnnotOk2_pi] at hpi
  exact hpi.1

/-! ### And the question back: should `InferClaims2A` conclude
`AnnotOk2` of the returned type?

It would retire `TypeOk2` outright, and this quarter's clause-by-clause
assessment is that it is **provable but not free** — three of the
eleven clauses would have to be paid for, and all three payments are in
residues this file already owns:

* `.sort`, `.forallE` (a sort), `.lit (.natVal _)` (an `acval` leaf,
  `acval_ok2`), `.bvar`, `.lit (.strVal _)` and `.proj` (routed): free
  or already carried;
* `.lam` and `.letE`: **free by induction** — their returned types'
  annotations are the body's, which the extended claim would supply
  from the IH.  `.lam` additionally needs `AnnotOk2` of the domain,
  which `SortSem2` already gives it;
* `.fvar`: **not free.**  The returned type is the leaf's own
  annotation and `CtxOk2`'s leaf package carries definedness and an
  `interp2` equation but no truthfulness.  `CtxOk2` would need an
  `AnnotOk2` component — a change in the *supplier's* file;
* `.const`: not free, but cheap — `ConstType2A` would carry the
  conjunct;
* `.app`: not free — the returned type is the crossed annotation `ra`,
  and `BetaCross2A` currently transports truthfulness only in the
  direction `ra ⟶ Ba.inst aa`.  It would need the converse back (the
  sealed `BetaCross2` had both).

**No STOP**: nothing here is refuted, and the trade is one residue
(`TypeOk2`) against one supplier change and two residue conjuncts.
This quarter's recommendation is to make it, because `TypeOk2` is the
*weakest-motivated* of the four new residues — it is assumed about
every inferred type at every fuel, whereas the three payments above are
each local to one clause. -/

/-! # Seal 14 — generation four: the returned type's grading

`InferClaims2C` (`Interp2/Claims2C.lean`) is the first generation in
this arc that **extends** the inference claim rather than only
re-quantifying it: beside the subject's `AnnotOk2` it now delivers the
**returned type's**, ρ-uniformly.  That is seal 8's open question,
answered from two consuming sites (`infer_app_claim2A`,
`betaCert2P_of_claims`).

Everything above stays as the `…A`/`…B` tombstones.  What follows is
the same eleven clauses once more, against the hoisted claims.

## The ledger of the extension, clause by clause

The "question back" note at the end of the `…B` lane predicted eight
free clauses and three payments.  **It was right about all three, and
about all three prices** — including the one that is *not* a residue
of this quarter: it said, correctly, that `.fvar` would need "an
`AnnotOk2` component — a change in the *supplier's* file".

| clause | the returned type's `AnnotOk2` |
|---|---|
| `.sort`, `.forallE` | a sort: `True` |
| `.bvar` | vacuous |
| `.lit (.natVal _)` | an `acval` leaf: `acval_ok2` |
| `.lam` | `AnnotOk2_pi` of `SortSem2`'s domain fact and the IH |
| `.letE` | the IH's own new conjunct, verbatim |
| `.lit (.strVal _)`, `.proj` | routed; the residue carries it |
| `.const` | **paid**: one conjunct in `ConstType2C` |
| `.app` | **paid**: `BetaCross2C` transports truthfulness both ways |
| `.fvar` | **paid, and not by a residue of this quarter** — below |

## What the extension buys, which is more than it costs

`TypeOk2` is **retired**, and `InferInputs2C` sheds the field.  It was
assumed about *every* inferred type at *every* fuel; the `.app` clause
consumed it three times — twice to grade the reduction claim, once to
grade the defeq claim — and all three uses are now the induction
hypothesis's own new conjunct, at the same annotation and the same
fuel.  Together with the hoist, both graded consumers are fed
**ρ-uniformly**, which is precisely what a ρ-local claim could not do.

## FINDING — `.fvar`'s payment is a `CtxOk2` component, not a residue

The `.fvar` clause returns the leaf's **own** annotation `tya`, and
`CtxOk2`'s leaf package carries three things — definedness of `tya`,
the context index, and an `interp2` equation — and **no
truthfulness**.  Nothing in the clause recovers it:

* `Sat2` supplies *inhabitation* of each context entry, never
  `AnnotOk2` of it — the same gap `CtxOk2.openCong`'s consumer note
  records one binder up;
* the leaf's link is an equation between *interpretations*, and
  `AnnotOk2` is not an `interp2` invariant — the #100 currency lesson,
  mechanized as `ctxOk2R_refuted_nonvacuous`;
* the clause performs no run on `ty`, so no induction hypothesis
  applies to it.

So the honest repair is a **fourth component of `CtxOk2`'s leaf
package**, in the supplier's file (`Step2/Dispatch.lean`).  It
self-propagates exactly as the hoist does: at `CtxOk2.open`/`openS`/
`openCong` the new head leaf's annotation is `ta.liftN 1 0`, whose
`AnnotOk2` is `AnnotOk2_liftN` of the *domain's* ρ-uniform `AnnotOk2`
— which is exactly what generation four makes available at every
binder site.  Until that change lands the fact is routed here as
`CtxAnn2`, stated at the granularity the component would have so that
it can be moved verbatim (the `CtxOk2Open` precedent, which became
`CtxOk2.openS` unchanged).
-/

/-- **The `.fvar` clause's payment** — `CtxOk2`'s missing fourth leaf
component, routed.  A leaf's annotation is truthful at every valuation
satisfying the context.

Stated over `CtxOk2` rather than as a standalone fact on purpose: an
unconditional "every `denote2` is truthful" is *false* (`denote2`
performs no membership check at an `app` node), and the conditional
form is what a strengthened `CtxOk2` would hand its reader.

**The trap-checks, and what they do and do not say.**  The
smallest-fuel test has nothing to bite on: the statement is uniform in
`F` and asserts no `denote2` success its consumer does not hand it —
the same clean-but-uninformative result seal 11 recorded for
`CtxOk2R`, and the same warning applies.  Non-vacuity *is* checked
(`ctxAnn2_nonvacuous` below): the hypothesis package is jointly
satisfiable at `d = 1` with a satisfiable `Sat2`.

**Refutation attempted, and it does not go through parametrically** —
recorded because the attempt is informative.  A witness needs a leaf
annotation whose `AnnotOk2` fails while its interpretation is
*inhabited* (else `Sat2` dies and the instance is vacuous, the honest
half of seal 11's `⟪Empty⟫` discipline).  The `AnnotOk2` failures
`denote2` can actually produce are at `app` and `proj` nodes — a λ
node's fibre is free at positive kind (`unitSet`) and its kind is the
checker's own `lamSortE`, never a chosen `0` — and there the
interpretation is `SetTheory.app`/`sfst` of junk, which the `SetTheory`
interface constrains **in neither direction**.  So the residue is
parametrically neither provable nor refutable; it is a genuine
statement about the *supplier*, which is the finding above. -/
def CtxAnn2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d idx : Nat} {n : Name} {ty : Expr} {Δa : List AVExpr}
    {tya : AVExpr},
    CtxOk2 m μ φ F d Δa (.fvar idx n ty) →
    denote2 μ m.acval env φ F d ty = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya

/-- **`CtxAnn2` is not vacuous.**  Its three hypotheses are jointly
satisfiable at a depth where the `.fvar` clause actually fires, with a
`Sat2` that *has* a witness — so the residue is a real obligation and
not a `Sat2`-unsatisfiability artifact. -/
theorem ctxAnn2_nonvacuous {env : Env} (m : EnvS2 V env)
    (μ : CheckMode) (φ : Name → Nat) (F : Nat) (nm : Name) :
    CtxOk2 m μ φ F 1 [AVExpr.sort 0]
        (.fvar 0 nm (.sort .zero)) ∧
      denote2 μ m.acval env φ F 1 (.sort .zero)
        = some (AVExpr.sort 0) ∧
      Sat2 V [AVExpr.sort 0] (fun _ => empty) := by
  refine ⟨⟨rfl, fun l hl => ?_⟩, by rw [denote2]; rfl, ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_singleton] at hl
    subst hl
    exact ⟨by omega, trivial, .sort 0, .sort 0,
      by rw [denote2]; rfl, rfl, fun _ _ => rfl⟩
  · intro i Aa hi
    cases i with
    | zero =>
      obtain rfl : AVExpr.sort 0 = Aa := by simpa using hi
      simpa using empty_mem_univ (V := V) 0
    | succ i => simp at hi

/-- **The `const` clause's residue, extended.**  `ConstType2A` plus
the returned type's truthfulness, in the same unguarded `∀ ρ` shape as
its membership conjunct — the stored type's annotation is closed, so
no context enters. -/
def ConstType2C {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (n : Name) (ci : Setlec.ConstantInfo) (us : List Level),
    env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp2 V ρ ta

/-- **The β crossing, extended.**  `BetaCross2A` with its truthfulness
transport turned into a biconditional.  `.letE` uses it forwards (the
substituted annotation is the *subject*, the descended one is what
`sound_letE` reads); `.app` uses it backwards (the substituted
annotation is the *returned type*, and its truthfulness is now owed).
The sealed `BetaCross2` already had both directions, in the shape of
two separate implications; this is the same content on one crossing. -/
def BetaCross2C {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {n : Name} {ty b a : Expr} {Δa : List AVExpr}
    {aa ba : AVExpr},
    denote2 μ m.acval env φ F d a = some aa →
    denote2 μ m.acval env φ F (d + 1)
      (b.instantiate1 (.fvar d n ty)) = some ba →
    ∃ F' ra, F ≤ F' ∧
      denote2 μ m.acval env φ F' d (b.instantiate1 a) = some ra ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ra = interp2 V ρ (ba.inst aa) ∧
        (AnnotOk2 V ρ ra ↔ AnnotOk2 V ρ (ba.inst aa))

/-- The `String`-literal clause, extended. -/
def InferStrLitStep2C {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d F : Nat} {s : String} {t : Expr} {Δa : List AVExpr}
    {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t →
    denote2 μ m.acval env φ F d (.lit (.strVal s)) = some ea →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The projection clause, extended. -/
def InferProjStep2C {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i F : Nat} {sn : Name} {pe t : Expr} {Δa : List AVExpr}
    {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOk2 m μ φ F d Δa (.proj sn i pe) →
    denote2 μ m.acval env φ F d (.proj sn i pe) = some ea →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-! ### The three leaf clauses -/

/-- **`.sort`, extended.**  The returned type is `.sort (u + 1)` and
`AnnotOk2` of a sort is `True`: free. -/
theorem infer_sort_claim2C (m : EnvS2 V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr} {F : Nat} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.sort u) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
  subst h
  rw [denote2] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  refine ⟨F, .sort (u.eval φ + 1), Nat.le_refl F, ?_,
    fun _ _ => by simp, fun _ _ => by simp, ?_⟩
  · rw [denote2]; simp [Level.eval]
  · intro ρ _
    exact (sound_sort V ρ (u.eval φ)).2

/-- **`.bvar`, extended.**  Outside the fragment: the checker throws. -/
theorem infer_bvar_claim2C (m : EnvS2 V env) {d i : Nat} {t : Expr}
    {Δa : List AVExpr} {F : Nat} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t)
    (_hea : denote2 μ m.acval env φ F d (.bvar i) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.fvar`, extended — and the one clause that pays outside its own
ledger.**  Everything but the new conjunct is `infer_fvar_claim2A`;
the new conjunct is `CtxAnn2`, the leaf-package component `CtxOk2`
does not have. -/
theorem infer_fvar_claim2C (m : EnvS2 V env) (hann : CtxAnn2 m μ φ)
    {d idx : Nat} {n : Name} {ty t : Expr} {Δa : List AVExpr}
    {F : Nat} {ea : AVExpr}
    (hC : CtxOk2 m μ φ F d Δa (.fvar idx n ty))
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.fvar idx n ty) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tya, Aa, hden, hi, hlink⟩ := CtxOk2.fvar_leaf hC
  rw [denote2] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨F, tya, Nat.le_refl F, hden, fun _ _ => by simp,
      hann hC hden, ?_⟩
    intro ρ hρ
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### The two constant-shaped clauses -/

/-- **`.const`, extended.**  The residue answers with the conjunct. -/
theorem infer_const_claim2C (m : EnvS2 V env) (hct : ConstType2C m μ φ)
    {d F : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AVExpr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.const n us) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
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
      rw [denote2, hf] at hea
      dsimp only at hea
      rw [if_pos hlen] at hea
      obtain rfl : ea = m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us) :=
        (Option.some.inj hea).symm
      obtain ⟨F', ta, hle, hta, hok, hmem⟩ := hct F d n ci us hf hlen
      exact ⟨F', ta, hle, hta, fun ρ _ => m.acval_ok2 n _ ρ,
        fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.lit (.natVal k)`, extended.**  The returned type's annotation
is the `Nat` leaf's `acval`, so its truthfulness is `acval_ok2` — free
and already in the clause. -/
theorem infer_natLit_claim2C (m : EnvS2 V env) (hnh : NatHeads2 m φ)
    {d k F : Nat} {t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.lit (.natVal k)) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : Setlec.natLitSupported env = true := by simpa using hg
    rw [denote2, if_pos hgt] at hea
    obtain rfl : ea = natLitT2
        (m.acval natZeroName (Level.substFn φ [] []))
        (m.acval natSuccName (Level.substFn φ [] [])) k :=
      (Option.some.inj hea).symm
    cases hf : env.find? natName with
    | none =>
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        natName_levelParams_nil hgt hf
      have hrow : ∀ ρ : Nat → V,
          AnnotOk2 V ρ (natLitT2
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) k) ∧
            interp2 V ρ (natLitT2
                (m.acval natZeroName (Level.substFn φ [] []))
                (m.acval natSuccName (Level.substFn φ [] [])) k)
              ∈ˢ interp2 V ρ
                (m.acval natName (Level.substFn φ [] [])) :=
        fun ρ => natLit_facts2 (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ)
          (hnh hgt ρ).1 (hnh hgt ρ).2 k
      refine ⟨F, m.acval natName (Level.substFn φ [] []),
        Nat.le_refl F, ?_, fun ρ _ => (hrow ρ).1,
        fun ρ _ => m.acval_ok2 _ _ ρ, fun ρ _ => (hrow ρ).2⟩
      rw [denote2, hf]
      dsimp only
      rw [if_pos (by simp [hlp]), hlp]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### `.forallE` — still free -/

/-- **`.forallE`, extended.**  The returned type is a sort. -/
theorem infer_forallE_claim2C (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) {d F : Nat} {n : Name}
    {ty body t : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hC : CtxOk2 m μ φ F d Δa (.forallE n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.forallE n ty body mb)
      = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, vv, hty, hwu, hbt, hens, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  simp only [Expr.WScoped] at hws
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hu : sortOfE μ env φ F d ty with _ | u0
  · rw [hu] at hea; exact nomatch hea
  rw [hu] at hea
  rcases hv : sortOfE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .pi u0 v0 ta ba := (Option.some.inj hea).symm
  obtain rfl : u0 = u.eval φ :=
    sortOfE_crossFuel hu (sortOfE_of_run hty hwu)
  obtain rfl : v0 = vv.eval φ :=
    sortOfE_crossFuel hv
      (sortOfE_of_run hbt (Setlec.ensureSortCore_inv hens))
  have hCop := hop (n := n) hC.forallE_ty hC.forallE_body hta
    hws.1.fvarsBelow
  have hrow : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (AVExpr.pi (u.eval φ) (vv.eval φ) ta ba) ∧
        interp2 V ρ (.pi (u.eval φ) (vv.eval φ) ta ba)
          ∈ˢ interp2 V ρ
            (.sort (Setlec.TT.imax (u.eval φ) (vv.eval φ))) := by
    intro ρ hρ
    have hdom := hss hC.forallE_ty hu hta ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ ta →
        AnnotOk2 V (cons x ρ) ba ∧
          interp2 V (cons x ρ) ba ∈ˢ (univ (vv.eval φ) : V) :=
      fun x hx => hss hCop hv hba (cons x ρ) (Sat2_cons V hρ hx)
    exact sound_pi V hdom.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
  exact ⟨F, .sort (Setlec.TT.imax (u.eval φ) (vv.eval φ)),
    Nat.le_refl F, by rw [denote2_sortQ]; rfl,
    fun ρ hρ => (hrow ρ hρ).1, fun _ _ => by simp,
    fun ρ hρ => (hrow ρ hρ).2⟩

/-! ### `.lam` — free by induction -/

/-- **`.lam`, extended.**  The returned type is the `∀` whose domain
is the λ's own and whose codomain is the body's inferred type, so
`AnnotOk2_pi` splits the obligation into `SortSem2`'s domain fact —
already in the clause — and the induction hypothesis's new conjunct at
`ta :: Δa`, which `Sat2_cons` transports.  **Free.** -/
theorem infer_lam_claim2C (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) {d F : Nat} {n : Name}
    {ty body t : Expr} {mb : BinderMeta} {Δa : List AVExpr}
    {ea : AVExpr} (ihi : InferClaims2C μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOk2 m μ φ F d Δa (.lam n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.lam n ty body mb) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, -, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hv : lamSortE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .lam v0 ta ba := (Option.some.inj hea).symm
  have hsv : sortOfE μ env φ F (d + 1) bt = some v0 := by
    obtain ⟨bt0, hbt0, hs0⟩ := lamSortE_runs hv
    rwa [infer_crossFuel hbt0 hbt] at hs0
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hCop := hop (n := n) hC.lam_ty hC.lam_body hta hws.1.fvarsBelow
  obtain ⟨F1, tbt, hle1, htbt, hrowE, hrowT, hrowM⟩ :=
    ihi hbt hwopen hbopen hLopen hCop hba
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
  have hF1 : F1 ≤ F1 + fuel := Nat.le_add_right F1 fuel
  have hFF : F ≤ F1 + fuel := Nat.le_trans hle1 hF1
  have hfl : fuel ≤ F1 + fuel := Nat.le_add_left fuel F1
  have hdomS := hss (Δa := Δa)
    (CtxOk2.fuelMono (Nat.le_add_right F fuel) hC.lam_ty)
    (sortOfE_fuelMono (φ := φ) (Nat.le_add_left fuel F)
      (sortOfE_of_run hty hwu))
    (denote2_fuelMono (Nat.le_add_right F fuel) d ty hta)
  have hCbt : CtxOk2 m μ φ (F1 + fuel) (d + 1) (ta :: Δa) bt :=
    (CtxOk2.fuelMono hFF hCop).of_subset
      (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen)
  have hrow : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (AVExpr.lam v0 ta ba) ∧
        interp2 V ρ (.lam v0 ta ba)
          ∈ˢ interp2 V ρ (.pi (u.eval φ) v0 ta tbt) := by
    intro ρ hρ
    have hcodS : ∀ x, x ∈ˢ interp2 V ρ ta →
        interp2 V (cons x ρ) tbt ∈ˢ (univ v0 : V) :=
      fun x hx => (hss hCbt (sortOfE_fuelMono (φ := φ) hFF hsv)
        (denote2_fuelMono hF1 (d + 1) bt htbt) (cons x ρ)
        (Sat2_cons V hρ hx)).2
    refine sound_lam V (hdomS ρ hρ).1 (fun x hx => ?_) (fun x hx => ?_)
      (fun h0 x hx => ?_)
    · exact hrowE (cons x ρ) (Sat2_cons V hρ hx)
    · exact hrowM (cons x ρ) (Sat2_cons V hρ hx)
    · exact univ_zero (V := V) ▸ h0 ▸ hcodS x hx
  refine ⟨F1 + fuel, .pi (u.eval φ) v0 ta tbt, hFF, ?_,
    fun ρ hρ => (hrow ρ hρ).1, ?_, fun ρ hρ => (hrow ρ hρ).2⟩
  · rw [denote2, denote2_fuelMono hFF d ty hta, hround,
      denote2_fuelMono hF1 (d + 1) bt htbt,
      sortOfE_fuelMono (φ := φ) hfl (sortOfE_of_run hty hwu),
      sortOfE_fuelMono (φ := φ) hFF hsv]
    rfl
  · intro ρ hρ
    rw [AnnotOk2_pi]
    exact ⟨(hdomS ρ hρ).1,
      fun x hx => hrowT (cons x ρ) (Sat2_cons V hρ hx)⟩

/-! ### `.letE` — free by induction -/

/-- **`.letE`, extended.**  The returned type *is* the body's inferred
type, at the same depth and the same context, so the new conjunct is
the induction hypothesis's own, verbatim.  **Free.** -/
theorem infer_letE_claim2C (m : EnvS2 V env)
    (hbeta : BetaCross2C m μ φ) {d F : Nat} {n : Name}
    {ty val b t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihi : InferClaims2C μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOk2 m μ φ F d Δa (.letE n ty val b))
    (hea : denote2 μ m.acval env φ F d (.letE n ty val b) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, sv, tvv, hty, -, hvv, -, hbody⟩ :=
    Setlec.inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLval : Expr.LeavesBounded val := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) := fun l hl => by
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hLb l (by simp [Expr.fvarLeaves, h2])
    · exact hLval l h2
  have hCred : CtxOk2 m μ φ F d Δa (b.instantiate1 val) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hC.letE_body.2 l h2
    · exact hC.letE_val.2 l h2
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d val with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (b.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  obtain ⟨Ft, tta, -, -, hrowTE, -, -⟩ :=
    ihi hty hws.1 hb.1.1 hLty hC.letE_ty hta
  obtain ⟨Fv, tva, -, -, hrowVE, -, -⟩ :=
    ihi hvv hws.2.1 hb.1.2 hLval hC.letE_val hva
  obtain ⟨F2, ra, hle2, hra, hcross⟩ := hbeta (Δa := Δa) hva hba
  obtain ⟨F3, tbv, hle3, htbv, hrowBE, hrowBT, hrowBM⟩ :=
    ihi hbody hwred hbred hLred
      (CtxOk2.fuelMono hle2 hCred) hra
  refine ⟨F3, tbv, Nat.le_trans hle2 hle3, htbv, ?_, hrowBT, ?_⟩
  · intro ρ hρ
    have hokv := hrowVE ρ hρ
    have hokba : AnnotOk2 V (cons (interp2 V ρ va) ρ) ba :=
      (AnnotOk2_inst0 V hokv).mp ((hcross ρ hρ).2.mp (hrowBE ρ hρ))
    rw [AnnotOk2_letE]
    exact ⟨hrowTE ρ hρ, hokv, hokba⟩
  · intro ρ hρ
    rw [interp2_letE, ← interp2_inst0, ← (hcross ρ hρ).1]
    exact hrowBM ρ hρ

/-! ### `.app` — the clause the extension both taxes and relieves

Three things change here, and the balance is strongly in the
extension's favour.

* **`TypeOk2` is gone.**  Its three uses — `AnnotOk2` of the head's
  inferred type (twice, to grade `WhnfClaims2C`) and of the argument's
  (once, to grade `DefEqClaims2C`) — are the induction hypothesis's
  new conjunct.  And they are now **ρ-uniform**, which the hoisted
  reduction and defeq claims require and a ρ-local fact could not
  supply.
* **`AnnotOk2.hoist_pi`** splits the reduct's ρ-uniform truthfulness
  into the domain's (over `Δa`, for the defeq premise) and the
  codomain's (over `Aa :: Δa`, for the returned type).
* **The payment.**  The returned type is the crossed annotation `ra`,
  and the codomain's truthfulness lands on `Ba.inst aa` — so the
  crossing must carry truthfulness *back*, which is why `BetaCross2C`
  is a biconditional.  The sealed `BetaCross2` had both directions;
  `BetaCross2A` dropped one, and this buys it back. -/

theorem infer_app_claim2C (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hop : CtxOk2Open m μ φ) (hcr : CtxOk2R m μ φ)
    (hbeta : BetaCross2C m μ φ)
    {d F : Nat} {f a t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihw : WhnfClaims2C μ m φ fuel)
    (ihd : DefEqClaims2C μ m φ fuel) (ihi : InferClaims2C μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk2 m μ φ F d Δa (.app f a))
    (hea : denote2 μ m.acval env φ F d (.app f a) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tf, n', ty', body', mb', htf, hwf, rfl, tya, hta, hde⟩ :=
    Setlec.inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  rw [denote2] at hea
  rcases hfa : denote2 μ m.acval env φ F d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote2 μ m.acval env φ F d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨F1, tfa, hle1, htfa, hrowfE, hrowfT, hrowfM⟩ :=
    ihi htf hws.1 hb.1 hLf hC.app_fn hfa
  obtain ⟨htfw, htfb, htfL, htfC⟩ :=
    frame_inferR m.base.wf htf hws.1 hb.1 hLf (hcr hC.app_fn)
  obtain ⟨G, pa, hleG, hpa, hokpa, hredf⟩ :=
    ihw hwf htfw htfb htfL htfC htfa hrowfT
  have hle1G : F ≤ G := Nat.le_trans hle1 hleG
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
  have hCty' : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) ty' :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
  rw [denote2] at hpa
  rcases hAa : denote2 μ m.acval env φ G d ty' with _ | Aa
  · rw [hAa] at hpa; exact nomatch hpa
  rw [hAa] at hpa
  rcases hBa : denote2 μ m.acval env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | Ba
  · rw [hBa] at hpa; exact nomatch hpa
  rw [hBa] at hpa
  rcases hu' : sortOfE μ env φ G d ty' with _ | u'
  · rw [hu'] at hpa; exact nomatch hpa
  rw [hu'] at hpa
  rcases hv' : sortOfE μ env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | v'
  · rw [hv'] at hpa; exact nomatch hpa
  rw [hv'] at hpa
  obtain rfl : pa = .pi u' v' Aa Ba := (Option.some.inj hpa).symm
  -- the hoist: the reduct's ρ-uniform truthfulness, split
  obtain ⟨hokAa, hokBa⟩ := AnnotOk2.hoist_pi hokpa
  obtain ⟨F2, taa, hle2, htaa, hrowaE, hrowaT, hrowaM⟩ :=
    ihi hta hws.2 hb.2 hLa hC.app_arg haa
  obtain ⟨htaw, htab, htaL, htaC⟩ :=
    frame_inferR m.base.wf hta hws.2 hb.2 hLa (hcr hC.app_arg)
  -- the defeq claim's two graded premises: the argument type's from
  -- the induction hypothesis's new conjunct (this is what retires
  -- `TypeOk2`), the domain's from the hoist
  have hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ taa = interp2 V ρ Aa :=
    ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC hCty'
      (denote2_fuelMono (Nat.le_add_right F2 G) d tya htaa)
      (denote2_fuelMono (Nat.le_add_left G F2) d ty' hAa)
      hrowaT hokAa
  have hCf : CtxOk2 m μ φ G d Δa f := CtxOk2.fuelMono hle1G hC.app_fn
  have hCpi : CtxOk2 m μ φ G d Δa (.forallE n' ty' body' mb') :=
    (hCf.of_subset
      (inferTypeCore_fvarLeaves m.base.wf fuel htf hws.1)).of_subset
      (whnf_fvarLeaves m.base.wf fuel hwf)
  have hCop := hop (n := n') hCpi.forallE_ty hCpi.forallE_body hAa
    hwfe.1.fvarsBelow
  obtain ⟨F3, ra, hle3, hra, hcross⟩ :=
    hbeta (Δa := Δa) (denote2_fuelMono hle1G d a haa) hBa
  have ha2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ aa ∈ˢ interp2 V ρ Aa := by
    intro ρ hρ
    rw [← hdom ρ hρ]
    exact hrowaM ρ hρ
  have hf2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ fa ∈ˢ interp2 V ρ (.pi u' v' Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  have hcod0 : ∀ ρ : Nat → V, Sat2 V Δa ρ → v' = 0 →
      ∀ x, x ∈ˢ interp2 V ρ Aa →
        interp2 V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    have hmem := (hss hCop hv' hBa (cons x ρ) (Sat2_cons V hρ hx)).2
    rw [h0] at hmem
    exact univ_zero (V := V) ▸ hmem
  -- the returned type's truthfulness: the codomain's hoisted form at
  -- the argument's value, carried back across the crossing
  have hokra : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ra := by
    intro ρ hρ
    refine (hcross ρ hρ).2.mpr ((AnnotOk2_inst0 V (hrowaE ρ hρ)).mpr ?_)
    exact hokBa (cons (interp2 V ρ aa) ρ)
      (Sat2_cons V hρ (ha2 ρ hρ))
  refine ⟨F3, ra, Nat.le_trans hle1G hle3, hra, ?_, hokra, ?_⟩
  · intro ρ hρ
    exact (sound_app V (hrowfE ρ hρ) (hrowaE ρ hρ) (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).1
  · intro ρ hρ
    rw [(hcross ρ hρ).1]
    exact (sound_app V (hrowfE ρ hρ) (hrowaE ρ hρ) (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-! ### The assembly, generation four

`InferInputs2A` had nine fields.  **`type_ok` is gone** — the claim
now delivers what it assumed.  `const_ty`, `beta`, `str_lit` and
`proj` are extended with the new conjunct; `nat_heads`, `sort_sem`,
`ctx_R` and `ctx_open` are unchanged.  **`ctx_ann` is new**, and it is
not the extension's price but the supplier's: see the FINDING above. -/

/-- **The quarter's routed inputs**, generation four. -/
structure InferInputs2C (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- I3: the stored type's annotation, at a fuel of its own choosing,
  now carrying its truthfulness -/
  const_ty : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    ConstType2C m μ φ
  /-- I4: the two numeral head facts (unchanged) -/
  nat_heads : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    NatHeads2 m φ
  /-- I5: the `String`-literal clause -/
  str_lit : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferStrLitStep2C m μ φ fuel
  /-- I8/I10: the β crossing, transporting truthfulness both ways -/
  beta : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    BetaCross2C m μ φ
  /-- I9: the projection clause -/
  proj : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStep2C m μ φ fuel
  /-- the sort fact at an annotation fuel off the induction -/
  sort_sem : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    SortSem2 m μ φ
  /-- **refuted** (`not_ctxOk2R`): the context in the other currency.
  Generation five's context move is what removes it. -/
  ctx_R : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    CtxOk2R m μ φ
  /-- `CtxOkR.open`'s twin (a theorem: `CtxOk2.openS`) -/
  ctx_open : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    CtxOk2Open m μ φ
  /-- **new, and it belongs to the supplier**: `CtxOk2`'s missing
  fourth leaf component -/
  ctx_ann : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    CtxAnn2 m μ φ

/-- **`InferStep2C`, modulo the routed inputs.**  Eleven `Expr`
shapes, one line each, against the hoisted and extended claim.

Four clauses still close with no residue of their own: `.sort`,
`.bvar`, `.forallE` and `.lam`.  `.fvar` has left that list — not
because the clause got harder, but because the *claim* now asks for a
fact `CtxOk2` does not carry. -/
theorem inferStep2C_of (h : InferInputs2C V μ) : InferStep2C μ V := by
  intro env m φ fuel _ihwc ihw ihd ihi
  intro d e t Δa hrun hws hb hLb F ea hC hea
  match e, hrun, hws, hb, hLb, hC, hea with
  | .sort u, hrun, _, _, _, _, hea =>
    exact infer_sort_claim2C m hrun hea
  | .bvar i, hrun, _, _, _, _, hea =>
    exact infer_bvar_claim2C m hrun hea
  | .fvar idx nm ty, hrun, _, _, _, hC, hea =>
    exact infer_fvar_claim2C m (h.ctx_ann m φ) hC hrun hea
  | .const nm us, hrun, _, _, _, _, hea =>
    exact infer_const_claim2C m (h.const_ty m φ) hrun hea
  | .lit (.natVal k), hrun, _, _, _, _, hea =>
    exact infer_natLit_claim2C m (h.nat_heads m φ) hrun hea
  | .lit (.strVal s), hrun, _, _, _, _, hea =>
    exact h.str_lit m φ fuel hrun hea
  | .forallE nm ty body mb, hrun, hws, _, _, hC, hea =>
    exact infer_forallE_claim2C m (h.sort_sem m φ) (h.ctx_open m φ)
      hrun hws hC hea
  | .lam nm ty body mb, hrun, hws, hb, hLb, hC, hea =>
    exact infer_lam_claim2C m (h.sort_sem m φ) (h.ctx_open m φ) ihi
      hrun hws hb hLb hC hea
  | .app f a, hrun, hws, hb, hLb, hC, hea =>
    exact infer_app_claim2C m (h.sort_sem m φ) (h.ctx_open m φ)
      (h.ctx_R m φ) (h.beta m φ) ihw ihd ihi hrun hws hb hLb hC hea
  | .letE nm ty val b, hrun, hws, hb, hLb, hC, hea =>
    exact infer_letE_claim2C m (h.beta m φ) ihi hrun hws hb hLb hC hea
  | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
    exact h.proj m φ fuel hrun hws hb hLb hC hea


/-! # Generation five — the inference quarter, one currency

`Claims2D` puts `CtxOk2D` in all four claims.  For this quarter that
is not plumbing: it **retires two fields of `InferInputs2C`**, one of
them refuted.

* **`ctx_R` is gone.**  `CtxOk2R` — the bridge from the annotated
  context to `CtxOkR`-on-erasures — was carried in the structure with
  a docstring saying it is refuted (`not_ctxOk2R`), because the
  `.app` clause fed `WhnfClaims2C` and `DefEqClaims2C` a context it
  could only get by translating.  Under one currency the two claims
  read the hypothesis the clause already holds.  **This is the field
  the generation exists to remove.**
* **`ctx_ann` is gone.**  `CtxAnn2` said "a leaf's annotation is
  truthful at every satisfying valuation", routed because `CtxOk2`'s
  leaf package had three conjuncts and not that one.  `CtxOk2D`'s
  fourth conjunct *is* that statement, so `CtxOk2D.fvar_leaf` hands it
  over and the `.fvar` clause takes no residue.
* **`ctx_open` is gone** as a *field*: the opened context is
  `CtxOk2D.openS`, a kit theorem, and the extra premise it now takes —
  the domain's hoisted grading — is at each of the three sites a fact
  the clause already computes (`SortSem2` at `.forallE`/`.lam`,
  `AnnotOk2.hoist_pi` of the reduct at `.app`).

Four residues remain, and none of them mentions a context:
`ConstType2C`, `NatHeads2`, `InferStrLitStep2C`, `BetaCross2C`,
`SortSem2`, plus the projection clause.  All are **reused verbatim**
from the `…C` lane — `SortSem2` still takes `CtxOk2`, and consumers
pass `CtxOk2D.toCtxOk2`, which is the point of stating `CtxOk2D` as a
conjunction.
-/

/-- The projection clause, in one currency. -/
def InferProjStep2D {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i F : Nat} {sn : Name} {pe t : Expr} {Δa : List AVExpr}
    {ea : AVExpr},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOk2D m μ φ F d Δa (.proj sn i pe) →
    denote2 μ m.acval env φ F d (.proj sn i pe) = some ea →
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- **`.fvar`, with no residue.**  `CtxOk2D.fvar_leaf` returns the
three conjuncts `CtxOk2` had *and* the fourth, at the same `tya`; the
clause's `hann` premise disappears. -/
theorem infer_fvar_claim2D (m : EnvS2 V env)
    {d idx : Nat} {n : Name} {ty t : Expr} {Δa : List AVExpr}
    {F : Nat} {ea : AVExpr}
    (hC : CtxOk2D m μ φ F d Δa (.fvar idx n ty))
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.fvar idx n ty) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tya, Aa, hden, hi, hlink, hokTy⟩ := CtxOk2D.fvar_leaf hC
  rw [denote2] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨F, tya, Nat.le_refl F, hden, fun _ _ => by simp,
      hokTy, ?_⟩
    intro ρ hρ
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.forallE`, with the opened context built in place.**  The
domain's hoisted grading `CtxOk2D.openS` now asks for is the first
component of `SortSem2`'s own conclusion — already computed, one
`fun ρ hρ => (… ).1` away.

The `WScoped` premise is **gone**: the `…C` lane took it only to feed
`CtxOk2Open`'s `Expr.fvarsBelow d ty`, and `CtxOk2D` carries its own
scoping (`CtxOk2.wScoped`).  A premise disappearing from a clause
signature is the cheapest evidence that the currency move was
right. -/
theorem infer_forallE_claim2D (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    {d F : Nat} {n : Name} {ty body t : Expr} {mb : BinderMeta}
    {Δa : List AVExpr} {ea : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hC : CtxOk2D m μ φ F d Δa (.forallE n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.forallE n ty body mb)
      = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, vv, hty, hwu, hbt, hens, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hu : sortOfE μ env φ F d ty with _ | u0
  · rw [hu] at hea; exact nomatch hea
  rw [hu] at hea
  rcases hv : sortOfE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .pi u0 v0 ta ba := (Option.some.inj hea).symm
  obtain rfl : u0 = u.eval φ :=
    sortOfE_crossFuel hu (sortOfE_of_run hty hwu)
  obtain rfl : v0 = vv.eval φ :=
    sortOfE_crossFuel hv
      (sortOfE_of_run hbt (Setlec.ensureSortCore_inv hens))
  have hdomU := hss hC.toCtxOk2.forallE_ty hu hta
  have hCop : CtxOk2D m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
    CtxOk2D.openS (n := n) hC.forallE_ty hC.forallE_body hta
      (fun ρ hρ => (hdomU ρ hρ).1)
  have hrow : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (AVExpr.pi (u.eval φ) (vv.eval φ) ta ba) ∧
        interp2 V ρ (.pi (u.eval φ) (vv.eval φ) ta ba)
          ∈ˢ interp2 V ρ
            (.sort (Setlec.TT.imax (u.eval φ) (vv.eval φ))) := by
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ ta →
        AnnotOk2 V (cons x ρ) ba ∧
          interp2 V (cons x ρ) ba ∈ˢ (univ (vv.eval φ) : V) :=
      fun x hx => hss hCop.toCtxOk2 hv hba (cons x ρ)
        (Sat2_cons V hρ hx)
    exact sound_pi V hdom.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
  exact ⟨F, .sort (Setlec.TT.imax (u.eval φ) (vv.eval φ)),
    Nat.le_refl F, by rw [denote2_sortQ]; rfl,
    fun ρ hρ => (hrow ρ hρ).1, fun _ _ => by simp,
    fun ρ hρ => (hrow ρ hρ).2⟩

/-- **`.lam`, with the opened context built in place.**  Same move as
`.forallE`; the grading `openS` asks for is `hdomS`'s first component,
which the clause computes anyway to feed `sound_lam`. -/
theorem infer_lam_claim2D (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    {d F : Nat} {n : Name} {ty body t : Expr} {mb : BinderMeta}
    {Δa : List AVExpr} {ea : AVExpr} (ihi : InferClaims2D μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOk2D m μ φ F d Δa (.lam n ty body mb))
    (hea : denote2 μ m.acval env φ F d (.lam n ty body mb) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, -, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  rcases hv : lamSortE μ env φ F (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | v0
  · rw [hv] at hea; exact nomatch hea
  rw [hv] at hea
  obtain rfl : ea = .lam v0 ta ba := (Option.some.inj hea).symm
  have hsv : sortOfE μ env φ F (d + 1) bt = some v0 := by
    obtain ⟨bt0, hbt0, hs0⟩ := lamSortE_runs hv
    rwa [infer_crossFuel hbt0 hbt] at hs0
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hdomS := hss (Δa := Δa)
    (CtxOk2.fuelMono (Nat.le_add_right F fuel) hC.toCtxOk2.lam_ty)
    (sortOfE_fuelMono (φ := φ) (Nat.le_add_left fuel F)
      (sortOfE_of_run hty hwu))
    (denote2_fuelMono (Nat.le_add_right F fuel) d ty hta)
  have hCop : CtxOk2D m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
    CtxOk2D.openS (n := n) hC.lam_ty hC.lam_body hta
      (fun ρ hρ => (hdomS ρ hρ).1)
  obtain ⟨F1, tbt, hle1, htbt, hrowE, hrowT, hrowM⟩ :=
    ihi hbt hwopen hbopen hLopen hCop hba
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
  have hF1 : F1 ≤ F1 + fuel := Nat.le_add_right F1 fuel
  have hFF : F ≤ F1 + fuel := Nat.le_trans hle1 hF1
  have hfl : fuel ≤ F1 + fuel := Nat.le_add_left fuel F1
  have hCbt : CtxOk2 m μ φ (F1 + fuel) (d + 1) (ta :: Δa) bt :=
    (CtxOk2.fuelMono hFF hCop.toCtxOk2).of_subset
      (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen)
  have hrow : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOk2 V ρ (AVExpr.lam v0 ta ba) ∧
        interp2 V ρ (.lam v0 ta ba)
          ∈ˢ interp2 V ρ (.pi (u.eval φ) v0 ta tbt) := by
    intro ρ hρ
    have hcodS : ∀ x, x ∈ˢ interp2 V ρ ta →
        interp2 V (cons x ρ) tbt ∈ˢ (univ v0 : V) :=
      fun x hx => (hss hCbt (sortOfE_fuelMono (φ := φ) hFF hsv)
        (denote2_fuelMono hF1 (d + 1) bt htbt) (cons x ρ)
        (Sat2_cons V hρ hx)).2
    refine sound_lam V (hdomS ρ hρ).1 (fun x hx => ?_) (fun x hx => ?_)
      (fun h0 x hx => ?_)
    · exact hrowE (cons x ρ) (Sat2_cons V hρ hx)
    · exact hrowM (cons x ρ) (Sat2_cons V hρ hx)
    · exact univ_zero (V := V) ▸ h0 ▸ hcodS x hx
  refine ⟨F1 + fuel, .pi (u.eval φ) v0 ta tbt, hFF, ?_,
    fun ρ hρ => (hrow ρ hρ).1, ?_, fun ρ hρ => (hrow ρ hρ).2⟩
  · rw [denote2, denote2_fuelMono hFF d ty hta, hround,
      denote2_fuelMono hF1 (d + 1) bt htbt,
      sortOfE_fuelMono (φ := φ) hfl (sortOfE_of_run hty hwu),
      sortOfE_fuelMono (φ := φ) hFF hsv]
    rfl
  · intro ρ hρ
    rw [AnnotOk2_pi]
    exact ⟨(hdomS ρ hρ).1,
      fun x hx => hrowT (cons x ρ) (Sat2_cons V hρ hx)⟩

/-- **`.letE`, unchanged in substance.**  The ζ reduct's context is
`of_subset` of the subject's — one kit call where the `…C` lane
opened the leaf package by hand. -/
theorem infer_letE_claim2D (m : EnvS2 V env)
    (hbeta : BetaCross2C m μ φ) {d F : Nat} {n : Name}
    {ty val b t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihi : InferClaims2D μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOk2D m μ φ F d Δa (.letE n ty val b))
    (hea : denote2 μ m.acval env φ F d (.letE n ty val b) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, sv, tvv, hty, -, hvv, -, hbody⟩ :=
    Setlec.inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLval : Expr.LeavesBounded val := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hsubred : ∀ l ∈ (b.instantiate1 val).fvarLeaves,
      l ∈ (Expr.letE n ty val b).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) :=
    fun l hl => hLb l (hsubred l hl)
  have hCred : CtxOk2D m μ φ F d Δa (b.instantiate1 val) :=
    hC.of_subset hsubred
  rw [denote2] at hea
  rcases hta : denote2 μ m.acval env φ F d ty with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denote2 μ m.acval env φ F d val with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denote2 μ m.acval env φ F (d + 1)
      (b.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  obtain ⟨Ft, tta, -, -, hrowTE, -, -⟩ :=
    ihi hty hws.1 hb.1.1 hLty hC.letE_ty hta
  obtain ⟨Fv, tva, -, -, hrowVE, -, -⟩ :=
    ihi hvv hws.2.1 hb.1.2 hLval hC.letE_val hva
  obtain ⟨F2, ra, hle2, hra, hcross⟩ := hbeta (Δa := Δa) hva hba
  obtain ⟨F3, tbv, hle3, htbv, hrowBE, hrowBT, hrowBM⟩ :=
    ihi hbody hwred hbred hLred
      (CtxOk2D.fuelMono hle2 hCred) hra
  refine ⟨F3, tbv, Nat.le_trans hle2 hle3, htbv, ?_, hrowBT, ?_⟩
  · intro ρ hρ
    have hokv := hrowVE ρ hρ
    have hokba : AnnotOk2 V (cons (interp2 V ρ va) ρ) ba :=
      (AnnotOk2_inst0 V hokv).mp ((hcross ρ hρ).2.mp (hrowBE ρ hρ))
    rw [AnnotOk2_letE]
    exact ⟨hrowTE ρ hρ, hokv, hokba⟩
  · intro ρ hρ
    rw [interp2_letE, ← interp2_inst0, ← (hcross ρ hρ).1]
    exact hrowBM ρ hρ

/-- **`.app`, and the refuted residue's grave.**  `infer_app_claim2C`
took `hcr : CtxOk2R m μ φ` — the bridge `not_ctxOk2R` refutes — four
times: to hand `WhnfClaims2C` the head's type, `DefEqClaims2C` the
argument's type and the ∀'s domain, and to frame the reduct.  Every
one of those is now `CtxOk2D.fuelMono` and `of_subset` of the
hypothesis the clause is handed.  The clause takes **no context
residue at all**. -/
theorem infer_app_claim2D (m : EnvS2 V env) (hss : SortSem2 m μ φ)
    (hbeta : BetaCross2C m μ φ)
    {d F : Nat} {f a t : Expr} {Δa : List AVExpr} {ea : AVExpr}
    (ihw : WhnfClaims2D μ m φ fuel)
    (ihd : DefEqClaims2D μ m φ fuel) (ihi : InferClaims2D μ m φ fuel)
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk2D m μ φ F d Δa (.app f a))
    (hea : denote2 μ m.acval env φ F d (.app f a) = some ea) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tf, n', ty', body', mb', htf, hwf, rfl, tya, hta, hde⟩ :=
    Setlec.inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  rw [denote2] at hea
  rcases hfa : denote2 μ m.acval env φ F d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote2 μ m.acval env φ F d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨F1, tfa, hle1, htfa, hrowfE, hrowfT, hrowfM⟩ :=
    ihi htf hws.1 hb.1 hLf hC.app_fn hfa
  have htfsub := inferTypeCore_fvarLeaves m.base.wf fuel htf hws.1
  have htfw : Expr.WScoped d tf :=
    inferTypeCore_WScoped m.base.wf fuel htf hws.1
  have htfb : tf.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.base.wf fuel htf hws.1 hb.1 hLf
  have htfL : Expr.LeavesBounded tf := fun l hl => hLf l (htfsub l hl)
  have htfC : CtxOk2D m μ φ F1 d Δa tf :=
    (CtxOk2D.fuelMono hle1 hC.app_fn).of_subset htfsub
  obtain ⟨G, pa, hleG, hpa, hokpa, hredf⟩ :=
    ihw hwf htfw htfb htfL htfC htfa hrowfT
  have hle1G : F ≤ G := Nat.le_trans hle1 hleG
  have hwfe : Expr.WScoped d (Expr.forallE n' ty' body' mb') :=
    whnf_WScoped m.base.wf fuel hwf htfw
  have hbfe : (Expr.forallE n' ty' body' mb').looseBVarsBounded 0
      = true := whnf_looseBVars m.base.wf fuel hwf htfb
  have hLfe : Expr.LeavesBounded (.forallE n' ty' body' mb') :=
    fun l hl => htfL l (whnf_fvarLeaves m.base.wf fuel hwf l hl)
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty' := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCpi : CtxOk2D m μ φ G d Δa (.forallE n' ty' body' mb') :=
    ((CtxOk2D.fuelMono hle1G hC.app_fn).of_subset
      htfsub).of_subset (whnf_fvarLeaves m.base.wf fuel hwf)
  rw [denote2] at hpa
  rcases hAa : denote2 μ m.acval env φ G d ty' with _ | Aa
  · rw [hAa] at hpa; exact nomatch hpa
  rw [hAa] at hpa
  rcases hBa : denote2 μ m.acval env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | Ba
  · rw [hBa] at hpa; exact nomatch hpa
  rw [hBa] at hpa
  rcases hu' : sortOfE μ env φ G d ty' with _ | u'
  · rw [hu'] at hpa; exact nomatch hpa
  rw [hu'] at hpa
  rcases hv' : sortOfE μ env φ G (d + 1)
      (body'.instantiate1 (.fvar d n' ty')) with _ | v'
  · rw [hv'] at hpa; exact nomatch hpa
  rw [hv'] at hpa
  obtain rfl : pa = .pi u' v' Aa Ba := (Option.some.inj hpa).symm
  -- the hoist: the reduct's ρ-uniform truthfulness, split
  obtain ⟨hokAa, hokBa⟩ := AnnotOk2.hoist_pi hokpa
  obtain ⟨F2, taa, hle2, htaa, hrowaE, hrowaT, hrowaM⟩ :=
    ihi hta hws.2 hb.2 hLa hC.app_arg haa
  have htasub := inferTypeCore_fvarLeaves m.base.wf fuel hta hws.2
  have htaw : Expr.WScoped d tya :=
    inferTypeCore_WScoped m.base.wf fuel hta hws.2
  have htab : tya.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.base.wf fuel hta hws.2 hb.2 hLa
  have htaL : Expr.LeavesBounded tya := fun l hl => hLa l (htasub l hl)
  have htaC : CtxOk2D m μ φ (F2 + G) d Δa tya :=
    (CtxOk2D.fuelMono
      (Nat.le_trans hle2 (Nat.le_add_right F2 G)) hC.app_arg).of_subset
      htasub
  -- the defeq claim's two graded premises, both in one currency
  have hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ taa = interp2 V ρ Aa :=
    ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC
      (CtxOk2D.fuelMono (Nat.le_add_left G F2) hCpi.forallE_ty)
      (denote2_fuelMono (Nat.le_add_right F2 G) d tya htaa)
      (denote2_fuelMono (Nat.le_add_left G F2) d ty' hAa)
      hrowaT hokAa
  have hCop : CtxOk2D m μ φ G (d + 1) (Aa :: Δa)
      (body'.instantiate1 (.fvar d n' ty')) :=
    CtxOk2D.openS (n := n') hCpi.forallE_ty hCpi.forallE_body hAa
      hokAa
  obtain ⟨F3, ra, hle3, hra, hcross⟩ :=
    hbeta (Δa := Δa) (denote2_fuelMono hle1G d a haa) hBa
  have ha2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ aa ∈ˢ interp2 V ρ Aa := by
    intro ρ hρ
    rw [← hdom ρ hρ]
    exact hrowaM ρ hρ
  have hf2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ fa ∈ˢ interp2 V ρ (.pi u' v' Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  have hcod0 : ∀ ρ : Nat → V, Sat2 V Δa ρ → v' = 0 →
      ∀ x, x ∈ˢ interp2 V ρ Aa →
        interp2 V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    have hmem :=
      (hss hCop.toCtxOk2 hv' hBa (cons x ρ) (Sat2_cons V hρ hx)).2
    rw [h0] at hmem
    exact univ_zero (V := V) ▸ hmem
  have hokra : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ra := by
    intro ρ hρ
    refine (hcross ρ hρ).2.mpr ((AnnotOk2_inst0 V (hrowaE ρ hρ)).mpr ?_)
    exact hokBa (cons (interp2 V ρ aa) ρ)
      (Sat2_cons V hρ (ha2 ρ hρ))
  refine ⟨F3, ra, Nat.le_trans hle1G hle3, hra, ?_, hokra, ?_⟩
  · intro ρ hρ
    exact (sound_app V (hrowfE ρ hρ) (hrowaE ρ hρ) (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).1
  · intro ρ hρ
    rw [(hcross ρ hρ).1]
    exact (sound_app V (hrowfE ρ hρ) (hrowaE ρ hρ) (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-! ### The assembly, generation five

`InferInputs2C` had nine fields; `InferInputs2D` has six.  The three
that go are exactly the three that mention a context: `ctx_R`
(**refuted**), `ctx_ann` (now `CtxOk2D`'s fourth conjunct) and
`ctx_open` (now `CtxOk2D.openS`, a kit theorem, with its new grading
premise paid at each site from facts the clause already has). -/

/-- **The quarter's routed inputs**, generation five.  Every field is
literally its `…C` counterpart — no residue of this quarter changed
shape; three of them simply ceased to exist. -/
structure InferInputs2D (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- I3: the stored type's annotation, carrying its truthfulness -/
  const_ty : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    ConstType2C m μ φ
  /-- I4: the two numeral head facts -/
  nat_heads : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    NatHeads2 m φ
  /-- I5: the `String`-literal clause -/
  str_lit : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferStrLitStep2C m μ φ fuel
  /-- I8/I10: the β crossing, transporting truthfulness both ways -/
  beta : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    BetaCross2C m μ φ
  /-- I9: the projection clause, in the new currency -/
  proj : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStep2D m μ φ fuel
  /-- the sort fact at an annotation fuel off the induction -/
  sort_sem : ∀ {env : Env} (m : EnvS2 V env) (φ : Name → Nat),
    SortSem2 m μ φ

/-- **`InferStep2D`, modulo the routed inputs.**  Eleven `Expr`
shapes.  Six clauses close with no residue of their own now:
`.sort`, `.bvar`, `.fvar`, `.forallE`, `.lam` and `.letE` — `.fvar`
has rejoined that list, which is the seal-17 repair paying for
itself. -/
theorem inferStep2D_of (h : InferInputs2D V μ) : InferStep2D μ V := by
  intro env m φ fuel _ihwc ihw ihd ihi
  intro d e t Δa hrun hws hb hLb F ea hC hea
  match e, hrun, hws, hb, hLb, hC, hea with
  | .sort u, hrun, _, _, _, _, hea =>
    exact infer_sort_claim2C m hrun hea
  | .bvar i, hrun, _, _, _, _, hea =>
    exact infer_bvar_claim2C m hrun hea
  | .fvar idx nm ty, hrun, _, _, _, hC, hea =>
    exact infer_fvar_claim2D m hC hrun hea
  | .const nm us, hrun, _, _, _, _, hea =>
    exact infer_const_claim2C m (h.const_ty m φ) hrun hea
  | .lit (.natVal k), hrun, _, _, _, _, hea =>
    exact infer_natLit_claim2C m (h.nat_heads m φ) hrun hea
  | .lit (.strVal s), hrun, _, _, _, _, hea =>
    exact h.str_lit m φ fuel hrun hea
  | .forallE nm ty body mb, hrun, _, _, _, hC, hea =>
    exact infer_forallE_claim2D m (h.sort_sem m φ) hrun hC hea
  | .lam nm ty body mb, hrun, hws, hb, hLb, hC, hea =>
    exact infer_lam_claim2D m (h.sort_sem m φ) ihi hrun hws hb hLb
      hC hea
  | .app f a, hrun, hws, hb, hLb, hC, hea =>
    exact infer_app_claim2D m (h.sort_sem m φ) (h.beta m φ) ihw ihd
      ihi hrun hws hb hLb hC hea
  | .letE nm ty val b, hrun, hws, hb, hLb, hC, hea =>
    exact infer_letE_claim2D m (h.beta m φ) ihi hrun hws hb hLb hC hea
  | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
    exact h.proj m φ fuel hrun hws hb hLb hC hea


/-! ## `CtxAnn2`, retired — the fourth conjunct's receipt

Seal 17's FINDING (above, at `CtxAnn2`) said the `.fvar` clause's
missing fact was **not a residue of this quarter** but a missing
component of the *supplier's* `CtxOk2`.  `CtxOk2D` adds it.  What
follows is the receipt: the same statement, with `CtxOk2D` in place of
`CtxOk2`, is a **theorem, premise-free**.

*What this does and does not establish.*  It is true by construction —
`CtxOk2D`'s fourth conjunct is `CtxOk2Ann`, and `CtxAnn2` is that
conjunct read at one leaf — so on its own it is bookkeeping.  The
content is elsewhere and is already landed:

1. the conjunct **survives every constructor in the kit**
   (`CtxOk2Ann`'s survival lemmas in `Step2/Dispatch.lean`, lifted to
   `CtxOk2D` in `Interp2/CtxOk2D.lean`) — so adding it costs no site a
   new obligation;
2. the conjunct is **not vacuous** (`CtxOk2D.nonvacuous`), so the
   retirement is not an artifact of an empty hypothesis;
3. `inferStep2D_of` closes with **no `ctx_ann` field**, which is the
   only evidence that actually matters.

Stated anyway, because a retired residue that no declaration mentions
is a retirement nobody can check. -/

/-- `CtxAnn2` in the new currency. -/
def CtxAnn2D {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d idx : Nat} {n : Name} {ty : Expr} {Δa : List AVExpr}
    {tya : AVExpr},
    CtxOk2D m μ φ F d Δa (.fvar idx n ty) →
    denote2 μ m.acval env φ F d ty = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya

/-- **The residue is discharged.**  No environment shape, no fuel
condition, no mode, no level assignment, no extra premise. -/
theorem ctxAnn2D_of {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : CtxAnn2D m μ φ :=
  fun hC hden => CtxOk2Ann.fvar_leaf hC.toAnn _ hden

end Setlec.SetR.Interp2
