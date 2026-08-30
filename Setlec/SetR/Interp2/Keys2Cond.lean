import Setlec.SetR.Interp2.Claims2U
import Setlec.SetR.Interp2.EnvS2UPi
import Setlec.SetR.Interp2.EnvS2UDef
import Setlec.SetR.Interp2.Denote2Extend
import Setlec.SetR.Interp2.Step2.DefEqRun
import Setlec.SetR.Interp2.Keys2Probe

/-!
# The install keys, conditional on the claims — scope ruling (ii)

Seal 38 found the keys blocked on a tier that does not exist: every
v1 key's V content is proved through relational soundness over
`interp`, and there is no `interp2` counterpart.  Seal 39 ruled the
exit: **the keys re-route through the checker-run claims**, conditional
on the same residue set `checkSound2*` already carries.

Section 1 of this batch made that possible by re-pointing the claims
to `EnvS2U` (`Claims2U.lean`).  This file takes the route.

## The shape of a conditional key

Each theorem below concludes a key of `Keys2.lean` from

* **the install's own run** — the `isDefEqCore`/`inferTypeCore` call
  the checker actually made, as an `.ok` hypothesis;
* **the corresponding claim** at the environment's `EnvS2U`, which is
  what converts that run into an `interp2` fact;
* **V-free side conditions** the install already establishes.

No new axiom, no named semantic hypothesis: every premise is either a
checker run, a claim, or syntax.

## Where each key still costs something, stated up front

* **`ReducePin2`** — one extra premise, `ReduceOpFits2`: the
  operation's leaf is a function on the element type.  It is not
  slack.  Generation six's `DefEqClaims2*` takes `AnnotOk2` of **both**
  compared annotations as premises, and the certificate's left side is
  an application, whose `AnnotOk2` clause *is* "the head is a function
  and the argument is in its domain".  The environment supplies it —
  it is `mem_type2` at the operation's pinned type `∀ n : Elem, Elem`
  — as soon as that type annotates.  So the premise names the
  `Denote2Total` dependency instead of hiding it inside the proof.
* **`MemberBlock2`** — its existence conjunct is a `denote2` success
  as a *conclusion*, which no dual-success claim can produce.  The
  conditional form takes the annotation as a premise, which is exactly
  where generation six put every other one.
* **`DeclStep2`** — a construction, not a transport: the old
  constants' fields move by `denote2_envExtend`, and the new
  constant's `mem_type2` is `MemberBlock2`.

## What the re-point bought, and what it did not

Seal 46 re-pointed the quarters, so `checkSound2E` applies at the
install's own `EnvS2U` and no bridge residue is carried.  Two things
follow, and only two:

* the keys land on `CheckStep2E` directly
  (`reducePin2_of_checkStep`, `memberBlock2_of_checkStep`) — the
  claim premises stop being objects a caller must build;
* the *syntactic* premises two of the keys carried are read off
  `EnvS.wf` instead (`constsBound_of_constsResolve`,
  `envWF_constsBound`) — three at `memberBlock2_of_stored` and
  `hbound` at `declStep2_of_axiom`, four premises retired outright.

What it did **not** buy is any `denote2`-existence fact.  Every
remaining premise of every key below is either a checker run, a
syntactic side condition the invariant does not carry, or
`Denote2Total` at a named subject — and the last kind is exactly the
residue seal 33 parked.  Seal 40's non-uniformity stands: the member
keys' membership half is install-tier supplied, because `MemberValR`
pins by `Expr.eqUpToNames` and a standard axiom has no value to
infer.

## Vacuity — the check this file most needs

A key discharged from premises that cannot be met says nothing.  Each
theorem below is followed by an instance at a real environment:
`reducePin2_of_claims` at the identity witness, and the two
`EnvS2U` probes for the rest.  The claims themselves are inhabited at
any `EnvS2` by `checkSound2E` and `whnfCoreClaims2U_iff`
(`Claims2U.lean`), so conditioning on them is not conditioning on
nothing.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  reduceElemName reduceElemTy reduceCertVar isDefEqCore
  inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {μ : CheckMode} {φ : Name → Nat}

/-! ## Shared: what a constant leaf contributes -/

/-- **A leaf's interpretation does not read the environment.**  From
`acval_erase` and the collapse lane's `cval_closed`: the annotated
leaf erases to a closed `VExpr`, and `interp2` only ever reads a
bound index. -/
theorem acval_interp2_closed (m : EnvS2U V env) (n : Name)
    (ψ : Name → Nat) (ρ ρ' : Nat → V) :
    interp2 V ρ (m.acval n ψ) = interp2 V ρ' (m.acval n ψ) :=
  interp2_closed V
    (by rw [m.acval_erase]; exact m.base.cval_closed n ψ) ρ ρ'

/-! ## What the environment invariant already supplies

Three of the keys' premises below were carried because nobody had
checked `EnvWF` for them.  `ConstsBound` is `Expr.constsResolve` read
as a proposition, *weakened* at the literal and projection clauses
(where it is the `| _ => True` catch-all), so the invariant's own
`constsResolve` conjunct implies it — and `EnvS.wf` carries that
conjunct for every stored type and every stored `def`/`thm` body.

This is the opposite verdict to seal 44's: `EnvWF` is purely
syntactic, so it cannot supply the *run* facts `Denote2Bodies` wants,
but it does supply every *syntactic* one, and the keys were paying for
those twice. -/

/-- `constsResolve` is the decidable form of `ConstsBound`, and
strictly stronger: it additionally pins the literal-support block and
a projection's structure name. -/
theorem constsBound_of_constsResolve {env₀ : Env} :
    ∀ e : Expr,
      Expr.constsResolve env₀ e = true → ConstsBound env₀ e := by
  intro e
  induction e with
  | bvar i => intro _; simp
  | sort u => intro _; simp
  | lit l => intro _; simp
  | const n us =>
    intro h
    rw [constsBound_const]
    simpa [Expr.constsResolve] using h
  | fvar idx n ty ih =>
    intro h
    rw [constsBound_fvar]
    exact ih (by simpa [Expr.constsResolve] using h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam n ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE n ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE n ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_letE.mpr ⟨ihty h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i e ihe =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_proj.mpr (ihe h.2)

/-- **`declStep2_of_axiom`'s `hbound` premise, from the invariant.**
Every stored type and every stored `def`/`thm` body is prefix-bound,
because `ConstWF` says it resolves. -/
theorem envWF_constsBound {env : Env} (hwf : EnvWF env) :
    ∀ c ∈ env.consts,
      ConstsBound env c.toConstantVal.type ∧
      (∀ cv value hint, c = .defnInfo cv value hint →
        ConstsBound env value) ∧
      (∀ cv value, c = .thmInfo cv value → ConstsBound env value) := by
  intro c hc
  obtain ⟨-, -, hty, -, hdefn, -, hthm⟩ := hwf c hc
  exact ⟨constsBound_of_constsResolve _ hty,
    fun cv value hint heq =>
      constsBound_of_constsResolve _ (hdefn cv value hint heq).2.2.1,
    fun cv value heq =>
      constsBound_of_constsResolve _ (hthm cv value heq).2.2.1⟩

/-! ## `ReducePin2` -/

/-- The element type is the pinned constant, in both spellings. -/
theorem reduceElemTy_const (c : Name) :
    reduceElemTy c = .const (reduceElemName c) [] := by
  unfold reduceElemTy reduceElemName
  split <;> rfl

/-- …so it annotates to the element's own leaf, at every fuel and
depth: the element inductive is stored level-monomorphically. -/
theorem denote2_reduceElemTy (m : EnvS2U V env) {c : Name}
    {ciE : ConstantInfo}
    (hfE : env.find? (reduceElemName c) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = []) (F d : Nat) :
    denote2 μ m.acval env φ F d (reduceElemTy c)
      = some (m.acval (reduceElemName c) φ) := by
  rw [reduceElemTy_const, denote2_const hfE (by rw [hlpE]; rfl), hlpE,
    show Level.substFn φ ([] : List Name) ([] : List Level) = φ from by
      simpa using substFn_param_self φ []]

/-- **The premise `ReducePin2` needs that the certificate does not
carry.**  Generation six's defeq claim takes `AnnotOk2` of both sides,
and the certificate's left side is `valA a` — an application, whose
`AnnotOk2` clause asserts precisely that the head is a function whose
domain holds the argument.

This is the environment's `mem_type2` at the operation's pinned type
`∀ n : Elem, Elem`, and naming it here is the honest alternative to
assuming the pinned type annotates. -/
def ReduceOpFits2 (V : Type w) [SetTheory V]
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat)
    (c : Name) : Prop :=
  ∀ ρ : Nat → V, ∃ (v : Nat) (B : V → V),
    interp2 V ρ (acval c φ) ∈ˢ
        piR v (interp2 V ρ (acval (reduceElemName c) φ)) B ∧
      (v = 0 → ∀ x, x ∈ˢ interp2 V ρ (acval (reduceElemName c) φ) →
        B x ∈ˢ (univZero : V))

/-- **`ReducePin2`, from the install's own run.**  `checkReducePin`
compares `valA a` with `a` at depth `1` over the one-entry element
context; `DefEqClaims2U` turns that verdict into the `interp2`
identity the key asserts.

The v1 discharge cashed a `DefEq` *derivation* through `DefEq.sound`
(seal 38: there is no such soundness over `interp2`).  This one cashes
the *run* instead, which is what route (ii) means. -/
theorem reducePin2_of_claims (m : EnvS2U V env) {fuel F : Nat}
    {c : Name} {valA : Expr} {ciE : ConstantInfo}
    (hdeq : DefEqClaims2U μ m φ fuel)
    (hfE : env.find? (reduceElemName c) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = [])
    (hvf : valA.hasFvar = false)
    (hvb : valA.looseBVarsBounded 0 = true)
    (hva : denote2 μ m.acval env φ F 1 valA = some (m.acval c φ))
    (hfits : ReduceOpFits2 V m.acval φ c)
    (hrun : isDefEqCore μ env fuel 1
      (.app valA (reduceCertVar c)) (reduceCertVar c) = .ok true) :
    ReducePin2 V env m.acval φ c := by
  -- the certificate's syntax
  have hnilE : (reduceElemTy c).fvarLeaves = [] := by
    rw [reduceElemTy_const]; simp [Expr.fvarLeaves]
  have hcertLeaves : (reduceCertVar c).fvarLeaves
      = [(0, Name.str .anonymous "a", reduceElemTy c)] := by
    rw [reduceCertVar, Expr.fvarLeaves, hnilE]
  have hvaNil : valA.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf
  have happLeaves : (Expr.app valA (reduceCertVar c)).fvarLeaves
      = [(0, Name.str .anonymous "a", reduceElemTy c)] := by
    rw [Expr.fvarLeaves, hvaNil, hcertLeaves]; rfl
  -- the context predicate at any subject with only that leaf
  have hctx : ∀ e : Expr,
      e.fvarLeaves = [(0, Name.str .anonymous "a", reduceElemTy c)] →
      CtxOk2DU m μ φ F 1 [m.acval (reduceElemName c) φ] e := by
    intro e he
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · intro l hl
      rw [he] at hl
      obtain rfl := List.mem_singleton.mp hl
      refine ⟨by omega, ?_, m.acval (reduceElemName c) φ,
        m.acval (reduceElemName c) φ, ?_, rfl, ?_⟩
      · rw [reduceElemTy_const]; trivial
      · exact denote2_reduceElemTy m hfE hlpE F 1
      · exact fun ρ _ => acval_interp2_closed m _ _ _ _
    · intro l hl tya htya
      rw [he] at hl
      obtain rfl := List.mem_singleton.mp hl
      rw [denote2_reduceElemTy m hfE hlpE F 1] at htya
      obtain rfl : tya = m.acval (reduceElemName c) φ :=
        (Option.some.inj htya).symm
      exact fun ρ _ => m.acval_ok2 _ _ ρ
  -- the leaf annotations are bvar-closed
  have hLb : ∀ e : Expr,
      e.fvarLeaves = [(0, Name.str .anonymous "a", reduceElemTy c)] →
      Expr.LeavesBounded e := by
    intro e he l hl
    rw [he] at hl
    obtain rfl := List.mem_singleton.mp hl
    rw [reduceElemTy_const]
    rfl
  -- the two annotated sides
  have hdenA : denote2 μ m.acval env φ F 1
      (.app valA (reduceCertVar c))
      = some (.app (m.acval c φ) (.bvar 0)) := by
    rw [denote2_app, hva, reduceCertVar, denote2_fvar]
    rfl
  have hdenB : denote2 μ m.acval env φ F 1 (reduceCertVar c)
      = some (.bvar 0) := by
    rw [reduceCertVar, denote2_fvar]
  -- scoping
  have hwsCert : Expr.WScoped 1 (reduceCertVar c) := by
    rw [reduceCertVar, Expr.WScoped]
    exact ⟨by omega, by rw [reduceElemTy_const, Expr.WScoped]; trivial⟩
  have hbCert : (reduceCertVar c).looseBVarsBounded 0 = true := by
    rw [reduceCertVar, reduceElemTy_const]; rfl
  refine ⟨by rw [hfE]; rfl, ?_⟩
  intro ρ x hx
  have hsat : Sat2 V [m.acval (reduceElemName c) φ] (cons x ρ) :=
    Sat2_cons V (Sat2_nil V ρ) hx
  have hokA : ∀ ρ' : Nat → V,
      Sat2 V [m.acval (reduceElemName c) φ] ρ' →
      AnnotOk2 V ρ' (.app (m.acval c φ) (.bvar 0)) := by
    intro ρ' hρ'
    rw [AnnotOk2_app]
    obtain ⟨v, B, hmem, hz⟩ := hfits ρ'
    refine ⟨m.acval_ok2 c φ ρ', by simp, v,
      interp2 V ρ' (m.acval (reduceElemName c) φ), B, hmem, ?_, hz⟩
    rw [interp2_bvar,
      acval_interp2_closed m (reduceElemName c) φ ρ'
        (fun j => ρ' (j + 0 + 1))]
    exact hρ' 0 _ rfl
  have hwsApp : Expr.WScoped 1 (.app valA (reduceCertVar c)) := by
    rw [Expr.WScoped]
    exact ⟨Expr.WScoped.mono (Nat.zero_le 1)
      (Expr.WScoped.of_not_hasFvar hvf), hwsCert⟩
  have heq := hdeq hrun hwsApp
    (by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hvb, hbCert⟩)
    (hLb _ happLeaves) hwsCert hbCert (hLb _ hcertLeaves)
    (hctx _ happLeaves) (hctx _ hcertLeaves) hdenA hdenB hokA
    (fun _ _ => by simp) (cons x ρ) hsat
  rw [interp2_app, interp2_bvar] at heq
  rw [acval_interp2_closed m c φ ρ (cons x ρ)]
  exact heq


/-- **The added premise is satisfiable, and not by an empty domain.**
At `Keys2Probe`'s witness valuation the element leaf is `Prop` — a
non-empty set — and the operation's leaf is the identity graph over
it, so the `piR` membership is a real one. -/
theorem reduceOpFits2_witness (φ : Name → Nat) :
    ReduceOpFits2 V reduceAcvalW φ Setlec.reduceNatName := by
  have hnat : reduceElemName Setlec.reduceNatName = Setlec.natName := by
    rw [reduceElemName, if_pos rfl]
  have helem : reduceAcvalW (reduceElemName Setlec.reduceNatName) φ
      = .sort 0 := by
    rw [hnat, reduceAcvalW, if_pos rfl]
  have hop : reduceAcvalW Setlec.reduceNatName φ
      = .lam 1 (.sort 0) (.bvar 0) := by
    rw [reduceAcvalW,
      if_neg (show Setlec.reduceNatName ≠ Setlec.natName by decide)]
  intro ρ
  refine ⟨1, fun _ => (univ 0 : V), ?_, fun h => nomatch h⟩
  rw [helem, hop, interp2_lam, interp2_sort]
  exact lamR_mem fun x hx => by rw [interp2_bvar]; exact hx

/-! ## `MemberBlock2`

The key asserts a `denote2` **success** as a conclusion, which no
dual-success claim can produce — that half is `Denote2Total`, parked
at seal 33, and it stays a premise here.  What the claims do supply is
the *truthfulness* conjunct, and what the environment supplies is the
*membership* conjunct.

**A finding about route (ii)'s reach, recorded rather than routed
around.**  The brief named the install's own runs as the bridge, and
for `ReducePin2` they are — `checkReducePin` runs `isDefEq`.  For
`MemberKeyS`/`StdAxiomKeyS` they are **not**: `MemberValR`'s
model-counterpart pin is `Expr.eqUpToNames` — a *syntactic* rename
check, not a checker verdict — and a standard axiom has no value to
infer at all.  So neither key has a defeq run for route (ii) to cash;
their membership content is model-side, and the claims reach only the
`AnnotOk2` conjunct.  That is what the theorem below routes. -/

/-- The stored type's frame facts, all four read off `EnvWF` — the
shape both keys below open with. -/
theorem storedType_frames2 (m : EnvS2U V env) {c : ConstantInfo}
    (hc : c ∈ env.consts) :
    Expr.WScoped 0 c.toConstantVal.type ∧
      c.toConstantVal.type.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded c.toConstantVal.type ∧
      c.toConstantVal.type.fvarLeaves = [] := by
  obtain ⟨hfv, -, -, hb, -⟩ := m.base.wf c hc
  have hnil : c.toConstantVal.type.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  exact ⟨Expr.WScoped.of_not_hasFvar hfv, hb,
    fun l hl => absurd (hnil ▸ hl) (by simp), hnil⟩

/-- **`MemberBlock2` at an already-stored constant.**  Membership from
the environment's own `mem_type2`; truthfulness from `InferClaims2U`
applied to the install's `inferType` run on the stored type; the
existence conjunct from the given annotation, with the fuel slack
supplied by `denote2_fuelMono`.

**The run premise is the front door's own, not a fused one.**
`checkConstantVal` (`Kernel/CheckerBase.lean:88-89`) infers the type
to an *intermediate* `stype` and only then `ensureSort`s it, so
`inferTypeCore … = .ok (.sort u)` — the shape this key demanded until
seal 48 — is strictly stronger than anything the checker produces.
Taking `stype` instead makes the premise dischargeable from
`ConstantValR`'s exposed chain, and costs exactly one thing: the
literal-sort form supplied the claim's *other* dual-success premise
for free (`denote2` answers on a sort at every fuel), and at an
arbitrary `stype` it must be supplied — `hsty` below.

`hsty` is `Denote2TotalR`'s content at this run (`Dual2E.lean`), i.e.
the same parked existence residue as `hta`, one term further along;
`memberBlock2_of_checkStep` names it as the factor it is.  The
`ensureSort` half of the chain is **not** consumed here: `MemberBlock2`
asks only for the subject's `AnnotOk2`, and nothing in it turns on the
inferred type being — or reducing to — a sort. -/
theorem memberBlock2_of_stored (m : EnvS2U V env) {fuel F₀ F₁ : Nat}
    {ψ : Name → Nat} {c : ConstantInfo} {ta sa : AVExpr}
    {stype : Expr}
    (hinf : InferClaims2U μ m ψ fuel)
    (hc : c ∈ env.consts)
    (hrun : inferTypeCore μ env fuel 0 c.toConstantVal.type
      = .ok stype)
    (hsty : denote2 μ m.acval env ψ F₁ 0 stype = some sa)
    (hta : denote2 μ m.acval env ψ F₀ 0 c.toConstantVal.type
      = some ta) :
    MemberBlock2 V μ env m.acval ψ c.toConstantVal := by
  obtain ⟨hws, hb, hL, hnil⟩ := storedType_frames2 m hc
  intro F
  refine ⟨max F F₀, ta, Nat.le_max_left _ _,
    denote2_fuelMono (Nat.le_max_right _ _) 0 _ hta, fun ρ => ?_⟩
  refine ⟨m.mem_type2 μ ψ F₀ c hc ta hta ρ, ?_⟩
  exact (hinf hrun hws hb hL (CtxOk2DU.of_closed hnil) hta
    hsty).1 ρ (Sat2_nil V ρ)

/-- **The key at a stored type with a binder** — `memberBlock2_probe`
one binder further out, and unconditional.  Section 2's probe is the
subject, so the existence conjunct is not free: it costs the checker
two `sortOfE` runs and is `none` below fuel `2`. -/
theorem memberBlock2_piProbe (μ : CheckMode) (ψ : Name → Nat) :
    MemberBlock2 V μ piProbeEnv piProbeAcval ψ
      piProbeCi.toConstantVal := by
  intro F
  refine ⟨max F 2, .pi 1 1 (.sort 0) (.sort 0), Nat.le_max_left _ _,
    piProbe_denote2_ty (Nat.le_max_right _ _), fun ρ => ⟨?_, ?_⟩⟩
  · rw [show piProbeAcval piProbeCi.toConstantVal.name ψ
        = AVExpr.lam 1 (.sort 0) (.bvar 0) from piProbeAcval_head ψ,
      interp2_lam, interp2_pi, interp2_sort]
    exact lamR_mem fun x hx => by rw [interp2_bvar]; exact hx
  · rw [AnnotOk2_pi]
    exact ⟨by simp, fun _ _ => by simp⟩

/-! ## `DeclStep2` -/

/-- **`DeclStep2` at a fresh axiom install.**  The construction seal
38 said was blocked "exactly at `MemberBlock2` and nowhere else" —
here with `MemberBlock2` as a premise, so what the theorem shows is
that *nothing else* is missing.

Five of the nine fields extend by `Install2.lean`'s lemmas; the two
`denote2` fields and `mem_type2` compose two steps —
`denote2_acvalWith_fresh` at the prefix and `Denote2EnvExtend` across
the install.  The order matters: the valuation congruence cannot run
at the *extended* environment, because there the new name is stored
and is exactly where the two valuations differ. -/
theorem declStep2_of_axiom (m : EnvS2U V env) {cvA : ConstantVal}
    {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? cvA.name = none)
    (hbase : EnvS V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩)
    (hag : ∀ n, n ≠ cvA.name → m.base.cval n = hbase.cval n)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval cvA.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cvA.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hext : ∀ (ν : CheckMode) (ψ : Name → Nat),
      Denote2EnvExtend ν env
        ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
        (acvalWith m.acval cvA.name A) ψ)
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
        (acvalWith m.acval cvA.name A) ψ cvA) :
    DeclStep2 V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩ := by
  -- the prefix-boundness of the stored material is the invariant's
  have hbound := envWF_constsBound m.base.wf
  -- no stored constant carries the fresh name
  have hne : ∀ c ∈ env.consts, c.name ≠ cvA.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  -- the two-step composition, once
  have hcomp : ∀ (ν : CheckMode) (ψ : Name → Nat) (F d : Nat)
      (e : Expr), ConstsBound env e →
      denote2 ν (acvalWith m.acval cvA.name A)
          ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩ ψ F d e
        = denote2 ν m.acval env ψ F d e := by
    intro ν ψ F d e hcb
    rw [← hext ν ψ F d e hcb, denote2_acvalWith_fresh hfresh d e]
  refine ⟨{
    base := hbase
    acval := acvalWith m.acval cvA.name A
    acval_erase := ?_
    acval_closed := acvalWith_closed m.acval_closed hAclosed
    acval_params := acvalWith_params (c₀ := .axiomInfo cvA)
      m.acval_params hAparams
    acval_ok2 := acvalWith_ok2 m.acval_ok2 hAok
    acval_defn := ?_
    acval_thm := ?_
    mem_type2 := ?_ }⟩
  · -- `acval_erase`
    intro n ψ
    by_cases hn : n = cvA.name
    · subst hn; rw [acvalWith_self]; exact hAerase ψ
    · rw [acvalWith_ne hn, m.acval_erase, hag n hn]
  · -- `acval_defn`: the head is an axiom, so only stored `def`s apply
    intro ν ψ F cv value hint hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · exact nomatch h
    · rw [hcomp ν ψ F 0 value ((hbound _ h).2.1 cv value hint rfl)]
        at hra
      rw [acvalWith_ne (show cv.name ≠ cvA.name from hne _ h)]
      exact m.acval_defn ν ψ F cv value hint h hra
  · -- `acval_thm`
    intro ν ψ F cv value hc ra hra
    rcases List.mem_cons.mp hc with h | h
    · exact nomatch h
    · rw [hcomp ν ψ F 0 value ((hbound _ h).2.2 cv value rfl)] at hra
      rw [acvalWith_ne (show cv.name ≠ cvA.name from hne _ h)]
      exact m.acval_thm ν ψ F cv value h hra
  · -- `mem_type2`
    intro ν ψ fuel c hc ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h
      obtain ⟨F', ta', hle, hden', hall⟩ := hmem ν ψ fuel
      obtain rfl : ta = ta' :=
        Option.some.inj
          ((denote2_fuelMono hle 0 _ hta).symm.trans hden')
      exact (hall ρ).1
    · rw [hcomp ν ψ fuel 0 _ (hbound _ h).1] at hta
      rw [acvalWith_ne (hne _ h)]
      exact m.mem_type2 ν ψ fuel c h ta hta ρ

/-! ## Supplying the claims the three theorems above consume

Each key here is conditional on a `…2U` claim **at the install's own
`EnvS2U`** — the currency was already re-pointed at seal 40, so
nothing above consumes a `…2E` claim through a bridge.  What was
missing is the *supplier*.

**The residue is gone, and the re-point is why.**  Until the quarters
were re-pointed, `checkStep2U_of_2E` bought `CheckStep2U` only from
`EnvS2UInImage`, and the keys dodged the `∀ env` quantifier by taking
the *pointwise* residue instead (`claims2U_of_bodies`, deleted here:
its two hypotheses became unused binders).  With `CheckStep2E`
**stated at `EnvS2U`**, `checkSound2E` applies at the install's own
environment directly and no residue is carried at all.

`EnvS2UInImage` itself stays — it is still the honest statement of
what separates the two structures, and `EnvS2UDef.lean`'s
biconditional still characterises it.  What changed is that the
claims no longer need it. -/

/-- **The four claims at one `EnvS2U`.**  The `Iff.rfl` bridges of
`Claims2U.lean` are what make the conclusion the `…2U` family while
the proof is `checkSound2E`. -/
theorem claims2U_of_2E {m : EnvS2U V env} (h : CheckStep2E μ V)
    (ψ : Name → Nat) (fuel : Nat) :
    WhnfCoreClaims2U μ m ψ fuel ∧ WhnfClaims2U μ m ψ fuel ∧
      DefEqClaims2U μ m ψ fuel ∧ InferClaims2U μ m ψ fuel :=
  checkSound2E h m ψ fuel

/-- **The two claims this file's keys consume, at an environment that
stores a definition.**  Both earlier probes are axiom-only, so before
`EnvS2UDef.lean` the keys' claim premises were only ever inhabited at
environments where `acval_defn` says nothing. -/
theorem claims2U_lamDef (h : CheckStep2E μ V) (ψ : Name → Nat)
    (fuel : Nat) :
    DefEqClaims2U μ (lamDefEnvS2U V) ψ fuel ∧
      InferClaims2U μ (lamDefEnvS2U V) ψ fuel :=
  let c := claims2U_of_2E (m := lamDefEnvS2U V) h ψ fuel
  ⟨c.2.2.1, c.2.2.2⟩

/-! ### The keys at the lane's single named residue

With the quarters re-pointed there is nothing between a key and
`CheckStep2E` — the hypothesis `Capstone2E` assembles from the fifteen
residues.  These two corollaries are the landing: neither carries a
claim a caller has to build, and what is left in each premise list is
the honest cost, itemised at the stopping report below. -/

/-- **`ReducePin2`, landed.**  Cost after the landing: the install's
own `isDefEq` run, `valA`'s two syntactic guards, the element
constant's lookup and monomorphism — and the two `denote2` facts
(`hva`, `hfits`) that are `Denote2Total` at the operation's value and
at its pinned type. -/
theorem reducePin2_of_checkStep (m : EnvS2U V env) {fuel F : Nat}
    {c : Name} {valA : Expr} {ciE : ConstantInfo}
    (h : CheckStep2E μ V)
    (hfE : env.find? (reduceElemName c) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = [])
    (hvf : valA.hasFvar = false)
    (hvb : valA.looseBVarsBounded 0 = true)
    (hva : denote2 μ m.acval env φ F 1 valA = some (m.acval c φ))
    (hfits : ReduceOpFits2 V m.acval φ c)
    (hrun : isDefEqCore μ env fuel 1
      (.app valA (reduceCertVar c)) (reduceCertVar c) = .ok true) :
    ReducePin2 V env m.acval φ c :=
  reducePin2_of_claims m (claims2U_of_2E h φ fuel).2.2.1 hfE hlpE hvf
    hvb hva hfits hrun

/-- **`MemberBlock2`, landed.**  Cost after the landing: membership in
the environment, the type front door's own `inferType` run, the
stored type's annotation — and `InferExists2E`, the inference
existence factor (`Dual2E.lean`), which is what supplies the
annotation of the run's *result*.  The three syntactic premises the
key used to carry are now read off `EnvS.wf`, and the `AnnotOk2`
conjunct is entirely the claim's.

`hex` is named rather than inlined because it is the honest leftover:
`ConstantValR`'s exposed chain discharges `hrun` on the nose, and
`hex` is the one premise the front door does **not** supply. -/
theorem memberBlock2_of_checkStep (m : EnvS2U V env) {fuel F₀ : Nat}
    {ψ : Name → Nat} {c : ConstantInfo} {ta : AVExpr} {stype : Expr}
    (h : CheckStep2E μ V)
    (hex : InferExists2E μ m ψ fuel)
    (hc : c ∈ env.consts)
    (hrun : inferTypeCore μ env fuel 0 c.toConstantVal.type
      = .ok stype)
    (hta : denote2 μ m.acval env ψ F₀ 0 c.toConstantVal.type
      = some ta) :
    MemberBlock2 V μ env m.acval ψ c.toConstantVal :=
  let f := storedType_frames2 m hc
  let e := hex hrun f.1 f.2.1 f.2.2.1
    (CtxOk2DU.of_closed f.2.2.2) hta
  memberBlock2_of_stored m (claims2U_of_2E h ψ fuel).2.2.2 hc hrun
    e.choose_spec.choose_spec.2 hta

/-! ### The gate: does the exposure's consumer apply on the nose?

The composition below is the check itself, run as a theorem rather
than asserted in prose.  It takes `ConstantValR` **at the environment
the front door ran in** and produces `MemberBlock2` at an environment
that stores the constant, and every premise it needs beyond those two
is visible in its signature.

**Verdict: the run premise applies on the nose; two obligations
remain, and neither is supplied by the front door.**

1. `hE : EnvExtendStable μ env₀ env` — the *environment* crossing.
   `checkConstantVal` runs at the prefix; the key needs the run where
   the constant is already stored.  This is the forward direction, so
   the Θ lane's named hypothesis is the right shape, and its
   `ConstsBound` side condition is free — `ConstantValR`'s own
   `constsResolve` conjunct gives it.  A *named* hypothesis, still not
   a proved one.
2. `hex : InferExists2E μ m ψ fuel` — the annotation of the run's
   *result*.  Parked independently (`Dual2E.lean`), and not something
   any amount of exposure on the checker side can produce.

What the exposure **did** close is `hrun`: before it, the key demanded
`inferTypeCore … = .ok (.sort u)`, which `checkConstantVal` never
produces at all, so no supplier could have discharged it.  The chain's
first half discharges it exactly.  Its `ensureSort` half is unused
here, and `WhnfClaims2U` — seal 48's predicted cost — is not needed:
`MemberBlock2` asks for the subject's `AnnotOk2` and never for what
the inferred type reduces to. -/
theorem memberBlock2_of_constantValR (m : EnvS2U V env) {env₀ : Env}
    {fuel F₀ : Nat} {ψ : Name → Nat} {c : ConstantInfo}
    {cval : TConstVal} {cv : ConstantVal} {ta : AVExpr}
    (h : CheckStep2E μ V)
    (hex : InferExists2E μ m ψ fuel)
    (hE : EnvExtendStable μ env₀ env)
    (hcv : ConstantValR μ fuel env₀ cval cv c.toConstantVal.type)
    (hc : c ∈ env.consts)
    (hta : denote2 μ m.acval env ψ F₀ 0 c.toConstantVal.type
      = some ta) :
    MemberBlock2 V μ env m.acval ψ c.toConstantVal := by
  obtain ⟨stype, -, hrun, -⟩ := hcv.2.2.2.2.2.2.2.2.2.1
  exact memberBlock2_of_checkStep m h hex hc
    (hE.2.2.1
      (constsBound_of_constsResolve _ hcv.2.2.2.2.2.2.2.2.1) hrun)
    hta

/-- **The `env₀ = env` reading, for contrast.**  With no environment
crossing the transport disappears and the exposed chain feeds `hrun`
with nothing in between — which isolates `hex` as the *only* residue
the exposure leaves.  The hypothesis pair is contradictory at a
non-fresh name (`ConstantValR`'s first conjunct says `cv.name` is
absent), so this is a shape check on the discharge, not a usable
key: it is stated at an arbitrary `cv`, and `c` need not be `cv`. -/
theorem memberBlock2_of_constantValR_same (m : EnvS2U V env)
    {fuel F₀ : Nat} {ψ : Name → Nat} {c : ConstantInfo}
    {cval : TConstVal} {cv : ConstantVal} {ta : AVExpr}
    (h : CheckStep2E μ V)
    (hex : InferExists2E μ m ψ fuel)
    (hcv : ConstantValR μ fuel env cval cv c.toConstantVal.type)
    (hc : c ∈ env.consts)
    (hta : denote2 μ m.acval env ψ F₀ 0 c.toConstantVal.type
      = some ta) :
    MemberBlock2 V μ env m.acval ψ c.toConstantVal := by
  obtain ⟨stype, -, hrun, -⟩ := hcv.2.2.2.2.2.2.2.2.2.1
  exact memberBlock2_of_checkStep m h hex hc hrun hta

/-! ## The three sweeps

**1. Smallest fuel.** `memberBlock2_of_stored` is the only theorem
here whose conclusion asserts a `denote2` success, and it asserts one
it was given, at a fuel it chooses (`max F F₀`).  `ReducePin2` and
`DeclStep2` assert none.

**1a. Where each key stops.**  Recorded here so the report is in the
tree rather than only in a seal.

* `reducePin2_of_checkStep` — stops at `hva` and `hfits`, both
  `Denote2Total`: the operation's annotated value must annotate, and
  its pinned type `∀ n : Elem, Elem` must annotate for `mem_type2` to
  yield the `piR` membership.  Nothing else is semantic.
* `memberBlock2_of_checkStep` — stops at `hta` (`Denote2Total` at the
  stored type) and at `hex` (`InferExists2E`).  **`hrun` no longer
  stops it**: `ConstantValR` now records `checkConstantVal`'s own run
  chain, and the chain's first half discharges `hrun` on the nose.
  What the exposure does *not* close is `hex` — the annotation of the
  run's *result*, which is `Denote2TotalR`'s repair and is parked
  independently of anything the front door records.  The chain's
  `ensureSort` half is not consumed at all: reaching `MemberBlock2`'s
  `AnnotOk2` never asks what the inferred type reduces to, so
  `WhnfClaims2U` — the cost seal 48 predicted — buys nothing here.
* `declStep2_of_axiom` — stops at `hext` (`Denote2EnvExtend`, frozen
  on Θ), `hmem` (`MemberBlock2` at the new axiom, which is the
  install-tier half seal 40 measured), and `hbase`.  The `hbound`
  premise is gone.

**2. Vacuity.** `reduceOpFits2_witness` shows the one premise this
file adds is satisfiable at a non-empty domain;
`memberBlock2_piProbe` is `MemberBlock2` at a stored type whose
annotation the checker has to compute; `nonempty_envS2U_piProbe`
(section 2) inhabits `DeclStep2`'s subject one binder past the first
probe.  The claims themselves are inhabited at every `EnvS2` by
`checkSound2E` and the `Iff.rfl` bridges of `Claims2U.lean`, and
`claims2U_lamDef` inhabits the two *this file* consumes at an
environment that stores a **definition** — where `acval_defn` is not
vacuous, which no axiom-only probe could witness.

`memberBlock2_of_constantValR`'s premise pair is *not* contradictory:
`ConstantValR` speaks about `cv`, which is fresh at `env₀`, while the
key's `c` is stored at the extension — a prefix/extension pair, which
is the shape every install produces.  The `_same` variant is a shape
check only, and says so at its docstring: it needs `cv ≠ c` to be
inhabited, and is stated at an arbitrary `cv`.

**3. Tombstones.** Files added, none edited. -/

end Setlec.SetR.Interp2
