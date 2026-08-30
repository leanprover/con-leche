import Setlec.SetR.Interp2.Claims2U
import Setlec.SetR.Interp2.EnvS2UPi
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

/-- **`MemberBlock2` at an already-stored constant.**  Membership from
the environment's own `mem_type2`; truthfulness from `InferClaims2U`
applied to the install's `ensureSort` run on the stored type; the
existence conjunct from the given annotation, with the fuel slack
supplied by `denote2_fuelMono`.

The inferred type is taken as a literal `.sort`, which is what
`ensureSort` guarantees at every stored type — and it is what makes
the claim's *other* dual-success premise free, since `denote2` answers
on a sort at every fuel. -/
theorem memberBlock2_of_stored (m : EnvS2U V env) {fuel F₀ : Nat}
    {ψ : Name → Nat} {c : ConstantInfo} {ta : AVExpr} {u : Level}
    (hinf : InferClaims2U μ m ψ fuel)
    (hc : c ∈ env.consts)
    (hrun : inferTypeCore μ env fuel 0 c.toConstantVal.type
      = .ok (.sort u))
    (hws : Expr.WScoped 0 c.toConstantVal.type)
    (hb : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (hnil : c.toConstantVal.type.fvarLeaves = [])
    (hta : denote2 μ m.acval env ψ F₀ 0 c.toConstantVal.type
      = some ta) :
    MemberBlock2 V μ env m.acval ψ c.toConstantVal := by
  have hL : Expr.LeavesBounded c.toConstantVal.type := by
    intro l hl; rw [hnil] at hl; exact absurd hl (by simp)
  intro F
  refine ⟨max F F₀, ta, Nat.le_max_left _ _,
    denote2_fuelMono (Nat.le_max_right _ _) 0 _ hta, fun ρ => ?_⟩
  refine ⟨m.mem_type2 μ ψ F₀ c hc ta hta ρ, ?_⟩
  exact (hinf hrun hws hb hL (CtxOk2DU.of_closed hnil) hta
    (denote2_sort m.acval F₀ 0 u)).1 ρ (Sat2_nil V ρ)

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
    (hbound : ∀ c ∈ env.consts,
      ConstsBound env c.toConstantVal.type ∧
      (∀ cv value hint, c = .defnInfo cv value hint →
        ConstsBound env value) ∧
      (∀ cv value, c = .thmInfo cv value → ConstsBound env value))
    (hmem : ∀ (ν : CheckMode) (ψ : Name → Nat),
      MemberBlock2 V ν ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
        (acvalWith m.acval cvA.name A) ψ cvA) :
    DeclStep2 V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩ := by
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

/-! ## The three sweeps

**1. Smallest fuel.** `memberBlock2_of_stored` is the only theorem
here whose conclusion asserts a `denote2` success, and it asserts one
it was given, at a fuel it chooses (`max F F₀`).  `ReducePin2` and
`DeclStep2` assert none.

**2. Vacuity.** `reduceOpFits2_witness` shows the one premise this
file adds is satisfiable at a non-empty domain;
`memberBlock2_piProbe` is `MemberBlock2` at a stored type whose
annotation the checker has to compute; `nonempty_envS2U_piProbe`
(section 2) inhabits `DeclStep2`'s subject one binder past the first
probe.  The claims themselves are inhabited at every `EnvS2` by
`checkSound2E` and the `Iff.rfl` bridges of `Claims2U.lean`.

**3. Tombstones.** Files added, none edited. -/

end Setlec.SetR.Interp2
