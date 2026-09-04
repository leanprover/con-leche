import Setlec.SetR.Install.Cons
import Setlec.SetR.Sound.Main
import Setlec.SetBase.Decl
import Setlec.Verify.Denote.SubstConst
import Setlec.Verify.Abstract

/-!
# The value-carrying installs (task #148, T5 stage a)

`def`, `theorem` and `opaque` are the same install: a checked constant
whose value front door certifies it against its annotated type, stored
and **valued by the value's denotation** — the choice `EnvS.defn_eq`
forces, exactly as `EnvTT.defn_eq` forces it in the TT lane
(`Setlec/TTVerify/DeclValue.lean`, whose organization this file
transposes).  The inputs here are `DeclR`'s per-kind premises (T2's
statements, T3's bridge obligations), not checker runs — the
case-bashing inversion work lives on the bridge side, and these
lemmas consume relation-shaped packs only.

The semantic key is `valueKeyS`: the front doors' `Infer`/`DefEq`
derivations pass through T4's soundness theorems (at `Sat`-trivial
`Δ = []`) and come out as memberships and truthfulness — the value's
`AnnotOkV` (the subject conjunct that supplies `EnvS.annot_okV`), its
membership in the denoted type's interpretation (via the unconditional
`DefEq.sound` — the linked-reshape pair of the T4 record), and the
denoted type's own truthfulness from the *type* front door's subject
conjunct.

The structural-`Nat` recurrence pack is discharged inline (its content
is `denote_substConst0` plus `DefEq.sound` — the relation pack already
carries the denote facts the TT lane's `NatOpPinTT` had to re-derive);
the WF-recursive div/mod pack and the compiler-trust identity are
stated as obligations (`DivModPinS`, `ReducePinS`) and discharged in
their own modules, mirroring `DivModPinTT`/`checkReducePin`'s split.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The front doors, semantically -/

/-- The type front door's yield at one assignment: the denoted
annotated type is truthful (its `Infer`-subject conjunct). -/
theorem typeFrontS {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValR μ F env m.cval cv type') (φ : Name → Nat) :
    ∃ Tv, denoteClosed m.cval env φ type' = some Tv ∧
      ∀ ρ : Nat → V, AnnotOkV V ρ Tv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfront⟩ := hcv
  obtain ⟨Tv, tT, u, hden, hInf, -⟩ := hfront φ
  exact ⟨Tv, hden, fun ρ =>
    (Infer.sound (m.toHyp φ) hInf ρ (Sat_nil V ρ)).1⟩

/-- The value front door's yield at one assignment: the denoted value
is truthful and inhabits the denoted type's interpretation, which is
itself truthful. -/
theorem valueKeyS {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) {cv : ConstantVal} {value type' value' : Expr}
    (hcv : ConstantValR μ F env m.cval cv type')
    (hvf : ValueFrontR μ F env m.cval cv value type' value')
    (φ : Name → Nat) :
    ∃ Vv Tv, denoteClosed m.cval env φ value' = some Vv ∧
      denoteClosed m.cval env φ type' = some Tv ∧
      ∀ ρ : Nat → V,
        AnnotOkV V ρ Vv ∧ interp V ρ Vv ∈ˢ interp V ρ Tv ∧
        AnnotOkV V ρ Tv := by
  obtain ⟨Tv, hTv, hTannot⟩ := typeFrontS m hcv φ
  obtain ⟨-, -, -, -, -, -, hfront⟩ := hvf
  obtain ⟨Tv', Vv, tv, hTv', hVv, hInf, hDeq⟩ := hfront φ
  rw [hTv] at hTv'
  obtain rfl := Option.some.inj hTv'
  refine ⟨Vv, Tv, hVv, hTv, fun ρ => ?_⟩
  obtain ⟨hsubj, hmem⟩ := Infer.sound (m.toHyp φ) hInf ρ (Sat_nil V ρ)
  have heq := DefEq.sound (m.toHyp φ) hDeq ρ (Sat_nil V ρ)
  exact ⟨hsubj, heq ▸ hmem, hTannot ρ⟩

/-! ## The shared install -/

/-- **The value-carrying install** — transpose of `extendValueTT`,
consuming the [set] key.

**The conclusion names the extension and its agreement**, not just
`Nonempty`.  A `Nonempty` is a one-way door: the interp2 tier's
`acval_erase` is an equation against `m'.cval`, so it cannot even be
*stated* against a witness the install threw away.  The agreement is
`Installs.ag` at the install's own `cvalAt` leaf, so exposing it costs
one term.  The family-law and reservation refutations
are discharged internally from the kind disequalities (the TT lane
repeats them per kind); the two `Nat` pin clauses and the
compiler-trust clause stay parameters, because each kind discharges
them differently (and most vacuously). -/
theorem extendValueS {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {name : Name} {lps : List Name} {type value : Expr}
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hfresh : env.find? name = none)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hvf : value.hasFvar = false)
    (hvb : value.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v t,
      denoteClosed m.cval env ψ value = some v ∧
      denoteClosed m.cval env ψ type = some t ∧
      ∀ ρ : Nat → V,
        AnnotOkV V ρ v ∧ interp V ρ v ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t)
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ lps, φ₁ p = φ₂ p) →
      denoteClosed m.cval env φ₁ value = denoteClosed m.cval env φ₂ value)
    (hc₀defn : ∀ cv2 value2 h2, c₀ = .defnInfo cv2 value2 h2 →
      value2 = value)
    (hc₀thm : ∀ cv2 value2, c₀ = .thmInfo cv2 value2 → value2 = value)
    (hc₀nrec : ∀ cv2 mI rP rules, c₀ ≠ .recInfo cv2 mI rP rules)
    (hc₀nind : ∀ cv2 caps, c₀ ≠ .indInfo cv2 caps)
    (hc₀nproj : ∀ entry, c₀ ≠ .projInfo entry)
    (hc₀nctor : ∀ cv2 cnP cnF, c₀ ≠ .ctorInfo cv2 cnP cnF)
    (hnres : reservedBasisNames.contains name = false)
    (hheadNat : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ φ : Name → Nat, ∀ eq ∈ natOpEquations 0 c₀.name, ∃ L R,
        denote (cvalAt m.cval env name value) ⟨c₀ :: env.consts⟩ φ 2 eq.1
          = some L ∧
        denote (cvalAt m.cval env name value) ⟨c₀ :: env.consts⟩ φ 2 eq.2
          = some R ∧
        ∀ (ρ : Nat → V) (x y : V),
          x ∈ˢ interp V ρ (cvalAt m.cval env name value natName
            (Level.substFn φ [] [])) →
          y ∈ˢ interp V ρ (cvalAt m.cval env name value natName
            (Level.substFn φ [] [])) →
          interp V (cons V y (cons V x ρ)) L
            = interp V (cons V y (cons V x ρ)) R)
    (hheadDivMod : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (cvalAt m.cval env name value natName
          (Level.substFn φ [] [])) →
        y ∈ˢ interp V ρ (cvalAt m.cval env name value natName
          (Level.substFn φ [] [])) →
        DivModClausesV V
          (fun n => interp V ρ (cvalAt m.cval env name value n
            (Level.substFn φ [] [])))
          c₀.name x y)
    (hheadReduce : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
          x ∈ˢ interp V ρ (cvalAt m.cval env name value
            (reduceElemName c₀.name) ψ) →
          SetTheory.app
            (interp V ρ (cvalAt m.cval env name value c₀.name ψ)) x
            = x) :
    ∃ m' : EnvS V ⟨c₀ :: env.consts⟩,
      (∀ n, n ≠ name → m.cval n = m'.cval n) ∧
      ∀ ψ : Name → Nat,
        denoteClosed m.cval env ψ value = some (m'.cval name ψ) := by
  have hfresh' : env.find? c₀.name = none := by rw [hc₀name]; exact hfresh
  have hi : Installs env m.cval (cvalAt m.cval env name value) c₀ :=
    Installs.of_fresh hfresh' (fun n hn => by
      rw [hc₀name] at hn; exact (cvalAt_ne hn).symm)
  refine ⟨EnvS.cons m hi hwf ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun cv2 mI rP rules heq => absurd heq (hc₀nrec cv2 mI rP rules))
    (fun cv2 mI rP rules heq => absurd heq (hc₀nrec cv2 mI rP rules))
    ?_
    (fun cv2 caps heq => absurd heq (hc₀nind cv2 caps))
    (fun entry heq => absurd heq (hc₀nproj entry))
    (fun _ entry heq => absurd heq (hc₀nproj entry))
    ?_ ?_ hheadNat hheadDivMod hheadReduce,
    fun n hn => (cvalAt_ne hn).symm,
    fun ψ => by
      obtain ⟨v, t, hv, -⟩ := hkey ψ
      rw [hv]
      exact congrArg some (cvalAt_self hv).symm⟩
  · -- the new valuation is closed
    intro ψ
    obtain ⟨v, t, hv, -, -⟩ := hkey ψ
    rw [hc₀name, cvalAt_self hv]
    exact denote_closed m.cval_closed hvf hvb hv
  · -- it reads only the declared level parameters
    intro φ₁ φ₂ hp
    rw [hc₀name] at *
    obtain ⟨v₁, -, hv₁, -, -⟩ := hkey φ₁
    obtain ⟨v₂, -, hv₂, -, -⟩ := hkey φ₂
    rw [cvalAt_self hv₁, cvalAt_self hv₂]
    have := hparams φ₁ φ₂ (by rw [hc₀cv] at hp; exact hp)
    rw [hv₁, hv₂] at this
    exact Option.some.inj this
  · -- it is truthful (the value front door's subject conjunct)
    intro ψ ρ
    obtain ⟨v, t, hv, -, hlaw⟩ := hkey ψ
    rw [hc₀name, cvalAt_self hv]
    exact (hlaw ρ).1
  · -- and it inhabits its denoted type, which is truthful
    intro φ
    obtain ⟨v, t, hv, ht, hlaw⟩ := hkey φ
    refine ⟨t, ?_, ?_⟩
    · rw [hc₀cv]
      exact hi.denoteUp ht
    · rw [hc₀name, cvalAt_self hv]
      exact fun ρ => ⟨(hlaw ρ).2.1, (hlaw ρ).2.2⟩
  · -- a stored definition is denoted by its body
    intro cv2 value2 h2 heq φ
    obtain rfl := hc₀defn cv2 value2 h2 heq
    obtain ⟨v, -, hv, -, -⟩ := hkey φ
    have hn : cv2.name = name := by
      rw [← hc₀name, heq]; rfl
    rw [hn, cvalAt_self hv]
    exact hi.denoteUp hv
  · -- and a stored theorem by its proof
    intro cv2 value2 heq φ
    obtain rfl := hc₀thm cv2 value2 heq
    obtain ⟨v, -, hv, -, -⟩ := hkey φ
    have hn : cv2.name = name := by
      rw [← hc₀name, heq]; rfl
    rw [hn, cvalAt_self hv]
    exact hi.denoteUp hv
  · -- `Empty` is reserved, so this install is not at it
    intro hE
    rw [hc₀name] at hE
    exact absurd (hE ▸ hnres) (by decide)
  · -- no eta-capable family part is installed (the kind refutations)
    intro T cvT caps hf _ _ hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [hT, Env.find?_cons, if_pos rfl] at hf
      exact absurd (Option.some.inj hf) (hc₀nind cvT caps)
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC
      exact absurd (Option.some.inj hfC)
        (hc₀nctor cvC caps.etaParams caps.etaFields)
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hfPj
      exact absurd (Option.some.inj hfPj) (hc₀nrec cvP mI rP rules)
  · -- `Eq` is reserved, so this install is not at it
    intro hE
    rw [hc₀name] at hE
    rw [hE] at hnres
    exact nomatch hnres
  · -- and the name is not reserved, so the pinned clause is vacuous
    intro hres
    rw [hc₀name] at hres
    rw [hres] at hnres
    exact nomatch hnres

/-! ## The pin obligations

Stated in the shapes their per-kind consumers feed them (the TT lane's
`NatOpPinTT`/`DivModPinTT` pattern); `DivModPinS` and `ReducePinS` are
discharged in their own modules. -/

/-- The `ble`-guarded value recurrences of a pinned WF-recursive
operation, from its `DeclR` certificate pack.  The obligation
`checkDivModPin`'s relation transpose leaves behind. -/
def DivModPinS (V : Type w) [SetTheory V] : Prop :=
  ∀ {F : Nat} {env : Env} (m : EnvS V env)
    {cv : ConstantVal} {type' value value' : Expr}
    {hint : ReducibilityHint},
    cv.name ∈ natDivModNames →
    env.find? cv.name = none →
    ConstantValR modeR F env m.cval cv type' →
    ValueFrontR modeR F env m.cval cv value type' value' →
    DivModPinR modeR F env
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ m.cval cv.name value' →
    natOpGuard ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ cv.name = true ∧
    ∀ (φ : Name → Nat) (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
        (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
        (Level.substFn φ [] [])) →
      DivModClausesV V
        (fun n => interp V ρ (cvalAt m.cval env cv.name value' n
          (Level.substFn φ [] [])))
        cv.name x y

/-- The compiler-trust opaque's identity, from its `DeclR` certificate
pack.  The obligation `checkReducePin`'s relation transpose leaves
behind. -/
def ReducePinS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {env : Env} (m : EnvS V env)
    {cv : ConstantVal} {type' value value' : Expr},
    cv.name ∈ reduceOpNames →
    env.find? cv.name = none →
    ConstantValR μ F env m.cval cv type' →
    ValueFrontR μ F env m.cval cv value type' value' →
    ReducePinR μ F env
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩
      m.cval cv.name value →
    ConstantVal.matchesPin ⟨cv.name, cv.levelParams, type'⟩
      (reduceOpCvA cv.name) = true →
    ((⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ :
        Env).find? (reduceElemName cv.name)).isSome = true ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ (cvalAt m.cval env cv.name value'
        (reduceElemName cv.name) ψ) →
      SetTheory.app (interp V ρ (cvalAt m.cval env cv.name value'
        cv.name ψ)) x = x

end Setlec.SetR
