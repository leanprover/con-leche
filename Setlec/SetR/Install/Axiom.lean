import Setlec.SetR.Install.ValueKinds
import Setlec.SetBase.EraseInv
import Setlec.SetBase.Ok2
import Setlec.Verify.OfReducePin
import Setlec.Verify.Denote.Inst

/-!
# The `axiom` case (task #148, T5)

Transpose of `Setlec/TTVerify/DeclAxiom.lean`: the tolerated-skip
branch is one line (the environment never moves), and the three
installing branches owe a **closed inhabitant of the axiom's denoted
pinned type** — there is no value to denote, so the valuation is
chosen outright (`cvalWith`) and the model must supply the membership.

The three keys mirror the TT lane's split (`StdAxiomKeyTT` /
`TrustCompilerKeyTT` / `OfReduceKeyTT`), with `HasType [] (V ψ) t`
replaced by the membership-plus-truthfulness pair the `EnvS` fields
want.  `trustCompiler` is discharged here (the pin fixes the type to
the stored `True` on the nose, and the stored `True.intro`'s
`mem_type` is the inhabitant); the standard axioms and the
`ofReduce*` pair are stated as obligations and discharged in their
own modules (the `Model/StdAxioms.lean` / `Model/TrustAxioms.lean`
re-hangs).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The annotated-lane half of a key

`AxiomResidues2M.ok2` (`Interp2/Step2Cons.lean`) wants `AnnotOk2` of
the *annotated* leaf at the fresh axiom, and seal 61 established there
is nothing to transport it from: `AnnotOkV`'s clauses carry no fibre
packages.  So the content is established **where the model is built** —
here, as a fifth conjunct of each key, alongside (never instead of)
the `AnnotOkV` one v1's install reads.

The annotated leaf may be drawn from the annotated valuation the
consumer already carries (`EnvS2UM.acval`), which enters as
`AcvalLink` — the two `EnvS2` fields that make an `acval` leaf usable:
its erasure and its truthfulness.  Only `trustCompiler`'s leaf uses
it; the other four are annotation-free (a `BConst` leaf, or `prf`). -/

/-- **An annotated valuation, linked to a collapse-lane one.**  The two
`EnvS2` fields an annotated leaf key reads. -/
structure AcvalLink (V : Type w) [SetTheory V] (cval : TConstVal)
    (acval : Name → (Name → Nat) → AVExpr) : Prop where
  /-- the leaves erase to the collapse-lane valuation -/
  erase : ∀ (n : Name) (ψ : Name → Nat),
    (acval n ψ).erase = cval n ψ
  /-- …and are truthful over `interp2` -/
  ok2 : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    Interp2.AnnotOk2 V ρ (acval n ψ)

/-- **An annotated counterpart of a chosen leaf.**  An `AVExpr` family
erasing to `Vf` on the nose and truthful over `interp2` — exactly what
`AxiomResidues2M`'s `erase` and `ok2` fields ask of the fresh leaf. -/
def AnnotLeaf2 (V : Type w) [SetTheory V]
    (Vf : (Name → Nat) → VExpr) : Prop :=
  ∃ Af : (Name → Nat) → AVExpr,
    (∀ ψ : Name → Nat, (Af ψ).erase = Vf ψ) ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Interp2.AnnotOk2 V ρ (Af ψ)

/-- A `BConst` leaf is its own annotation, and truthful for free —
`AnnotOk2`'s `const` clause is `True`. -/
theorem annotLeaf2_const (V : Type w) [SetTheory V] (c : BConst)
    (us : (Name → Nat) → List Nat) :
    AnnotLeaf2 V (fun ψ => .const c (us ψ)) :=
  ⟨fun ψ => .const c (us ψ), fun _ => rfl, fun _ _ => by simp⟩

/-- The canonical proof leaf is its own annotation, and truthful for
free — `AnnotOk2`'s `prf` clause is `True`. -/
theorem annotLeaf2_prf (V : Type w) [SetTheory V] :
    AnnotLeaf2 V (fun _ => .prf) :=
  ⟨fun _ => .prf, fun _ => rfl, fun _ _ => by simp⟩

/-! ## Small [set] helpers -/

/-- `stdAxiomOk` accepts only the two standard axioms' names (local
twin of the TT lane's `stdAxiomOk_name`). -/
theorem stdAxiomOk_nameS {env : Env} {cvA : ConstantVal}
    (h : stdAxiomOk env cvA = true) :
    cvA.name = propextName ∨ cvA.name = choiceName := by
  by_cases h1 : cvA.name = propextName
  · exact Or.inl h1
  by_cases h2 : cvA.name = choiceName
  · exact Or.inr h2
  rw [stdAxiomOk, if_neg h1, if_neg h2] at h
  exact nomatch h

/-- A stored level-monomorphic constant's bare reference denotes to its
valuation. -/
theorem denote_const_nolevelsS {env : Env} {cval : TConstVal} {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (ψ : Name → Nat) (d : Nat) :
    denote cval env ψ d (.const n []) = some (cval n ψ) := by
  rw [denote_const, hf]
  dsimp only
  rw [if_pos (by rw [hlp]; rfl), hlp,
    show Level.substFn ψ [] [] = ψ from funext fun _ => rfl]

/-- A stored constant's valuation inhabits its denoted type, which is
truthful — `mem_type` keyed on a `find?` hit. -/
theorem EnvS.cval_memType {env : Env} (m : EnvS V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci) (ψ : Name → Nat) :
    ∃ t, denoteClosed m.cval env ψ ci.toConstantVal.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.cval n ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t := by
  obtain ⟨t, ht, hlaw⟩ := m.mem_type ci (Env.find?_mem hf) ψ
  refine ⟨t, ht, fun ρ => ?_⟩
  have := hlaw ρ
  rwa [Env.find?_name hf] at this

/-! ## The axiom install -/

/-- **The axiom install** — transpose of `extendAxiomTT`: the
valuation is chosen outright; `defn_eq` and `thm_ok` are vacuous at an
`axiomInfo`, so the install is strictly smaller than the value one.

**The conclusion names the extension and its agreement**, on
`extendValueS`'s shape and for its reason: a `Nonempty` is a one-way
door, and the interp2 tier's `acval_erase` is an equation against the
extension's own valuation, so it cannot be *stated* against a witness
the install discarded.  The agreement is `cvalWith`'s own off-name
clause, so exposing it costs one term. -/
theorem extendAxiomS {env : Env} (m : EnvS V env) {cv : ConstantVal}
    {Vf : (Name → Nat) → VExpr}
    (hfresh : env.find? cv.name = none)
    (hwf : EnvWF ⟨ConstantInfo.axiomInfo cv :: env.consts⟩)
    (hVcl : ∀ ψ : Name → Nat, VExpr.Closed (Vf ψ))
    (hVp : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂)
    (hVannot : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ))
    (hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cv.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t)
    (hnres : reservedBasisNames.contains cv.name = false)
    (hnred : cv.name ∉ reduceOpNames) :
    ∃ m' : EnvS V ⟨ConstantInfo.axiomInfo cv :: env.consts⟩,
      (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
      ∀ ψ : Name → Nat, m'.cval cv.name ψ = Vf ψ := by
  have hi : Installs env m.cval (cvalWith m.cval cv.name Vf)
      (.axiomInfo cv) :=
    Installs.of_fresh hfresh (fun n hn => (cvalWith_ne hn).symm)
  refine ⟨EnvS.cons m hi hwf ?_ ?_ ?_ ?_ (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq) ?_
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    ?_ (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) ?_,
    fun n hn => (cvalWith_ne hn).symm,
    fun ψ => congrFun cvalWith_self ψ⟩
  · intro ψ
    show VExpr.Closed (cvalWith m.cval cv.name Vf cv.name ψ)
    rw [cvalWith_self]; exact hVcl ψ
  · intro φ₁ φ₂ hp
    show cvalWith m.cval cv.name Vf cv.name φ₁
      = cvalWith m.cval cv.name Vf cv.name φ₂
    rw [cvalWith_self]
    exact hVp φ₁ φ₂ hp
  · intro ψ ρ
    show AnnotOkV V ρ (cvalWith m.cval cv.name Vf cv.name ψ)
    rw [cvalWith_self]
    exact hVannot ψ ρ
  · intro φ
    obtain ⟨t, ht, hd⟩ := hkey φ
    refine ⟨t, hi.denoteUp ht, ?_⟩
    show ∀ ρ : Nat → V,
      interp V ρ (cvalWith m.cval cv.name Vf cv.name φ) ∈ˢ interp V ρ t ∧
      AnnotOkV V ρ t
    rw [cvalWith_self]
    exact hd
  · intro hE
    have : reservedBasisNames.contains emptyName = false := by
      rw [show emptyName = cv.name from hE.symm]; exact hnres
    exact nomatch this
  · intro T cvT caps hf hcape hres hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [hT, Env.find?_cons, if_pos rfl] at hf; exact nomatch hf
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC; exact nomatch hfC
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hfPj; exact nomatch hfPj
  · intro hE
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hE
    rw [hE] at hnres
    exact nomatch hnres
  · intro hres
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hres
    rw [hres] at hnres
    exact nomatch hnres
  · intro cv2 heq hmem
    exact absurd hmem hnred

/-! ## The three keys -/

/-- The two standard axioms are inhabited (`propext` through the
pinned `Iff` family, `Classical.choice` through the pinned
`Nonempty`) — the `Model/StdAxioms.lean` re-hang's interface.

The fifth conjunct is the annotated lane's (see above); the fourth is
untouched, so v1's install reads exactly what it always did. -/
def StdAxiomKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) ∧
      ∀ acval : Name → (Name → Nat) → AVExpr,
        AcvalLink V m.cval acval → AnnotLeaf2 V Vf

/-- The `ofReduce*` axioms are inhabited: the identity certificate
(`reduce_ops`) makes the hypothesis be the conclusion — the
`Model/TrustAxioms.lean` re-hang's interface. -/
def OfReduceKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    ofReduceAxOk env cvA = true →
    (cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) ∧
      ∀ acval : Name → (Name → Nat) → AVExpr,
        AcvalLink V m.cval acval → AnnotLeaf2 V Vf

/-! ## `Lean.trustCompiler`, discharged

The smallest key, mirroring `trustCompilerKeyTT`: the pin fixes the
axiom's type to the stored `True` on the nose, so the witness is the
stored `True.intro`'s valuation and the membership is its own
`mem_type` (whose denoted type is the same bare constant). -/

/-- **The `trustCompiler` key.** -/
theorem trustCompilerKeyS {env : Env} (m : EnvS V env)
    {cvA : ConstantVal} (hok : trustCompilerOk env cvA = true)
    (_hname : cvA.name = trustCompilerName)
    (_hfresh : env.find? cvA.name = none) :
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) ∧
      (∀ acval : Name → (Name → Nat) → AVExpr,
        AcvalLink V m.cval acval → AnnotLeaf2 V Vf) := by
  simp only [trustCompilerOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hok
  cases hfT : env.find? trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? trueIntroName with
  | none => rw [hfTi] at hTi; exact nomatch hTi
  | some ciTi =>
  rw [hfT] at hT
  rw [hfTi] at hTi
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    cases ciT with
    | indInfo cvT caps =>
      simp only [ConstantVal.matchesPin, Bool.and_eq_true,
        decide_eq_true_eq] at hT
      exact hT.1.2
    | _ => exact nomatch hT
  obtain ⟨hlpTi, htyTi⟩ : ciTi.toConstantVal.levelParams = [] ∧
      ciTi.toConstantVal.type = .const trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, erasePw_const_invS (eraseNames_const_invS hTi.2)⟩
    | _ => exact nomatch hTi
  have htyA : cvA.type = .const trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact erasePw_const_invS (eraseNames_const_invS hA.2)
  refine ⟨fun ψ => m.cval trueIntroName ψ, fun ψ => m.cval_closed _ _,
    ?_, fun ψ ρ => m.annot_okV _ _ ρ, fun ψ => ?_,
    fun acval hlink => ⟨fun ψ => acval trueIntroName ψ,
      fun ψ => hlink.erase _ ψ, fun ψ ρ => hlink.ok2 _ ψ ρ⟩⟩
  · intro φ₁ φ₂ _
    exact m.val_params trueIntroName ciTi hfTi φ₁ φ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfTi ψ
    rw [htyTi] at ht
    rw [show denoteClosed m.cval env ψ (Expr.const trueName [])
        = denote m.cval env ψ 0 (.const trueName []) from rfl,
      denote_const_nolevelsS hfT hlpT ψ 0] at ht
    obtain rfl := Option.some.inj ht
    refine ⟨m.cval trueName ψ, ?_, hlaw⟩
    rw [htyA]
    show denote m.cval env ψ 0 (.const trueName []) = _
    rw [denote_const_nolevelsS hfT hlpT ψ 0]

/-! ## The guard chain -/

/-- An accepted `axiom` extends the invariant, **with the extension
and its valuation agreement exposed**, given the two remaining keys.

All four of `DeclAxiomR`'s branches are answered here.  The three that
store funnel through the single `extendAxiomS` call in `hgo` and differ
only in where `Vf` comes from — `hstd`, the in-tree theorem
`trustCompilerKeyS`, and `hofr`.  The tolerated skip does not move the
environment, so its extension **is** the prefix and its agreement is
`rfl`. -/
theorem declAxiomExtS (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (m : EnvS V env) (h : DeclAxiomR μ F env m.cval cv env₂) :
    ∃ m' : EnvS V env₂, ∀ n, n ≠ cv.name → m.cval n = m'.cval n := by
  obtain ⟨type', hcv, hbranch⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  have hgo : ∀ (Vf : (Name → Nat) → VExpr),
      (∀ ψ, VExpr.Closed (Vf ψ)) →
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) →
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) →
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ type' = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) →
      cv.name ∉ reduceOpNames →
      ∃ m' : EnvS V ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩, ∀ n, n ≠ cv.name → m.cval n = m'.cval n := by
    intro Vf hVcl hVp hVannot hkey hnr
    exact ⟨_, (extendAxiomS m (cv := ⟨cv.name, cv.levelParams, type'⟩)
      (Vf := Vf) hfresh hwfc hVcl hVp hVannot hkey hres
      hnr).choose_spec.1⟩
  rcases hbranch with ⟨hstdok, rfl⟩ | ⟨hnameTC, htcok, rfl⟩ |
    ⟨hofn, hofok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, -⟩ := hstd m hstdok hfresh
    exact hgo Vf hVcl hVp hVannot hkey
      (by rcases stdAxiomOk_nameS hstdok with hh | hh <;> rw [hh] <;> decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, -⟩ :=
      trustCompilerKeyS m htcok hnameTC hfresh
    exact hgo Vf hVcl hVp hVannot hkey (by rw [hnameTC]; decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, -⟩ := hofr m hofok hofn hfresh
    exact hgo Vf hVcl hVp hVannot hkey
      (by rcases hofn with hh | hh <;> rw [hh] <;> decide)
  · exact ⟨m, fun _ _ => rfl⟩

/-- An accepted `axiom` extends the invariant — `declAxiomExtS`'s
conclusion with the extension forgotten.  The signature is unchanged,
so `declStepS` and the fourteen read exactly what they always did. -/
theorem declAxiomS (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (m : EnvS V env) (h : DeclAxiomR μ F env m.cval cv env₂) :
    Nonempty (EnvS V env₂) :=
  ⟨(declAxiomExtS hstd hofr m h).choose⟩

/-- **An accepted `axiom` extends the invariant, with an annotated
leaf.**  `declAxiomExtS`'s conclusion plus the two `AxiomResidues2M`
fields that speak about the fresh leaf's *annotation*: it erases to the
extension's valuation at the new name, and it is `AnnotOk2`.

All four branches answer, and the fourth answers for a reason worth
naming: the **tolerated skip** stores nothing, so the leaf wanted is
the annotated valuation's own reading at that name — and `AcvalLink`'s
two laws hold at *every* name, stored or not, so `acval cv.name` is it.
The three storing branches take the leaf from the branch key's fifth
conjunct, at the valuation `extendAxiomS` installs
(`extendAxiomS`'s third component pins it to `Vf`).

This is the `.ok2` discharge's supply side: nothing here is premised
on an uninhabited hypothesis — `stdAxiomKeyS` (`StdAxiomKey.lean`),
`trustCompilerKeyS` and `ofReduceKeyS` are theorems, and `AcvalLink`
is two `EnvS2U` fields the consumer already carries. -/
theorem declAxiomLeafExtS (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    {acval : Name → (Name → Nat) → AVExpr} (m : EnvS V env)
    (hlink : AcvalLink V m.cval acval)
    (h : DeclAxiomR μ F env m.cval cv env₂) :
    ∃ (m' : EnvS V env₂) (A : (Name → Nat) → AVExpr),
      (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
      (∀ ψ : Name → Nat, (A ψ).erase = m'.cval cv.name ψ) ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Interp2.AnnotOk2 V ρ (A ψ) := by
  obtain ⟨type', hcv, hbranch⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  have hgo : ∀ (Vf : (Name → Nat) → VExpr),
      (∀ ψ, VExpr.Closed (Vf ψ)) →
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) →
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) →
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ type' = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) →
      AnnotLeaf2 V Vf → cv.name ∉ reduceOpNames →
      ∃ (m' : EnvS V ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩) (A : (Name → Nat) → AVExpr),
        (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
        (∀ ψ : Name → Nat, (A ψ).erase = m'.cval cv.name ψ) ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V),
          Interp2.AnnotOk2 V ρ (A ψ) := by
    intro Vf hVcl hVp hVannot hkey hleaf hnr
    obtain ⟨m', hag, hself⟩ :=
      extendAxiomS m (cv := ⟨cv.name, cv.levelParams, type'⟩)
        (Vf := Vf) hfresh hwfc hVcl hVp hVannot hkey hres hnr
    obtain ⟨Af, hAe, hAo⟩ := hleaf
    exact ⟨m', Af, hag, fun ψ => by rw [hAe ψ, hself ψ], hAo⟩
  rcases hbranch with ⟨hstdok, rfl⟩ | ⟨hnameTC, htcok, rfl⟩ |
    ⟨hofn, hofok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, hleaf⟩ := hstd m hstdok hfresh
    exact hgo Vf hVcl hVp hVannot hkey (hleaf acval hlink)
      (by rcases stdAxiomOk_nameS hstdok with hh | hh <;> rw [hh] <;> decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, hleaf⟩ :=
      trustCompilerKeyS m htcok hnameTC hfresh
    exact hgo Vf hVcl hVp hVannot hkey (hleaf acval hlink)
      (by rw [hnameTC]; decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey, hleaf⟩ :=
      hofr m hofok hofn hfresh
    exact hgo Vf hVcl hVp hVannot hkey (hleaf acval hlink)
      (by rcases hofn with hh | hh <;> rw [hh] <;> decide)
  · exact ⟨m, fun ψ => acval cv.name ψ, fun _ _ => rfl,
      fun ψ => hlink.erase _ ψ, fun ψ ρ => hlink.ok2 _ ψ ρ⟩

/-- The equality former's valuation at the pinned level `1`. -/
def eqVS {env : Env} (m : EnvS V env) (ψ : Name → Nat) : VExpr :=
  m.cval eqName
    (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])

/-- **The pinned `ofReduce` type, denoted.**  The `EnvS` restatement
of `denote_ofReducePin`: it used its `EnvTT` only through
`denote_const_nolevels`. -/
theorem denote_ofReducePinS {env : Env} (m : EnvS V env) {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName)
    {ciE : ConstantInfo} {cvR : ConstantVal}
    (hfE : env.find? (reduceElemName (ofReduceOp n)) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = [])
    (hfR : env.find? (ofReduceOp n) = some (.axiomInfo cvR))
    (hlpR : cvR.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 (ofReducePinA n).type =
      some (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
        (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
          (.pi (VExpr.mkAppN (eqVS m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .app (m.cval (ofReduceOp n) ψ) (.bvar 1), .bvar 0])
            (VExpr.mkAppN (eqVS m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .bvar 2, .bvar 1])))) := by
  have hE : ∀ d, denote m.cval env ψ d
      (.const (reduceElemName (ofReduceOp n)) [])
      = some (m.cval (reduceElemName (ofReduceOp n)) ψ) :=
    fun d => denote_const_nolevelsS hfE hlpE ψ d
  have hR : ∀ d, denote m.cval env ψ d (.const (ofReduceOp n) [])
      = some (m.cval (ofReduceOp n) ψ) :=
    fun d => denote_const_nolevelsS hfR hlpR ψ d
  have hQ : ∀ d, denote m.cval env ψ d (.const eqName [.succ .zero])
      = some (eqVS m ψ) := by
    intro d
    rw [denote_const, hEq, eqVS]
    exact if_pos rfl
  rw [ofReducePin_type hn]
  simp [denote_forallE, hE, Expr.instantiate1, denote_app, denote_fvar,
    Expr.mkAppN, VExpr.mkAppN, hQ, hR]

/-- **The pinned `Eq` former's type, denoted** at any assignment
sending its one level parameter to `1`. -/
theorem denote_eqA_typeS {env : Env} {cval : TConstVal}
    (ψ' : Name → Nat) (hu : ψ' (Name.anonymous.str "u") = 1) :
    denoteClosed cval env ψ' eqA.toConstantVal.type
      = some (.pi (.sort 1)
          (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := by
  have hty : eqA.toConstantVal.type =
      Expr.forallE (Name.anonymous.str "α")
        (Expr.sort (Level.param (Name.anonymous.str "u")))
        (Expr.forallE (Name.anonymous.str "a") (Expr.bvar 0)
          (Expr.forallE (Name.anonymous.str "b") (Expr.bvar 1)
            (Expr.sort Level.zero) ⟨.default, .never⟩) ⟨.default, .never⟩)
        ⟨.implicit, .never⟩ := rfl
  rw [denoteClosed, hty]
  simp [denote_forallE, denote_sort, Expr.instantiate1,
    denote_fvar, Level.eval, hu]

/-! ## `Lean.ofReduceBool`/`Lean.ofReduceNat`, discharged

The pin fixes the axiom's type to `∀ a b : E, op a = b → a = b`, whose
inhabitant is `fun a b h => h`: `reduce_ops` says the trusted operation
is the identity on `E`, so the hypothesis' `Eq`-spine and the
conclusion's interpret to the *same* truth set.  The witness is built
out of the type's own subterms, so its `AnnotOkV` **is** the type's,
component for component (`AnnotOkV`'s `.lam` and `.pi` clauses have the
same shape), with `trivial` for the `.bvar` tail. -/

set_option maxHeartbeats 3200000 in
/-- **The `ofReduce*` key's membership, at the NAMED witness** (task
#161 ENDGAME D; `propextKeyS_mem`/`choiceKeyS_mem`'s sibling).  The
key's `∃ Vf` is one currency too coarse for a P leaf, which must know
*which* witness was installed so its annotated twin can erase to it —
and here the witness is `.prf`, the canonical proof: the pinned type
`∀ a b : E, op a = b → a = b` is a `Prop`.  See the seal's note below
for why the η-expanded identity is *not* the witness. -/
theorem ofReduceKeyS_mem {env : Env} (m : EnvS V env)
    {cvA : ConstantVal} (hok : ofReduceAxOk env cvA = true)
    (hor : cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) :
    ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cvA.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (VExpr.prf : VExpr) ∈ˢ interp V ρ t ∧
        AnnotOkV V ρ t := by
  simp only [ofReduceAxOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hEq, helem⟩, hstored⟩, hpin⟩ := hok
  obtain ⟨ciE, hfE, hlpE, htyE⟩ := reduceElem_sort helem
  obtain ⟨cvR, hfR, hmpR⟩ : ∃ cvR,
      env.find? (ofReduceOp cvA.name) = some (.axiomInfo cvR) ∧
      ConstantVal.matchesPin cvR
        (reduceOpCvA (ofReduceOp cvA.name)) = true := by
    rw [reduceStoredOk] at hstored
    cases hf : env.find? (ofReduceOp cvA.name) with
    | none => rw [hf] at hstored; exact nomatch hstored
    | some ci =>
      rw [hf] at hstored
      cases ci with
      | axiomInfo cvR => exact ⟨cvR, rfl, hstored⟩
      | _ => exact nomatch hstored
  obtain ⟨-, hlpR⟩ := matchesPin_invT hmpR
  rw [show (reduceOpCvA (ofReduceOp cvA.name)).levelParams = [] from by
    unfold reduceOpCvA; split <;> rfl] at hlpR
  have hmem : ofReduceOp cvA.name ∈ reduceOpNames := by
    unfold ofReduceOp; split <;> decide
  -- task #161 P5: `matchesPin` forgives the binder prop-ness datum as
  -- well as binder names, so the pin hit no longer gives `ErasedEq` on
  -- the stored types themselves.  It gives what these two facts are
  -- *for* — the denotations agree — directly: `denote_matchesPin`,
  -- whose statement is unchanged, because `denote` reads neither.
  have htyA : ∀ ψ : Name → Nat,
      denote m.cval env ψ 0 cvA.type
        = denote m.cval env ψ 0 (ofReducePinA cvA.name).type :=
    fun _ => denote_matchesPin hpin 0
  have htyR : ∀ ψ : Name → Nat,
      denote m.cval env ψ 0 cvR.type
        = denote m.cval env ψ 0 (reduceOpCvA (ofReduceOp cvA.name)).type :=
    fun _ => denote_matchesPin hmpR 0
  have hden : ∀ ψ : Name → Nat,
      denoteClosed m.cval env ψ cvA.type
        = some (.pi (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
          (.pi (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
            (.pi (VExpr.mkAppN (eqVS m ψ)
                [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
                 .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1),
                 .bvar 0])
              (VExpr.mkAppN (eqVS m ψ)
                [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
                 .bvar 2, .bvar 1])))) := by
    intro ψ
    rw [denoteClosed, htyA ψ]
    exact denote_ofReducePinS m hor hfE hlpE hfR hlpR hEq ψ
  -- the `Eq` former's one level parameter is pinned to `1`
  have hsub : ∀ (φ : Name → Nat) (p : Name),
      p ∈ eqA.toConstantVal.levelParams →
      Level.substFn φ eqA.toConstantVal.levelParams
        [Level.zero.succ] p = 1 := by
    intro φ p hp
    have hlpEq : eqA.toConstantVal.levelParams
        = [Name.anonymous.str "u"] := rfl
    rw [hlpEq] at hp
    have hpu : p = Name.anonymous.str "u" := List.mem_singleton.mp hp
    subst hpu
    rfl
  have heqψ : ∀ φ : Name → Nat,
      Level.substFn φ eqA.toConstantVal.levelParams
        [Level.zero.succ] uN = 1 :=
    fun φ => hsub φ _ (List.Mem.head _)
  -- the element type is closed, and inhabits `Sort 1`
  have hEc : ∀ (ψ : Name → Nat) (ρ ρ' : Nat → V),
      interp V ρ (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        = interp V ρ'
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) :=
    fun ψ ρ ρ' => interp_closed V (m.cval_closed _ ψ) ρ ρ'
  have hEmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        ∈ˢ univ 1 := by
    intro ψ ρ
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfE ψ
    rw [htyE, show denoteClosed m.cval env ψ (Expr.sort (.succ .zero))
        = denote m.cval env ψ 0 (Expr.sort (.succ .zero)) from rfl,
      denote_sort] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ).1
  -- the pinned `Eq` former inhabits its three-fold product
  have hQmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (eqVS m ψ) ∈ˢ piC (univ 1)
        (fun A => piC A (fun _ => piC A (fun _ => univ 0))) := by
    intro ψ ρ
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hEq
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
    rw [denote_eqA_typeS _ (heqψ ψ)] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ).1
  -- the trusted operation inhabits `E → E`
  have hOpi : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.cval (ofReduceOp cvA.name) ψ)
        ∈ˢ piC (interp V ρ
            (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ))
          (fun _ => interp V ρ
            (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)) := by
    intro ψ ρ
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfR ψ
    rw [show ((ConstantInfo.axiomInfo cvR).toConstantVal) = cvR
        from rfl, denoteClosed, htyR ψ,
      reduceOpCv_type hor] at ht
    simp only [denote_forallE,
      denote_const_nolevelsS hfE hlpE, Expr.instantiate1] at ht
    obtain rfl := Option.some.inj ht
    have h1 := (hlaw ρ).1
    rw [interp_pi,
      show (fun x => interp V (cons V x ρ)
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ))
        = (fun _ : V => interp V ρ
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)) from
        funext fun x => hEc ψ _ ρ] at h1
    exact h1
  -- one application of the operation: truthful, and the identity
  have hOpApp : ∀ (ψ : Name → Nat) (ρ : Nat → V) (a : VExpr),
      interp V ρ a ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      AnnotOkV V ρ a →
      AnnotOkV V ρ (.app (m.cval (ofReduceOp cvA.name) ψ) a) ∧
        interp V ρ (.app (m.cval (ofReduceOp cvA.name) ψ) a)
          = interp V ρ a := by
    intro ψ ρ a ha hoka
    refine ⟨?_, ?_⟩
    · rw [AnnotOkV_app]
      exact ⟨m.annot_okV _ _ _, hoka, _, _, hOpi ψ ρ, ha⟩
    · rw [interp_app]
      exact (m.reduce_ops _ hmem cvR hfR hmpR).2 ψ ρ _ ha
  -- an `Eq`-spine over the element type is truthful
  have hEqApp : ∀ (ψ : Name → Nat) (ρ : Nat → V) (a b : VExpr),
      interp V ρ a ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      interp V ρ b ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      AnnotOkV V ρ a → AnnotOkV V ρ b →
      AnnotOkV V ρ (VExpr.mkAppN (eqVS m ψ)
        [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ, a, b]) := by
    intro ψ ρ a b ha hb hoka hokb
    have hQ := hQmem ψ ρ
    have hE := hEmem ψ ρ
    have h1 : AnnotOkV V ρ (.app (eqVS m ψ)
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)) := by
      rw [AnnotOkV_app]
      exact ⟨m.annot_okV _ _ _, m.annot_okV _ _ _, _, _, hQ, hE⟩
    have h1m := app_mem_piC hQ hE
    have h2 : AnnotOkV V ρ (.app (.app (eqVS m ψ)
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)) a) := by
      rw [AnnotOkV_app]
      exact ⟨h1, hoka, _, _, h1m, ha⟩
    have h2m := app_mem_piC h1m ha
    show AnnotOkV V ρ (.app (.app (.app (eqVS m ψ) _) a) b)
    rw [AnnotOkV_app]
    exact ⟨h2, hokb, _, _, h2m, hb⟩
  -- the two `Eq`-statement frames, at their own de Bruijn depths
  have hframe : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ρ 1 ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      ρ 0 ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      AnnotOkV V ρ (VExpr.mkAppN (eqVS m ψ)
          [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1),
           .bvar 0]) ∧
        interp V ρ (VExpr.mkAppN (eqVS m ψ)
          [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           .app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1),
           .bvar 0]) = eqv (ρ 1) (ρ 0) := by
    intro ψ ρ h1 h0
    obtain ⟨hok1, hev1⟩ := hOpApp ψ ρ (.bvar 1) h1 trivial
    have hm1 : interp V ρ (.app (m.cval (ofReduceOp cvA.name) ψ)
        (.bvar 1)) ∈ˢ interp V ρ
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
      rw [hev1]; exact h1
    have happ := EqLawV.app₃ V m.eq_lawV hEq
      (Level.substFn ψ eqA.toConstantVal.levelParams [Level.zero.succ])
      ρ (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
      (.app (m.cval (ofReduceOp cvA.name) ψ) (.bvar 1)) (.bvar 0)
      (by rw [heqψ]; exact hEmem ψ ρ) hm1 h0
    rw [hev1] at happ
    exact ⟨hEqApp ψ ρ _ _ hm1 h0 hok1 trivial, happ⟩
  have hframe2 : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ρ 2 ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      ρ 1 ∈ˢ interp V ρ
        (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) →
      AnnotOkV V ρ (VExpr.mkAppN (eqVS m ψ)
          [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           .bvar 2, .bvar 1]) ∧
        interp V ρ (VExpr.mkAppN (eqVS m ψ)
          [m.cval (reduceElemName (ofReduceOp cvA.name)) ψ,
           .bvar 2, .bvar 1]) = eqv (ρ 2) (ρ 1) := by
    intro ψ ρ h2 h1
    exact ⟨hEqApp ψ ρ _ _ h2 h1 trivial trivial,
      EqLawV.app₃ V m.eq_lawV hEq
        (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.zero.succ])
        ρ (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ)
        (.bvar 2) (.bvar 1)
        (by rw [heqψ]; exact hEmem ψ ρ) h2 h1⟩
  -- **The witness is the canonical proof.**  The pinned type
  -- `∀ a b : E, op a = b → a = b` is a `Prop`, so `pt` inhabits it,
  -- and `prf` is the leaf that denotes `pt` in *both* lanes.  The
  -- η-expanded identity `fun a b h => h` inhabits it too — and was
  -- this key's witness until the annotated lane was asked for — but
  -- its annotation's `AnnotOk2` is not establishable here: the `.app`
  -- clause's fibre slot wants `interp2`-lane membership for the
  -- pinned `Eq` former and the trusted op, whose only supplier is
  -- `EnvS2U.mem_type2`, gated on a `denote2` success and hence on
  -- `sortOfE`, i.e. on running `inferTypeCore`/`whnf`.  `prf` carries
  -- no binder for `AnnotOk2` to be about, so the annotated conjunct
  -- is `annotLeaf2_prf` — see the module note above.
  · intro ψ
    refine ⟨_, hden ψ, fun ρ => ⟨?_, ?_⟩⟩
    · rw [interp_prf, interp_pi]
      refine pt_mem_piC_iff.mpr fun x hx => ?_
      rw [interp_pi]
      refine pt_mem_piC_iff.mpr fun y hy => ?_
      rw [interp_pi]
      refine pt_mem_piC_iff.mpr fun h hh => ?_
      have hx2 : (cons V y (cons V x ρ)) 1 ∈ˢ interp V
          (cons V y (cons V x ρ))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show x ∈ˢ _
        rw [← hEc ψ ρ]; exact hx
      have hy2 : (cons V y (cons V x ρ)) 0 ∈ˢ interp V
          (cons V y (cons V x ρ))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show y ∈ˢ _
        rw [← hEc ψ (cons V x ρ)]; exact hy
      have hx3 : (cons V h (cons V y (cons V x ρ))) 2 ∈ˢ interp V
          (cons V h (cons V y (cons V x ρ)))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show x ∈ˢ _
        rw [← hEc ψ ρ]; exact hx
      have hy3 : (cons V h (cons V y (cons V x ρ))) 1 ∈ˢ interp V
          (cons V h (cons V y (cons V x ρ)))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show y ∈ˢ _
        rw [← hEc ψ (cons V x ρ)]; exact hy
      rw [(hframe2 ψ _ hx3 hy3).2]
      rw [(hframe ψ _ hx2 hy2).2] at hh
      have hh' : h ∈ˢ eqv x y := hh
      show (pt : V) ∈ˢ eqv x y
      rw [mem_eqv hh']
      exact pt_mem_eqv_self y
    · rw [AnnotOkV_pi]
      refine ⟨m.annot_okV _ _ _, fun x hx => ?_⟩
      rw [AnnotOkV_pi]
      refine ⟨m.annot_okV _ _ _, fun y hy => ?_⟩
      have hx2 : (cons V y (cons V x ρ)) 1 ∈ˢ interp V
          (cons V y (cons V x ρ))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show x ∈ˢ _
        rw [← hEc ψ ρ]; exact hx
      have hy2 : (cons V y (cons V x ρ)) 0 ∈ˢ interp V
          (cons V y (cons V x ρ))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show y ∈ˢ _
        rw [← hEc ψ (cons V x ρ)]; exact hy
      rw [AnnotOkV_pi]
      refine ⟨(hframe ψ _ hx2 hy2).1, fun h hh => ?_⟩
      have hx3 : (cons V h (cons V y (cons V x ρ))) 2 ∈ˢ interp V
          (cons V h (cons V y (cons V x ρ)))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show x ∈ˢ _
        rw [← hEc ψ ρ]; exact hx
      have hy3 : (cons V h (cons V y (cons V x ρ))) 1 ∈ˢ interp V
          (cons V h (cons V y (cons V x ρ)))
          (m.cval (reduceElemName (ofReduceOp cvA.name)) ψ) := by
        show y ∈ˢ _
        rw [← hEc ψ (cons V x ρ)]; exact hy
      exact (hframe2 ψ _ hx3 hy3).1

/-- **The `ofReduce*` key**, re-derived from the split form above; the
statement is unchanged. -/
theorem ofReduceKeyS : OfReduceKeyS V := by
  intro env m cvA hok hor _hfresh
  exact ⟨fun _ => .prf, fun _ => trivial, fun _ _ _ => rfl,
    fun _ _ => trivial, ofReduceKeyS_mem m hok hor,
    fun _ _ => annotLeaf2_prf V⟩

end Setlec.SetR
