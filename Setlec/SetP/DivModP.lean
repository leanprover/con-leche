import Setlec.SetP.NatSemP

/-!
# The WF-recursive `Nat` operations' guarded clauses at `interp2`
(task #161, literal tier — the divmod leg, part 1)

`DivModP` (`Annot/EnvS2P.lean`) is `DivModV`'s mirror at the
validated-annotation currency, and `DivModClausesV` is reused verbatim
because it was already stated over a bare valuation `Name → V`: only
the valuation it is fed changes (`fun n => interp2 V ρ (m.acval n φ)`
in place of `fun n => interp V ρ (cval n (Level.substFn φ [] []))`).

This file carries the two currency-independent halves of the field:

* `divModClausesV_congr` — the clauses depend on the valuation only at
  the finitely many names the operation's own branch mentions
  (`dmValNames`), so agreement there transports them;
* `divModP_cons_fresh` — preservation across every fresh cons.  Unlike
  `natOpsP_cons_fresh` there is no `denoteP` crossing to make: a clause
  is a *pure value fact* over closed leaves, so the whole transport is
  `acvalWith_ne` at each mentioned head, and each head is `≠` the fresh
  name because the guard says it is stored.

The establishment at the operation's own install is part 2
(`Interp2/DivModCertP.lean`).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The names a clause block reads -/

/-- Every head a `DivModClausesV` block can mention: the frame's `Nat`
and its two constructors, the two `Bool` constructors, the guard's
`Nat.ble`, the operation itself, and its recurrence dependencies.
(`natBleName` is in `natOpDeps c` for every WF-recursive `c`, but it is
listed here too so the congruence's users need not know that.) -/
def dmValNames (c : Name) : List Name :=
  Setlec.natName :: Setlec.boolTrueName :: Setlec.boolFalseName ::
    Setlec.natZeroName :: Setlec.natSuccName :: Setlec.natBleName ::
    c :: Setlec.natOpDeps c

-- The nine branches sit at different depths of `DivModClausesV`'s
-- `if`-chain, so `if_true` fires in one of them and `if_false` in the
-- rest: the same escape `Setlec/SetR/DivModPin.lean` takes, for the
-- same reason.
set_option linter.unusedSimpArgs false in
/-- **The clauses read the valuation only at `dmValNames`.**  Proved
per operation: with `c` concrete the `if`-chain reduces to one branch,
and that branch's heads are exactly the ones supplied. -/
theorem divModClausesV_congr {val val' : Name → V} {c : Name} {x y : V}
    (hc : c ∈ Setlec.natDivModNames)
    (h : ∀ n ∈ dmValNames c, val n = val' n) :
    DivModClausesV V val c x y ↔ DivModClausesV V val' c x y := by
  have hT := h Setlec.boolTrueName (by simp [dmValNames])
  have hF := h Setlec.boolFalseName (by simp [dmValNames])
  have hZ := h Setlec.natZeroName (by simp [dmValNames])
  have hS := h Setlec.natSuccName (by simp [dmValNames])
  have hB := h Setlec.natBleName (by simp [dmValNames])
  rcases (show c = Setlec.natDivName ∨ c = Setlec.natModName ∨
      c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
      c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
      c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName
      from by
    simpa [Setlec.natDivModNames] using hc) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc' := h Setlec.natDivName (by decide)
    have hSub := h Setlec.natSubName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hSub]
  · have hc' := h Setlec.natModName (by decide)
    have hSub := h Setlec.natSubName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hSub]
  · have hc' := h Setlec.natGcdName (by decide)
    have hMod := h Setlec.natModName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hMod]
  · have hc' := h Setlec.natLandName (by decide)
    have hAdd := h Setlec.natAddName (by decide)
    have hMul := h Setlec.natMulName (by decide)
    have hDiv := h Setlec.natDivName (by decide)
    have hMod := h Setlec.natModName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hAdd,
      hMul, hDiv, hMod]
  · have hc' := h Setlec.natLorName (by decide)
    have hAdd := h Setlec.natAddName (by decide)
    have hSub := h Setlec.natSubName (by decide)
    have hMul := h Setlec.natMulName (by decide)
    have hDiv := h Setlec.natDivName (by decide)
    have hMod := h Setlec.natModName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hAdd,
      hSub, hMul, hDiv, hMod]
  · have hc' := h Setlec.natXorName (by decide)
    have hAdd := h Setlec.natAddName (by decide)
    have hMul := h Setlec.natMulName (by decide)
    have hDiv := h Setlec.natDivName (by decide)
    have hMod := h Setlec.natModName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hAdd,
      hMul, hDiv, hMod]
  · have hc' := h Setlec.natShiftLeftName (by decide)
    have hSub := h Setlec.natSubName (by decide)
    have hMul := h Setlec.natMulName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hSub,
      hMul]
  · have hc' := h Setlec.natShiftRightName (by decide)
    have hSub := h Setlec.natSubName (by decide)
    have hDiv := h Setlec.natDivName (by decide)
    simp +decide only [DivModClausesV, if_false, if_true, hT, hF, hZ, hS, hB, hc', hSub,
      hDiv]

/-! ## Every mentioned head is stored -/

/-- **The guard stores every head the clauses read.**  `natOpGuard`'s
inversion supplies the numeral heads (`natLitSupported`), the
dependencies, and — because a WF-recursive name is in the `Bool`
branch of the guard — the two `Bool` constructors; the operation
itself is stored by hypothesis. -/
theorem dmValNames_stored {c : Name} (hc : c ∈ Setlec.natDivModNames)
    (hg : natOpGuard env c = true) (hcs : (env.find? c).isSome = true) :
    ∀ n ∈ dmValNames c, (env.find? n).isSome = true := by
  obtain ⟨hs, hdeps, hbool⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, -⟩, ⟨ciF, hfF, -⟩⟩ :=
    hbool (Or.inr (Or.inr (by simpa using hc)))
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, -⟩ :=
    Setlec.natLitSupported_inv hs
  have hble : Setlec.natBleName ∈ Setlec.natOpDeps c := by
    rcases (show c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName
        from by
      simpa [Setlec.natDivModNames] using hc) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro n hn
  simp only [dmValNames, List.mem_cons] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
  · simp [hfN]
  · simp [hfT]
  · simp [hfF]
  · simp [hfZ]
  · simp [hfS]
  · obtain ⟨cvb, vb, hb, hfb, -⟩ := hdeps _ hble
    simp [hfb]
  · exact hcs
  · obtain ⟨cvn, vn, hn', hfn, -⟩ := hdeps n hn
    simp [hfn]

/-! ## Preservation across a fresh cons -/

/-- **The per-operation crossing at a fresh cons.**  A WF-recursive
operation stored in the prefix keeps its `DivModP` entry at the
extension: the guard by `natOpGuard_cons`, the clauses by
`divModClausesV_congr` at the heads the fresh valuation does not
move. -/
theorem divModP_entry_cons {m : EnvS2Core V env} {φ : Name → Nat}
    (hprev : DivModP m φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A)
    {c : Name} (hcN : c ∈ Setlec.natDivModNames) (hne : c ≠ c₀.name)
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (hf₂ : (⟨c₀ :: env.consts⟩ : Env).find? c
      = some (.defnInfo cv' v' hint')) :
    natOpGuard (⟨c₀ :: env.consts⟩ : Env) c = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
      DivModClausesV V (fun n => interp2 V ρ (m₂.acval n φ)) c x y := by
  have hfE : env.find? c = some (.defnInfo cv' v' hint') := by
    rw [Setlec.Env.find?_cons] at hf₂
    split at hf₂
    · next heq => exact absurd heq.symm hne
    · exact hf₂
  obtain ⟨hg, hclauses⟩ := hprev c hcN cv' v' hint' hfE
  -- every head the clauses read is stored, hence not the fresh name
  have hstored := dmValNames_stored hcN hg (by simp [hfE])
  have hmove : ∀ n ∈ dmValNames c, m₂.acval n φ = m.acval n φ := by
    intro n hn
    have hnn : n ≠ c₀.name := by
      intro hh
      have hs := hstored n hn
      rw [hh, hfresh] at hs
      exact nomatch hs
    rw [hac, show acvalWith m.acval c₀.name A n = m.acval n from
      acvalWith_ne hnn]
  have hnat : m₂.acval Setlec.natName φ = m.acval Setlec.natName φ :=
    hmove _ (by simp [dmValNames])
  refine ⟨Setlec.TTVerify.natOpGuard_cons hfresh hg,
    fun ρ x y hx hy => ?_⟩
  rw [hnat] at hx hy
  exact (divModClausesV_congr hcN
    (fun n hn => by rw [hmove n hn])).mp (hclauses ρ x y hx hy)

/-- **`DivModP` at a fresh non-operation cons** — every value-kind step
except a WF operation's own install discharges its obligation here. -/
theorem divModP_cons_fresh {m : EnvS2Core V env} {φ : Name → Nat}
    (hprev : DivModP m φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnothead : (∀ cv v hint, c₀ ≠ .defnInfo cv v hint) ∨
      c₀.name ∉ Setlec.natDivModNames)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    DivModP m₂ φ := by
  intro c hcN cv' v' hint' hf₂
  by_cases hne : c = c₀.name
  · subst hne
    rw [Setlec.Env.find?_cons_self] at hf₂
    rcases hnothead with hnd | hnn
    · exact absurd (Option.some.inj hf₂) (hnd cv' v' hint')
    · exact absurd hcN hnn
  · exact divModP_entry_cons hprev hfresh m₂ hac hcN hne hf₂

/-! ## The `Eq` law at a fresh cons

`EqLawP` mentions one leaf, and `Eq` is stored wherever the law's own
premise holds, so the transport is one `acvalWith_ne`. -/

/-- **`EqLawP` crosses every fresh cons.**  (The law's premise pins
`Eq` in the *extended* environment; `Eq` is therefore stored in the
prefix as well, since the cons is fresh and `Eq` is not it — unless
the cons *is* `Eq`, which is the basis install's own case and is
excluded by the premise's shape there.) -/
theorem eqLawP_cons_fresh {m : EnvS2Core V env}
    (hprev : EqLawP m)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hne : eqName ≠ c₀.name)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    EqLawP m₂ := by
  intro hfind ψ
  have hfE : env.find? eqName = some eqA := by
    rw [Setlec.Env.find?_cons] at hfind
    split at hfind
    · next heq => exact absurd heq.symm hne
    · exact hfind
  have hmove : m₂.acval eqName = m.acval eqName := by
    rw [hac]; exact acvalWith_ne hne
  rw [hmove]
  exact hprev hfE ψ

/-- **`EqLawP` at a value-kind cons.**  No freshness side condition is
needed: `Eq`'s pin is an `indInfo`, so a `defn`/`thm`/`axiom`/`opaque`
cons named `Eq` makes the law's own premise false. -/
theorem eqLawP_cons_valueKind {m : EnvS2Core V env}
    (hprev : EqLawP m)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    EqLawP m₂ := by
  by_cases hn : eqName = c₀.name
  · intro hfind ψ
    exfalso
    rw [Setlec.Env.find?_cons, if_pos hn.symm] at hfind
    exact hnotind _ _ (Option.some.inj hfind)
  · exact eqLawP_cons_fresh hprev hn m₂ hac

/-! ## The compiler-trust identity law at a fresh cons

`ReduceOpsP` mentions exactly two stored leaves — the operation and
its element type — and both are stored in the *prefix* whenever the
law's own premise fires there, so the transport is two `acvalWith_ne`s
and a monotone `find?`.  The one case the transport cannot cover is
the operation's **own** install, which is the establishment
(`Interp2/ReduceOpsP.lean`); it is excluded here by the disjunctive
premise, exactly as `divModP_cons_fresh` excludes a WF operation's
own install. -/

/-- **`ReduceOpsP` crosses every fresh cons that is not a reduce
operation's own opaque install.**  The head disjunct is what a
`defn`/`thm` cons supplies (its kind is not `axiomInfo`); the name
disjunct is what an axiom cons supplies (its pinned name is one of the
standard/`trustCompiler`/`ofReduce*` family, none of which is a reduce
operation). -/
theorem reduceOpsP_entry_cons {m : EnvS2Core V env}
    (hprev : ReduceOpsP m)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A)
    {c : Name} (hcN : c ∈ Setlec.reduceOpNames) (hne : c ≠ c₀.name)
    {cv : ConstantVal}
    (hf₂ : (⟨c₀ :: env.consts⟩ : Env).find? c = some (.axiomInfo cv))
    (hpin : ConstantVal.matchesPin cv (Setlec.reduceOpCvA c) = true) :
    ((⟨c₀ :: env.consts⟩ : Env).find?
        (Setlec.reduceElemName c)).isSome = true ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
        x ∈ˢ interp2 V ρ (m₂.acval (Setlec.reduceElemName c) ψ) →
        SetTheory.app (interp2 V ρ (m₂.acval c ψ)) x = x := by
  have hf : env.find? c = some (.axiomInfo cv) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hne h.symm)] at hf₂
    exact hf₂
  obtain ⟨helem, hid⟩ := hprev c hcN cv hf hpin
  -- the element type is stored in the prefix, hence is not the fresh
  -- cons either
  have hneE : Setlec.reduceElemName c ≠ c₀.name := by
    intro heq
    rw [heq, hfresh] at helem
    exact nomatch helem
  have hmoveC : m₂.acval c = m.acval c := by
    rw [hac]; exact acvalWith_ne hne
  have hmoveE : m₂.acval (Setlec.reduceElemName c)
      = m.acval (Setlec.reduceElemName c) := by
    rw [hac]; exact acvalWith_ne hneE
  refine ⟨?_, fun ψ ρ x hx => ?_⟩
  · cases hfe : env.find? (Setlec.reduceElemName c) with
    | none => rw [hfe] at helem; exact nomatch helem
    | some ci =>
      rw [Setlec.Env.find?_cons, if_neg (fun h => hneE h.symm), hfe]
      rfl
  · rw [hmoveC]
    rw [hmoveE] at hx
    exact hid ψ ρ x hx

/-- **`ReduceOpsP` crosses every fresh cons that is not a reduce
operation's own opaque install.**  The head disjunct is what a
`defn`/`thm` cons supplies (its kind is not `axiomInfo`); the name
disjunct is what an axiom cons supplies (its pinned name is one of the
standard/`trustCompiler`/`ofReduce*` family, none of which is a reduce
operation). -/
theorem reduceOpsP_cons_fresh {m : EnvS2Core V env}
    (hprev : ReduceOpsP m)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnothead : (∀ cv, c₀ ≠ .axiomInfo cv) ∨
      c₀.name ∉ Setlec.reduceOpNames)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    ReduceOpsP m₂ := by
  intro c hcN cv hf₂ hpin
  have hne : c ≠ c₀.name := by
    intro heq
    subst heq
    rw [Setlec.Env.find?_cons_self] at hf₂
    rcases hnothead with hnd | hnn
    · exact absurd (Option.some.inj hf₂) (hnd cv)
    · exact absurd hcN hnn
  exact reduceOpsP_entry_cons hprev hfresh m₂ hac hcN hne hf₂ hpin

end Setlec.SetP
