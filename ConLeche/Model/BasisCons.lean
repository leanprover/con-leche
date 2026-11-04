module

public import ConLeche.Model.RecRulesCons

public section

/-!
# The basis-cons preservation kit (task #161)

`BasisStepPB` conses *inductive-kind* heads — `indInfo`, `ctorInfo`,
`recInfo` — and the existing preservation lemmas are all keyed on the
value kinds:

| field | value-kind lemma | at a basis cons |
| --- | --- | --- |
| `nat_ops` | `natOps_cons_fresh` | **reusable** (`Or.inl`: not a `defnInfo`) |
| `div_mod` | `divMod_cons_fresh` | **reusable**, same disjunct |
| `eq_law` | `eqLaw_cons_fresh` | **reusable** (the `Eq` disequality, off freshness) |
| `nat_heads` | `natHeads_cons_fresh` | **REFUTED** — its `hknd` premise is the cons's own kind |
| `caps_ok` | `capsOk_cons_fresh` | **REFUTED** — same three kind premises |
| `rec_rules` | `recRules_cons_fresh` | **reusable** at a non-recursor (below) |

This file supplies the two replacements.

## The replacement is `reservedBasisNames`, and it was designed in

`EtaFamilyStored`'s **name-only conjunct**
(`Verify/EnvGuards.lean:49`) says the capability constructor is
never a reserved name, and its docstring says why it is there: "which
keeps the basis installs' head obligations vacuous by computation".
`CapsOk`'s two halves both carry `reservedBasisNames.contains T =
false`.  So at a cons whose name *is* reserved, the disequalities
`capsOk_cons_fresh` derives from the cons's kind come instead from
the name, and the body transposes unchanged — `capsOk_cons_basis`.

`nat_heads` is easier still: the guard reads exactly three names, so a
cons that is none of them moves neither the guard nor the three leaves
(`natHeads_cons_offNat`).  The `Nat` block supplies its own
`nat_heads` bespoke — that is the block where the guard *becomes*
true, and no back-transfer exists or should.

## `rec_rules` at a basis cons

`recRules_cons_fresh` needs `RecRule.ctor rl ≠ c₀.name` for every rule
of every *stored* recursor.  `EnvWF`'s `recInfo` clause never says that
`RecRule.ctor` resolves, but `EnvModel.rec_ctors` (`RecCtorsStored`,
reachable as `mp.base2.rec_ctors`) says every stored recursor rule's
constructor is itself stored, so with the cons fresh the disequality is
immediate and the row is reusable at every basis cons whose kind is not
a recursor.  A basis *recursor* cons establishes its own rules
bespoke from its firing laws.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule)


universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

/-- **`nat_heads` at a cons that is none of the three literal
heads.**  The guard reads `natName`, `natZeroName` and `natSuccName`
and nothing else, so a cons named otherwise moves neither the guard
nor the three leaves — the basis blocks other than `Nat` discharge
their obligation here, and so would any inductive-kind cons.  (The
`Nat` block itself is where the guard *becomes* true; it supplies
`nat_heads` bespoke, and no back-transfer exists.) -/
theorem natHeads_cons_offNat (mp : EnvModelM V env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hnN : c₀.name ≠ natName) (hnZ : c₀.name ≠ natZeroName)
    (hnS : c₀.name ≠ natSuccName)
    (m2 : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hacval : m2.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : NatHeads m2 φ := by
  intro hg ρ
  rw [hacval]
  -- the three lookups are the prefix's, so the guard reflects
  have hfind : ∀ p : Name, c₀.name ≠ p →
      (⟨c₀ :: env.consts, env.tables⟩ : Env).find? p = env.find? p := by
    intro p hp
    show List.find? _ (c₀ :: env.consts) = _
    rw [List.find?_cons_of_neg (by simpa using hp)]
    rfl
  have hgold : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hg
    rw [hfind _ hnN] at h1
    rw [hfind _ hnZ] at h2
    rw [hfind _ hnS] at h3
    exact ⟨⟨h1, h2⟩, h3⟩
  have e1 : acvalWith mp.base2.acval c₀.name A natZeroName
      = mp.base2.acval natZeroName :=
    acvalWith_ne (fun h => hnZ h.symm)
  have e2 : acvalWith mp.base2.acval c₀.name A natSuccName
      = mp.base2.acval natSuccName :=
    acvalWith_ne (fun h => hnS h.symm)
  have e3 : acvalWith mp.base2.acval c₀.name A natName
      = mp.base2.acval natName :=
    acvalWith_ne (fun h => hnN h.symm)
  have := mp.nat_heads φ hgold ρ
  simpa only [e1, e2, e3] using this

/-- **The stored family descends past a *reserved-named* cons.**
`etaFamilyStored_descend`'s twin, with both disequalities taken
from the name rather than from the kind: the law's own
`reservedBasisNames.contains T = false` premise separates the former,
and `EtaFamilyStored`'s name-only conjunct separates the capability
constructor. -/
theorem etaFamilyStored_descend_reserved {c₀ : ConstantInfo} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    (hres₀ : ConLeche.reservedBasisNames.contains c₀.name = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hf : (⟨c₀ :: env.consts, env.tables⟩ : Env).find? T = some (.indInfo cvT caps))
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts, env.tables⟩ T caps) :
    env.find? T = some (.indInfo cvT caps) ∧
      ConLeche.EtaFamilyStored env T caps ∧
      T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name := by
  obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
  have hnT : T ≠ c₀.name := fun hh => by rw [hh, hres₀] at hresT
                                         exact nomatch hresT
  have hnC : caps.etaCtor ≠ c₀.name := fun hh => by
    rw [hh, hres₀] at hCres; exact nomatch hCres
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts, env.tables⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hn hh.symm)]
  exact ⟨by rwa [hdown _ hnT] at hf, ⟨hCres, ⟨cvC, by rwa [hdown _ hnC] at hfC⟩, hfP⟩,
    hnT, hnC⟩

/-- **`CapsOk` at a fresh cons whose name is reserved** —
`capsOk_cons_fresh`'s basis twin.  Every basis block's constant is a
reserved name (`BasisKind.declsA` ⊆ `reservedBasisNames`), and both
`CapsOk` halves are premised on a *non*-reserved family, so no
stored family can be completed here and the law's leaves are all
prefix leaves. -/
theorem capsOk_cons_basis (mp : EnvModelM V env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (hres₀ : ConLeche.reservedBasisNames.contains c₀.name = true)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  constructor
  · -- the η half
    intro T cvT caps hf hcape hres hfam φ' us hlen
    obtain ⟨hfE, hfam₀, hnT, hnC⟩ :=
      etaFamilyStored_descend_reserved hres₀ hres hf hfam
    obtain ⟨TVa, hTVa, hokTVa, hlaw, hcoh⟩ :=
      hprev.1 T cvT caps hfE hcape hres hfam₀ φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_, ?_⟩
    · rw [hac]
      exact denote_cons_mono hfresh _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT] at hmem
      rw [hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
    · refine hcoh.transport (fun cvC nPc nFc hf₂ => ?_)
        (fun cvC nPc nFc TCa hf hTCa => ?_) (by rw [hac, acvalWith_ne hnT])
        (fun _ _ _ => rfl)
      · rwa [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnC hh.symm)] at hf₂
      · rw [hac]
        exact denote_cons_mono hfresh _ 0
          (constsBound_instType mp.base2.wf
            (ConLeche.Env.find?_mem hf) us) hTCa
  · -- the unit-like half: one leaf to move, the disequality off the
    -- law's own non-reserved premise
    intro T cvT caps hf hcapu hres φ' us hlen
    have hnT : T ≠ c₀.name := fun hh => by
      rw [hh, hres₀] at hres; exact nomatch hres
    have hfE : env.find? T = some (.indInfo cvT caps) := by
      rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnT hh.symm)] at hf
      exact hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.2 T cvT caps hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denote_cons_mono hfresh _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hx hy
      rw [hac, acvalWith_ne hnT] at hx hy
      exact hlaw ρ ts rest x y hlents hfit hx hy

end ConLeche.Model
