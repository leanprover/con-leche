module

public import ConLeche.Model.RecRulesCons

public section

/-!
# The basis-cons preservation kit (task #161)

A basis block conses *inductive-kind* heads — `indInfo`, `ctorInfo`,
`recInfo` — and the existing preservation lemmas are all keyed on the
value kinds:

| field | value-kind lemma | at a basis cons |
| --- | --- | --- |
| `nat_ops` | `natOps_cons_fresh` | **reusable** (`Or.inl`: not a `defnInfo`) |
| `div_mod` | `divMod_cons_fresh` | **reusable**, same disjunct |
| `eq_law` | `eqLaw_cons_fresh` | **reusable** (the `Eq` disequality, off freshness) |
| `nat_heads` | `natHeads_cons_fresh` | **REFUTED** — its `hknd` premise is the cons's own kind |
| `rec_rules` | `recRules_cons_fresh` | **reusable** at a non-recursor (below) |

This file supplies the replacement.

`nat_heads`: the guard reads exactly three names, so a
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

end ConLeche.Model
