import Setlec.SetR.Interp2.Keys2Cond

/-!
# `empty_pinned` at the annotated tier — and why no field is needed

Seal 51 recorded, as a stall, that `no_constant_of_Empty_R2` reads its
`Empty` content off `base`: there is no `empty_pinned` counterpart on
the `acval` side, so the emptiness fact is the collapse lane's and the
swap does not re-derive it over `interp2`.

**The check comes back: the counterpart is already determined, and no
`EnvS2U` field is wanted.**  `acval_erase` says the annotated leaf
erases to the collapse-lane one, `EnvS.empty_pinned` says that one is
`emptyT u = .const .empty [u]`, and **`erase` is injective at the
constant clause** — a `VExpr` constant is the image of exactly one
`AVExpr`.  So the annotated leaf *is* `.const .empty [u]`, and
`interp2` values it by `bval2 … .empty = empty` as `interp` does.

## Why the erasure refutation does not bite

`interp2_ne_interp_erase` (`Keys2Probe.lean`) says `interp2` is **not**
`interp ∘ erase`, and its countermodel is an empty-domain λ: the
collapse sends it to the proof point, the two-regime reading keeps it
a graph.  That is a **binder** disagreement.  At a *constant* leaf the
two readings are `bval` and `bval2` at the same `BConst`, and at
`.empty` both are the empty set — so the one place this argument needs
them to agree is the one place the refutation does not reach.

*Rule the check exercises: a refutation names the shape it refutes.
Before routing around one, look at whether the subject is that shape.*

## What is still read off `base`

`EnvS.empty_pinned` itself, and nothing else.  That is not a gap this
tier can close: the pin is what makes `Empty` empty, and the annotated
valuation is defined to erase to the pinned one.  The syntactic
`find?`/arity facts come from the collapse lane's `mem_type` exactly
as they do in v1; the **membership** is the annotated tier's own
(`mem_type2` over `interp2`), which is the half seal 51 said was
missing.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo emptyName)

universe w

variable {V : Type w} [SetTheory V]

/-- **`erase` is injective at the constant clause.**  Every other
`AVExpr` constructor erases to a different `VExpr` constructor, so a
constant erasure has a constant source — with the *same* name and the
*same* level numerals, since the constant clause carries no
annotation to forget. -/
theorem erase_eq_const {ea : AVExpr} {c : BConst} {us : List Nat}
    (h : ea.erase = .const c us) : ea = .const c us := by
  cases ea with
  | bvar i => rw [AVExpr.erase_bvar] at h; exact nomatch h
  | sort u => rw [AVExpr.erase_sort] at h; exact nomatch h
  | const c' us' =>
    rw [AVExpr.erase_const] at h
    injection h with h1 h2
    rw [h1, h2]
  | app f a => rw [AVExpr.erase_app] at h; exact nomatch h
  | lam u ty b => rw [AVExpr.erase_lam] at h; exact nomatch h
  | pi u v ty b => rw [AVExpr.erase_pi] at h; exact nomatch h
  | letE ty v b => rw [AVExpr.erase_letE] at h; exact nomatch h
  | eqE ty l r => rw [AVExpr.erase_eqE] at h; exact nomatch h
  | proj i e => rw [AVExpr.erase_proj] at h; exact nomatch h
  | prf => rw [AVExpr.erase_prf] at h; exact nomatch h

/-- **`empty_pinned`, transported to the annotated valuation.**  The
whole of item 2's check, as one lemma: `acval_erase` plus the
collapse-lane pin plus erasure injectivity determine the annotated
leaf outright.

*No `EnvS2U` field is added, and none is wanted.*  A field is earned
when a consumer can attempt its discharge and the invariant cannot
supply it; here the invariant supplies it. -/
theorem acval_empty_pinned {env : Env} (m : EnvS2U V env)
    (ψ : Name → Nat) : ∃ u, m.acval emptyName ψ = .const .empty [u] := by
  obtain ⟨u, hu⟩ := m.base.empty_pinned ψ
  exact ⟨u, erase_eq_const (by rw [m.acval_erase, hu]; rfl)⟩

/-- …so its `interp2` reading is the empty set, at every assignment. -/
theorem interp2_acval_empty {env : Env} (m : EnvS2U V env)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (m.acval emptyName ψ) = empty := by
  obtain ⟨u, hu⟩ := acval_empty_pinned m ψ
  rw [hu, interp2_const]
  rfl

/-- **`no_constant_of_Empty_R`, over `interp2`.**  The membership is
now the annotated tier's own — `mem_type2` at the stored constant,
against the `denote2` of its type — and only the pin itself is read
off `base`.

Contrast with `no_constant_of_Empty_R2`, whose whole proof is v1's at
`m.base`: there the annotated valuation plays no part at all. -/
theorem no_constant_of_Empty_2 {env : Env} (m : EnvS2U V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨t, hTi, -⟩ := m.base.mem_type c hc (fun _ => 0)
  rw [hty, denoteClosed, denote_const] at hTi
  revert hTi
  cases hf : env.find? emptyName with
  | none => intro hTi; exact nomatch hTi
  | some ci =>
    dsimp only
    split
    · next hlen =>
      intro hTi
      obtain rfl := (Option.some.inj hTi).symm
      have hden2 : denote2 CheckMode.setModel m.acval env (fun _ => 0)
          0 0 c.toConstantVal.type
          = some (m.acval emptyName (Level.substFn (fun _ => 0)
            ci.toConstantVal.levelParams [])) := by
        rw [hty]
        exact denote2_const hf hlen
      have hmem := m.mem_type2 CheckMode.setModel (fun _ => 0) 0 c hc _
        hden2 (fun _ => (SetTheory.empty : V))
      rw [interp2_acval_empty m] at hmem
      exact not_mem_empty _ hmem
    · intro hTi; exact nomatch hTi

/-! ## The three sweeps

**1. Smallest fuel.**  `no_constant_of_Empty_2` asserts a `denote2`
success — at fuel `0`, the smallest there is — and it is the constant
clause, which consults no run.  Nothing here is fuel-sensitive.

**2. Vacuity.**  Every hypothesis is met at a real environment: the
premise pair is `EnvS`'s own `mem_type` shape, and the conclusion is
`False`, which is not `rfl`-provable from anything present.
`acval_empty_pinned` is exercised by `interp2_acval_empty`, which is
exercised here.

**3. Tombstones.**  A file added, none edited.  In particular
`interp2_ne_interp_erase` is **not** routed around: this file does not
use an erasure bridge at all, it uses erasure *injectivity* at one
constructor, and the module docstring records why the two are
different. -/

end Setlec.SetR.Interp2
