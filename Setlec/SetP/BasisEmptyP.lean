import Setlec.SetP.BasisStepP
import Setlec.SetR.Install.BasisS

/-!
# The `Empty` block, P tier: the type-reading recipe, executed once
(task #161, ENDGAME F)

The ENDGAME E seal itemized the basis tier's remaining bill and its
item 2 — "compute `denoteP` at each basis `ConstantInfo`'s type and
exhibit `AVExpr.BitAgree` to `BConst.type2 c us`" — is the only item
with twenty-two instances.  This file executes it at the smallest
block, and the point is not the two constants: it is that **the recipe
is now a proof and not a design**.

## The recipe, in four moves

1. `show` the pinned `ConstantInfo`'s type as a literal `Expr` tree
   (`show … from rfl`) — the `denoteP` clauses are `match`es and will
   not reduce until the scrutinee is a constructor application.  v1's
   `extendEmptyRecS` needs the same move for the same reason;
2. walk it with `denoteP_forallE`/`denoteP_sort`/`denoteP_app`/
   `denoteP_fvar` and `Expr.instantiate1_eq_self` at every closed
   binder body, with the constant leaves supplied by
   `acval_basis_pinned` (`Interp2/BasisConsP.lean`) — the P tier's
   basis leaves are pinned *for free*, so no new field is needed;
3. exhibit `AVExpr.BitAgree` from the reading to `BConst.type2`;
4. `bitAgree_okP` + `AnnotOkP_bconst_type` grades it and
   `interp2_eq` + `bval2_mem_type` inhabits it.

## THE FINDING: the bits match because `pwBit` and `type2` were written
## from the same pin

Move 3 is where the batch could have failed, and it does not, for a
reason worth naming.  `denoteP`'s codomain slot at a binder is
`pwBit ψ mb.pw`, and `pwBit ψ pw = if pw.holds ψ then 0 else 1`.  At
`Empty.rec`'s stored binders the pins are `.never` (the motive's
domain) and `.ifAllZero [u]` (the two outer binders), so the reading's
numerals are `1` and `0 ↔ ψ u = 0`.  `BConst.type2 .emptyRec [1, v]`
carries `v + 1` and `v` in those same three slots.  Zero-ness agrees on
the nose — `1 = 0 ↔ v + 1 = 0` (both false) and `pwBit ψ (.ifAllZero
[u]) = 0 ↔ ψ u = 0` — which is the ENDGAME E doctrine *seen from the
other side*: E showed the hand-built towers' bits are read off the type
pins; here the **type readings'** bits are read off the same pins, and
`BitAgree` is precisely the statement that the two readings never
disagree where anything looks.

Nothing in this file chooses a numeral.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  emptyA emptyRecA emptyName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `Empty` former's type reading: `Sort 1`, which is
`BConst.type2 .empty [1]` on the nose (no `BitAgree` needed — the
former has no binder, so there is no numeral to disagree about). -/
theorem denoteP_emptyA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨emptyA :: env.consts⟩ ψ 0 emptyA.toConstantVal.type
      = some (BConst.type2 .empty [1]) := by
  rw [show emptyA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denoteP_sort]
  rfl

/-- **`Empty`, installed at the P tier.** -/
theorem extendEmptyP (mp : EnvS2PM V μ env)
    (hfresh : env.find? emptyName = none)
    (hbase : EnvS V ⟨emptyA :: env.consts⟩)
    (hag : ∀ n, n ≠ emptyA.name → mp.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval emptyA.name ψ = VExpr.const .empty [1]) :
    Nonempty (EnvS2PM V μ ⟨emptyA :: env.consts⟩) := by
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun _ => AVExpr.const .empty [1]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteP_emptyA_type ψ⟩) ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteP_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact AnnotOkP_bconst_type V .empty [1] ρ
  · intro ψ ta h ρ
    rw [denoteP_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval2_mem_type V .empty [1] ρ

/-! ## `Empty.rec` — the recipe's real instance

Two binders, three stored `PropWhen` pins, and the reading's numerals
are all three of them. -/

/-- `pwBit` at a `.never` pin: the graph regime, unconditionally. -/
theorem pwBit_never (ψ : Name → Nat) :
    pwBit ψ Setlec.PropWhen.never = 1 := rfl

/-- `pwBit` at a one-parameter `.ifAllZero` pin: zero exactly when the
parameter is.  One of the *three* shapes every basis binder reduces to
— see `pwBit_ifAllZero_nil`/`pwBit_ifAllZero_pair` for the other two. -/
theorem pwBit_ifAllZero_single (ψ : Name → Nat) (n : Name) :
    pwBit ψ (Setlec.PropWhen.ifAllZero [n]) = 0 ↔ ψ n = 0 := by
  rw [pwBit_eq_zero_iff]
  simp [Setlec.PropWhen.holds]

/-! ### STOP-AND-NAME: two `pwBit` shapes, not one (ENDGAME G)

The ENDGAME F resume-here's item 1 grants a freedom — "the two `pwBit`
lemmas cover every binder" — and the discipline ledger's rule is that a
recorded freedom is a claim.  Re-checked by `#eval` over
`BasisKind.declsA`'s stored `PropWhen`s, and **it is false**: the
twenty remaining readings carry *three* pin shapes, not two.

| shape | where | `pwBit` |
|---|---|---|
| `.never` | everywhere | `1` (`pwBit_never`) |
| `.ifAllZero [p]` | `Nat.rec`, `PUnit.rec`, `Empty.rec`, `Eq.rec`, `Quot.mk`, `Quot.lift` | `0 ↔ ψ p = 0` |
| **`.ifAllZero []`** | `Eq.refl`, `PSigma'.rec`, `Quot.lift`, `Quot.ind`, `Quot.sound` | **`0`, unconditionally** |
| **`.ifAllZero [u, v]`** | `PSigma'.mk` | **`0 ↔ ψ u = 0 ∧ ψ v = 0`** |

Neither missing shape is a wall — both are one-liners below — but the
freedom was granted unchecked and the ledger's dual entries are why it
cost an `#eval` rather than a walled block.  F retired E's granted
vacuity the same way; this is the third such retirement running. -/

/-- `pwBit` at the *empty* `.ifAllZero` pin: zero unconditionally,
because `[].all _` is `true`.  The pin the `Prop`-valued basis
constants carry (`Eq.refl`, `PSigma'.rec`, `Quot.ind`, `Quot.sound`,
and `Quot.lift`'s invariance binder). -/
theorem pwBit_ifAllZero_nil (ψ : Name → Nat) :
    pwBit ψ (Setlec.PropWhen.ifAllZero []) = 0 := by
  rw [pwBit_eq_zero_iff]
  simp [Setlec.PropWhen.holds]

/-- `pwBit` at a two-parameter `.ifAllZero` pin: zero exactly when
*both* parameters are.  `PSigma'.mk`'s pin, and the basis tier's only
instance. -/
theorem pwBit_ifAllZero_pair (ψ : Name → Nat) (n m : Name) :
    pwBit ψ (Setlec.PropWhen.ifAllZero [n, m]) = 0 ↔ (ψ n = 0 ∧ ψ m = 0) := by
  rw [pwBit_eq_zero_iff]
  simp [Setlec.PropWhen.holds]

/-- **`Empty.rec`'s type reading.**  The four moves of the module
docstring; the leaves are `acval_basis_pinned` at `Empty`. -/
theorem denoteP_emptyRecA_type {m : EnvS2Core V env}
    {A : (Name → Nat) → AVExpr} (ψ : Name → Nat)
    (hE : env.find? emptyName = some emptyA) :
    denoteP (acvalWith m.acval emptyRecA.name A)
        ⟨emptyRecA :: env.consts⟩ ψ 0 emptyRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .empty [1]) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [1])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : Setlec.TTVerify.pinnedDirectT emptyName ψ
      = some (VExpr.const .empty [1]) := by
    simp +decide [Setlec.TTVerify.pinnedDirectT]
  have hleaf : acvalWith m.acval emptyRecA.name A emptyName ψ
      = AVExpr.const .empty [1] := by
    rw [acvalWith_ne (by decide)]
    exact acval_basis_pinned hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval emptyRecA.name A)
          ⟨emptyRecA :: env.consts⟩ ψ d (.const emptyName [])
        = some (AVExpr.const .empty [1]) := by
    intro d
    have hf : (⟨emptyRecA :: env.consts⟩ : Env).find? emptyName
        = some emptyA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hE
    rw [denoteP_levelless_const hf (by rfl), hleaf]
  rw [show emptyRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
            (.sort (.param uN)) { bi := .default, pw := .never })
          (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
            (.app (.bvar 1) (.bvar 0))
            { bi := .default, pw := .ifAllZero [uN] })
          { bi := .default, pw := .ifAllZero [uN] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading agrees with `BConst.type2` on every numeral anything
reads.**  Three binders, three `pwBit`s, three `type2` slots, and the
iffs are `pwBit_never` and `pwBit_ifAllZero_single` — nothing here is
chosen. -/
theorem bitAgree_emptyRecA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .empty [1]) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [1])
          (.app (.bvar 1) (.bvar 0))))
      (BConst.type2 .emptyRec [1, ψ uN]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.const _ _) (.app (.bvar 1) (.bvar 0)))
  rw [pwBit_never]
  simp

/-- **`Empty.rec`, installed at the P tier.** -/
theorem extendEmptyRecP (mp : EnvS2PM V μ env)
    (hE : env.find? emptyName = some emptyA)
    (hfresh : env.find? emptyRecA.name = none)
    (hbase : EnvS V ⟨emptyRecA :: env.consts⟩)
    (hag : ∀ n, n ≠ emptyRecA.name →
      mp.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval emptyRecA.name ψ
      = VExpr.const .emptyRec [1, ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨emptyRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_emptyRecA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .emptyRec [1, ψ uN]) ψ hE
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .emptyRec [1, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_emptyRecA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .emptyRec [1, ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_emptyRecA ψ) ρ]
    exact bval2_mem_type V .emptyRec [1, ψ uN] ρ

/-! ## The block

The dispatch mirrors `declBasisS_emptyK` link for link, and drives the
two lanes in lockstep: each cons runs the v1 install first (for the
`EnvS` base and its `cval` equation) and then the P install on top of
it.  `BasisInstallR` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `Empty` block, installed at the P tier.**  `BasisStepPB`'s
`emptyK` branch. -/
theorem declBasisPB_emptyK {env₂ : Env} (mp : EnvS2PM V μ env)
    (h : Setlec.SetR.BasisInstallR env Setlec.BasisKind.emptyK.declsA env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  rw [show Setlec.BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? emptyA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨emptyA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ := extendEmptyS mp.base hf1 hwf1
  obtain ⟨mp1⟩ := extendEmptyP mp hf1 m1
    (fun n hn => by rw [hm1, cvalWith_ne hn])
    (fun ψ => by rw [hm1, cvalWith_self]; rfl)
  have hE : (⟨emptyA :: env.consts⟩ : Env).find? emptyName
      = some emptyA := by
    rw [Setlec.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨emptyA :: env.consts⟩ : Env).find? emptyRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨emptyRecA :: emptyA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ emptyRecA.toConstantVal.type = true
    simp only [show emptyRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.sort (.param uN)) { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.app (.bvar 1) (.bvar 0))
              { bi := .default, pw := .ifAllZero [uN] })
            { bi := .default, pw := .ifAllZero [uN] } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find?
        emptyName = some emptyA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]
      exact hE
    rw [hf]
    simp
  obtain ⟨m2, hm2⟩ := extendEmptyRecS mp1.base hE hf2 hwf2
  exact extendEmptyRecP mp1 hE hf2 m2
    (fun n hn => by rw [hm2, cvalWith_ne hn])
    (fun ψ => by rw [hm2, cvalWith_self])

/-! ## STOP-AND-NAME: no basis `rec_rules` row is vacuous by `fire`

The ENDGAME E seal's resume-here item 4 reads "`Eq.rec`'s single rule
is `.inert`, so its row is **vacuous** — `RecRulesP` premises
`fire ≠ .inert`".  That is false, and the two lemmas below mechanize
why: the **raw** pins (`eqBasis`, `natBasis`, …) all carry `.inert`,
the **annotated** pins (`BasisKind.declsA`) all carry `.plain`, and
`BasisStepPB` conses the annotated ones.  The annotator rewrites
`fire`; E read the raw pin.

So `Eq.rec` owes a full `RecRuleLawP`, and so do `PUnit.rec`,
`Nat.rec` (twice), `PSigma'.rec`, `Quot.lift` and `Quot.ind` — seven
rules across six recursors.  The one genuinely vacuous row is
`Empty.rec`'s, and it is vacuous because it has **no rules at all**,
which is exactly the case `declStepPM_of_basis_cons`'s `hnotrec`
premise covers, and exactly the block this file closes.

The compensation is real and general: since every stored rule is
`.plain`, `RecRuleLawP`'s two `.nested` conjuncts are unsatisfiable
across the whole basis tier, so the nested-aux machinery of task #105
is not needed here at all.  What is live in each of the seven rows is
the `.plain` conjunct and the fold contract. -/

/-- **Every stored basis recursor rule fires `.plain`.**  Computed, not
argued — and it is the *annotated* pin that governs. -/
theorem basis_rec_rules_plain (kind : Setlec.BasisKind) :
    ∀ ci ∈ kind.declsA,
      (match ci with
       | .recInfo _ _ _ rules =>
         rules.all fun rl => Setlec.RecRule.fire rl == .plain
       | _ => true) = true := by
  cases kind <;> decide

/-- **`Empty.rec` is the only basis recursor with no rules** — the sole
row `declStepPM_of_basis_cons`'s `hnotrec` premise can discharge, and
the reason this file's block is the one that closes. -/
theorem basis_rec_rules_nonempty (kind : Setlec.BasisKind)
    (hk : kind ≠ .emptyK) :
    ∀ ci ∈ kind.declsA,
      (match ci with
       | .recInfo _ _ _ rules => !rules.isEmpty
       | _ => true) = true := by
  cases kind
  case emptyK => exact absurd rfl hk
  all_goals decide

end Setlec.SetR.Interp2
