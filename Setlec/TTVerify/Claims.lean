import Setlec.TTVerify.EnvTT
import Setlec.TTVerify.Inversion
import Setlec.TTVerify.Inst
import Setlec.Verify.Leaves
import Setlec.TT.Deq
import Setlec.Verify.Knot

/-!
# The fuel-induction claims

The transpose of `Setlec/Model/Core/Claims.lean` and
`Setlec/Model/TypeChecker.lean`.  Reduction, definitional equality and
inference are mutually recursive on a shared fuel — the beta rule
certifies redexes by inference plus defeq — so their soundness is one
mutual fuel induction, exactly as on the set-model side.

The transposition rule is the one from `Setlec/TTVerify/EnvTT.lean`:
**an equation between interpretations becomes a `Setlec.TT.Deq` between
denotations, and a membership becomes a `HasType` derivation.**
Concretely

| set model | here |
|---|---|
| `interpExpr e' = interpExpr e` | `Deq Δ ⟦e'⟧ ⟦e⟧` |
| `va = vb` (defeq) | `Deq Δ ⟦a⟧ ⟦b⟧` |
| `v ∈ˢ tv` (infer) | `HasType Δ ⟦e⟧ ⟦t⟧` |
| `FvarsOk … ρ e` | `CtxOk … Δ e` |
| `AnnotOk …` | **nothing** |

Two differences are worth reading off that table.

**`AnnotOk` is gone from every claim.**  On the set-model side it is a
hypothesis of the whnf/defeq claims and a *conclusion* of the infer
claim (task #100 stage 6, replacing the deleted annotation pass).  Here
there is nothing to carry: a derivation supplies at each binder what
`AnnotOk` was reconstructing, so the infer claim's conclusion is just
the typing, and the whnf claims lose two hypotheses and a conjunct.

**Definedness of the denotation replaces truthfulness.**  `denote` is
`Option`-valued, like `interpExpr` and unlike the layer's own total
`interp`, because it reads arbitrary `Expr`s.  So the reduction claims
are stated *conditionally on the subject denoting* — "if the input
denotes, the output denotes and the two are `Deq`" — which is the
partial-function form of `interpExpr e' = interpExpr e`.  The infer
claim, being the one that establishes definedness, asserts it outright.

## The typing hypothesis is threaded — but the conclusion is
## *typeability*, not typing at the same type

The reduction and defeq claims below take **`Typeable Δ ⟦e⟧`** as a
hypothesis, and the reduction claims return `Typeable Δ ⟦e'⟧` — "the
reduct is typeable at *some* type", not "at the same type".  Both the
threading and the existential form need their reasons on the record,
because an earlier revision of this file got the second one wrong.

### Why thread at all (unchanged, and measured)

The checker's whole certificate tax is **one** call, the per-argument
re-check in `inferSpineI`, which establishes exactly `⟦a⟧ ∈ˢ ⟦A⟧` at
every application node — `AnnotOk`'s app clause — and exists only
because `AnnotOk` is a *conclusion* of the inference claim rather than
a hypothesis carried along.  A typing judgment is the channel that fact
was missing.  See `Setlec/TTVerify/DESIGN.md` §6.

### RETRACTED: "subject reduction is free, since conversion is
### equality reflection"

**That claim was written here as fact and it is false.**  `conv`
(`Setlec/TT/Judgment.lean`) changes the *type* of a fixed subject; **no
rule changes the subject of a fixed typing**.  So the schema

> `Γ ⊢ t : A` and `Deq Γ t t'` imply `Γ ⊢ t' : A`

is not merely underivable — it is **refutable**.  Take
`G := .app (.sort 0) (.sort 0)`, `t := natZeroT`,
`t' := .letE G natZeroT (.bvar 0)`:

1. `[] ⊢ natZeroT : natT` by `const`;
2. `(.bvar 0).inst natZeroT = natZeroT` definitionally, so the
   premise-free `zeta` and `symm` give `Deq [] natZeroT t'`;
3. `t'` has **no type at all**: only `letE` and `conv` have
   `.letE`-shaped conclusions and `conv` preserves the subject, so any
   derivation bottoms out at `letE`, which demands `⊢ G : sort u` —
   requiring a derivable chain from `sort 1` to a syntactic `pi`, which
   soundness refutes in every model (`∅ ∈ˢ univ 1` but `∅ ∉ piC X F`),
   unconditionally, the Aczel instance being `sorry`-free.

The culprit is the premise-free equational discipline of
`Setlec/TT/DESIGN.md` §2.4: `zeta`, and `beta`'s unconstrained body,
**equate typed terms with untypeable ones by design**.  That discipline
is right — it keeps bridge obligations minimal — but it means an
equation carries no typing information whatsoever.

### Why the conclusion is existential

Given the retraction, a reduct's typing has to be *built*, not
transported.  For beta that is: invert the λ, use the beta certificate
for the argument, and apply a `HasType` substitution lemma.  That
yields `Δ ⊢ b.inst x : B'.inst x` — a typing at the *substituted body
type*, which is **not** the redex's ambient type `A`.

Bridging the two would need `Deq Δ (B'.inst x) A`, and the only route
from what inversion supplies runs through **Π-codomain-injectivity** —
refuted by the same `propext` witness that refutes domain-injectivity
(`Setlec/TTVerify/DESIGN.md` §6): `False → False` and
`Nat → PUnit.{0}` are interderivable `Prop`s whose domains *and*
codomains differ.  (Whether some other route exists is open; the
existential form makes the question unnecessary, so it is not pursued.)

`Typeable` is what the loop actually needs anyway: `whnf` re-enters
`whnfCore` on the reduct, and all it must know is that the reduct *has*
a type — which is what feeds the next step's inversions.
## Status (task #119 stage 2)

This module states the claims, proves the **fuel-zero** case of the
mutual induction outright, and assembles the induction from four
per-level step hypotheses.  Those four steps — the `succ` case, i.e.
the clause-by-clause mirror of `Setlec/Model/Core/{Whnf,DefEq,Infer,
Iota,…}.lean` — are the remaining work of stage 2 and are named `Prop`s
here for the same reason `CheckDeclTT` is one: so that every consumer
of an unproved step is visible in the source rather than in a comment.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {V : Type u}

/-! ## The context correspondence

The transpose of `FvarsOk`.  `FvarsOk` constrains the free-variable
*valuation* `ρ`; there is no valuation here (see
`Setlec/TTVerify/Denote.lean`), so what it constrains instead is the de
Bruijn context `Δ`.

The index arithmetic is the whole content: an `fvar` opened at depth
`i` sits at de Bruijn *level* `i`, hence at index `d - 1 - i` when read
at depth `d`, and `HasType.bvar` types `.bvar j` at `Δ[j]` lifted by
`j + 1`.  With `j = d - 1 - i` and `i < d` that lift is by `d - i`,
which is what the clause below demands of the leaf's annotation. -/
def CtxOk (cval : TConstVal) (env : Env) (φ : Name → Nat) (d : Nat)
    (Δ : List VExpr) (e : Expr) : Prop :=
  Δ.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ A, Δ[d - 1 - l.1]? = some A ∧
      denote cval env φ d l.2.2 = some (A.liftN (d - l.1))

/-- At depth `0` the context is empty and there are no leaves to
constrain — the shape every declaration-level statement uses. -/
theorem CtxOk.nil {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {e : Expr} (h : e.fvarLeaves = []) : CtxOk cval env φ 0 [] e := by
  refine ⟨rfl, ?_⟩
  intro l hl
  rw [h] at hl
  exact nomatch hl

/-- **Opening a binder extends the context correspondence.**  Every
binder clause of `CheckStepTT` needs exactly this, and it is where
`denote_lift` earns its keep: an old leaf's annotation, denoted one
level deeper, is its old denotation lifted by one
(`denote_weaken_top`), which is precisely the extra `liftN` that
`Δ`'s new entry shifts every old index by.  The freshly opened
variable is the new head of `Δ`, at index `0`.

Note that `denote_weaken_top` is applied to the *annotations*, which is
why `CtxOk` demands them scoped below their own variable's index —
`WScoped`'s own condition on an `fvar` leaf, and what the checker's
scope guards establish. -/
theorem CtxOk.open {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {body ty : Expr} {n : Name} {A : VExpr}
    (hb : CtxOk cval env φ d Δ body) (ht : CtxOk cval env φ d Δ ty)
    (hty : denote cval env φ d ty = some A)
    (htyb : Expr.fvarsBelow d ty) :
    CtxOk cval env φ (d + 1) (A :: Δ) (body.instantiate1 (.fvar d n ty)) := by
  -- an already-present leaf: index unchanged, slot shifted by `Δ`'s new
  -- head, annotation one lift deeper
  have shift : ∀ l : Nat × Name × Expr, l.1 < d → Expr.fvarsBelow l.1 l.2.2 →
      ∀ B, Δ[d - 1 - l.1]? = some B →
        denote cval env φ d l.2.2 = some (B.liftN (d - l.1)) →
        l.1 < d + 1 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
          ∃ C, (A :: Δ)[d + 1 - 1 - l.1]? = some C ∧
            denote cval env φ (d + 1) l.2.2 = some (C.liftN (d + 1 - l.1)) := by
    intro l hlt hfb B hΔl hden
    refine ⟨by omega, hfb, B, ?_, ?_⟩
    · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
      simpa using hΔl
    · rw [denote_weaken_top hcl (Expr.fvarsBelow_mono (by omega) hfb), hden]
      simp only [Option.map_some, liftN_liftN]
      congr 2
      omega
  refine ⟨by simp [hb.1], ?_⟩
  intro l hl
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · obtain ⟨hlt, hfb, B, hΔl, hden⟩ := hb.2 l hl'
    exact shift l hlt hfb B hΔl hden
  · -- a leaf of the opened variable: either the variable itself (the
    -- new head of `Δ`, at index `0`) or one of its annotation's own
    -- leaves, which is an already-present leaf
    rw [Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, htyb, A, by simp, ?_⟩
      rw [denote_weaken_top hcl htyb, hty]
      simp only [Option.map_some]
      congr 2
      omega
    · obtain ⟨hlt, hfb, B, hΔl, hden⟩ := ht.2 l hl''
      exact shift l hlt hfb B hΔl hden

/-- `v` has a type in `Δ`.  The reduction claims' hypothesis and
conclusion, deliberately existential — see the module docstring, and in
particular the retraction: a reduct's typing at the *same* type is not
transportable along an equation, and is not reachable from what
inversion supplies either. -/
def Typeable (Δ : List VExpr) (v : VExpr) : Prop := ∃ A, HasType Δ v A

/-! ## The four claims -/

variable (m : EnvTT env) (φ : Name → Nat)

/-- Head normalization (no delta) preserves the denotation up to a
derivable equation.  Transpose of `WhnfCoreClaims`. -/
def WhnfCoreClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnfCore env fuel d e = .ok e' →
    CtxOk m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v → Typeable Δ v →
      ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' ∧
        Typeable Δ v'

/-- The reduction loop, ditto.  Transpose of `WhnfClaims`. -/
def WhnfClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnf env fuel d e = .ok e' →
    CtxOk m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v → Typeable Δ v →
      ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' ∧
        Typeable Δ v'

/-- A positive definitional-equality verdict yields a derivable
equation.  Transpose of `DefEqClaims`. -/
def DefEqClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δ : List VExpr},
    isDefEqCore env fuel d a b = .ok true →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb →
      Typeable Δ va → Typeable Δ vb → Deq Δ va vb

/-- Successful inference yields a typing derivation.  Transpose of
`InferClaims` — note that the set-model version's `AnnotOk` conjuncts
have no counterpart, so this is the whole of it. -/
def InferClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δ : List VExpr},
    inferTypeCore env fuel d e = .ok t →
    CtxOk m.cval env φ d Δ e →
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv

/-! ## The induction

`checkSoundTT` below is the transpose of `check_sound`.  Its `zero`
case is proved here (every fuel-zero spelling throws, so every claim is
vacuous); its `succ` case is the clause-by-clause work of stage 2, and
is taken as the hypothesis `CheckStepTT`. -/

/-- The step of the mutual fuel induction: the four claims at `fuel + 1`
from the four claims at `fuel`.  This is the transpose of the four
`*_claims` lemmas of `Setlec/Model/Core/*`, and it is what stage 2 of
task #119 discharges. -/
def CheckStepTT : Prop :=
  ∀ (env : Env) (m : EnvTT env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaimsTT m φ fuel → WhnfClaimsTT m φ fuel →
    DefEqClaimsTT m φ fuel → InferClaimsTT m φ fuel →
    WhnfCoreClaimsTT m φ (fuel + 1) ∧ WhnfClaimsTT m φ (fuel + 1) ∧
      DefEqClaimsTT m φ (fuel + 1) ∧ InferClaimsTT m φ (fuel + 1)

/-- The mutual soundness induction.  Transpose of `check_sound`; only
the step is outstanding. -/
theorem checkSoundTT {env : Env} (hstep : CheckStepTT) (m : EnvTT env)
    (φ : Name → Nat) :
    ∀ fuel : Nat, WhnfCoreClaimsTT m φ fuel ∧ WhnfClaimsTT m φ fuel ∧
      DefEqClaimsTT m φ fuel ∧ InferClaimsTT m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δ h
      rw [whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δ h
      rw [whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δ h
      rw [isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δ h
      rw [inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

/-! ## Fuel-generic wrappers

The forms every consumer uses; transposes of the `*_facts` / `*_sound`
wrappers at the end of `Setlec/Model/TypeChecker.lean`. -/

/-- Successful inference is sound: the subject denotes, its inferred
type denotes, and the first has a derivation of the second. -/
theorem inferTypeCore_soundTT {env : Env} (hstep : CheckStepTT)
    (m : EnvTT env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {e t : Expr}
    {Δ : List VExpr} (h : inferTypeCore env fuel d e = .ok t)
    (hΔ : CtxOk m.cval env φ d Δ e) :
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv :=
  (checkSoundTT hstep m φ fuel).2.2.2 h hΔ

/-- A positive definitional-equality verdict identifies denotations up
to a derivable equation. -/
theorem isDefEqCore_soundTT {env : Env} (hstep : CheckStepTT)
    (m : EnvTT env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {a b : Expr}
    {Δ : List VExpr} (h : isDefEqCore env fuel d a b = .ok true)
    (hΔa : CtxOk m.cval env φ d Δ a) (hΔb : CtxOk m.cval env φ d Δ b)
    {va vb : VExpr} (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb)
    (hta : Typeable Δ va) (htb : Typeable Δ vb) : Deq Δ va vb :=
  (checkSoundTT hstep m φ fuel).2.2.1 h hΔa hΔb hva hvb hta htb

/-- Reduction preserves the denotation up to a derivable equation and
keeps the reduct **typeable**.

That third conjunct is what lets the `whnf` loop re-enter on the
reduct without re-deriving anything.  It is *not* free — see the
retraction in this module's docstring: an equation transports no
typing, so the reduct's typing is built (inversion, the step's own
certificate, and `HasType` substitution), and it lands at the reduct's
own type rather than the subject's, which is why the conjunct is
existential. -/
theorem whnf_factsTT {env : Env} (hstep : CheckStepTT) (m : EnvTT env)
    (φ : Name → Nat) (fuel : Nat) {d : Nat} {e e' : Expr}
    {Δ : List VExpr} (h : whnf env fuel d e = .ok e')
    (hΔ : CtxOk m.cval env φ d Δ e) {v : VExpr}
    (hv : denote m.cval env φ d e = some v) (ht : Typeable Δ v) :
    ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' ∧
      Typeable Δ v' :=
  (checkSoundTT hstep m φ fuel).2.1 h hΔ hv ht

end Setlec.TTVerify
