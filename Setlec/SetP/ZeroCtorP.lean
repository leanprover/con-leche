import Setlec.SetP.CapstoneP
import Setlec.SetP.AxiomMemP

/-!
# Zero-constructor inductives are uninhabited (task #181)

The pinned `Empty`/`False` capstones (`CapstoneP.lean`) read the leaf's
value off the pin.  This module proves the **general** statement for
every zero-constructor inductive an accepted stream declares — `PEmpty`,
a user's `inductive Void : Type where`, `False` itself had it not been
pinned — with no knowledge of how the block was installed (the direct
sum route at `n = 0`, task #175, or anything else), from one fact the
P invariant records about every stored constant: it inhabits its type's
reading (`EnvS2PM.mem_typeP`).

## The argument

A zero-constructor block's recursor eliminates into every sort (the
official kernel's `elim_only_at_universe_zero` is `false` at zero
constructors), so the environment stores

    R : ∀ (motive : T → Sort u) (t : T), motive t

for the family `T`.  Its value `r` inhabits that type's reading, a
Π-tower.  Instantiate the motive at the constant `λ _. ∅` — a member of
`T → Sort u`'s reading, since `∅` is in every universe — and the major
at the alleged proof `c : T`: `r (λ _. ∅) c ∈ (λ _. ∅) c = ∅`.  The two
squash regimes are read off the validated annotations: a binder whose
bit is `0` has a truth-value codomain (`AnnotValidV`), which is exactly
`app_mem_piR`'s fibre premise; and the motive domain's bit cannot be
`0` — that would make `Sort u` a truth value at the witness `c`
(`univ_not_mem_univZero`).

So the hypotheses are the stored recursor's *type* (the syntactic
`zeroCtorRecTy` shape, binder names and annotations free) and the
stored constant's type `T ls` at any level instance; nothing about the
recursor's name, rules, or the block's constructors.  A block with
constructors cannot store such a recursor — its minors would be
binders in between — so "has a stored large eliminator of this shape"
*is* "is a stored zero-constructor inductive", read off the
environment.

**Parameters.**  The statement is at a parameterless family.  The
parameter-applied form `c : T q⃗` needs the readings `⟦q_i⟧` to fit the
recursor's parameter binders, which the P invariant supplies only
through domain uniqueness (`piR_dom_unique`) at *graph-regime*
parameter bits — and the validated-annotation invariant is
one-directional (`bit = 0 → truth value`), so a parameter binder over
an empty domain may carry bit `0` as far as the environment invariant
knows.  Making the bits part of the hypothesis, or tracing the block's
install through the fold, are the two routes; neither is taken here —
see DESIGN.md, task #181.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- The type of a zero-constructor block's recursor over a parameterless
family `T` at its level parameters `lps`:
`∀ (motive : T → Sort elim) (t : T), motive t`, with the binder names
and the stored binder annotations left free. -/
def zeroCtorRecTy (T : Name) (lps : List Name) (elim : Name)
    (mN tN₁ tN₂ : Name) (mb₁ mb₂ mb₃ : BinderMeta) : Expr :=
  .forallE mN
    (.forallE tN₁ (.const T (lps.map .param)) (.sort (.param elim)) mb₁)
    (.forallE tN₂ (.const T (lps.map .param)) (.app (.bvar 1) (.bvar 0)) mb₂)
    mb₃

/-- The reading of `zeroCtorRecTy` at any assignment: the Π-tower over
the family's leaf, its bits the stored annotations'. -/
theorem denoteP_zeroCtorRecTy {m : EnvS2Core V env} {T : Name}
    {ci : ConstantInfo} (hT : env.find? T = some ci) (ψ : Name → Nat)
    (elim mN tN₁ tN₂ : Name) (mb₁ mb₂ mb₃ : BinderMeta) :
    denoteP m.acval env ψ 0
        (zeroCtorRecTy T ci.toConstantVal.levelParams elim mN tN₁ tN₂ mb₁ mb₂ mb₃)
      = some (.pi 0 (pwBit ψ mb₃.pw)
          (.pi 0 (pwBit ψ mb₁.pw) (m.acval T ψ) (.sort (ψ elim)))
          (.pi 0 (pwBit ψ mb₂.pw) (m.acval T ψ) (.app (.bvar 1) (.bvar 0)))) := by
  have hleaf : ∀ d, denoteP m.acval env ψ d
      (.const T (ci.toConstantVal.levelParams.map .param)) = some (m.acval T ψ) := by
    intro d
    rw [denoteP_const hT (by simp)]
    congr 1
    exact m.acval_params T ci hT _ _ (fun p _ => Level.substFn_map_param)
  simp [zeroCtorRecTy, denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, hleaf, Level.eval]

/-- **An environment carrying the P invariant stores no inhabitant of a
family with a stored zero-constructor eliminator.**  See the module
docstring for the argument. -/
theorem no_constant_of_zeroCtorRec_P (mp : EnvS2PM V μ env)
    {T : Name} {ci : ConstantInfo} (hT : env.find? T = some ci)
    {R : ConstantInfo} (hR : R ∈ env.consts)
    {elim mN tN₁ tN₂ : Name} {mb₁ mb₂ mb₃ : BinderMeta}
    (hRty : R.toConstantVal.type =
      zeroCtorRecTy T ci.toConstantVal.levelParams elim mN tN₁ tN₂ mb₁ mb₂ mb₃)
    (c : ConstantInfo) (hc : c ∈ env.consts) {ls : List Level}
    (hty : c.toConstantVal.type = .const T ls) : False := by
  -- the alleged proof's type reads to the family's leaf
  obtain ⟨ta, hta0⟩ := mp.type_reads c hc (fun _ => 0)
  have hta := hta0
  rw [hty] at hta
  have hlen : ls.length = ci.toConstantVal.levelParams.length :=
    Classical.byContradiction fun hlen => by
      rw [denoteP, hT] at hta
      dsimp only at hta
      rw [if_neg hlen] at hta
      exact nomatch hta
  rw [denoteP_const hT hlen] at hta
  obtain rfl : ta = mp.base2.acval T
      (Level.substFn (fun _ => 0) ci.toConstantVal.levelParams ls) :=
    (Option.some.inj hta).symm
  generalize hψ : Level.substFn (fun _ => 0) ci.toConstantVal.levelParams ls = ψ at hta0
  let ρ : Nat → V := fun _ => empty
  have hcX := mp.mem_typeP c hc (fun _ => 0) _ hta0 ρ
  -- the recursor's type reads to the Π-tower over that leaf
  have hRread := denoteP_zeroCtorRecTy (m := mp.base2) hT ψ elim mN tN₁ tN₂ mb₁ mb₂ mb₃
  rw [← hRty] at hRread
  obtain ⟨-, hval⟩ := mp.type_okP R hR ψ _ hRread ρ
  have hr := mp.mem_typeP R hR ψ _ hRread ρ
  have hX : ∀ σ : Nat → V,
      interp2 V σ (mp.base2.acval T ψ) = interp2 V ρ (mp.base2.acval T ψ) :=
    fun σ => interp2_closed (V := V) (mp.base2.cval_closedL T ψ) σ ρ
  simp only [interp2_pi, interp2_sort, interp2_app, interp2_bvar, cons_zero, cons_succ, hX] at hr
  rw [AnnotValidV_pi] at hval
  obtain ⟨hvalD, hvalB, hz₃⟩ := hval
  -- the motive: the constant `∅`, a member of `T → Sort u`'s reading
  have hM : lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ)) (fun _ => (empty : V))
      ∈ˢ piR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ))
        (fun _ => (univ (ψ elim) : V)) :=
    lamR_mem fun _ _ => empty_mem_univ (ψ elim)
  have hMdom : lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ)) (fun _ => (empty : V))
      ∈ˢ interp2 V ρ (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval T ψ) (.sort (ψ elim))) := by
    simpa only [interp2_pi, interp2_sort] using hM
  -- `r motive ∈ ∀ t : T, motive t`
  have h1 : app (interp2 V ρ (mp.base2.acval R.name ψ))
        (lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ)) (fun _ => (empty : V)))
      ∈ˢ piR (pwBit ψ mb₂.pw) (interp2 V ρ (mp.base2.acval T ψ))
        (fun t => app (lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ))
          (fun _ => (empty : V))) t) := by
    refine app_mem_piR hr hM ?_
    intro h0 M hMm
    have := hz₃ h0 M (by simpa only [interp2_pi, interp2_sort] using hMm)
    simpa only [interp2_pi, interp2_app, interp2_bvar, cons_zero, cons_succ, hX] using this
  -- `r motive c ∈ motive c`
  have h2 : app (app (interp2 V ρ (mp.base2.acval R.name ψ))
        (lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ)) (fun _ => (empty : V))))
        (interp2 V ρ (mp.base2.acval c.name (fun _ => 0)))
      ∈ˢ app (lamR (pwBit ψ mb₁.pw) (interp2 V ρ (mp.base2.acval T ψ)) (fun _ => (empty : V)))
        (interp2 V ρ (mp.base2.acval c.name (fun _ => 0))) := by
    refine app_mem_piR h1 hcX ?_
    intro h0 t ht
    have hvM := hvalB _ hMdom
    rw [AnnotValidV_pi] at hvM
    have := hvM.2.2 h0 t (by rwa [hX])
    simpa only [interp2_app, interp2_bvar, cons_zero, cons_succ] using this
  -- `motive c = ∅` in the graph regime; the squash regime is refuted
  by_cases hb₁ : pwBit ψ mb₁.pw = 0
  · rw [AnnotValidV_pi] at hvalD
    have := hvalD.2.2 hb₁ _ hcX
    rw [interp2_sort] at this
    exact univ_not_mem_univZero (ψ elim) this
  · rw [app_lamR_pos hb₁ hcX] at h2
    exact not_mem_empty _ h2

/-! ## The pinned instances have the shape

The two pinned zero-constructor recursors are `zeroCtorRecTy` at their
stored annotations — so the general theorem specialises to the pinned
capstones' families (it is not *used* for them: their capstones read the
pin directly, `CapstoneP.lean`). -/

example : Setlec.emptyRecA.toConstantVal.type =
    zeroCtorRecTy Setlec.emptyName [] Setlec.uN
      (.str .anonymous "motive") (.str .anonymous "t") (.str .anonymous "t")
      ⟨.default, .never⟩ ⟨.default, .ifAllZero [Setlec.uN]⟩
      ⟨.default, .ifAllZero [Setlec.uN]⟩ := rfl

example : Setlec.falseRecA.toConstantVal.type =
    zeroCtorRecTy Setlec.falseName [] Setlec.uN
      (.str .anonymous "motive") (.str .anonymous "t") (.str .anonymous "t")
      ⟨.default, .never⟩ ⟨.default, .ifAllZero [Setlec.uN]⟩
      ⟨.default, .ifAllZero [Setlec.uN]⟩ := rfl

end Setlec.SetP
