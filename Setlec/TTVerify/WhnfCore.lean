import Setlec.TTVerify.Claims
import Setlec.TTVerify.Inst
import Setlec.TTVerify.Certs
import Setlec.Verify.InferLemmas

/-!
# `whnfCore`, clause by clause

The transpose of `Setlec/Model/Core/Whnf.lean`, against the
certificate-only claims of `Setlec/TTVerify/Claims.lean`.

`whnfCoreBody` (`Setlec/Kernel/Core.lean`) has four groups of clauses:

| clause | bridge side |
|---|---|
| leaves (`sort`, `fvar`, `forallE`, `lam`, `const`, `lit`) | the reduct *is* the subject; `Deq.refl` |
| `.app` with a λ head | `denote_beta_step` (`Setlec/TTVerify/Inst.lean`) |
| `.app` otherwise | `iotaRec`, plus `congrApp` for the head's own reduction |
| `.proj` | `projTeleCert_inv` → `certs_typed` → `projFstMk`/`projSndMk` |
| `.letE` | `HasType.zeta`, premise-free |

This module holds them as they are proved.  Leaves and zeta are here;
the rest is noted at the end of `Setlec/TTVerify/DESIGN.md` §7 with its
scale.

**The `.proj` clause is unblocked** (task #126 landed).  Its rule
(`projFstMk`/`projSndMk`) wants the four telescope domains of
`PSigma'.mk`; the checker now certifies exactly those, and
`projTeleCert_inv` hands the `iotaCertsP` fact straight to
`certs_typed` — see `proj_tele_typed` below.

What still stands between that and the clause is the **pinned-basis
valuation** clause of `ind_ok` (`Setlec/TTVerify/DESIGN.md` §11): the
four premises arrive as typings at the denotations of `PSigma'.mk`'s
*stored* telescope domains, and matching them to `projFstMk`'s
`.sort u` / `arrow A (.sort v)` / `A` / `.app B a` needs the pinned
constants' denotations fixed.  That is an `EnvTT` field, not a
blocker.

**The leaf clauses are the cheapest available evidence that
certificate-only was the right shape.**  Threaded, each of the six
would have had to carry a typing across a subject that does not move —
pure bookkeeping, six times over, for nothing.  Here each is
`Deq.refl`.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {env : Env} {fuel d : Nat}

/-! ## The leaf clauses

Six shapes that `whnfCoreBody` returns unchanged.  Each unfolding is
`rfl`: the body's clause is `pure e`, and `pure` at `Except` is `.ok`.

These are the clauses where the certificate-only shape shows its
economy — with a typing hypothesis threaded they would each have had to
carry it across, which for a subject that does not move is pure
bookkeeping. -/

@[simp] theorem whnfCore_sort (u : Level) :
    whnfCore env (fuel + 1) d (.sort u) = .ok (.sort u) := rfl

@[simp] theorem whnfCore_fvar (idx : Nat) (n : Name) (ty : Expr) :
    whnfCore env (fuel + 1) d (.fvar idx n ty) = .ok (.fvar idx n ty) := rfl

@[simp] theorem whnfCore_forallE (n : Name) (ty body : Expr)
    (bi : BinderMeta) :
    whnfCore env (fuel + 1) d (.forallE n ty body bi) =
      .ok (.forallE n ty body bi) := rfl

@[simp] theorem whnfCore_lam (n : Name) (ty body : Expr) (mb : BinderMeta) :
    whnfCore env (fuel + 1) d (.lam n ty body mb) =
      .ok (.lam n ty body mb) := rfl

@[simp] theorem whnfCore_const (n : Name) (us : List Level) :
    whnfCore env (fuel + 1) d (.const n us) = .ok (.const n us) := rfl

@[simp] theorem whnfCore_lit (l : Literal) :
    whnfCore env (fuel + 1) d (.lit l) = .ok (.lit l) := rfl

/-- The leaf clauses satisfy the `whnfCore` claim, for any denotation
and context: the reduct is the subject, so the equation is `refl` and
nothing has to be re-denoted.

Stated over the six shapes at once because that is how the eventual
`CheckStepTT` case split consumes them. -/
theorem whnfCore_leaf_claim {cval : TConstVal} {φ : Name → Nat}
    {Δ : List VExpr} {e e' : Expr} {v : VExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx n ty, e = .fvar idx n ty) ∨
      (∃ n ty body bi, e = .forallE n ty body bi) ∨
      (∃ n ty body mb, e = .lam n ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore env (fuel + 1) d e = .ok e')
    (hv : denote cval env φ d e = some v) :
    ∃ v', denote cval env φ d e' = some v' ∧ Deq Δ v v' := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, n, ty, rfl⟩ | ⟨n, ty, body, bi, rfl⟩ |
      ⟨n, ty, body, mb, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCore_sort, whnfCore_fvar, whnfCore_forallE,
        whnfCore_lam, whnfCore_const, whnfCore_lit, Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  exact ⟨v, hv, Deq.refl⟩

/-! ## The zeta clause

`whnfCoreBody`'s `.letE` clause reduces to `b.instantiate1 v` and
recurses.  On the bridge side this is where **keeping `denote`
structural pays a second time** (`Setlec/TTVerify/DESIGN.md` §7): the
denotation of the `let` is `VExpr.letE`, the denotation of its zeta
reduct is that term's own `inst`, and the equation between them is
`HasType.zeta` — *premise-free*, so this clause needs no certificate
and no typing at all.

Had `denote` computed the reduct directly, the two sides would have
been syntactically identical and this clause trivial — but the shift
and substitution lemmas would each have cost two commutation lemmas
(§7), which is the trade that was made. -/

/-- The zeta step: a `let` and its reduct denote to `Deq`-equal terms,
and the reduct denotes. -/
theorem denote_zeta_step {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {d : Nat} {n : Name} {ty v b : Expr} {V : VExpr}
    (hfb : Expr.fvarsBelow d b) (hwv : Expr.WScoped d v)
    (hbv : v.looseBVarsBounded 0 = true)
    (hden : denote cval env φ d (.letE n ty v b) = some V) :
    ∃ W, denote cval env φ d (b.instantiate1 v) = some W ∧ Deq Δ V W := by
  rw [denote_letE] at hden
  split at hden
  · next A xv hA hv =>
    split at hden
    · exact nomatch hden
    · next B hB =>
      obtain rfl : V = .letE A xv B := (Option.some.inj hden).symm
      refine ⟨VExpr.inst B xv, ?_, ⟨.sort 0, HasType.zeta⟩⟩
      rw [denote_beta (n := n) (ty := ty) hcl hfb hwv hbv hv 0, hB]
      rfl
  · exact nomatch hden

/-! ## The projection clause

Task #126 added the constructor-spine certification this clause needs
(`Setlec/TTVerify/DESIGN.md` §10.1 — the bridge's first request of the
checker).  `projTeleCert_inv` converts a successful run into the
constructor's stored type plus the `iotaCertsP` fact, which is
`certs_typed`'s entry point, so the four premises of
`projFstMk`/`projSndMk` arrive as premises. -/

/-- The projection's constructor spine is a typed telescope.  The
`.proj` counterpart of `rec_rules_fire`'s first half, and the direct
consumer of task #126. -/
theorem proj_tele_typed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {c : Name} {us : List Level}
    {args : List Expr} {cvj : ConstantVal} {nP nF : Nat} {T : VExpr}
    (hcert : projTeleCertP env fuel d c us args = .ok true)
    (hfind : env.find? c = some (.ctorInfo cvj nP nF))
    (hw : Expr.WScoped d (cvj.type.instantiateLevelParams cvj.levelParams us))
    (hb : (cvj.type.instantiateLevelParams cvj.levelParams us).looseBVarsBounded 0
      = true)
    (hC : CtxOk m.cval env φ d Δ
      (cvj.type.instantiateLevelParams cvj.levelParams us))
    (hi : denote m.cval env φ d
      (cvj.type.instantiateLevelParams cvj.levelParams us) = some T)
    (hargs : ∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      CtxOk m.cval env φ d Δ x) :
    ∃ xs rest, TeleTyped m.cval env φ d Δ
      (cvj.type.instantiateLevelParams cvj.levelParams us) args xs rest := by
  obtain ⟨cvj', nP', nF', hfind', hcerts⟩ := projTeleCert_inv hcert
  obtain rfl : cvj' = cvj := by
    rw [hfind'] at hfind
    exact (ConstantInfo.ctorInfo.inj (Option.some.inj hfind)).1
  exact certs_typed m φ hcl ihd ihi _ _ T hcerts hw hb hC hi hargs

/-- **The projection reduction step.**  Given the pinned pair's four
telescope premises, a projection of a constructor application is
`Deq`-equal to the selected field.

The premises are stated rather than extracted because that is where
they *come from*: task #126's certification, through
`projTeleCert_inv` and `certs_typed`, produces exactly this list as a
`TeleTyped` over `PSigma'.mk`'s stored type
(`∀ (α : Sort u) (β : α → Sort v) (fst : α) (snd : β fst), …`), whose
four telescope domains **are** these four premises.  Unpacking that
walk into them is mechanical; it is the clause's remaining plumbing,
not a further obligation. -/
theorem proj_reduction_step {Δ : List VExpr} {u v : Nat}
    {VA VB Va Vb : VExpr}
    (hA : HasType Δ VA (.sort u))
    (hB : HasType Δ VB (arrow VA (.sort v)))
    (ha : HasType Δ Va VA)
    (hb : HasType Δ Vb (.app VB Va)) :
    Deq Δ (VExpr.proj 0 (psigmaMkT u v VA VB Va Vb)) Va ∧
    Deq Δ (VExpr.proj 1 (psigmaMkT u v VA VB Va Vb)) Vb :=
  ⟨⟨.sort 0, HasType.projFstMk (T := .sort 0) hA hB ha hb⟩,
   ⟨.sort 0, HasType.projSndMk (T := .sort 0) hA hB ha hb⟩⟩

end Setlec.TTVerify
