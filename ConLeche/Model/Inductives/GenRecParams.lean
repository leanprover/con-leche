module

public import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.DeclNative
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.StreamConsts
import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Deep
import ConLeche.Verify.Shift
import ConLeche.Verify.Knot

public section

/-!
# The generated recursors' parameter domains fit the block's

`genParams_fit`: every generated (stored) recursor type's first `nP`
prefix domains read as the block's parameters — a spine fitting the
recursor's rule prefix fits `dR.params` on its first `nP` values.  The
old target check had this from its K6 `isDefEqCore` run (the stream's
parameter domains against the major's former, `tgtGuard_params`); the
generated stage runs no such comparison, and none is needed:

* the generated prefix is SHARED (every generated type is the reset
  prefix's telescope, annotated: `SameDoms`), so it suffices to look at
  ONE recursor whose class is a MEMBER `T_t` (one exists: the member
  recursors' name pins);
* that recursor's major domain is `T_t p⃗ ı⃗` over the prefix's own
  parameter variables (the class key moved to the canonical parameters,
  `classKeyCanon`; a member key's parameters ARE them, `targetMajorOf`);
  the stored type's inference (`checkConstantVal`) infers it, and the
  application rule compares each parameter variable's type — the stored
  prefix domain — with `T_t`'s parameter domain at the earlier
  variables (`inferTypeCore_spine_defeq`); depth invariance moves the
  comparison to the prefix's own depth;
* that comparison is the certified hop's premise
  (`prefixDoms_agree_inst`, the `prefixDoms_agree` of
  `BlockRecPreRun.lean` with the second telescope's domains given as
  terms over the FIRST opening's variables), and the members' parameter
  agreement moves `T_t`'s parameters to the block's.

(Syntactic identity of the stored and the former's domains is NOT
available: annotation keeps an input's written binder data, so the
reset-and-reannotated domains need not equal the former's annotated ones;
the application rule's comparison is what ties them.)
-/

namespace ConLeche

variable {μ : CheckMode}

/-! ## Syntax -/

/-- A term with `n` leading `∀`s has the same first `n` domains as itself. -/
theorem SameDoms.of_stripPis :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      e.stripPis n = some (bs, r) → SameDoms n e e
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, bs, r, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', r'⟩, h', -⟩ := h
    exact ⟨rfl, SameDoms.of_stripPis n h'⟩
  | n + 1, .bvar _, _, _, h | n + 1, .fvar _ _, _, _, h | n + 1, .sort _, _, _, h
  | n + 1, .const _ _, _, _, h | n + 1, .app _ _, _, _, h | n + 1, .lam _ _ _, _, _, h
  | n + 1, .letE _ _ _, _, _, h | n + 1, .lit _, _, _, h | n + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

/-- Fewer leading domains. -/
theorem SameDoms.mono :
    ∀ {n m : Nat} {e₁ e₂ : Expr}, m ≤ n → SameDoms n e₁ e₂ → SameDoms m e₁ e₂
  | _, 0, _, _, _, _ => trivial
  | 0, m + 1, _, _, hle, _ => absurd hle (by omega)
  | n + 1, m + 1, .forallE A b _, .forallE A' b' _, hle, h =>
    ⟨h.1, SameDoms.mono (by omega) h.2⟩

/-- A run on a `∀` carries a run on its domain. -/
theorem inferTypeCore_forallE_dom {envK : Env} {F d : Nat} {ty bd s : Expr}
    {mb : BinderMeta} (h : inferTypeCore μ envK F d (.forallE ty bd mb) = .ok s) :
    ∃ F₀ tty, F = F₀ + 1 ∧ inferTypeCore μ envK F₀ d ty = .ok tty := by
  cases F with
  | zero =>
    rw [inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ F₀ =>
    rw [inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, -⟩ := exceptBind_ok h
    exact ⟨F₀, tty, rfl, htty⟩

/-- **The application rule along a spine**: a run on `f a₀ … aₙ₋₁`, `f`
typed at a telescope with (at least) `m` leading `∀`s, compares every
argument `aₗ` (`l < m`) with the telescope's `l`-th domain at the
earlier arguments. -/
theorem inferTypeCore_spine_defeq {envK : Env} {F d : Nat} :
    ∀ (as : List Expr) {f tf t : Expr} {m : Nat}, m ≤ as.length → SameDoms m tf tf →
      inferTypeCore μ envK F d f = .ok tf →
      inferTypeCore μ envK F d (Expr.mkAppN f as) = .ok t →
      ∀ l, l < m → ∃ D b mb ta, instPisWith (as.take l) tf = some (.forallE D b mb) ∧
        inferTypeCore μ envK F d (as.getD l default) = .ok ta ∧
        isDefEqCore μ envK F d ta D = .ok true
  | [], _, _, _, m, hm, _, _, _, l, hl => absurd hl (by simp at hm; omega)
  | a :: as, f, tf, t, m, hm, hsd, hf, h, l, hl => by
    obtain ⟨tfa, hfa⟩ := Model.inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf', ty', body', m', hf', hw, rfl, ta, hta, hde⟩ := inferTypeCore_app_inv' hfa
    rw [show tf' = tf from Except.ok.inj (hf'.symm.trans hf)] at hw
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    match tf, hsd, hw with
    | .forallE A b mb, hsd, hw =>
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (whnf_forallE_eq hw)
      cases l with
      | zero => exact ⟨ty', body', m', ta, rfl, hta, hde⟩
      | succ l =>
        obtain ⟨D, b', mb', ta', hi, hta', hde'⟩ := inferTypeCore_spine_defeq as
          (f := .app f a) (tf := body'.instantiate1 a) (m := m₀) (by simp at hm; omega)
          (SameDoms.instantiate1 m₀ 0 hsd.2) hfa h l (by omega)
        exact ⟨D, b', mb', ta', hi, hta', hde'⟩

/-- An application spine erasure-equal to another: heads and arguments
pairwise. -/
theorem erasedEq_mkAppN_args :
    ∀ (as : List Expr) {as' : List Expr} {f f' : Expr}, as'.length = as.length →
      Expr.ErasedEq (Expr.mkAppN f' as') (Expr.mkAppN f as) →
      Expr.ErasedEq f' f ∧
        ∀ (j : Nat) (x x' : Expr), as[j]? = some x → as'[j]? = some x' → Expr.ErasedEq x' x
  | [], [], _, _, _, h => ⟨h, fun j x x' hx _ => nomatch hx⟩
  | a :: as, a' :: as', f, f', hl, h => by
    obtain ⟨hh, hargs⟩ := erasedEq_mkAppN_args as (as' := as') (f := .app f a) (f' := .app f' a')
      (by simpa using hl) h
    refine ⟨hh.1, fun j x x' hx hx' => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
      subst hx hx'
      exact hh.2
    | succ j => exact hargs j x x' (by simpa using hx) (by simpa using hx')

end ConLeche
