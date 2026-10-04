module

import ConLeche.Verify.Inductives.NestedRuleSyn
public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.Subst
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.AbstractRange

public section

/-!
# The auxiliary recursors' `.nested` rules

The install (`tgtStoredRules`) stores every rule of a recursor
whose major is OUTSIDE its block (a nested block's container) as
`auxRuleFireR` reads it: `.nested lvls pins`, the syntactic reading of
the recursor type's major domain (`Expr.nestedRuleSyn`), or `.inert`.
That every such rule satisfies `EnvWF`'s `.nested` clause is
`envWF_consBlockRecsT` (`Verify/Cached/TargetRecC.lean`), by
`nestedRuleSyn_inv`.

* `nestedRuleSyn_open` — **the round trip**: the stored pins are the
  major's parameters as the check resolved them (`TargetMajor.ds`, read
  off the recursor type opened at fresh variables) closed over the rule
  prefix, `abstractRange 0 rP`; the levels are the major's.  This is
  the one lemma the soundness side (`RecRuleLaw`'s `.nested` conjuncts
  at an outside major) needs about the stored form.
-/

namespace ConLeche

/-! ## The round trip: the stored pins are the resolved parameters, closed -/

/-- A variable below every cut of an instantiation sequence stays. -/
theorem instSeq_bvar_below :
    ∀ (args : List Expr) (t j : Nat), j + args.length ≤ t →
      Expr.instSeq args t (.bvar j) = .bvar j := by
  intro args t j h
  exact instSeq_eq_self_of_bounded args t (k := j + 1)
    (by simp [Expr.looseBVarsBounded]) (by omega)

theorem instSeq_lam :
    ∀ (args : List Expr) (t : Nat) (d b : Expr) (m : BinderMeta), args.length ≤ t + 1 →
      Expr.instSeq args t (.lam d b m) =
        .lam (Expr.instSeq args t d) (Expr.instSeq args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    show Expr.instSeq as (t - 1)
      (.lam (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) m =
      Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

theorem instSeq_letE :
    ∀ (args : List Expr) (t : Nat) (ty v b : Expr), args.length ≤ t + 1 →
      Expr.instSeq args t (.letE ty v b) =
        .letE (Expr.instSeq args t ty) (Expr.instSeq args t v)
          (Expr.instSeq args (t + 1) b) := by
  intro args
  induction args with
  | nil => intro t ty v b _; rfl
  | cons a as ih =>
    intro t ty v b hlen
    show Expr.instSeq as (t - 1)
      (.letE (ty.instantiate1 a t) (v.instantiate1 a t) (b.instantiate1 a (t + 1))) = _
    rw [ih (t - 1) _ _ _ (by simp only [List.length_cons] at hlen; omega)]
    show Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) =
      Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1)))
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

/-- **Opening then closing a range of variables is the identity**: an
fvar-free term, instantiated at the opened variables `0 … n-1` for its
loose variables `c … c+n-1` (cursor `c`), and abstracted back over the
same range at the same cursor, is itself. -/
theorem abstractRange_instSeq_open {pre : List Expr}
    (hpre : ∀ j (hj : j < pre.length), ∃ ty, pre[j] = .fvar j ty) :
    ∀ (p : Expr) (c : Nat), p.hasFvar = false →
      p.looseBVarsBounded (c + pre.length) = true →
      (Expr.instSeq pre (c + pre.length - 1) p).abstractRange 0 pre.length c = p := by
  have hcl : ∀ a ∈ pre, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hty⟩ := hpre j hj
    rw [hty]; rfl
  cases hn : pre.length with
  | zero =>
    have : pre = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    intro p c _ _
    exact abstractRange_zero _ _ _
  | succ n =>
  intro p
  induction p with
  | bvar i =>
    intro c _ hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    by_cases hic : i < c
    · rw [instSeq_bvar_below pre _ i (by omega)]
      rfl
    · have hget := Expr.instSeq_bvar pre (c + (n + 1) - 1) i hcl (by omega) (by omega)
      obtain ⟨ty, hty⟩ := hpre (c + (n + 1) - 1 - i) (by omega)
      rw [List.getElem?_eq_getElem (by omega), hty] at hget
      rw [← Option.some.inj hget]
      simp only [Expr.abstractRange]
      rw [ite_eq_left (by omega)]
      congr 1
      omega
  | fvar _ _ _ => intro c h; simp [Expr.hasFvar] at h
  | sort u =>
    intro c _ _
    rw [Expr.instSeq_eq_self pre _ (by rfl)]; rfl
  | const n us =>
    intro c _ _
    rw [Expr.instSeq_eq_self pre _ (by rfl)]; rfl
  | lit l =>
    intro c _ _
    rw [Expr.instSeq_eq_self pre _ (by rfl)]; rfl
  | app f a ihf iha =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [Expr.instSeq_app]
    simp only [Expr.abstractRange]
    rw [ihf c hf.1 hb.1, iha c hf.2 hb.2]
  | lam ty b m iht ihb =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [instSeq_lam pre _ _ _ _ (by omega)]
    simp only [Expr.abstractRange]
    rw [iht c hf.1 hb.1,
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hf.2 (by rw [show c + 1 + (n + 1) = c + (n + 1) + 1 by omega]; exact hb.2)]
  | forallE ty b m iht ihb =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [Expr.instSeq_forallE pre _ _ _ _ (by omega)]
    simp only [Expr.abstractRange]
    rw [iht c hf.1 hb.1,
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hf.2 (by rw [show c + 1 + (n + 1) = c + (n + 1) + 1 by omega]; exact hb.2)]
  | letE ty v b iht ihv ihb =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [instSeq_letE pre _ _ _ _ (by omega)]
    simp only [Expr.abstractRange]
    rw [iht c hf.1.1 hb.1.1, ihv c hf.1.2 hb.1.2,
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hf.2 (by rw [show c + 1 + (n + 1) = c + (n + 1) + 1 by omega]; exact hb.2)]
  | proj s i e ih =>
    intro c hf hb
    simp only [Expr.hasFvar] at hf
    simp only [Expr.looseBVarsBounded] at hb
    rw [instSeq_proj]
    simp only [Expr.abstractRange]
    rw [ih c hf hb]

/-- Opening one binder more: the last opener is the next binder's
domain as the shorter opening leaves it. -/
theorem openPisAtFvars_succ_last :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs fvsT : List Expr} {B dom b : Expr} {m : BinderMeta},
      openPisAtFvars (n + 1) e d = some (fvs, B) →
      openPisAtFvars n e d = some (fvsT, .forallE dom b m) →
      fvs[n]? = some (.fvar (d + n) dom) := by
  intro n
  induction n with
  | zero =>
    intro e d fvs fvsT B dom b m h h0
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨-, rfl⟩ := h0
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | succ n ih =>
    intro e d fvs fvsT B dom b m h h0
    cases e with
    | forallE dom₀ body₀ m₀ =>
      simp only [openPisAtFvars] at h h0
      split at h
      · rename_i fvs' e' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        split at h0
        · rename_i fvs'' e'' h''
          simp only [Option.some.injEq, Prod.mk.injEq] at h0
          obtain ⟨-, rfl⟩ := h0
          have := ih h' h''
          rw [List.getElem?_cons_succ, this]
          congr 2
          omega
        · exact nomatch h0
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

/-- **The round trip**: where
the recursor type opens at fresh variables `0 … mI` and the syntactic
reading succeeds, the major's opened type is headed by the reading's
levels, and its first `cnP` arguments — the parameters the check
resolved — closed over the rule prefix (`abstractRange 0 rP`) ARE the
stored pins. -/
theorem nestedRuleSyn_open {resolves : Expr → Bool} {lps : List Name} {ty : Expr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr} {fvs : List Expr} {concl maj : Expr}
    (hsyn : Expr.nestedRuleSyn resolves lps ty mI rP cnP = some (lvls, pins))
    (hopen : openPisAtFvars (mI + 1) ty 0 = some (fvs, concl))
    (hmaj : fvs[mI]? = some maj) :
    (∃ D, maj.fvarTypeD.getAppFn = .const D lvls) ∧
    (maj.fvarTypeD.getAppArgs.take cnP).map (·.abstractRange 0 rP) = pins := by
  obtain ⟨hrP, -, hpins, pre, dom, body, bm, D, hstrip, hfn, hargs, hlen⟩ :=
    nestedRuleSyn_inv hsyn
  obtain ⟨o', ho'⟩ := openPisAtFvars_prefix mI (mI + 1) ty 0 (by omega) hopen
  have ho'eq := Verify.openPisAtFvars_instSeq mI ho' hstrip
  have hTlen : (fvs.take mI).length = mI := by
    obtain ⟨-, -, -, hl, -⟩ := Verify.openPisAtFvars_stripPis mI ho'
    exact hl
  rw [Expr.instSeq_forallE _ _ _ _ _ (by omega)] at ho'eq
  rw [ho'eq] at ho'
  have hlast := openPisAtFvars_succ_last mI hopen ho'
  rw [hmaj] at hlast
  cases Option.some.inj hlast
  -- the opened major domain: the stripped one instantiated at the openers
  have hvar : ∀ j (hj : j < (fvs.take mI).length), ∃ ty, (fvs.take mI)[j] = .fvar j ty := by
    intro j hj
    obtain ⟨-, -, -, -, hidx, -⟩ := Verify.openPisAtFvars_stripPis mI ho'
    obtain ⟨tyj, htyj⟩ := hidx j (by omega)
    exact ⟨tyj, by rw [List.getElem?_eq_getElem hj] at htyj; simpa using htyj⟩
  have hcl : ∀ a ∈ fvs.take mI, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨tyj, htyj⟩ := hvar j hj
    rw [htyj]; rfl
  have hdom : Expr.instSeq (fvs.take mI) (mI - 1) dom =
      Expr.mkAppN (.const D lvls)
        (dom.getAppArgs.map (Expr.instSeq (fvs.take mI) (mI - 1) ·)) := by
    conv => lhs; rw [← Expr.mkAppN_getApp dom]
    rw [Expr.instSeq_mkAppN, hfn, Expr.instSeq_eq_self _ _ (by rfl)]
  simp only [Expr.fvarTypeD]
  rw [hdom, Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN]
  refine ⟨⟨D, rfl⟩, ?_⟩
  simp only [Expr.getAppArgs, List.nil_append]
  rw [hargs, List.map_append, List.take_append_of_le_length (by simp [hlen]),
    List.take_of_length_le (by simp [hlen]), List.map_map]
  rw [List.map_map]
  conv => rhs; rw [← List.map_id pins]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨hpF, -, -, hpB⟩ := hpins p hp
  simp only [Function.comp_apply, id]
  -- split the openers at the rule prefix: the lift skips the index slots
  have hsplit : fvs.take mI = (fvs.take mI).take rP ++ (fvs.take mI).drop rP :=
    (List.take_append_drop _ _).symm
  have hpl : ((fvs.take mI).take rP).length = rP := by simp [hTlen]; omega
  have hdl : ((fvs.take mI).drop rP).length = mI - rP := by simp [hTlen]
  rw [hsplit, show mI - 1 = ((fvs.take mI).take rP).length + ((fvs.take mI).drop rP).length - 1
    by rw [hpl, hdl]; omega, show mI - rP = ((fvs.take mI).drop rP).length from hdl.symm,
    Expr.instSeq_liftLooseBVars_prefix _ _
      (fun a ha => hcl a (List.mem_of_mem_take ha)) (by rw [hpl]; exact hpB)]
  have hvar' : ∀ j (hj : j < ((fvs.take mI).take rP).length),
      ∃ ty, ((fvs.take mI).take rP)[j] = .fvar j ty := by
    intro j hj
    obtain ⟨tyj, htyj⟩ := hvar j (by rw [hTlen]; simp at hj; omega)
    exact ⟨tyj, by simpa using htyj⟩
  have := abstractRange_instSeq_open hvar' p 0 hpF (by rw [hpl]; simpa using hpB)
  rw [hpl, Nat.zero_add] at this
  rw [hpl]
  exact this

end ConLeche
