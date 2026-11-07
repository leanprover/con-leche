module

public import ConLeche.Verify.Inductives.NestedRead
public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.Subst
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.AbstractRange
public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# The auxiliary recursors' `.nested` rules

The install (`generatedRules`) stores every rule of a recursor
whose major is OUTSIDE its block (a nested block's container) as
`auxRuleFire`: `.nested lvls pins`, the class's levels and its
parameters closed over the rule prefix (`Expr.abstractPrefix`).

* `genStage_nestedRead` — **the datum reads off the generated type**
  (`NestedRead`): the generated recursor type's major domain is the
  class's inductive at `lvls` applied to the pins lifted past the index
  binders, then the index variables, and the pins satisfy `EnvWF`'s
  `.nested` guards.  `envWF_consBlockRecsT`
  (`Verify/Cached/TargetRecC.lean`) and the model read it.
* `nestedRead_open` — **the round trip**: the stored pins are the
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
    ∀ (args : List Expr) (t : Nat) (d b : Expr), args.length ≤ t + 1 →
      Expr.instSeq args t (.lam d b) =
        .lam (Expr.instSeq args t d) (Expr.instSeq args (t + 1) b) := by
  intro args
  induction args with
  | nil => intro t d b _; rfl
  | cons a as ih =>
    intro t d b hlen
    show Expr.instSeq as (t - 1)
      (.lam (d.instantiate1 a t) (b.instantiate1 a (t + 1))) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1))
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) =
      Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1)))
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
  | lam ty b iht ihb =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [instSeq_lam pre _ _ _ (by omega)]
    simp only [Expr.abstractRange]
    rw [iht c hf.1 hb.1,
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hf.2 (by rw [show c + 1 + (n + 1) = c + (n + 1) + 1 by omega]; exact hb.2)]
  | forallE ty b iht ihb =>
    intro c hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [Expr.instSeq_forallE pre _ _ _ (by omega)]
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
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs fvsT : List Expr} {B dom b : Expr},
      openPisAtFvars (n + 1) e d = some (fvs, B) →
      openPisAtFvars n e d = some (fvsT, .forallE dom b) →
      fvs[n]? = some (.fvar (d + n) dom) := by
  intro n
  induction n with
  | zero =>
    intro e d fvs fvsT B dom b h h0
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨-, rfl⟩ := h0
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | succ n ih =>
    intro e d fvs fvsT B dom b h h0
    cases e with
    | forallE dom₀ body₀ =>
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
the recursor type opens at fresh variables `0 … mI` and a `.nested`
datum reads against it, the major's opened type is headed by the reading's
levels, and its first `cnP` arguments — the parameters the check
resolved — closed over the rule prefix (`abstractRange 0 rP`) ARE the
stored pins. -/
theorem nestedRead_open {resolves : Expr → Bool} {lps : List Name} {ty : Expr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr} {fvs : List Expr} {concl maj : Expr}
    (hsyn : NestedRead resolves lps ty mI rP cnP lvls pins)
    (hopen : openPisAtFvars (mI + 1) ty 0 = some (fvs, concl))
    (hmaj : fvs[mI]? = some maj) :
    (∃ D, maj.fvarTypeD.getAppFn = .const D lvls) ∧
    (maj.fvarTypeD.getAppArgs.take cnP).map (·.abstractRange 0 rP) = pins := by
  obtain ⟨hrP, -, hpins, pre, dom, body, D, hstrip, hfn, hargs, hlen⟩ := hsyn
  obtain ⟨o', ho'⟩ := openPisAtFvars_prefix mI (mI + 1) ty 0 (by omega) hopen
  have ho'eq := Verify.openPisAtFvars_instSeq mI ho' hstrip
  have hTlen : (fvs.take mI).length = mI := by
    obtain ⟨-, -, -, hl, -⟩ := Verify.openPisAtFvars_stripPis mI ho'
    exact hl
  rw [Expr.instSeq_forallE _ _ _ _ (by omega)] at ho'eq
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

/-! ## The generated type's major domain reads as the datum -/

/-- Peeling the OUTERMOST variable off a bulk abstraction (the twin of
`abstractRange_succ`, which peels the innermost). -/
theorem abstractRange_succ_outer :
    ∀ (e : Expr) (d k c : Nat),
      (e.abstractRange (d + 1) k c).abstract1 d (c + k) = e.abstractRange d (k + 1) c := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro d k c
    by_cases h0 : idx = d
    · subst h0
      rw [Expr.abstractRange, ite_eq_right (by omega), Expr.abstract1, ite_eq_left rfl,
        Expr.abstractRange, ite_eq_left (by omega)]
      congr 1
      omega
    · by_cases hin : d + 1 ≤ idx ∧ idx < d + 1 + k
      · rw [Expr.abstractRange, ite_eq_left hin, Expr.abstract1, Expr.abstractRange,
          ite_eq_left (by omega)]
        congr 1
        omega
      · rw [Expr.abstractRange, ite_eq_right hin, Expr.abstract1, ite_eq_right h0, Expr.abstractRange,
          ite_eq_right (by omega)]
  | _ =>
    intro d k c
    simp only [Expr.abstractRange, Expr.abstract1, Nat.add_right_comm c k 1, *]

/-- `abstractPrefix` is the bulk abstraction of the prefix variables. -/
theorem abstractPrefix_eq :
    ∀ (k c : Nat) (e : Expr), Expr.abstractPrefix k c e = e.abstractRange 0 k c
  | 0, c, e => (abstractRange_zero e 0 c).symm
  | k + 1, c, e => by
    rw [Expr.abstractPrefix, abstractPrefix_eq k (c + 1), abstractRange_succ e 0 k c,
      Nat.zero_add]

/-- `abstract1` passes `stripPis`, one cursor deeper per binder. -/
theorem stripPis_abstract1 :
    ∀ (n : Nat) {e : Expr} (x c : Nat) {pre : List Expr} {r : Expr},
      e.stripPis n = some (pre, r) →
      ∃ pre', (e.abstract1 x c).stripPis n = some (pre', r.abstract1 x (c + n))
  | 0, e, x, c, pre, r, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | n + 1, e, x, c, pre, r, h => by
    cases e with
    | forallE t b =>
      simp only [Expr.stripPis] at h
      obtain ⟨⟨pre₀, r₀⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨pre', hpre'⟩ := stripPis_abstract1 n x (c + 1) hb
      refine ⟨t.abstract1 x c :: pre', ?_⟩
      simp only [Expr.abstract1, Expr.stripPis, hpre', Option.map_some,
        show c + 1 + n = c + (n + 1) by omega]
    | _ => simp [Expr.stripPis] at h

/-- **Stripping a closed telescope**: the first `n` binders off
`closeTelescope bs i body` leave the rest of the telescope with the
variables `i … i+n-1` closed (`abstractRange i n`). -/
theorem closeTelescope_stripPis :
    ∀ (n : Nat) (bs : List Expr) (i : Nat) (body : Expr), n ≤ bs.length →
      ∃ pre, (closeTelescope bs i body).stripPis n
        = some (pre, (closeTelescope (bs.drop n) (i + n) body).abstractRange i n 0)
  | 0, bs, i, body, _ => ⟨[], by simp [Expr.stripPis, abstractRange_zero]⟩
  | n + 1, [], _, _, h => absurd h (by simp)
  | n + 1, b :: bs, i, body, h => by
    obtain ⟨pre, hpre⟩ := closeTelescope_stripPis n bs (i + 1) body
      (by simp only [List.length_cons] at h; omega)
    obtain ⟨pre', hpre'⟩ := stripPis_abstract1 n i 0 hpre
    refine ⟨b :: pre', ?_⟩
    simp only [closeTelescope, Expr.stripPis, hpre', Option.map_some, List.drop_succ_cons,
      Nat.zero_add]
    rw [show i + (n + 1) = i + 1 + n by omega, ← abstractRange_succ_outer _ i n 0,
      Nat.zero_add]

/-- Bulk abstraction distributes over an application spine. -/
theorem abstractRange_mkAppN (d k c : Nat) :
    ∀ (args : List Expr) (f : Expr), (Expr.mkAppN f args).abstractRange d k c
      = Expr.mkAppN (f.abstractRange d k c) (args.map (·.abstractRange d k c))
  | [], _ => rfl
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).abstractRange d k c = _
    rw [abstractRange_mkAppN d k c as]
    rfl

/-- **Closing a prefix of variables, then lifting past the rest**: a
bound-variable-closed term whose free variables are the first `rP`
closes over `rP + k` variables as it closes over `rP`, lifted by `k`. -/
theorem abstractRange_split (rP k : Nat) :
    ∀ (e : Expr) (c : Nat), e.fvarsBelow rP → e.looseBVarsBounded c = true →
      e.abstractRange 0 (rP + k) c = (e.abstractRange 0 rP c).liftLooseBVars k c := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro c hf _
    simp only [Expr.fvarsBelow] at hf
    rw [Expr.abstractRange, ite_eq_left (by omega), Expr.abstractRange, ite_eq_left (by omega),
      Expr.liftLooseBVars, ite_eq_left (by omega)]
    congr 1
    omega
  | bvar i =>
    intro c _ hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    rw [Expr.abstractRange, Expr.abstractRange, Expr.liftLooseBVars, ite_eq_right (by omega)]
  | _ =>
    intro c hf hb
    simp_all [Expr.abstractRange, Expr.liftLooseBVars, Expr.fvarsBelow,
      Expr.looseBVarsBounded]

/-- Closing every free variable leaves none. -/
theorem abstractRange_hasFvar (rP : Nat) :
    ∀ (e : Expr) (c : Nat), e.fvarsBelow rP → (e.abstractRange 0 rP c).hasFvar = false := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro c hf
    simp only [Expr.fvarsBelow] at hf
    rw [Expr.abstractRange, ite_eq_left (by omega)]
    rfl
  | _ =>
    intro c hf
    simp_all [Expr.abstractRange, Expr.hasFvar, Expr.fvarsBelow]

/-- Closing `rP` variables at cursor `c` binds below `c + rP`. -/
theorem abstractRange_bounded (rP : Nat) :
    ∀ (e : Expr) (c : Nat), e.fvarsBelow rP → e.looseBVarsBounded c = true →
      (e.abstractRange 0 rP c).looseBVarsBounded (c + rP) = true := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro c hf _
    simp only [Expr.fvarsBelow] at hf
    rw [Expr.abstractRange, ite_eq_left (by omega)]
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  | bvar i =>
    intro c _ hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  | _ =>
    intro c hf hb
    simp_all [Expr.abstractRange, Expr.fvarsBelow, Expr.looseBVarsBounded,
      show c + rP + 1 = c + 1 + rP by omega]

/-- A predicate closed under a `∀`'s body survives `stripPis`. -/
theorem stripPis_pred {P : Expr → Bool} (hP : ∀ t b, P (.forallE t b) = true → P b = true) :
    ∀ (n : Nat) {e : Expr} {pre : List Expr} {r : Expr},
      e.stripPis n = some (pre, r) → P e = true → P r = true
  | 0, e, pre, r, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact he
  | n + 1, e, pre, r, h, he => by
    cases e with
    | forallE t b =>
      simp only [Expr.stripPis] at h
      obtain ⟨⟨pre₀, r₀⟩, hb, hq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hq
      obtain ⟨-, rfl⟩ := hq
      exact stripPis_pred hP n hb (hP t b he)
    | _ => simp [Expr.stripPis] at h

/-- A predicate closed under an application's parts reaches a spine's
head and arguments. -/
theorem mkAppN_pred {P : Expr → Bool}
    (hP : ∀ f a, P (.app f a) = true → P f = true ∧ P a = true) :
    ∀ (args : List Expr) (f : Expr), P (Expr.mkAppN f args) = true →
      P f = true ∧ ∀ a ∈ args, P a = true
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hfa, has⟩ := mkAppN_pred hP as (.app f a) h
    obtain ⟨hf, ha⟩ := hP f a hfa
    refine ⟨hf, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact has x hx

theorem allLevelParamsDefined_liftLooseBVars (lps : List Name) (k : Nat) :
    ∀ (e : Expr) (c : Nat),
      (e.liftLooseBVars k c).allLevelParamsDefined lps = e.allLevelParamsDefined lps := by
  intro e
  induction e <;> intro c <;>
    simp_all [Expr.liftLooseBVars, Expr.allLevelParamsDefined] <;> split <;> rfl

theorem constsResolve_liftLooseBVars (env : Env) (k : Nat) :
    ∀ (e : Expr) (c : Nat), (e.liftLooseBVars k c).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> intro c <;>
    simp_all [Expr.liftLooseBVars, Expr.constsResolve] <;> split <;> rfl

/-- **An outside class's parameters are the block's** (what `targetMajorOf`
checks of an outside class): one per parameter of the inductive, closed,
mentioning only the block's `nP` parameters. -/
@[expose] def ClassOutParams (nP : Nat) (M : TargetMajor) : Prop :=
  M.member = none → M.ds.length = M.nPc ∧ ∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ nP

/-- The generator's prefix: the parameters, then a binder per slot. -/
theorem ClassGen.prefixBinders_length {g : ClassGen} {pre : List Expr}
    (h : g.prefixBinders = some pre) : pre.length = g.params.length + g.slots.length := by
  unfold ClassGen.prefixBinders at h
  obtain ⟨slotBs, hsl, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hsll := option_mapM_length hsl
  simp only [List.length_range] at hsll
  simp [hsll]

/-- **The `.nested` datum reads off the generated recursor type**: at an
outside class, the stored type (`classGenRecTy`) strips to the major
domain `I.{lvls} (pins⇑ ++ indices)`, the pins being the class's
parameters closed over the rule prefix (`auxRuleFire`), and the pins
pass `EnvWF`'s guards (their levels and constants are the type's). -/
theorem genStage_nestedRead {env : Env} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (S : GenStageRun mode F (mkFEnv env) p nestedBit params tbl rd Ms₀ block out)
    (hpl : params.length = p.nP) (hMs₀ : ∀ M ∈ Ms₀, ClassOutParams p.nP M)
    {j : Nat} {t : ConstantVal × TargetMajor × List Expr} (ht : out[j]? = some t)
    (hm : t.2.1.member = none) :
    NestedRead (·.constsResolve env) t.1.levelParams t.1.type (p.majorIdxAt j)
      (p.rulePrefixAt j) t.2.1.nPc t.2.1.lvls
      (t.2.1.ds.map (Expr.abstractPrefix (p.rulePrefixAt j) 0)) := by
  -- the stored entry: a generated constant at its class
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run S.hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run S.hrules
  have hjo : j < out.length := (List.getElem?_eq_some_iff.mp ht).1
  have hjl : j < p.recs.length := by rw [hlenO, hlenG] at hjo; omega
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG j p.recs[j] (List.getElem?_eq_getElem hjl)
  obtain ⟨rhss, hoj, -⟩ := hallO j cvG c hG hc
  rw [ht] at hoj
  obtain rfl := Option.some.inj hoj
  dsimp only at hm ⊢
  have hrP : p.rulePrefixAt j = p.recs[j].rP := by
    simp [BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
  have hmI : p.majorIdxAt j = p.recs[j].mI := by
    simp [BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
  rw [hrP, hmI]
  have hrPg : p.recs[j].rP = p.nP + rd.slots.length := T.hrP
  have hmIg := T.hmI
  generalize hg : genRecGen p params S.Ms S.formerTysC rd S.ctors S.pre = g at *
  generalize hM : g.cls.getD c default = M at *
  -- the class: an outside class's parameters are the block's
  have hMout : ClassOutParams p.nP M := by
    obtain ⟨hlenN, hallN⟩ := classesNfs_run S.hMs
    rw [← hM, ← hg]
    simp only [genRecGen]
    rw [List.getD_eq_getElem?_getD]
    cases hcM : S.Ms[c]? with
    | none => exact fun _ => ⟨rfl, fun _ h => nomatch h⟩
    | some N =>
      have hcl : c < Ms₀.length := by
        have := (List.getElem?_eq_some_iff.mp hcM).1; omega
      obtain ⟨nfs, hN, -⟩ := hallN c Ms₀[c] (List.getElem?_eq_getElem hcl)
      rw [hcM] at hN
      obtain rfl := Option.some.inj hN
      simp only [Option.getD_some]
      exact fun hmem => hMs₀ Ms₀[c] (List.getElem_mem hcl) hmem
  obtain ⟨hdsLen, hdsSc⟩ := hMout hm
  -- the generated type
  obtain ⟨-, -, hlb, hfv, hlp, hcr, -, -, -, -⟩ := classConstOk_inv T.hcv
  rw [T.hcvG] at hlb hfv hlp hcr ⊢
  dsimp only at hlb hfv hlp hcr ⊢
  have hgty := T.hgty
  unfold classGenRecTy at hgty
  obtain ⟨⟨ifs₀, maj⟩, hmaj, hgty⟩ := Option.bind_eq_some_iff.mp hgty
  simp only [Option.pure_def, Option.some.injEq] at hgty
  unfold ClassGen.major at hmaj
  rw [hM] at hmaj
  obtain ⟨ty, hty, hmaj⟩ := Option.bind_eq_some_iff.mp hmaj
  obtain ⟨⟨ifs, o⟩, hifs, hmaj⟩ := Option.bind_eq_some_iff.mp hmaj
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hmaj
  obtain ⟨rfl, rfl⟩ := hmaj
  obtain ⟨-, -, -, hifl, hidx, -⟩ := Verify.openPisAtFvars_stripPis _ hifs
  -- the rule prefix is the generator's prefix
  have hpre : g.pre.length = p.recs[j].rP := by
    rw [hrPg, ← hg]
    have := ClassGen.prefixBinders_length S.hpre
    simp only [genRecGen] at this ⊢
    rw [this, hpl]
  have hmIv : p.recs[j].mI = p.recs[j].rP + ifs.length := by rw [hmIg, hifl]
  have hnP : p.nP ≤ p.recs[j].rP := by rw [hrPg]; omega
  generalize p.recs[j].rP = rP at *
  generalize p.recs[j].mI = mI at *
  subst hmIv
  -- strip to the major domain
  have hbsl : (g.pre ++ ifs.map g.binder).length = rP + ifs.length := by simp [hpre]
  obtain ⟨pre', hstrip⟩ := closeTelescope_stripPis (rP + ifs.length)
    (g.pre ++ ifs.map g.binder ++ [Expr.mkAppN (.const M.ind M.lvls) (M.ds ++ ifs)]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length)
      (Expr.mkAppN (.const M.ind M.lvls) (M.ds ++ ifs))]))
    (by simp [hpre])
  rw [List.drop_left' hbsl] at hstrip
  simp only [closeTelescope, Expr.abstractRange, Nat.zero_add] at hstrip
  rw [hgty] at hstrip
  generalize hdomE : ((Expr.const M.ind M.lvls).mkAppN (M.ds ++ ifs)).abstractRange 0
    (rP + ifs.length) = dom at hstrip
  generalize Expr.abstractRange _ 0 (rP + ifs.length) 1 = body at hstrip
  have hdom : dom = Expr.mkAppN (.const M.ind M.lvls)
      ((M.ds ++ ifs).map (·.abstractRange 0 (rP + ifs.length) 0)) := by
    rw [← hdomE, abstractRange_mkAppN]
    rfl
  -- the parameters' scope
  have hxF : ∀ x ∈ M.ds, x.fvarsBelow rP := fun x hx =>
    Expr.fvarsBelow_mono hnP
      (Expr.fvarsBelow_iff.mpr (by rw [← Expr.fvarB_eq]; exact (hdsSc x hx).2))
  have hxB : ∀ x ∈ M.ds, x.looseBVarsBounded 0 = true := fun x hx =>
    Expr.looseBVarsBounded_iff.mpr (by rw [← Expr.bvarB_eq]; exact Nat.le_of_eq (hdsSc x hx).1)
  -- the parameters: closed over the prefix, lifted past the indices
  have hdsArg : ∀ x ∈ M.ds, x.abstractRange 0 (rP + ifs.length) 0
      = (Expr.abstractPrefix rP 0 x).liftLooseBVars ifs.length 0 := fun x hx => by
    rw [abstractPrefix_eq]
    exact abstractRange_split rP ifs.length x 0 (hxF x hx) (hxB x hx)
  have hdsArgs : M.ds.map (·.abstractRange 0 (rP + ifs.length) 0)
      = (M.ds.map (Expr.abstractPrefix rP 0)).map (Expr.liftLooseBVars ifs.length 0) := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx => hdsArg x hx
  -- the indices: the index variables, in order
  have hifsArgs : ifs.map (·.abstractRange 0 (rP + ifs.length) 0)
      = (List.range ifs.length).map (fun i => Expr.bvar (ifs.length - 1 - i)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map] at h1
    obtain ⟨tyi, hti⟩ := hidx i (by omega)
    rw [List.getElem?_eq_getElem h1, Option.some.injEq] at hti
    simp only [List.getElem_map, List.getElem_range, hti]
    rw [Expr.abstractRange, ite_eq_left (by omega)]
    congr 1
    omega
  -- the type's guards reach the major domain's parts
  have hpred : ∀ {P : Expr → Bool}, (∀ t b, P (.forallE t b) = true ↔ P t = true ∧ P b = true) →
      (∀ f a, P (.app f a) = true ↔ P f = true ∧ P a = true) → P T.gty = true →
      P (.const M.ind M.lvls) = true ∧
        ∀ a ∈ (M.ds ++ ifs).map (·.abstractRange 0 (rP + ifs.length) 0), P a = true := by
    intro P hPf hPa hP
    have h1 := stripPis_pred (fun t b h => ((hPf t b).mp h).2) _ hstrip hP
    have h2 := ((hPf _ _).mp h1).1
    rw [hdom] at h2
    exact mkAppN_pred (fun f a h => (hPa f a).mp h) _ _ h2
  obtain ⟨hlpC, hlpA⟩ := hpred (P := (·.allLevelParamsDefined p.recs[j].cvR.levelParams))
    (fun t b => by simp [Expr.allLevelParamsDefined]) (fun f a => by simp [Expr.allLevelParamsDefined])
    hlp
  obtain ⟨-, hcrA⟩ := hpred (P := (·.constsResolve env))
    (fun t b => by simp [Expr.constsResolve]) (fun f a => by simp [Expr.constsResolve]) hcr
  have hpinArg : ∀ x ∈ M.ds, (Expr.abstractPrefix rP 0 x).liftLooseBVars ifs.length 0 ∈
      (M.ds ++ ifs).map (·.abstractRange 0 (rP + ifs.length) 0) := fun x hx => by
    rw [← hdsArg x hx]
    exact List.mem_map_of_mem (List.mem_append_left _ hx)
  unfold NestedRead
  rw [Nat.add_sub_cancel_left]
  refine ⟨by omega, ?_, ?_, pre', dom, body, M.ind, hstrip, ?_, ?_, by simp [hdsLen]⟩
  · simpa [Expr.allLevelParamsDefined] using hlpC
  · intro pin hpin
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpin
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abstractPrefix_eq]; exact abstractRange_hasFvar rP x 0 (hxF x hx)
    · have := hlpA _ (hpinArg x hx)
      rwa [allLevelParamsDefined_liftLooseBVars] at this
    · have := hcrA _ (hpinArg x hx)
      rwa [constsResolve_liftLooseBVars] at this
    · rw [abstractPrefix_eq]
      have := abstractRange_bounded rP x 0 (hxF x hx) (hxB x hx)
      rwa [Nat.zero_add] at this
  · rw [hdom, Expr.getAppFn_mkAppN]
    rfl
  · rw [hdom, Expr.getAppArgs_mkAppN, List.map_append, hdsArgs, hifsArgs]
    simp [Expr.getAppArgs]

/-- The stage of a run with the pass's classes (`GenRecRun` carries
every bind of `GenStageRun`). -/
def GenRecRun.stage {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {pos : NestState} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nestedBit pos block out) :
    GenStageRun mode F fe p nestedBit R.ctx.params R.st.ctorNfs.toList R.rd R.Ms₀ block
      out where
  cvRis := R.cvRis
  Ms := R.Ms
  ctors := R.ctors
  formerTysC := R.formerTysC
  pre := R.pre
  cvGs := R.cvGs
  pins := R.pins
  hcvRis := R.hcvRis
  hk := R.hk
  helim := R.helim
  hMs := R.hMs
  hctors := R.hctors
  hminors := R.hminors
  hformer := R.hformer
  hpre := R.hpre
  hcvGs := R.hcvGs
  hrules := R.hrules

/-- **The `.nested` datum reads off the stored type, at a run**: the
run's canonical parameters are the block's, and every outside class's
parameters pass `targetMajorOf`'s check (`TargetMajorRun.outside_facts`). -/
theorem GenRecRun.nestedRead {F : Nat} {fe₁ : FEnv} {env₁ : Env} {env : Env} {p : BlockShape}
    {nestedBit : Bool} {pos : NestState} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ (mkFEnv env) p nestedBit pos block out)
    {j : Nat} {t : ConstantVal × TargetMajor × List Expr} (ht : out[j]? = some t)
    (hm : t.2.1.member = none) :
    NestedRead (·.constsResolve env) t.1.levelParams t.1.type (p.majorIdxAt j)
      (p.rulePrefixAt j) t.2.1.nPc t.2.1.lvls
      (t.2.1.ds.map (Expr.abstractPrefix (p.rulePrefixAt j) 0)) := by
  refine genStage_nestedRead R.stage ?_ ?_ ht hm
  · obtain ⟨cvTa0, fvsP, rest, -, hop, hctx, -⟩ := blockNestCtx_inv R.hctx
    rw [hctx]
    obtain ⟨-, -, -, hl, -⟩ := Verify.openPisAtFvars_stripPis _ hop
    exact hl
  · intro M hM hmM
    obtain ⟨hlen, hall⟩ := R.majors
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
    have hik : i < R.keys.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    obtain ⟨M', hM', ⟨C⟩⟩ := hall i R.keys[i] (List.getElem?_eq_getElem hik)
    rw [hi] at hM'
    obtain rfl := Option.some.inj hM'
    obtain ⟨-, -, -, -, -, -, hl, hsc, -⟩ := C.major.outside_facts hmM
    exact ⟨hl, hsc⟩

/-- **A stored `.nested` firing reads off the stored type**, at a run
(`GenRecRun.nestedRead` at the firing's datum, `tgtFireOf_nested_eq`). -/
theorem GenRecRun.fire_nestedRead {F : Nat} {fe₁ : FEnv} {env₁ : Env} {env : Env}
    {p : BlockShape} {nestedBit : Bool} {pos : NestState}
    {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ (mkFEnv env) p nestedBit pos block out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {lvls : List Level} {pins : List Expr}
    (hf : tgtFireOf p (tgtMajorsOf out) j r = .nested lvls pins) :
    NestedRead (·.constsResolve env) r.1.levelParams r.1.type (p.majorIdxAt j)
      (p.rulePrefixAt j) (tgtMajorsOf out j).nPc lvls pins := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, out[j]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) := by
    simp only [tgtRs, List.getElem?_map] at hr
    cases ho : out[j]? with
    | none => rw [ho] at hr; exact nomatch hr
    | some t => rw [ho] at hr; exact ⟨t, rfl, (Option.some.inj hr).symm⟩
  have hM : tgtMajorsOf out j = t.2.1 := by
    simp [tgtMajorsOf, List.getD_eq_getElem?_getD, ht]
  obtain ⟨hm, rfl, rfl⟩ := tgtFireOf_nested_eq hf
  rw [hM] at hm ⊢
  exact R.nestedRead ht hm

end ConLeche
