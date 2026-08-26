import Setlec.TTVerify.StdAxiomKey

/-!
# The structural-`Nat` recurrence pin

`NatOpPinTT`, the obligation `DeclDefnTT` left at `certifyNatEqs`.

The content is `denote_substConst0` (`Setlec/TTVerify/SubstConst.lean`)
plus one induction.  `certifyNatEqs` certifies the recurrences in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value; the bridge moves the resulting `Deq`
across that substitution, and what it needs on the way is that both
sides of every equation *denote* and carry their frame conditions.

## The fragment, and why the guard already delimits it

`natOpEquations` are spines over `Nat.zero`, `Nat.succ`, the operation
itself, at most one dependency operation, and (for `beq`/`ble`) the two
`Bool` constructors — with two free variables and no binder anywhere.
Every one of those constants is *exactly* what `natOpGuard` checks is
stored at empty level parameters: `natLitSupported` covers `Nat.zero`
and `Nat.succ`, `natOpDeps` lists the dependency operations, and the
`beq`/`ble` branch adds the `Bool` pair.

> **`natOpDeps` was written so the checker could certify the
> recurrences; it lists precisely the constants the bridge must be able
> to denote.**  §8.4 once more, and unusually literally: the guard's
> dependency list and the bridge's denotation obligation are the same
> list.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- The syntactic fragment the recurrence equations live in: spines
over constants stored at empty level parameters, and free variables
below `d` annotated by `Nat`. -/
def natFragOk (env : Env) (c : Name) (d : Nat) : Expr → Bool
  | .sort _ => true
  | .fvar i _ ty => decide (i < d) && (ty == .const natName [])
  | .const n us => us.isEmpty && ((n == c) ||
      (match env.find? n with
       | some ci => ci.toConstantVal.levelParams.isEmpty
       | none => false))
  | .app f a => natFragOk env c d f && natFragOk env c d a
  | _ => false

/-- A fragment expression is shallow, so `substConst0` is faithful on
it. -/
theorem shallowE_of_natFragOk {env : Env} {c : Name} {d : Nat} :
    ∀ {e : Expr}, natFragOk env c d e = true → shallowE e = true
  | .sort _, _ => rfl
  | .fvar _ _ _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, h => by
    simp only [natFragOk, Bool.and_eq_true] at h
    simp only [shallowE, Bool.and_eq_true]
    exact ⟨shallowE_of_natFragOk h.1, shallowE_of_natFragOk h.2⟩
  | .bvar _, h | .lam _ _ _ _, h | .forallE _ _ _ _, h
  | .letE _ _ _ _, h | .proj _ _ _, h | .lit _, h => by
    simp [natFragOk] at h

/-- **Everything the claim needs about a substituted equation side**,
in one induction: its frame conditions at depth `2`, its context
correspondence in `[Nat, Nat]`, and its denotation. -/
theorem natFrag_subst_facts {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {c : Name} {v : Expr} {V : VExpr}
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true)
    (hv : denoteClosed m.cval env φ v = some V)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    ∀ e : Expr, natFragOk env c 2 e = true →
      Expr.WScoped 2 (Expr.substConst0 c v e) ∧
      (Expr.substConst0 c v e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.substConst0 c v e) ∧
      CtxOk m.cval env φ 2 [m.cval natName φ, m.cval natName φ]
        (Expr.substConst0 c v e) ∧
      ∃ w, denote m.cval env φ 2 (Expr.substConst0 c v e) = some w := by
  intro e
  induction e with
  | sort u =>
    intro _
    rw [show Expr.substConst0 c v (.sort u) = .sort u from rfl]
    exact ⟨by simp [Expr.WScoped], rfl,
      fun l hl => by simp [Expr.fvarLeaves] at hl,
      ⟨rfl, fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      _, by rw [denote_sort]⟩
  | fvar i n ty =>
    intro h
    simp only [natFragOk, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨hlt, rfl⟩ := h
    rw [show Expr.substConst0 c v (.fvar i n (.const natName []))
      = .fvar i n (.const natName []) from rfl]
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hlt, trivial⟩, rfl, ?_,
      ⟨rfl, ?_⟩, _, by rw [denote_fvar]⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · simp [Expr.fvarLeaves] at hl'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · refine ⟨hlt, by simp [Expr.fvarsBelow], m.cval natName φ, ?_, ?_⟩
        · exact denote_const_nolevels m φ hfN hlpN 2
        · have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
            (i := 2 - 1 - i) (A := m.cval natName φ) (by
              have hi : i = 0 ∨ i = 1 := by omega
              rcases hi with rfl | rfl <;> simp)
          rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ)
            _ 0] at this
      · simp [Expr.fvarLeaves] at hl'
  | const n us =>
    intro h
    simp only [natFragOk, Bool.and_eq_true, List.isEmpty_iff,
      Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    by_cases hn : n = c
    · subst hn
      rw [show Expr.substConst0 n v (.const n []) = v from by
        rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
      exact ⟨Expr.WScoped.of_not_hasFvar hvf, hvb,
        Expr.LeavesBounded.of_not_hasFvar hvf,
        ⟨rfl, fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
          exact nomatch hl⟩,
        V, by rw [denote_depth_closed m.cval_closed hvf hvb 2]; exact hv⟩
    · rw [show Expr.substConst0 c v (.const n []) = .const n [] from by
        rw [Expr.substConst0, if_neg (fun hh => hn hh.1)]]
      refine ⟨by simp [Expr.WScoped], rfl,
        fun l hl => by simp [Expr.fvarLeaves] at hl,
        ⟨rfl, fun l hl => by simp [Expr.fvarLeaves] at hl⟩, ?_⟩
      replace h2 : (match env.find? n with
          | some ci => ci.toConstantVal.levelParams.isEmpty
          | none => false) = true := by
        rcases h2 with h2 | h2
        · exact absurd h2 hn
        · exact h2
      cases hf : env.find? n with
      | none => rw [hf] at h2; exact nomatch h2
      | some ci =>
        rw [hf] at h2
        exact ⟨_, denote_const_nolevels m φ hf
          (by simpa [List.isEmpty_iff] using h2) 2⟩
  | app f a ihf iha =>
    intro h
    simp only [natFragOk, Bool.and_eq_true] at h
    obtain ⟨hwf, hbf, hLf, hCf, wf, hdf⟩ := ihf h.1
    obtain ⟨hwa, hba, hLa, hCa, wa, hda⟩ := iha h.2
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from rfl]
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hwf, hwa⟩,
      by simp [Expr.looseBVarsBounded, hbf, hba], ?_,
      CtxOk.app hCf hCa, VExpr.app wf wa, ?_⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hLf l h'
      · exact hLa l h'
    · rw [denote_app, hdf, hda]
  | bvar _ | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ _
  | proj _ _ _ | lit _ =>
    intro h; simp [natFragOk] at h

/-! ## The equations are in the fragment

Seven operations carry recurrences (`natOpEquations` is `[]` for the
WF-recursive family, so their obligation is vacuous), and each mentions
exactly the constants the guard pins. -/

/-- A constant is stored at empty level parameters. -/
def storedNoLevels (env : Env) (n : Name) : Prop :=
  (match env.find? n with
   | some ci => ci.toConstantVal.levelParams.isEmpty
   | none => false) = true

theorem natFragOk_const {env : Env} {c n : Name}
    (h : storedNoLevels env n) : natFragOk env c 2 (.const n []) = true := by
  simp only [natFragOk, List.isEmpty_nil, Bool.true_and, Bool.or_eq_true]
  exact Or.inr h

theorem natFragOk_self {env : Env} {c : Name} :
    natFragOk env c 2 (.const c []) = true := by
  simp [natFragOk]

/-- Both sides of every recurrence lie in the fragment. -/
theorem natOpEquations_frag {env : Env} {c : Name}
    (hz : storedNoLevels env natZeroName)
    (hs : storedNoLevels env natSuccName)
    (hdep : ∀ n ∈ natOpDeps c, n ≠ c → storedNoLevels env n)
    (hbT : c = natBeqName ∨ c = natBleName → storedNoLevels env boolTrueName)
    (hbF : c = natBeqName ∨ c = natBleName →
      storedNoLevels env boolFalseName) :
    ∀ eq ∈ natOpEquations 0 c,
      natFragOk env c 2 eq.1 = true ∧ natFragOk env c 2 eq.2 = true := by
  have hx : natFragOk env c 2
      (.fvar 0 (.str .anonymous "x") (.const natName [])) = true := by
    simp [natFragOk]
  have hy : natFragOk env c 2
      (.fvar 1 (.str .anonymous "y") (.const natName [])) = true := by
    simp [natFragOk]
  have happ : ∀ f a, natFragOk env c 2 f = true → natFragOk env c 2 a = true →
      natFragOk env c 2 (.app f a) = true := by
    intro f a h1 h2; simp [natFragOk, h1, h2]
  have hzc := natFragOk_const (c := c) hz
  have hsc := natFragOk_const (c := c) hs
  have hself : natFragOk env c 2 (.const c []) = true := natFragOk_self
  unfold natOpEquations
  split
  · next hc =>
    intro eq hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ⟨happ _ _ hself hzc, hzc⟩
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · exact ⟨happ _ _ hself (happ _ _ hsc hx), hx⟩
      · exact nomatch hq''
  · split
    · next hc =>
      intro eq hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hx⟩
      · rcases List.mem_cons.mp hq' with rfl | hq''
        · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
            happ _ _ hsc (happ _ _ (happ _ _ hself hx) hy)⟩
        · exact nomatch hq''
    · split
      · next hc =>
        intro eq hq
        have hdc := natFragOk_const (c := c)
          (hdep natPredName (by subst hc; decide) (by subst hc; decide))
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hx⟩
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
              happ _ _ hdc (happ _ _ (happ _ _ hself hx) hy)⟩
          · exact nomatch hq''
      · split
        · next hc =>
          intro eq hq
          have hdc := natFragOk_const (c := c)
            (hdep natAddName (by subst hc; decide) (by subst hc; decide))
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hzc⟩
          · rcases List.mem_cons.mp hq' with rfl | hq''
            · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
                happ _ _ (happ _ _ hdc
                  (happ _ _ (happ _ _ hself hx) hy)) hx⟩
            · exact nomatch hq''
        · split
          · next hc =>
            intro eq hq
            have hdc := natFragOk_const (c := c)
              (hdep natMulName (by subst hc; decide) (by subst hc; decide))
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact ⟨happ _ _ (happ _ _ hself hx) hzc, happ _ _ hsc hzc⟩
            · rcases List.mem_cons.mp hq' with rfl | hq''
              · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
                  happ _ _ (happ _ _ hdc
                    (happ _ _ (happ _ _ hself hx) hy)) hx⟩
              · exact nomatch hq''
          · split
            · next hc =>
              intro eq hq
              have hT := natFragOk_const (c := c) (hbT (Or.inl hc))
              have hF := natFragOk_const (c := c) (hbF (Or.inl hc))
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact ⟨happ _ _ (happ _ _ hself hzc) hzc, hT⟩
              · rcases List.mem_cons.mp hq' with rfl | hq'
                · exact ⟨happ _ _ (happ _ _ hself hzc) (happ _ _ hsc hy), hF⟩
                · rcases List.mem_cons.mp hq' with rfl | hq'
                  · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx)) hzc,
                      hF⟩
                  · rcases List.mem_cons.mp hq' with rfl | hq'
                    · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx))
                        (happ _ _ hsc hy),
                        happ _ _ (happ _ _ hself hx) hy⟩
                    · exact nomatch hq'
            · split
              · next hc =>
                intro eq hq
                have hT := natFragOk_const (c := c) (hbT (Or.inr hc))
                have hF := natFragOk_const (c := c) (hbF (Or.inr hc))
                rcases List.mem_cons.mp hq with rfl | hq'
                · exact ⟨happ _ _ (happ _ _ hself hzc) hy, hT⟩
                · rcases List.mem_cons.mp hq' with rfl | hq'
                  · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx)) hzc,
                      hF⟩
                  · rcases List.mem_cons.mp hq' with rfl | hq'
                    · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx))
                        (happ _ _ hsc hy),
                        happ _ _ (happ _ _ hself hx) hy⟩
                    · exact nomatch hq'
              · intro eq hq; exact nomatch hq

/-! ## The guard delivers exactly those facts -/

theorem storedNoLevels_exists {env : Env} {n : Name}
    (h : storedNoLevels env n) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  unfold storedNoLevels at h
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci => rw [hf] at h; exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using h⟩

theorem storedNoLevels_of_cons {env : Env} {ci : ConstantInfo} {c n : Name}
    (hname : ci.name = c) (hne : n ≠ c)
    (h : storedNoLevels ⟨ci :: env.consts⟩ n) : storedNoLevels env n := by
  unfold storedNoLevels at h ⊢
  rwa [Env.find?_cons, if_neg (by rw [hname]; exact Ne.symm hne)] at h

/-- A name that occurs in no `natOpNames` entry differs from the
operation being installed. -/
theorem ne_of_mem_natOpNames {n c : Name}
    (h : natOpNames.all (fun x => n != x) = true) (hc : c ∈ natOpNames) :
    n ≠ c := fun hh => by
  have := List.all_eq_true.mp h c hc
  rw [hh] at this; simp at this

theorem storedNoLevels_of_ctorOk {env : Env} {n : Name}
    (h : natZeroOk (env.find? n) = true ∨ natSuccOk (env.find? n) = true) :
    storedNoLevels env n := by
  unfold storedNoLevels
  rcases h with h | h
  · unfold natZeroOk at h
    split at h
    · next _ _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
    · exact nomatch h
  · unfold natSuccOk at h
    split at h
    · next _ _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
    · exact nomatch h

/-- The guard's three clauses, as the fragment lemma wants them. -/
theorem natOpGuard_stored {env : Env} {c : Name}
    (h : natOpGuard env c = true) :
    storedNoLevels env natName ∧ storedNoLevels env natZeroName ∧
    storedNoLevels env natSuccName ∧
    (∀ n ∈ natOpDeps c, storedNoLevels env n) ∧
    (c = natBeqName ∨ c = natBleName →
      storedNoLevels env boolTrueName ∧ storedNoLevels env boolFalseName) := by
  simp only [natOpGuard, Bool.and_eq_true] at h
  obtain ⟨⟨hlit, hdeps⟩, hbool⟩ := h
  simp only [natLitSupported, Bool.and_eq_true] at hlit
  obtain ⟨⟨hind, hzero⟩, hsucc⟩ := hlit
  refine ⟨?_, storedNoLevels_of_ctorOk (Or.inl hzero),
    storedNoLevels_of_ctorOk (Or.inr hsucc), ?_, ?_⟩
  · unfold storedNoLevels
    unfold natIndOk at hind
    split at hind
    · next _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ hind : _ ∧ _).1
    · exact nomatch hind
  · intro n hn
    have hd := List.all_eq_true.mp hdeps n hn
    unfold storedNoLevels
    split at hd
    · next _ _ _ hfd => rw [hfd]; exact hd
    · exact nomatch hd
  · intro hc
    rw [if_pos (by rcases hc with rfl | rfl <;> simp)] at hbool
    simp only [Bool.and_eq_true] at hbool
    exact ⟨hbool.1, hbool.2⟩

/-! ## The assembly -/

/-- **`NatOpPinTT`.**  `certifyNatEqs` certified each recurrence in the
pre-insertion environment with the operation replaced by its stored
value; `denote_substConst0` carries that certificate — and only it —
into the extended environment. -/
theorem natOpPinTT : NatOpPinTT F := by
  intro env m cv value value' hint hmem hfresh _hannv hvf hbv hden hguard
    hcerts eq hq φ
  obtain ⟨V, hV⟩ := hden φ
  obtain ⟨hN', hz', hs', hdeps', hbool'⟩ := natOpGuard_stored hguard
  have tr : ∀ {n : Name}, n ≠ cv.name →
      storedNoLevels ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ n →
      storedNoLevels env n := fun hne h =>
    storedNoLevels_of_cons (ci := .defnInfo cv value' hint) (c := cv.name)
      rfl hne h
  have hnN : natName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnz : natZeroName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hns : natSuccName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnT : boolTrueName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnF : boolFalseName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  obtain ⟨ciN, hfN, hlpN⟩ := storedNoLevels_exists (tr hnN hN')
  -- the operation is its own dependency, so the guard pins its levels
  have hselfdep : cv.name ∈ natOpDeps cv.name := by
    simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hlp : (ConstantInfo.defnInfo cv value' hint).toConstantVal.levelParams
      = [] := by
    have hd := hdeps' cv.name hselfdep
    unfold storedNoLevels at hd
    rw [show (⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ : Env).find?
          cv.name = some (.defnInfo cv value' hint) from by
        rw [Env.find?_cons]; exact if_pos rfl] at hd
    simpa [List.isEmpty_iff] using hd
  -- both sides are in the fragment
  obtain ⟨hf1, hf2⟩ := natOpEquations_frag (env := env) (c := cv.name)
    (tr hnz hz') (tr hns hs') (fun n hn hne => tr hne (hdeps' n hn))
    (fun hc => tr hnT (hbool' hc).1)
    (fun hc => tr hnF (hbool' hc).2) eq hq
  obtain ⟨hw1, hb1, hL1, hC1, w1, hd1⟩ :=
    natFrag_subst_facts m φ hvf hbv hV hfN hlpN _ hf1
  obtain ⟨hw2, hb2, hL2, hC2, w2, hd2⟩ :=
    natFrag_subst_facts m φ hvf hbv hV hfN hlpN _ hf2
  -- the certificate, transported by `checkClaimsTT`
  obtain ⟨-, -, ihd, -⟩ := checkClaimsTT m φ F
  have hdeq := ihd (hcerts _ (List.mem_map.mpr ⟨eq, hq, rfl⟩))
    hw1 hb1 hL1 hw2 hb2 hL2 hC1 hC2 hd1 hd2
  -- and moved across the install by `denote_substConst0`
  have hsub := denote_substConst0 m (c₀ := .defnInfo cv value' hint)
    (c := cv.name) φ rfl hfresh hlp hV hvf hbv 2
  refine ⟨w1, w2, ?_, ?_, ?_⟩
  · rw [hsub _ (shallowE_of_natFragOk hf1)]; exact hd1
  · rw [hsub _ (shallowE_of_natFragOk hf2)]; exact hd2
  · rw [cvalAt_ne hnN]; exact hdeq

end Setlec.TTVerify
