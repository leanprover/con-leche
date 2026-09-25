module

public import ConLeche.Verify.Inductives.PosCompleteElim
public import ConLeche.Verify.Inductives.PosCompleteSteps
import ConLeche.Verify.Inductives.PosCompleteUnif
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstList

public section

/-!
# Official's keys are uniform (lane COMPLETE-6M3, (A))

The member constructors' M3 check (`Expr.holesApplied`, `nestMemberCtor`)
reads a container instantiation's parameters `ds` in the walk's normal
form, which official's `check_positivity` never looks into.  What
official's acceptance says about them: they are the parameters of a key of
its final auxiliary map (`KeysApplied`'s premise, `σ.contAux`), and every
key is UNIFORM — every member occurrence in it is the member applied to
(at least) the declaration's parameters, `T ps …` (`unifA`).  Why: the
keys are argument subterms of the eliminated declaration's constructors
(`replaceAll`, `isNestedApp`), whose member constructors passed official's
`check_uniform_ind_occs` (`Official.DeclChecks`, the parameters then
instantiated at the canonical variables: `unifA_of_uniformOcc`) and whose
auxiliary constructors are containers' constructors — which mention no
member (`StoredEnv.fresh`) — instantiated at earlier keys (`unifA` is
stable under instantiation, `unifA_instantiate1`).  The invariant `UInv`
carries it through official's elimination loop (`keys_unif_of_elimNested`).

**The residual, a RESTRICTION (a finding).**  The walk's M3 is STRICTER
than official's uniformity: `holesApplied` admits no member at all under
a `let` or a projection, which `check_uniform_ind_occs` descends into.
So (A) needs the premise `KeysLetProjFree`: no key parameter of
official's final map has a member under a `let` or a projection.  It is
not a fact of official's acceptance; it names that divergence.  Measured
(e2e `complete_m3_proj_param`, probed on official v4.29.1/v4.33.0/v4.34.0):
* the PROJECTION half is live — `T | mk : List ((T, Nat).1) → T` passes
  official and the walk's M3 rejects it (whnf leaves a container's
  parameters alone);
* the `let` half is not — `restrict_a25_nest_let_param`
  (`List (let X := T; X)`) is accepted by the walk: the kernel's whnf
  annotates first, and annotation ζ-reduces every `let` (`annotateBody`),
  so the walk's key is `List T` while official's is `List (let X := T; X)`.
  There the named hypothesis `WhnfSim` (which relates the walk's key to
  official's by read-back) fails, and (A) says nothing.
-/

namespace ConLeche

open Expr

/-! ## Uniformity at the canonical parameter variables -/

/-- **Uniformity at the parameters `ps`** (official's
`check_uniform_ind_occs` after the parameters are instantiated at the
canonical variables): every occurrence of a member of `mem` heads a spine
whose first `ps.length` arguments are `ps`.  `args` are the arguments the
node is applied to in its spine. -/
@[expose] def unifA (mem : List Name) (ps : List Expr) : List Expr → Expr → Bool
  | args, .const n _ =>
    !mem.contains n || (decide (ps.length ≤ args.length) && args.take ps.length == ps)
  | args, .app f a => unifA mem ps (a :: args) f && unifA mem ps [] a
  | _, .lam t b _ => unifA mem ps [] t && unifA mem ps [] b
  | _, .forallE t b _ => unifA mem ps [] t && unifA mem ps [] b
  | _, .letE t v b => unifA mem ps [] t && unifA mem ps [] v && unifA mem ps [] b
  | _, .proj _ _ x => unifA mem ps [] x
  | _, _ => true

/-- **No member under a `let` or a projection** (the residual premise,
see the module doc). -/
@[expose] def letProjFree (names : List Name) : Expr → Bool
  | .app f a => letProjFree names f && letProjFree names a
  | .lam t b _ => letProjFree names t && letProjFree names b
  | .forallE t b _ => letProjFree names t && letProjFree names b
  | .letE t v b => !(Expr.letE t v b).nestOcc names 0 0
  | .proj s i x => !(Expr.proj s i x).nestOcc names 0 0
  | _ => true

section Unif

variable {mem : List Name} {ps : List Expr}

theorem unifA_mkAppN : ∀ (xs args : List Expr) (f : Expr),
    unifA mem ps args (Expr.mkAppN f xs) = true →
    unifA mem ps (xs ++ args) f = true ∧ ∀ x ∈ xs, unifA mem ps [] x = true
  | [], args, f, h => ⟨h, fun _ hx => nomatch hx⟩
  | x :: xs, args, f, h => by
    obtain ⟨h1, h2⟩ := unifA_mkAppN xs args (.app f x) h
    simp only [unifA, Bool.and_eq_true] at h1
    refine ⟨by simpa using h1.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1.2
    · exact h2 y hy

theorem unifA_mkAppN_of : ∀ (xs args : List Expr) (f : Expr), unifA mem ps (xs ++ args) f = true →
    (∀ x ∈ xs, unifA mem ps [] x = true) → unifA mem ps args (Expr.mkAppN f xs) = true
  | [], args, f, h, _ => h
  | x :: xs, args, f, h, hx =>
    unifA_mkAppN_of xs args (.app f x)
      (by simp only [unifA, Bool.and_eq_true]; exact ⟨h, hx x List.mem_cons_self⟩)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

/-- More arguments keep a spine uniform. -/
theorem unifA_append : ∀ (e : Expr) (args more : List Expr), unifA mem ps args e = true →
    unifA mem ps (args ++ more) e = true := by
  intro e
  induction e with
  | const n us =>
    intro args more h
    simp only [unifA, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact .inl h
    · refine .inr ⟨by simp; omega, ?_⟩
      rw [List.take_append_of_le_length h1]; exact h2
  | app f a ihf _ =>
    intro args more h
    simp only [unifA, Bool.and_eq_true] at h ⊢
    exact ⟨ihf (a :: args) more h.1, h.2⟩
  | _ => intro args more h; exact h

theorem unifA_nil_any {e : Expr} (h : unifA mem ps [] e = true) (args : List Expr) :
    unifA mem ps args e = true := by
  simpa using unifA_append e [] args h

/-- A term naming no member is uniform. -/
theorem unifA_of_nestOcc : ∀ (e : Expr) (args : List Expr), e.nestOcc mem 0 0 = false →
    unifA mem ps args e = true := by
  intro e
  induction e with
  | const n us =>
    intro args h
    simp only [Expr.nestOcc] at h
    simp only [unifA, h, Bool.not_false, Bool.true_or]
  | app f a ihf iha =>
    intro args h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [unifA, ihf _ h.1, iha _ h.2]
  | lam t b _ iht ihb =>
    intro args h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [unifA, iht _ h.1, ihb _ h.2]
  | forallE t b _ iht ihb =>
    intro args h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [unifA, iht _ h.1, ihb _ h.2]
  | letE t v b iht ihv ihb =>
    intro args h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    simp [unifA, iht _ h.1.1, ihv _ h.1.2, ihb _ h.2]
  | proj s i x ih =>
    intro args h
    simp only [Expr.nestOcc] at h
    simp [unifA, ih _ h]
  | _ => intro args _; rfl

/-- **Uniformity is stable under instantiation** by a uniform term (the
parameters, variables, are left alone). -/
theorem unifA_instantiate1 {v : Expr} (hv : unifA mem ps [] v = true)
    (hps : ∀ p ∈ ps, ∀ k, p.instantiate1 v k = p) :
    ∀ (e : Expr) (args : List Expr) (k : Nat), unifA mem ps args e = true →
      unifA mem ps (args.map (·.instantiate1 v k)) (e.instantiate1 v k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro args k _
    simp only [Expr.instantiate1]
    split
    · exact unifA_nil_any hv _
    · split <;> rfl
  | const n us =>
    intro args k h
    simp only [unifA, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    simp only [Expr.instantiate1, unifA, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_map]
    rcases h with h | ⟨h1, h2⟩
    · exact .inl h
    · refine .inr ⟨h1, ?_⟩
      rw [← List.map_take, h2]
      exact List.map_congr_left (fun p hp => hps p hp k) |>.trans (List.map_id _)
  | app f a ihf iha =>
    intro args k h
    simp only [unifA, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, unifA, Bool.and_eq_true]
    exact ⟨by simpa using ihf (a :: args) k h.1, by simpa using iha [] k h.2⟩
  | lam t b _ iht ihb =>
    intro args k h
    simp only [unifA, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, unifA, Bool.and_eq_true]
    exact ⟨by simpa using iht [] k h.1, by simpa using ihb [] (k + 1) h.2⟩
  | forallE t b _ iht ihb =>
    intro args k h
    simp only [unifA, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, unifA, Bool.and_eq_true]
    exact ⟨by simpa using iht [] k h.1, by simpa using ihb [] (k + 1) h.2⟩
  | letE t v' b iht ihv ihb =>
    intro args k h
    simp only [unifA, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, unifA, Bool.and_eq_true]
    exact ⟨⟨by simpa using iht [] k h.1.1, by simpa using ihv [] k h.1.2⟩,
      by simpa using ihb [] (k + 1) h.2⟩
  | proj s i x ih =>
    intro args k h
    simp only [unifA] at h
    simp only [Expr.instantiate1, unifA]
    simpa using ih [] k h
  | fvar _ _ => intro args k _; rfl
  | sort _ => intro args k _; rfl
  | lit _ => intro args k _; rfl

/-- **A telescope instantiated at uniform terms is uniform.** -/
theorem unifA_instPisWith (hps : ∀ p ∈ ps, ∀ v k, p.instantiate1 v k = p) :
    ∀ (ds : List Expr) (e r : Expr), (∀ d ∈ ds, unifA mem ps [] d = true) →
      unifA mem ps [] e = true → instPisWith ds e = some r → unifA mem ps [] r = true
  | [], e, r, _, he, h => by simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | d :: ds, .forallE a b bm, r, hds, he, h => by
    simp only [instPisWith] at h
    simp only [unifA, Bool.and_eq_true] at he
    have := unifA_instantiate1 (hds d List.mem_cons_self) (fun p hp k => hps p hp d k) b [] 0 he.2
    exact unifA_instPisWith hps ds _ r (fun x hx => hds x (List.mem_cons_of_mem _ hx))
      (by simpa using this) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, h | _ :: _, .sort _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, h | _ :: _, .app _ _, _, _, _, h | _ :: _, .lam _ _ _, _, _, _, h
  | _ :: _, .letE _ _ _, _, _, _, h | _ :: _, .lit _, _, _, _, h
  | _ :: _, .proj _ _ _, _, _, _, h => by
    simp [instPisWith] at h

theorem nestOcc_instantiateLevelParams {names : List Name} {lo hi : Nat} {ks : List Name}
    {us : List Level} : ∀ (e : Expr),
      (e.instantiateLevelParams ks us).nestOcc names lo hi = e.nestOcc names lo hi := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.nestOcc]

/-! ### Official's uniformity check, at the canonical parameters -/

/-- **`check_uniform_ind_occs` ⇒ uniformity at the parameters**: a
sub-term at depth `k` below the parameters, passing official's check,
closed, instantiated at the (closed, variable) parameters. -/
theorem unifA_of_uniformOcc {lvls : List Level}
    (hcl : ∀ p ∈ ps, p.looseBVarsBounded 0 = true)
    (hpu : ∀ p ∈ ps, ∀ args, unifA mem ps args p = true) :
    ∀ (e : Expr) (k : Nat), Official.uniformOcc mem lvls ps.length (ps.length + k) e = true →
      e.hasFvar = false → ∀ args, unifA mem ps args (e.instantiateList ps.reverse k) = true := by
  have hcl' : ∀ v ∈ ps.reverse, v.looseBVarsBounded 0 = true :=
    fun v hv => hcl v (List.mem_reverse.mp hv)
  intro e
  induction e with
  | bvar j =>
    intro k _ _ args
    by_cases hjk : j < k
    · simp only [Expr.instantiateList, if_pos hjk]; rfl
    · by_cases hj : j - k < ps.reverse.length
      · rw [instantiateList_bvar_closed (by omega) hj hcl']
        exact hpu _ (List.mem_reverse.mp (List.getElem_mem hj)) args
      · simp only [Expr.instantiateList, if_neg hjk, dif_neg hj]; rfl
  | fvar i ty _ => intro k _ h; simp [Expr.hasFvar] at h
  | sort u => intro k _ _ args; simp [Expr.instantiateList, unifA]
  | lit l => intro k _ _ args; simp [Expr.instantiateList, unifA]
  | const c us =>
    intro k hu _ args
    simp only [Official.uniformOcc, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_true, beq_iff_eq] at hu
    simp only [Expr.instantiateList, unifA, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases hu with hu | hu
    · exact .inl hu
    · have hps0 : ps = [] := List.eq_nil_of_length_eq_zero hu.1
      exact .inr ⟨by simp [hps0], by simp [hps0]⟩
  | app f a ihf iha =>
    intro k hu hfv args
    have hfv' := hfv
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv'
    have hcong : Official.uniformOcc mem lvls ps.length (ps.length + k) f = true →
        Official.uniformOcc mem lvls ps.length (ps.length + k) a = true →
        unifA mem ps args ((Expr.app f a).instantiateList ps.reverse k) = true := by
      intro h1 h2
      simp only [Expr.instantiateList, unifA, Bool.and_eq_true]
      exact ⟨ihf k h1 hfv'.1 _, iha k h2 hfv'.2 []⟩
    simp only [Official.uniformOcc] at hu
    split at hu
    · rename_i c us' hfn
      split at hu
      · split at hu
        · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
        · -- the exact occurrence: the member at the parameters
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
          obtain ⟨⟨⟨hlen, -⟩, -⟩, hargs⟩ := hu
          have hE : Expr.app f a = Expr.mkAppN (.const c us') (Expr.app f a).getAppArgs := by
            conv => lhs; rw [← Expr.mkAppN_getApp (.app f a)]
            rw [hfn]
          rw [hE, instantiateList_mkAppN]
          have hmap : (Expr.app f a).getAppArgs.map (·.instantiateList ps.reverse k) = ps := by
            rw [hargs]
            apply List.ext_getElem (by simp)
            intro i hi₁ hi₂
            simp only [List.getElem_map, List.getElem_range]
            rw [instantiateList_bvar_closed (by omega) (by simp at hi₁ ⊢; omega) hcl']
            rw [List.getElem_reverse]
            congr 1
            simp at hi₁
            omega
          rw [hmap]
          refine unifA_mkAppN_of ps args _ ?_ (fun p hp => hpu p hp [])
          simp [Expr.instantiateList, unifA]
      · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
    · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
  | lam t b m iht ihb =>
    intro k hu hfv args
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.instantiateList, unifA, Bool.and_eq_true]
    exact ⟨iht k hu.1 hfv.1 [], ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 []⟩
  | forallE t b m iht ihb =>
    intro k hu hfv args
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.instantiateList, unifA, Bool.and_eq_true]
    exact ⟨iht k hu.1 hfv.1 [], ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 []⟩
  | letE t v b iht ihv ihb =>
    intro k hu hfv args
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.instantiateList, unifA, Bool.and_eq_true]
    exact ⟨⟨iht k hu.1.1 hfv.1.1 [], ihv k hu.1.2 hfv.1.2 []⟩,
      ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 []⟩
  | proj s i x ih =>
    intro k hu hfv args
    simp only [Official.uniformOcc] at hu
    simp only [Expr.hasFvar] at hfv
    simp only [Expr.instantiateList, unifA]
    exact ih k hu hfv []

theorem le_piArity_of_instPisWith (hvar : ∀ p ∈ ps, ∃ i ty, p = .fvar i ty) :
    ∀ (e r : Expr), instPisWith ps e = some r → ps.length ≤ e.piArity := by
  induction ps with
  | nil => intro _ _ _; simp
  | cons p ps ih =>
    intro e r h
    cases e with
    | forallE a b bm =>
      simp only [instPisWith] at h
      obtain ⟨i, ty, rfl⟩ := hvar _ List.mem_cons_self
      have := ih (fun q hq => hvar q (List.mem_cons_of_mem _ hq)) _ r h
      rw [piArity_instantiate1] at this
      simp only [Expr.piArity, List.length_cons]
      omega
    | _ => simp [instPisWith] at h

/-- **A member constructor, at the canonical parameters, is uniform**
(official's `check_uniform_ind_occs` on the declared type). -/
theorem unifA_of_declared {lvls : List Level} {t r : Expr}
    (hvar : ∀ p ∈ ps, ∃ i ty, p = .fvar i ty)
    (hu : Official.uniformOcc mem lvls ps.length 0 t = true) (hfv : t.hasFvar = false)
    (h : instPisWith ps t = some r) : unifA mem ps [] r = true := by
  have hcl : ∀ p ∈ ps, p.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, ty, rfl⟩ := hvar p hp
    rfl
  have hpu : ∀ p ∈ ps, ∀ args, unifA mem ps args p = true := by
    intro p hp args
    obtain ⟨i, ty, rfl⟩ := hvar p hp
    rfl
  obtain ⟨bs, r0, hr0⟩ := stripPis_of_le_piArity ps.length t (le_piArity_of_instPisWith hvar t r h)
  rw [instPisWith_of_stripPis ps t hr0, Option.some.injEq] at h
  subst h
  have hur := uniformOcc_stripPis ps.length t 0 hr0 hu
  rw [Nat.zero_add, show ps.length = ps.length + 0 from rfl] at hur
  exact unifA_of_uniformOcc hcl hpu r0 0 hur (hasFvar_stripPis _ _ hr0 hfv) []

end Unif

/-! ## The invariant through official's elimination -/

section Inv

variable {c : Official.ElimCtx} {mem : List Name}

/-- **The keys' uniformity invariant** at queue position `q`: every key's
parameters are uniform, and so is every constructor of every type not yet
processed. -/
structure UInv (c : Official.ElimCtx) (mem : List Name) (q : Nat) (s : Official.ElimSt) : Prop where
  keys : ∀ k a, (k, a) ∈ s.aux → ∀ x ∈ k.getAppArgs, unifA mem c.ps [] x = true
  raws : ∀ i t, q ≤ i → s.types.toList[i]? = some t → ∀ u ∈ t.ctors, unifA mem c.ps [] u = true

/-- What the invariant is preserved under: the parameters are variables,
the containers' constructors name no member. -/
structure UHyp (c : Official.ElimCtx) (mem : List Name) : Prop where
  psVar : ∀ p ∈ c.ps, ∃ i ty, p = .fvar i ty
  ctorFree : ∀ J x, x ∈ c.ctorsOf J → x.1.type.nestOcc mem 0 0 = false

theorem UHyp.psInst (hU : UHyp c mem) : ∀ p ∈ c.ps, ∀ v k, p.instantiate1 v k = p := by
  intro p hp v k
  obtain ⟨i, ty, rfl⟩ := hU.psVar p hp
  rfl

theorem getAppArgs_mkAppN_const (n : Name) (us : List Level) (xs : List Expr) :
    (Expr.mkAppN (.const n us) xs).getAppArgs = xs := by
  rw [Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]

theorem UInv.copyBlock {q : Nat} {s s' : Official.ElimSt} (hU : UHyp c mem) (hI : UInv c mem q s)
    {us : List Level} {ds : List Expr}
    (hds : ∀ x ∈ ds, unifA mem c.ps [] x = true) {Js : List Name}
    (hcb : (Official.copyBlock c us ds Js).run s = .ok ((), s')) :
    UInv c mem q s' ∧ s.types.toList <+: s'.types.toList := by
  obtain ⟨-, ha, ts, hts, htl, hj⟩ := Official.copyBlock_spec _ _ _ hcb
  refine ⟨⟨fun k a hka => ?_, fun i t hi ht => ?_⟩, ⟨_, hts.symm⟩⟩
  · rw [ha] at hka
    rcases List.mem_append.mp hka with h | h
    · exact hI.keys k a h
    · obtain ⟨⟨k', a'⟩, hm, he⟩ : ∃ p ∈ Js.mapIdx (fun j J => (Expr.mkAppN (.const J us) ds,
          c.auxName (s.next + j))), p = (k, a) := ⟨_, h, rfl⟩
      rw [List.mem_iff_getElem] at hm
      obtain ⟨j, hj', hjeq⟩ := hm
      simp only [List.getElem_mapIdx] at hjeq
      rw [he] at hjeq
      simp only [Prod.mk.injEq] at hjeq
      rw [← hjeq.1, getAppArgs_mkAppN_const]
      exact hds
  · rw [hts] at ht
    rcases Nat.lt_or_ge i s.types.toList.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at ht
      exact hI.raws i t hi ht
    · rw [List.getElem?_append_right hge] at ht
      have hk : i - s.types.toList.length < Js.length := by
        rw [← htl]
        exact (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨t', ht', -, hcp⟩ := hj _ hk
      rw [ht] at ht'
      cases ht'
      obtain ⟨cv, caps, -, -, hcs⟩ := hcp
      intro u hu
      obtain ⟨x, hx, hxu⟩ := Official.mapM_except_mem' hcs u hu
      refine unifA_instPisWith hU.psInst ds _ u hds ?_ (Official.instPiParams_ok.mp hxu)
      exact unifA_of_nestOcc _ _ (by rw [nestOcc_instantiateLevelParams]; exact hU.ctorFree _ x hx)

theorem UInv.replaceIfNested {q : Nat} {s s' : Official.ElimSt} {e : Expr} {r : Option Expr}
    {args : List Expr} (hU : UHyp c mem) (hI : UInv c mem q s) (hq : q ≤ s.types.size)
    (he : unifA mem c.ps args e = true)
    (h : (Official.replaceIfNested c e).run s = .ok (r, s')) :
    UInv c mem q s' ∧ s.types.toList <+: s'.types.toList := by
  rcases Official.replaceIfNested_spec h with ⟨-, -, rfl⟩ | ⟨I, us, np, xs, a, -, hN, -, hs⟩
  · exact ⟨hI, List.prefix_refl _⟩
  · rcases hs with rfl | hcb
    · exact ⟨hI, List.prefix_refl _⟩
    · obtain ⟨-, hargs, -⟩ := Official.isNestedApp_some hN
      have hsp := unifA_mkAppN e.getAppArgs args e.getAppFn (by rw [Expr.mkAppN_getApp]; exact he)
      exact hI.copyBlock hU (fun x hx => hsp.2 x (hargs ▸ List.mem_of_mem_take hx)) hcb

theorem size_le_of_prefix' {s s' : Official.ElimSt} (h : s.types.toList <+: s'.types.toList) :
    s.types.size ≤ s'.types.size := by
  simpa using h.length_le

theorem UInv.replaceAll {q : Nat} (hU : UHyp c mem) : ∀ (e : Expr) {args : List Expr}
    {s s' : Official.ElimSt} {r : Expr}, UInv c mem q s → q ≤ s.types.size →
    unifA mem c.ps args e = true → (Official.replaceAll c e).run s = .ok (r, s') →
    UInv c mem q s' ∧ s.types.toList <+: s'.types.toList := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨o, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨hI1, hT1⟩ := hI.replaceIfNested hU hq he h1
    have hq1 := Nat.le_trans hq (size_le_of_prefix' hT1)
    rcases o with _ | x
    · simp only at h2
      obtain ⟨rf, s2, h3, h4⟩ := stateT_bind_ok h2
      obtain ⟨ra, s3, h5, h6⟩ := stateT_bind_ok h4
      obtain ⟨rfl, rfl⟩ := stateT_pure_ok h6
      simp only [unifA, Bool.and_eq_true] at he
      obtain ⟨hI2, hT2⟩ := ihf hI1 hq1 he.1 h3
      obtain ⟨hI3, hT3⟩ := iha hI2 (Nat.le_trans hq1 (size_le_of_prefix' hT2)) he.2 h5
      exact ⟨hI3, hT1.trans (hT2.trans hT3)⟩
    · simp only at h2
      obtain ⟨rfl, rfl⟩ := stateT_pure_ok h2
      exact ⟨hI1, hT1⟩
  | lam t b m iht ihb =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    simp only [unifA, Bool.and_eq_true] at he
    obtain ⟨hI1, hT1⟩ := iht hI hq he.1 h1
    obtain ⟨hI2, hT2⟩ := ihb hI1 (Nat.le_trans hq (size_le_of_prefix' hT1)) he.2 h3
    exact ⟨hI2, hT1.trans hT2⟩
  | forallE t b m iht ihb =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    simp only [unifA, Bool.and_eq_true] at he
    obtain ⟨hI1, hT1⟩ := iht hI hq he.1 h1
    obtain ⟨hI2, hT2⟩ := ihb hI1 (Nat.le_trans hq (size_le_of_prefix' hT1)) he.2 h3
    exact ⟨hI2, hT1.trans hT2⟩
  | letE t v b iht ihv ihb =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨r3, s3, h5, h6⟩ := stateT_bind_ok h4
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h6
    simp only [unifA, Bool.and_eq_true] at he
    obtain ⟨hI1, hT1⟩ := iht hI hq he.1.1 h1
    have hq1 := Nat.le_trans hq (size_le_of_prefix' hT1)
    obtain ⟨hI2, hT2⟩ := ihv hI1 hq1 he.1.2 h3
    obtain ⟨hI3, hT3⟩ := ihb hI2 (Nat.le_trans hq1 (size_le_of_prefix' hT2)) he.2 h5
    exact ⟨hI3, hT1.trans (hT2.trans hT3)⟩
  | proj sn i x ih =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h2
    simp only [unifA] at he
    exact ih hI hq he h1
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro args s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h
    exact ⟨hI, List.prefix_refl _⟩

theorem UInv.mapM_replaceAll {q : Nat} (hU : UHyp c mem) : ∀ (l : List Expr)
    {s s' : Official.ElimSt} {cs : List Expr}, UInv c mem q s → q ≤ s.types.size →
    (∀ u ∈ l, unifA mem c.ps [] u = true) →
    (l.mapM (Official.replaceAll c)).run s = .ok (cs, s') →
    UInv c mem q s' ∧ s.types.toList <+: s'.types.toList
  | [], s, s', cs, hI, _, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h
    exact ⟨hI, List.prefix_refl _⟩
  | u :: l, s, s', cs, hI, hq, hl, h => by
    rw [List.mapM_cons] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    obtain ⟨hI1, hT1⟩ := hI.replaceAll hU u hq (hl u List.mem_cons_self) h1
    obtain ⟨hI2, hT2⟩ := UInv.mapM_replaceAll hU l hI1 (Nat.le_trans hq (size_le_of_prefix' hT1))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h3
    exact ⟨hI2, hT1.trans hT2⟩

/-- **The elimination loop keeps every key uniform.** -/
theorem UInv.elimLoop (hU : UHyp c mem) : ∀ (fuel q : Nat) {s st : Official.ElimSt},
    UInv c mem q s → q ≤ s.types.size → (Official.elimLoop c fuel q).run s = .ok ((), st) →
    ∀ k a, (k, a) ∈ st.aux → ∀ x ∈ k.getAppArgs, unifA mem c.ps [] x = true
  | 0, q, s, st, _, _, h => by
    simp only [Official.elimLoop] at h
    cases h
  | fuel + 1, q, s, st, hI, hq, h => by
    simp only [Official.elimLoop] at h
    obtain ⟨s0, s0', h0, h1⟩ := stateT_bind_ok h
    have e1 : s0 = s := by cases h0; rfl
    have e2 : s0' = s := by cases h0; rfl
    rw [e1, e2] at h1
    rcases ht : s.types[q]? with _ | t
    · simp only [ht] at h1
      obtain ⟨-, rfl⟩ := stateT_pure_ok h1
      exact hI.keys
    simp only [ht] at h1
    obtain ⟨cs, s2, h2, h3⟩ := stateT_bind_ok h1
    obtain ⟨u, s3, h4, h5⟩ := stateT_bind_ok h3
    have hs3 : s3 = { s2 with types := s2.types.set! q { t with ctors := cs } } := by
      cases h4; rfl
    subst hs3
    have hqlt : q < s.types.size := by
      rcases Nat.lt_or_ge q s.types.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at ht; cases ht
    have htl : s.types.toList[q]? = some t := by simpa using ht
    obtain ⟨hI2, hT2⟩ := hI.mapM_replaceAll hU t.ctors hq (hI.raws q t (Nat.le_refl _) htl) h2
    refine UInv.elimLoop hU fuel (q + 1)
      (s := { s2 with types := s2.types.set! q { t with ctors := cs } })
      ⟨hI2.keys, fun i t' hi ht' => ?_⟩
      (by simp only [Array.size_set!]; exact Nat.lt_of_lt_of_le hqlt (size_le_of_prefix' hT2)) h5
    have hne : q ≠ i := by omega
    simp only [Array.toList_set!, List.getElem?_set, hne, if_false] at ht'
    exact hI2.raws i t' (by omega) ht'

/-- **Every key of official's final map is uniform** (official's
elimination from a declaration whose constructors passed
`check_uniform_ind_occs`, closed). -/
theorem keys_unif_of_elimNested {lvls : List Level} (hU : UHyp c mem)
    {decl : List Official.MemberDecl}
    (hdecl : ∀ d ∈ decl, ∀ x ∈ d.ctors,
      x.hasFvar = false ∧ Official.uniformOcc mem lvls c.ps.length 0 x = true)
    {fuel : Nat} {st : Official.ElimSt} (h : Official.elimNested c decl fuel = .ok st) :
    ∀ k a, (k, a) ∈ st.aux → ∀ x ∈ k.getAppArgs, unifA mem c.ps [] x = true := by
  simp only [Official.elimNested, bind, Except.bind] at h
  split at h
  · cases h
  rename_i tys htys
  rcases hl : (Official.elimLoop c fuel 0).run { types := tys.toArray } with e | ⟨⟨⟩, st'⟩
  · simp [hl] at h
  simp only [hl, pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine UInv.elimLoop hU fuel 0 ⟨fun k a hka => by simp at hka, fun i t _ ht => ?_⟩
    (Nat.zero_le _) hl
  intro u hu
  have ht' : tys[i]? = some t := by simpa using ht
  obtain ⟨d, hd, hf⟩ := Official.mapM_except_mem' htys t (List.mem_of_getElem? ht')
  rcases hty : Official.instPiParams d.type c.ps with e | ty
  · simp [hty] at hf
  rcases hcs : d.ctors.mapM (fun t => Official.instPiParams t c.ps) with e | cs
  · simp [hty, hcs] at hf
  simp only [hty, hcs, pure, Except.pure, Except.ok.injEq] at hf
  subst hf
  obtain ⟨x, hx, hxu⟩ := Official.mapM_except_mem' hcs u hu
  obtain ⟨hfv, hun⟩ := hdecl d hd x hx
  exact unifA_of_declared hU.psVar hun hfv (Official.instPiParams_ok.mp hxu)

end Inv

/-! ## The walk's M3 at official's keys -/

section Walk

variable {ctx : NestCtx}

theorem rbE_nil_fvar {x : Expr} {j : Nat} {ty : Expr} (h : rbE ctx [] x = .fvar j ty) :
    x = .fvar j ty := by
  cases x with
  | fvar i t =>
    simp only [rbE, Expr.replaceFVars] at h
    revert h
    cases hn : nestHoleConst ctx [] i with
    | none => intro h; simpa using h
    | some c =>
      intro h
      simp only [Option.getD_some] at h
      subst h
      simp only [nestHoleConst] at hn
      split at hn
      · cases hn
      · split at hn
        · simp at hn
        · cases hn
  | _ => simp [rbE, Expr.replaceFVars] at h

theorem rbE_nil_hole {i : Nat} {ty : Expr} (hi : ctx.nP ≤ i ∧ i < ctx.hiAt 0) :
    rbE ctx [] (.fvar i ty) =
      .const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param) := by
  simp [rbE, Expr.replaceFVars, nestHoleConst, hi]

theorem rbE_nil_nohole {i : Nat} {ty : Expr} (hi : ¬ (ctx.nP ≤ i ∧ i < ctx.hiAt 0)) :
    rbE ctx [] (.fvar i ty) = .fvar i ty := by
  simp only [rbE, Expr.replaceFVars, nestHoleConst, if_neg hi]
  rw [if_neg (by simp only [List.length_nil]; omega)]
  rfl

theorem hole_name_mem {i : Nat} (hi : ctx.nP ≤ i ∧ i < ctx.hiAt 0) :
    ctx.names.contains (ctx.names.getD (i - ctx.nP) .anonymous) = true := by
  have : i - ctx.nP < ctx.names.length := by simp only [NestCtx.hiAt] at hi; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  simp [List.getElem_mem this]

/-- A walk term naming no member, whose read-back names no member, names no
hole either. -/
theorem nestOcc_of_rbE_nil : ∀ (x : Expr), x.nestOcc ctx.names 0 0 = false →
    (rbE ctx [] x).nestOcc ctx.names 0 0 = false →
    x.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false := by
  intro x
  induction x with
  | fvar i ty _ =>
    intro _ h
    by_cases hi : ctx.nP ≤ i ∧ i < ctx.hiAt 0
    · rw [rbE_nil_hole hi] at h
      simp only [Expr.nestOcc, hole_name_mem hi] at h
      exact absurd h (by decide)
    · simp only [Expr.nestOcc]; exact decide_eq_false hi
  | const n us => intro h _; exact h
  | app f a ihf iha =>
    intro h1 h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h1
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc, Bool.or_eq_false_iff] at h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨ihf h1.1 h2.1, iha h1.2 h2.2⟩
  | lam t b _ iht ihb =>
    intro h1 h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h1
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc, Bool.or_eq_false_iff] at h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht h1.1 h2.1, ihb h1.2 h2.2⟩
  | forallE t b _ iht ihb =>
    intro h1 h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h1
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc, Bool.or_eq_false_iff] at h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht h1.1 h2.1, ihb h1.2 h2.2⟩
  | letE t v b iht ihv ihb =>
    intro h1 h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h1
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc, Bool.or_eq_false_iff] at h2
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨⟨iht h1.1.1 h2.1.1, ihv h1.1.2 h2.1.2⟩, ihb h1.2 h2.2⟩
  | proj s i x ih =>
    intro h1 h2
    simp only [Expr.nestOcc] at h1
    simp only [rbE, Expr.replaceFVars, Expr.nestOcc] at h2
    simp only [Expr.nestOcc]
    exact ih h1 h2
  | bvar _ => intro _ _; rfl
  | sort _ => intro _ _; rfl
  | lit _ => intro _ _; rfl

/-- **M3 from uniformity of the read-back** (at the empty frame stack):
a walk term naming no member whose read-back is uniform at the parameters,
with no member under a `let` or a projection, passes the walk's check
(applied to arguments that do). -/
theorem holesApplied_of_unifA
    (hP : ∀ j (h : j < ctx.params.length), ∃ ty, ctx.params[j] = .fvar j ty)
    (hPl : ctx.params.length = ctx.nP) :
    ∀ (d : Expr) (args : List Expr), d.nestOcc ctx.names 0 0 = false →
      unifA ctx.names ctx.params (args.map (rbE ctx [])) (rbE ctx [] d) = true →
      letProjFree ctx.names (rbE ctx [] d) = true →
      (∀ x ∈ args, x.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true) →
      (Expr.mkAppN d args).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true := by
  intro d
  induction d with
  | app f a ihf iha =>
    intro args h0 hu hl hargs
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h0
    simp only [rbE, Expr.replaceFVars] at hu hl
    simp only [unifA, letProjFree, Bool.and_eq_true] at hu hl
    have ha := iha [] h0.2 hu.2 hl.2 (fun _ hx => nomatch hx)
    exact ihf (a :: args) h0.1 hu.1 hl.1 (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hargs x hx)
  | fvar i ty _ =>
    intro args _ hu _ hargs
    by_cases hi : ctx.nP ≤ i ∧ i < ctx.hiAt 0
    · rw [rbE_nil_hole hi] at hu
      simp only [unifA, hole_name_mem hi, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq, List.length_map] at hu
      obtain ⟨-, htk⟩ := hu
      have htk' : args.take ctx.nP = ctx.params := by
        rw [← List.map_take, hPl] at htk
        apply List.ext_getElem (by rw [← htk, List.length_map])
        intro j h1 h2
        obtain ⟨ty', hty'⟩ := hP j h2
        have := congrArg (·[j]?) htk
        simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
          Option.map_some, Option.some.injEq, hty'] at this
        rw [rbE_nil_fvar this, hty']
      exact holesApplied_holeApp hP hPl hi htk' (fun x hx => hargs x (List.mem_of_mem_drop hx))
    · refine holesApplied_mkAppN _ _ ?_ hargs
      simp only [Expr.holesApplied, Bool.or_eq_true]
      exact .inr (by rw [decide_eq_false hi]; rfl)
  | const n us =>
    intro args h0 _ _ hargs
    refine holesApplied_mkAppN _ _ ?_ hargs
    simp only [Expr.nestOcc] at h0
    simp only [Expr.holesApplied, h0, Bool.not_false]
  | lam t b m iht ihb =>
    intro args h0 hu hl hargs
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h0
    simp only [rbE, Expr.replaceFVars] at hu hl
    simp only [unifA, letProjFree, Bool.and_eq_true] at hu hl
    refine holesApplied_mkAppN _ _ ?_ hargs
    simp only [Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht [] h0.1 hu.1 hl.1 (fun _ hx => nomatch hx),
      ihb [] h0.2 hu.2 hl.2 (fun _ hx => nomatch hx)⟩
  | forallE t b m iht ihb =>
    intro args h0 hu hl hargs
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h0
    simp only [rbE, Expr.replaceFVars] at hu hl
    simp only [unifA, letProjFree, Bool.and_eq_true] at hu hl
    refine holesApplied_mkAppN _ _ ?_ hargs
    simp only [Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht [] h0.1 hu.1 hl.1 (fun _ hx => nomatch hx),
      ihb [] h0.2 hu.2 hl.2 (fun _ hx => nomatch hx)⟩
  | letE t v b _ _ _ =>
    intro args h0 _ hl hargs
    refine holesApplied_mkAppN _ _ ?_ hargs
    have hl' : (rbE ctx [] (.letE t v b)).nestOcc ctx.names 0 0 = false := by
      simp only [rbE, Expr.replaceFVars, letProjFree, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
      simpa only [rbE, Expr.replaceFVars] using hl
    simp only [Expr.holesApplied, nestOcc_of_rbE_nil _ h0 hl', Bool.not_false]
  | proj s i x _ =>
    intro args h0 _ hl hargs
    refine holesApplied_mkAppN _ _ ?_ hargs
    have hl' : (rbE ctx [] (.proj s i x)).nestOcc ctx.names 0 0 = false := by
      simp only [rbE, Expr.replaceFVars, letProjFree, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
      simpa only [rbE, Expr.replaceFVars] using hl
    simp only [Expr.holesApplied, nestOcc_of_rbE_nil _ h0 hl', Bool.not_false]
  | bvar _ => intro args _ _ _ hargs; exact holesApplied_mkAppN _ _ rfl hargs
  | sort _ => intro args _ _ _ hargs; exact holesApplied_mkAppN _ _ rfl hargs
  | lit l =>
    intro args _ _ _ hargs
    exact holesApplied_mkAppN _ _ (by simp [Expr.holesApplied, Expr.nestOcc]) hargs

theorem WShape.nestOcc_nil {isAux : Name → Bool} {d : Expr} (h : WShape ctx isAux [] d) :
    d.nestOcc ctx.names 0 0 = false := by
  induction h with
  | const hn _ => exact hn
  | par _ _ _ => rfl
  | mem _ => rfl
  | frm hk _ _ => simp at hk
  | app _ _ _ ihf iha => simp [Expr.nestOcc, ihf, iha]
  | lam _ _ iht ihb => simp [Expr.nestOcc, iht, ihb]
  | forallE _ _ iht ihb => simp [Expr.nestOcc, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.nestOcc, iht, ihv, ihb]
  | proj _ ih => simp [Expr.nestOcc, ih]
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl

/-- **(A)'s residual premise, a RESTRICTION** (see the module doc): no
parameter of a key of official's final map has a member under a `let` or
a projection.  NOT a consequence of official's acceptance: the walk's M3
check (`holesApplied`) is stricter there than `check_uniform_ind_occs`. -/
@[expose] def KeysLetProjFree (ctx : NestCtx) (M : List (Expr × Name)) : Prop :=
  ∀ k a, (k, a) ∈ M → ∀ x ∈ k.getAppArgs, letProjFree ctx.names x = true

/-- **`KeysApplied` at official's final map**: its keys uniform (the
elimination link) and free of members under `let`/projections (the
residual). -/
theorem keysApplied_of_map {c : Official.ElimCtx} {isAux : Name → Bool} {M : List (Expr × Name)}
    (hP : ∀ j (h : j < ctx.params.length), ∃ ty, ctx.params[j] = .fvar j ty)
    (hPl : ctx.params.length = ctx.nP)
    (hunif : ∀ k a, (k, a) ∈ M → ∀ x ∈ k.getAppArgs, unifA ctx.names ctx.params [] x = true)
    (hlp : KeysLetProjFree ctx M) :
    KeysApplied ctx (sigmaOfMap ctx c isAux M) := by
  intro C us ds a hca hok d hd
  have hmem : (rbKey ctx [] ⟨C, us, ds⟩, a) ∈ M := by
    obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp hca
    rw [heq]; simp
  have hargs : (rbKey ctx [] ⟨C, us, ds⟩).getAppArgs = ds.map (rbE ctx []) := by
    simp only [rbKey]; exact getAppArgs_mkAppN_const _ _ _
  have hx : rbE ctx [] d ∈ (rbKey ctx [] ⟨C, us, ds⟩).getAppArgs := by
    rw [hargs]; exact List.mem_map_of_mem hd
  have hws : WShape ctx (sigmaOfMap ctx c isAux M).isAux [] d := hok.2.2.2.2.2.2.2 d hd
  exact holesApplied_of_unifA hP hPl d [] hws.nestOcc_nil (hunif _ a hmem _ hx) (hlp _ a hmem _ hx)
    (fun _ hx => nomatch hx)

end Walk

end ConLeche
