module

public import ConLeche.Model.Modular.RestrictBase
import ConLeche.Model.DivMod
public import ConLeche.Verify.NatOpFrag

public section

/-!
# A context's certified `Nat` operations, read from their sources

The third part of `ctxModel` (`Model/Modular/Restrict.lean`): the context's `NatOps` and
`DivMod`, keyed on the stored name whatever its kind (a context may hold an operation as its
statement).  What an operation's guard, its dependencies' pins and its recurrences read is its
`pinFootprint` and itself, all read alike from its own source (`CtxRead.scope`), so the guard,
the pins and the readings are its source's, and so are the leaves the laws read.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term SetTheory

universe w

/-! ## What an operation's footprint lists -/

/-- The footprint facts one certified operation's laws use, by computation. -/
@[expose] def NatOpFoot (c : Name) : Prop :=
  (∀ d ∈ [natName, natZeroName, natSuccName], d ∈ pinFootprint c) ∧
  (∀ d ∈ natOpDeps c, d ∈ pinFootprint c) ∧
  ((decide (c = natBeqName) || decide (c = natBleName) || natDivModNames.contains c) = true →
    ∀ d ∈ [boolName, boolTrueName, boolFalseName], d ∈ pinFootprint c) ∧
  (∀ n ∈ natOpDeps c, (n = natBeqName ∨ n = natBleName) → boolName ∈ pinFootprint c) ∧
  (c ∈ natDivModNames → natBleName ∈ natOpDeps c)

instance (c : Name) : Decidable (NatOpFoot c) := by unfold NatOpFoot; infer_instance

theorem natOpFoot {c : Name} (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) : NatOpFoot c := by
  have h1 : ∀ c ∈ natOpNames, NatOpFoot c := by decide
  have h2 : ∀ c ∈ natDivModNames, NatOpFoot c := by decide
  rcases hc with hc | hc
  · exact h1 c hc
  · exact h2 c hc

/-- `natOpTyPinned` reads `Bool`'s constant value only, and only at the comparisons. -/
theorem natOpTyPinned_congr {E E' : Env} {c : Name} {ty : Expr}
    (hb : (c = natBeqName ∨ c = natBleName) →
      (E.find? boolName).map (·.toConstantVal) = (E'.find? boolName).map (·.toConstantVal)) :
    natOpTyPinned E c ty = natOpTyPinned E' c ty := by
  have hcod : ∀ e, natOpCod E c e = natOpCod E' c e := by
    intro e
    unfold natOpCod
    split
    · rename_i hcond
      have hb' := hb (by simpa using hcond)
      cases hE : E.find? boolName <;> cases hE' : E'.find? boolName <;> rw [hE, hE'] at hb' <;>
        simp at hb' <;> simp [hb']
    · rfl
  unfold natOpTyPinned
  split
  · split <;> simp [hcod]
  · split <;> simp [hcod]

/-- A fragment term resolves wherever the operation and `Nat` are stored. -/
theorem constsResolve_of_natFragOk {E : Env} {c : Name} (hc : (E.find? c).isSome = true)
    (hnat : (E.find? natName).isSome = true) :
    ∀ {e : Expr}, natFragOk E c e = true → e.constsResolve E = true := by
  intro e
  induction e with
  | sort u => intro _; rfl
  | fvar idx ty =>
    intro h
    simp only [natFragOk, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Expr.constsResolve, h.2]
    exact hnat
  | const n us =>
    intro h
    simp only [natFragOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Expr.constsResolve]
    rcases h with ⟨rfl, -⟩ | h
    · exact hc
    · revert h; cases E.find? n <;> simp
  | app f a ihf iha =>
    intro h
    simp only [natFragOk, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | _ => intro h; simp [natFragOk] at h

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-- What an operation's footprint lists is read alike from its source. -/
theorem footR {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci) {d : Name}
    (hd : d ∈ pinFootprint c) : ((R c).find? d).isSome = true :=
  (S.scopeR hf).2.2.2.2 d hd

theorem cvMap {n d : Name} (hn : (C.find? n).isSome = true) (hd : ((R n).find? d).isSome = true) :
    (C.find? d).map (·.toConstantVal) = ((E n).find? d).map (·.toConstantVal) :=
  (S.look hn hd).cv

/-- **The guard is the source's.** -/
theorem natOpGuard_eq {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci)
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    natOpGuard C c = natOpGuard (E c) c := by
  have hn := isSome_of hf
  obtain ⟨hb3, hdeps, hbool, -, -⟩ := natOpFoot hc
  have hR : ∀ d ∈ pinFootprint c, ((R c).find? d).isSome = true := fun d hd => S.footR hf hd
  unfold natOpGuard
  rw [natLitSupported_alike (S.look hn (hR _ (hb3 _ (by simp)))) (S.look hn (hR _ (hb3 _ (by simp))))
    (S.look hn (hR _ (hb3 _ (by simp))))]
  have hall : ((natOpDeps c).all fun n => (C.find? n).isSome) =
      (natOpDeps c).all fun n => ((E c).find? n).isSome := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun _ d hd => S.storedE (hR d (hdeps d hd)), fun _ d hd => S.storedC (hR d (hdeps d hd))⟩
  rw [hall]
  congr 1
  split
  · rename_i hcond
    have hcond' : (decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true := by simpa using hcond
    obtain ⟨a, b, e1, e2, h⟩ := S.look hn (hR _ (hbool hcond' boolTrueName (by simp)))
    obtain ⟨a', b', e1', e2', h'⟩ := S.look hn (hR _ (hbool hcond' boolFalseName (by simp)))
    rw [e1, e2, e1', e2']
    dsimp only
    rw [h.cv, h'.cv]
  · rfl

/-- **The dependencies' pins are the source's.** -/
theorem natOpPinned_eq {c : Name} {ci : ConstantInfo} (hf : C.find? c = some ci)
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    (natOpDeps c).all (natOpPinnedOk C) = (natOpDeps c).all (natOpPinnedOk (E c)) := by
  have hn := isSome_of hf
  obtain ⟨-, hdeps, -, hbq, -⟩ := natOpFoot hc
  have hR : ∀ d ∈ pinFootprint c, ((R c).find? d).isSome = true := fun d hd => S.footR hf hd
  have key : ∀ n ∈ natOpDeps c, natOpPinnedOk C n = natOpPinnedOk (E c) n := by
    intro n hnd
    obtain ⟨a, b, e1, e2, h⟩ := S.look hn (hR n (hdeps n hnd))
    unfold natOpPinnedOk
    rw [e1, e2]
    dsimp only
    rw [h.cv, natOpTyPinned_congr (fun hb => S.cvMap hn (hR _ (hbq n hnd hb)))]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h n hnd => (key n hnd) ▸ h n hnd, fun h n hnd => (key n hnd).symm ▸ h n hnd⟩

/-- The part read alike stores what the source does, at a name read alike. -/
theorem storedNoLevels_R {c d : Name} (hd : ((R c).find? d).isSome = true)
    (h : storedNoLevels (E c) d) : storedNoLevels (R c) d := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hd
  exact storedNoLevels_congr (by rw [hci, (S.read.R_sub c d ci hci).1]) h

theorem nat_ops (φ : Name → Nat) : NatOps S.base φ := by
  intro c hcN ci hf
  have hc : c ∈ natOpNames ∨ c ∈ natDivModNames := .inl hcN
  have hn := isSome_of hf
  obtain ⟨ci', hf', -⟩ := S.src hf
  obtain ⟨hg, hpin, hlaws⟩ := (S.m c).nat_ops φ c hcN ci' hf'
  obtain ⟨hb3, hdeps, hbool, -, -⟩ := natOpFoot hc
  have hR : ∀ d ∈ pinFootprint c, ((R c).find? d).isSome = true := fun d hd => S.footR hf hd
  obtain ⟨-, hsZ, hsS, hsD, hsB⟩ := natOpGuard_stored hg hpin
  have hcond : c = natBeqName ∨ c = natBleName →
      (decide (c = natBeqName) || decide (c = natBleName) || natDivModNames.contains c) = true := by
    rintro (rfl | rfl) <;> simp
  have hfrag := natOpEquations_frag (env := R c) (c := c)
    (S.storedNoLevels_R (hR _ (hb3 _ (by simp))) hsZ)
    (S.storedNoLevels_R (hR _ (hb3 _ (by simp))) hsS)
    (fun d hd _ => S.storedNoLevels_R (hR _ (hdeps d hd)) (hsD d hd))
    (fun hb => S.storedNoLevels_R (hR _ (hbool (hcond hb) _ (by simp))) (hsB (hcond hb)).1)
    (fun hb => S.storedNoLevels_R (hR _ (hbool (hcond hb) _ (by simp))) (hsB (hcond hb)).2)
  have hnatR := hR _ (hb3 natName (by simp))
  have hres : ∀ e, natFragOk (R c) c e = true → e.constsResolve (R c) = true :=
    fun e he => constsResolve_of_natFragOk (S.selfR hf) hnatR he
  refine ⟨by rw [S.natOpGuard_eq hf hc]; exact hg, by rw [S.natOpPinned_eq hf hc]; exact hpin,
    fun eq hq => ?_⟩
  obtain ⟨L, Rr, hL, hRr, hlaw⟩ := hlaws eq hq
  obtain ⟨f1, f2⟩ := hfrag eq hq
  refine ⟨L, Rr, ?_, ?_, fun ρ x y hx hy => ?_⟩
  · rw [base_acval, S.denote_eq hn φ 2 _ (hres _ f1)]; exact hL
  · rw [base_acval, S.denote_eq hn φ 2 _ (hres _ f2)]; exact hRr
  · rw [base_acval, S.leaf c hn _ hnatR] at hx hy
    exact hlaw ρ x y hx hy

theorem div_mod (φ : Name → Nat) : DivMod S.base φ := by
  intro c hcN ci hf
  have hc : c ∈ natOpNames ∨ c ∈ natDivModNames := .inr hcN
  have hn := isSome_of hf
  obtain ⟨ci', hf', -⟩ := S.src hf
  obtain ⟨hg, hpin, hlaw⟩ := (S.m c).div_mod φ c hcN ci' hf'
  obtain ⟨hb3, hdeps, hbool, -, hble⟩ := natOpFoot hc
  have hR : ∀ d ∈ pinFootprint c, ((R c).find? d).isSome = true := fun d hd => S.footR hf hd
  have hcond : (decide (c = natBeqName) || decide (c = natBleName) ||
      natDivModNames.contains c) = true := by
    simp only [Bool.or_eq_true]; exact .inr (List.contains_iff_mem.mpr hcN)
  refine ⟨by rw [S.natOpGuard_eq hf hc]; exact hg, by rw [S.natOpPinned_eq hf hc]; exact hpin,
    fun ρ x y hx hy => ?_⟩
  have hleaf : ∀ n ∈ dmValNames c,
      interp V ρ (aC n φ) = interp V ρ ((S.m c).base2.acval n φ) := by
    intro n hnm
    have hnR : ((R c).find? n).isSome = true := by
      simp only [dmValNames, List.mem_cons] at hnm
      rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnm
      · exact hR _ (hb3 _ (by simp))
      · exact hR _ (hbool hcond _ (by simp))
      · exact hR _ (hbool hcond _ (by simp))
      · exact hR _ (hb3 _ (by simp))
      · exact hR _ (hb3 _ (by simp))
      · exact hR _ (hdeps _ (hble hcN))
      · exact S.selfR hf
      · exact hR _ (hdeps _ hnm)
    rw [S.leaf c hn _ hnR]
  rw [base_acval] at hx hy ⊢
  rw [hleaf natName (by simp [dmValNames])] at hx hy
  exact (divModClausesV_congr hcN (fun n hn => (hleaf n hn).symm)).mp (hlaw ρ x y hx hy)

end CtxSrc

end ConLeche.Model.Modular
