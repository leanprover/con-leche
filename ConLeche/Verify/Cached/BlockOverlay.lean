module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The overlay answers as the pushes would (task #329)

The cached driver's block tail (`checkBlockTailS`,
`ConLeche/Cached/CheckerC.lean`) keeps the constructors' index unique at
every push: the rule-less recursors are an overlay sharing the index
(`classFeROvl`, the `ruleEnv` of `shadowOpsC`) and the stored
recursors' records are built before the first push (`blockRecInfosTF`,
pushed by `FEnv.pushAll`).  The facts the proofs about that code need:

* `find?_overlay_pushAll`, `env_overlay_pushAll` — an overlay answers
  `find?` and `env` as pushing its constants would, on an environment
  without an overlay;
* `classRecsRulesOk_classFeROvl` — the rule stage at the cached
  operations, which read the rule environment only through `find?` and
  `env` (`ConLeche/Verify/Cached/KnotCongr.lean`), answers at the overlay
  as at the pushed `classFeR`;
* `pushAll_mkFEnv` — pushing a list onto a canonical index is the
  canonical index of the extended environment.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The overlay answers as the pushes would -/

/-- The bounded index lookup, as `FEnv.find?` reads it. -/
private def bnd (idx : Std.HashMap Name (Nat × ConstantInfo)) (b : Nat) (n : Name) :
    Option ConstantInfo :=
  match idx[n]? with
  | some (c, ci) => if c < b then some ci else none
  | none => none

private theorem find?_of_ovl_nil {fe : FEnv} (h : fe.ovl = []) (n : Name) :
    fe.find? n = bnd fe.idx fe.visibleBelow n := by
  obtain ⟨env, idx, vis, ovl⟩ := fe
  subst h
  rfl

private theorem find?_overlay_bnd {fe : FEnv} (h : fe.ovl = []) (new : List ConstantInfo)
    (n : Name) :
    (fe.overlay new).find? n
      = (new.find? (·.name == n)).or (bnd fe.idx (fe.visibleBelow + new.length) n) := by
  obtain ⟨env, idx, vis, ovl⟩ := fe
  subst h
  cases new with
  | nil => rfl
  | cons ci rest =>
    show (match (ci :: rest ++ []).find? (·.name == n) with
        | some ci => some ci
        | none => bnd idx (vis + (ci :: rest ++ []).length) n) = _
    rw [List.append_nil]
    cases (ci :: rest).find? (·.name == n) <;> rfl

private theorem bnd_insert (idx : Std.HashMap Name (Nat × ConstantInfo)) {vis b : Nat}
    (hb : vis < b) (ci : ConstantInfo) (n : Name) :
    bnd (idx.insert ci.name (vis, ci)) b n
      = if ci.name == n then some ci else bnd idx b n := by
  unfold bnd
  rw [Std.HashMap.getElem?_insert]
  by_cases hn : ci.name == n
  · rw [ite_eq_left hn, ite_eq_left hn]
    exact ite_eq_left hb
  · rw [ite_eq_right hn, ite_eq_right hn]

private theorem pushAll_shape : ∀ (cis : List ConstantInfo) (fe : FEnv), fe.ovl = [] →
    (FEnv.pushAll cis fe).ovl = [] ∧
    (FEnv.pushAll cis fe).env = ⟨cis.reverse ++ fe.env.consts⟩ ∧
    ∀ n, (FEnv.pushAll cis fe).find? n
      = (cis.reverse.find? (·.name == n)).or (bnd fe.idx (fe.visibleBelow + cis.length) n)
  | [], fe, h => by
    refine ⟨h, rfl, fun n => ?_⟩
    rw [FEnv.pushAll, find?_of_ovl_nil h]
    rfl
  | ci :: rest, fe, h => by
    have h' : (fe.push ci).ovl = [] := h
    obtain ⟨ho, he, hf⟩ := pushAll_shape rest (fe.push ci) h'
    refine ⟨ho, ?_, fun n => ?_⟩
    · rw [FEnv.pushAll, he]
      simp [FEnv.push]
    · rw [FEnv.pushAll, hf n]
      show (rest.reverse.find? (·.name == n)).or
          (bnd (fe.idx.insert ci.name (fe.visibleBelow, ci)) (fe.visibleBelow + 1 + rest.length) n)
        = _
      rw [bnd_insert _ (by omega), List.reverse_cons, List.find?_append, Option.or_assoc,
        List.length_cons, show fe.visibleBelow + (rest.length + 1)
          = fe.visibleBelow + 1 + rest.length by omega]
      congr 1
      simp only [List.find?_cons, List.find?_nil]
      by_cases hn : ci.name == n
      · simp [hn]
      · simp [hn]

/-- **An overlay answers `find?` as pushing its constants would**, on
an environment without an overlay. -/
theorem find?_overlay_pushAll {fe : FEnv} (h : fe.ovl = []) (cis : List ConstantInfo) :
    (fe.overlay cis.reverse).find? = (FEnv.pushAll cis fe).find? := by
  funext n
  rw [find?_overlay_bnd h, (pushAll_shape cis fe h).2.2 n, List.length_reverse]

/-- An overlay's environment is the pushed one. -/
theorem env_overlay_pushAll (fe : FEnv) (h : fe.ovl = []) (cis : List ConstantInfo) :
    (fe.overlay cis.reverse).env = (FEnv.pushAll cis fe).env := by
  rw [(pushAll_shape cis fe h).2.1]
  rfl

/-! ## The rule-less recursors -/

theorem consBlockRecsBareF_eq_pushAll (p : BlockShape) :
    ∀ (m : Nat) (rs : List (ConstantVal × Nat)) (fe : FEnv),
      consBlockRecsBareF p m rs fe = FEnv.pushAll (blockRecInfosBare p m rs) fe
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, fe => by
    simp only [consBlockRecsBareF, blockRecInfosBare, FEnv.pushAll]
    exact consBlockRecsBareF_eq_pushAll p (m + 1) rest _

theorem classFeROvl_find? {fe : FEnv} (h : fe.ovl = []) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    (classFeROvl p Ms cvGs recCls fe).find? = (classFeR p Ms cvGs recCls fe).find? := by
  unfold classFeROvl classFeR
  rw [consBlockRecsBareF_eq_pushAll, find?_overlay_pushAll h]

theorem classFeROvl_env {fe : FEnv} (h : fe.ovl = []) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    (classFeROvl p Ms cvGs recCls fe).env = (classFeR p Ms cvGs recCls fe).env := by
  unfold classFeROvl classFeR
  rw [consBlockRecsBareF_eq_pushAll, env_overlay_pushAll fe h]

/-! ## The rule stage reads `feR` through `resolve` and `env` -/

section RulesCongr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
  {ops : CheckerOps m} {w : StructWalkers} {feT feR₁ feR₂ : FEnv}

theorem classRuleOk_congrR (hres : w.resolve feR₁ = w.resolve feR₂)
    (henv : feR₁.env = feR₂.env) (cvR : ConstantVal) (pw : PropWhen) (n : Nat) (gen : Expr) :
    classRuleOk ops w feT feR₁ cvR pw n gen = classRuleOk ops w feT feR₂ cvR pw n gen := by
  unfold classRuleOk
  rw [hres, henv]

theorem classRulesOk_congrR (hres : w.resolve feR₁ = w.resolve feR₂)
    (henv : feR₁.env = feR₂.env) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (pw : PropWhen) (c : Nat) :
    ∀ xs, classRulesOk ops w feT feR₁ g recOf cvR pw c xs
      = classRulesOk ops w feT feR₂ g recOf cvR pw c xs
  | [] => rfl
  | x :: xs => by
    simp only [classRulesOk, classRuleOk_congrR hres henv,
      classRulesOk_congrR hres henv g recOf cvR pw c xs]

theorem classRecsRulesOk_congrR (hres : w.resolve feR₁ = w.resolve feR₂)
    (henv : feR₁.env = feR₂.env) (g : ClassGen) (recOf : Nat → Option Name) (pw : PropWhen) :
    ∀ cvs cs, classRecsRulesOk ops w feT feR₁ g recOf pw cvs cs
      = classRecsRulesOk ops w feT feR₂ g recOf pw cvs cs
  | cvG :: cvs, c :: cs => by
    simp only [classRecsRulesOk, classRulesOk_congrR hres henv,
      classRecsRulesOk_congrR hres henv g recOf pw cvs cs]
  | [], _ => by simp only [classRecsRulesOk]
  | _ :: _, [] => by simp only [classRecsRulesOk]

end RulesCongr

/-! ## The cached stage -/

variable (mode : CheckMode)

/-- `sharedOpsRuleR` reads `fe` only through `find?`. -/
theorem sharedOpsRuleR_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    sharedOpsRuleR mode fe₁ = sharedOpsRuleR mode fe₂ := by
  unfold sharedOpsRuleR sharedOpsC opE opB opS
  rw [coreKnotI_congr hfe]

/-- **The rule stage at the overlay is the rule stage at the pushes**,
at the cached operations, on an environment without an overlay. -/
theorem classRecsRulesOk_classFeROvl {fe : FEnv} (h : fe.ovl = []) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat)
    (g : ClassGen) (recOf : Nat → Option Name) (pw : PropWhen) :
    classRecsRulesOk (sharedOpsRuleR mode (classFeROvl p Ms cvGs recCls fe))
        structWalkersC fe (classFeROvl p Ms cvGs recCls fe) g recOf pw cvGs recCls
      = classRecsRulesOk (sharedOpsRuleR mode (classFeR p Ms cvGs recCls fe))
        structWalkersC fe (classFeR p Ms cvGs recCls fe) g recOf pw cvGs recCls := by
  have hfind := classFeROvl_find? h p Ms cvGs recCls
  rw [sharedOpsRuleR_congr mode hfind]
  exact classRecsRulesOk_congrR (constsResolveFC_congr hfind)
    (classFeROvl_env h p Ms cvGs recCls) g recOf pw cvGs recCls

/-! ## The stored recursors' pushes -/

/-- Pushing a list onto a canonical index is the canonical index of the
environment with the list consed on, newest (last pushed) first. -/
theorem pushAll_mkFEnv : ∀ (cis : List ConstantInfo) (env : Env),
    FEnv.pushAll cis (mkFEnv env) = mkFEnv ⟨cis.reverse ++ env.consts⟩
  | [], env => rfl
  | ci :: rest, env => by
    show FEnv.pushAll rest (mkFEnv ⟨ci :: env.consts⟩) = _
    rw [pushAll_mkFEnv rest]
    simp

end ConLeche.Cached
