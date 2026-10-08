module

public import ConLeche.Cached.CheckerC
import ConLeche.Cached.KnotCongr

public section

/-!
# The block tail's in-place pushes are the reference's (task #329)

The cached driver runs `checkBlockTailS` (`ConLeche/Cached/CheckerC.lean`),
which keeps the constructors' index unique at every push: the rule-less
recursors are an overlay sharing the index (`classFeROvl`,
`genRecCheckOvl`) and the stored recursors' records are built before the
first push (`blockRecInfosTF`).  This file proves it equal to the
reference `checkBlockTailSRef`, which every other proof reads
(`checkBlockTailS_eq_ref`).

* `find?_overlay_pushAll` — an overlay answers `find?` as pushing its
  constants would, on an environment without an overlay;
* `genRecCheckOvl_eq` — at the cached operations, which read the index
  only through `find?` (`ConLeche/Cached/KnotCongr.lean`), the
  overlay stage is `genRecCheck`.

It sits in the implementation tier because the parallel install's
driver carries the install's congruence in the index
(`ConLeche/Cached/ViewCongr.lean`), which reads the block tail through
this equality; it imports the cached checker and `KnotCongr` only (the
self-contained exception of CLAUDE.md).
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The overlay answers as the pushes would -/

/-- The bounded index lookup, as `FEnv.find?` reads it. -/
private def bnd (idx : Std.HashMap Name (Nat × ConstantInfo)) (base : FBase) (b : Nat)
    (n : Name) : Option ConstantInfo :=
  match idx[n]? with
  | some (c, ci) => if c < b then some ci else none
  | none => base.find? n

private theorem find?_of_ovl_nil {fe : FEnv} (h : fe.ovl = []) (n : Name) :
    fe.find? n = bnd fe.idx fe.base fe.visibleBelow n := by
  obtain ⟨env, idx, vis, base, ovl⟩ := fe
  subst h
  rfl

private theorem find?_overlay_bnd {fe : FEnv} (h : fe.ovl = []) (new : List ConstantInfo)
    (n : Name) :
    (fe.overlay new).find? n
      = (new.find? (·.name == n)).or (bnd fe.idx fe.base (fe.visibleBelow + new.length) n) := by
  obtain ⟨env, idx, vis, base, ovl⟩ := fe
  subst h
  cases new with
  | nil => rfl
  | cons ci rest =>
    show (match (ci :: rest ++ []).find? (·.name == n) with
        | some ci => some ci
        | none => bnd idx base (vis + (ci :: rest ++ []).length) n) = _
    rw [List.append_nil]
    cases (ci :: rest).find? (·.name == n) <;> rfl

private theorem bnd_insert (idx : Std.HashMap Name (Nat × ConstantInfo)) (base : FBase)
    {vis b : Nat} (hb : vis < b) (ci : ConstantInfo) (n : Name) :
    bnd (idx.insert ci.name (vis, ci)) base b n
      = if ci.name == n then some ci else bnd idx base b n := by
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
      = (cis.reverse.find? (·.name == n)).or
          (bnd fe.idx fe.base (fe.visibleBelow + cis.length) n)
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
          (bnd (fe.idx.insert ci.name (fe.visibleBelow, ci)) fe.base
            (fe.visibleBelow + 1 + rest.length) n)
        = _
      rw [bnd_insert _ _ (by omega), List.reverse_cons, List.find?_append, Option.or_assoc,
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

/-- **The overlay stage is `genRecCheck`** at the cached operations, on
an environment without an overlay. -/
theorem genRecCheckOvl_eq {fe : FEnv} (h : fe.ovl = []) (p : BlockShape) (nestedBit : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (cvTas : List ConstantVal) (block : List ConstantInfo) :
    genRecCheckOvl (shadowOpsC mode) fe p nestedBit params tbl rd Ms cvTas block
      = genRecCheck (shadowOpsC mode) fe p nestedBit params tbl rd Ms cvTas block := by
  have key : ∀ (Ms' : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat)
      (g : ClassGen) (recOf : Nat → Option Name) (pw : PropWhen),
      classRecsRulesOk ((shadowOpsC mode).opsRuleR (classFeROvl p Ms' cvGs recCls fe))
          (shadowOpsC mode).walkers fe (classFeROvl p Ms' cvGs recCls fe) g recOf pw
          cvGs recCls
        = classRecsRulesOk ((shadowOpsC mode).opsRuleR (classFeR p Ms' cvGs recCls fe))
          (shadowOpsC mode).walkers fe (classFeR p Ms' cvGs recCls fe) g recOf pw
          cvGs recCls := by
    intro Ms' cvGs recCls g recOf pw
    have hfind := classFeROvl_find? h p Ms' cvGs recCls
    show classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe _ g recOf pw cvGs recCls
      = classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe _ g recOf pw cvGs recCls
    rw [sharedOpsRuleR_congr mode hfind]
    exact classRecsRulesOk_congrR (constsResolveFC_congr hfind)
      (classFeROvl_env h p Ms' cvGs recCls) g recOf pw cvGs recCls
  unfold genRecCheckOvl genRecCheck
  simp only [key]

/-- **The driver's block tail is the reference's.** -/
theorem checkBlockTailS_eq_ref (block : List ConstantInfo) (q : BlockPass FEnv) :
    checkBlockTailS mode block q = checkBlockTailSRef mode block q := by
  obtain ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, params, rd, cls, tbl⟩ := q
  unfold checkBlockTailS checkBlockTailSRef
  by_cases hE : (consBlockCtorsF p.nP ctorsAs env₁).ovl.isEmpty
  · have h : (consBlockCtorsF p.nP ctorsAs env₁).ovl = [] := List.isEmpty_iff.mp hE
    simp only [hE, ↓reduceIte, genRecCheckOvl_eq mode h, consBlockRecsTF_eq_fast,
      consBlockRecsTFFast]
  · simp only [hE, Bool.false_eq_true, ↓reduceIte]

end ConLeche.Cached
