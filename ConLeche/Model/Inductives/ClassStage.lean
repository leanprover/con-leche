module

public import ConLeche.Model.Inductives.ClassSubst

public section

/-!
# A class fact's stage holes, and the coarser tier at stage values (P2d)

A container class `c`'s fact (PROOFPLAN §3, DESIGN CLASSCHECK / P2D3)
reads `c`'s abstracted constructors at STAGE values: `c`'s group (the
block mates of `c`'s inductive at `c`'s instantiation) at the lfp
variable, `c`'s FREE classes (the class check's free-set certificate,
`classFreeOk`) arbitrary, every other class coherent — its hole reads its
key in hole form (`StageCoh`, `ClassSubst.lean` §7).  This file:

* `classStageHoles` — the holes held at a stage value: the free classes'
  and the group's.  Closed under same keys (`classStageHoles_fclosed`,
  given that a hole names one class).
* The defeq tier in a container class's crest identifies only with
  classes of a strictly OLDER inductive outside its block
  (`classAliasesFor`) and — the certificate — never with a free class,
  so its holes are never stage holes: an alias hole reads its target's
  key in hole form, which the occurrence it replaced reads too — the
  per-component defeq, read (`AliasKeySem`).  So the whole abstraction —
  syntactic tier, then the defeq tier — reads as its restriction to the
  stage holes at every stage-coherent valuation (`crestAbs_read_stage`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo ClassAlias aliasOcc? classAbs classAbsGo
  classAliasesFor classOwn classSameKey classHoleOf ClassFreeV)

universe w

/-! ## 1. The stage holes -/

/-- **A hole names one class.** -/
@[expose] def HolesUniq (cls : List ClassInfo) : Prop :=
  ∀ d ∈ cls, ∀ d' ∈ cls, ∀ h, d.hole = some h → d'.hole = some h → d = d'

/-- The holes container class `c`'s fact holds at a STAGE value: its free
classes' and its group's (DESIGN CLASSCHECK / P2D3). -/
@[expose] def classStageHoles (V : ClassFreeV) (c : Nat) : Expr → Bool :=
  classHoleOf V.cls (V.stage c)

theorem classSameKey_iff {c d : ClassInfo} : classSameKey c d = true ↔ SameKey c d := by
  unfold classSameKey SameKey
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, lvEqL_of_zip h3 h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, h3.1⟩, zip_of_lvEqL h3⟩

theorem SameKey.symm {c d : ClassInfo} (h : SameKey c d) : SameKey d c :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameKey.trans {c d e : ClassInfo} (h1 : SameKey c d) (h2 : SameKey d e) : SameKey c e :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem classOwn_iff {mates : Name → List Name} {c d : ClassInfo} :
    classOwn mates c d = true ↔ (mates c.key.ind).contains d.key.ind = true ∧
      d.key.lvls.map Level.canon = c.key.lvls.map Level.canon ∧ LvEqL d.dsA c.dsA := by
  unfold classOwn
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, lvEqL_of_zip h3 h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, h3.1⟩, zip_of_lvEqL h3⟩

/-- Group membership reads the class only up to same keys. -/
theorem classOwn_sameKey {mates : Name → List Name} {c d d' : ClassInfo} (hs : SameKey d d') :
    classOwn mates c d = classOwn mates c d' := by
  obtain ⟨hI, hlv, hps⟩ := hs
  apply Bool.eq_iff_iff.mpr
  rw [classOwn_iff, classOwn_iff, hI, hlv]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => hps.symm.trans h, fun h => hps.trans h⟩

section Build

variable {cls : List ClassInfo} {mates : Name → List Name} {crests : List (List Expr)}
  {Fl : Nat → List Nat}

theorem ClassFreeV.build_own (c d : Nat) :
    (ClassFreeV.build cls mates crests Fl).own c d =
      (decide (c < cls.length) && decide (d < cls.length) &&
        classOwn mates (cls.getD c default) (cls.getD d default)) := by
  unfold ClassFreeV.own ClassFreeV.build
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases hc : c < cls.length <;> by_cases hd : d < cls.length <;> simp [hc, hd]

theorem ClassFreeV.build_sk (d e : Nat) :
    ((ClassFreeV.build cls mates crests Fl).skT.getD d #[]).getD e false =
      (decide (d < cls.length) && decide (e < cls.length) &&
        classSameKey (cls.getD d default) (cls.getD e default)) := by
  unfold ClassFreeV.build
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases hd : d < cls.length <;> by_cases he : e < cls.length <;> simp [hd, he]

/-- Freeness reads the class only up to same keys. -/
theorem ClassFreeV.build_isFree_sameKey {c j j' : Nat} (hj : j < cls.length) (hj' : j' < cls.length)
    (hs : SameKey (cls.getD j default) (cls.getD j' default)) :
    (ClassFreeV.build cls mates crests Fl).isFree c j =
      (ClassFreeV.build cls mates crests Fl).isFree c j' := by
  unfold ClassFreeV.isFree
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, ClassFreeV.build_sk, hj, hj', decide_true, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq, classSameKey_iff]
  exact ⟨fun ⟨e, he, hl, h⟩ => ⟨e, he, hl, hs.symm.trans h⟩,
    fun ⟨e, he, hl, h⟩ => ⟨e, he, hl, hs.trans h⟩⟩

theorem ClassFreeV.build_own_sameKey {c j j' : Nat} (hj : j < cls.length) (hj' : j' < cls.length)
    (hs : SameKey (cls.getD j default) (cls.getD j' default)) :
    (ClassFreeV.build cls mates crests Fl).own c j =
      (ClassFreeV.build cls mates crests Fl).own c j' := by
  rw [ClassFreeV.build_own, ClassFreeV.build_own, classOwn_sameKey hs]
  simp [hj, hj']

theorem ClassFreeV.build_stage_sameKey {c j j' : Nat} (hj : j < cls.length) (hj' : j' < cls.length)
    (hs : SameKey (cls.getD j default) (cls.getD j' default)) :
    (ClassFreeV.build cls mates crests Fl).stage c j =
      (ClassFreeV.build cls mates crests Fl).stage c j' := by
  unfold ClassFreeV.stage
  rw [ClassFreeV.build_isFree_sameKey hj hj' hs, ClassFreeV.build_own_sameKey hj hj' hs]

end Build

/-- A hole-selected predicate reads the class of the hole. -/
theorem classHoleOf_eq {cls : List ClassInfo} (hu : HolesUniq cls) {P : Nat → Bool}
    (hP : ∀ j j', j < cls.length → j' < cls.length → cls.getD j default = cls.getD j' default →
      P j = P j') {j : Nat} {d : ClassInfo}
    (hd : cls[j]? = some d) {h : Expr} (hh : d.hole = some h) : classHoleOf cls P h = P j := by
  unfold classHoleOf
  cases hk : P j
  · rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨j', hj', hp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hj'l : j' < cls.length := List.mem_range.mp hj'
    have hmem' : cls.getD j' default ∈ cls := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'l]; exact List.getElem_mem _
    have hdm : d ∈ cls := List.mem_of_getElem? hd
    have heq := hu _ hmem' d hdm h hp.1 hh
    have : cls.getD j default = d := by simp [List.getD_eq_getElem?_getD, hd]
    have hjl : j < cls.length := (List.getElem?_eq_some_iff.mp hd).1
    rw [hP j' j hj'l hjl (by rw [heq, this]), hk] at hp
    exact Bool.false_ne_true hp.2
  · have hjl : j < cls.length := (List.getElem?_eq_some_iff.mp hd).1
    exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr hjl, by
      simp [List.getD_eq_getElem?_getD, hd, hh, hk]⟩

theorem LvEqL_refl (as : List Expr) : LvEqL as as :=
  ⟨rfl, fun _ a b ha hb => by rw [ha] at hb; cases hb; exact Expr.eqUpToLevels_refl a⟩

/-- A class's index, from its membership. -/
theorem exists_index_of_mem {cls : List ClassInfo} {d : ClassInfo} (hd : d ∈ cls) :
    ∃ j : Nat, cls[j]? = some d := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  exact ⟨j, List.getElem?_eq_getElem hj⟩

/-- **The stage holes are closed under same keys.** -/
theorem classStageHoles_fclosed {cls : List ClassInfo} {mates : Name → List Name}
    {crests : List (List Expr)} {Fl : Nat → List Nat} (hu : HolesUniq cls) (c : Nat) :
    FClosed cls (classStageHoles (ClassFreeV.build cls mates crests Fl) c) := by
  intro d hd d' hd' h h' hh hh' hs
  obtain ⟨j, hj⟩ := exists_index_of_mem hd
  obtain ⟨j', hj'⟩ := exists_index_of_mem hd'
  have hP : ∀ i i', i < cls.length → i' < cls.length → cls.getD i default = cls.getD i' default →
      (ClassFreeV.build cls mates crests Fl).stage c i =
        (ClassFreeV.build cls mates crests Fl).stage c i' :=
    fun i i' hi hi' he => ClassFreeV.build_stage_sameKey hi hi' (by rw [he]; exact ⟨rfl, rfl, LvEqL_refl _⟩)
  unfold classStageHoles
  show classHoleOf cls _ h = classHoleOf cls _ h'
  rw [classHoleOf_eq hu hP hj hh, classHoleOf_eq hu hP hj' hh']
  apply ClassFreeV.build_stage_sameKey (List.getElem?_eq_some_iff.mp hj).1
    (List.getElem?_eq_some_iff.mp hj').1
  simpa [List.getD_eq_getElem?_getD, hj, hj'] using hs

/-- **The defeq tier of a container class's crest keeps no stage hole**:
its aliases identify only with classes of strictly older inductives
outside the block (not the group), and — the certificate — never with a
free class. -/
theorem classAliasesFor_notStage {cls : List ClassInfo} {mates : Name → List Name}
    {crests : List (List Expr)} {Fl : Nat → List Nat} {age : Name → Nat} (hu : HolesUniq cls)
    {c : Nat} {al : List ClassAlias}
    (hal : ∀ a ∈ al, ∃ di ∈ cls, di.hole = some a.hole ∧ di.key.ind = a.ind)
    (hc : (cls.getD c default).member = none)
    (hnf : ∀ a ∈ classAliasesFor age mates (cls.getD c default) al,
      classHoleOf cls ((ClassFreeV.build cls mates crests Fl).isFree c) a.hole = false) :
    ∀ a ∈ classAliasesFor age mates (cls.getD c default) al,
      classStageHoles (ClassFreeV.build cls mates crests Fl) c a.hole = false := by
  intro a ha
  have hnf' := hnf a ha
  have ha' := ha
  unfold classAliasesFor at ha'
  rw [hc] at ha'
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ha'
  obtain ⟨ha0, -, hmate⟩ := ha'
  obtain ⟨di, hdi, hh, hI⟩ := hal a ha0
  obtain ⟨j, hj⟩ := exists_index_of_mem hdi
  have hPf : ∀ i i', i < cls.length → i' < cls.length → cls.getD i default = cls.getD i' default →
      (ClassFreeV.build cls mates crests Fl).isFree c i =
        (ClassFreeV.build cls mates crests Fl).isFree c i' :=
    fun i i' hi hi' he => ClassFreeV.build_isFree_sameKey hi hi'
      (by rw [he]; exact ⟨rfl, rfl, LvEqL_refl _⟩)
  have hPs : ∀ i i', i < cls.length → i' < cls.length → cls.getD i default = cls.getD i' default →
      (ClassFreeV.build cls mates crests Fl).stage c i =
        (ClassFreeV.build cls mates crests Fl).stage c i' :=
    fun i i' hi hi' he => ClassFreeV.build_stage_sameKey hi hi'
      (by rw [he]; exact ⟨rfl, rfl, LvEqL_refl _⟩)
  unfold classStageHoles
  show classHoleOf cls _ a.hole = false
  rw [classHoleOf_eq hu hPs hj hh]
  rw [classHoleOf_eq hu hPf hj hh] at hnf'
  unfold ClassFreeV.stage
  rw [hnf', ClassFreeV.build_own]
  have hdj : cls.getD j default = di := by simp [List.getD_eq_getElem?_getD, hj]
  rw [hdj]
  unfold classOwn
  rw [hI, hmate]
  simp

/-! ## 2. The defeq tier at stage values -/

section Alias

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The per-component defeq, read**: at every admissible valuation an
alias's key reads as its target class's key in hole form. -/
@[expose] def AliasKeySem (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (al : List ClassAlias) (H : Nat)
    (Good : (Nat → V) → Prop) : Prop :=
  ∀ a ∈ al, ∃ ci ∈ cls, ci.hole = some a.hole ∧
    ∀ τ, Good τ → ∀ r r', denoteMeta acval env φ H (aliasKey a) = some r →
      denoteMeta acval env φ H (holeKey cls ci) = some r' → interp V τ r = interp V τ r'

/-- **The defeq tier reads as its input at stage values**, when it keeps
no hole: every alias hole is outside `F`, so at a stage-coherent
valuation it reads its target's key in hole form — which the replaced
occurrence reads too (`AliasKeySem`). -/
theorem aliasAbs_read_stage
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {al : List ClassAlias} {H : Nat} (hwf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (hhk : HoleKeysOk acval env φ cls H) {F : Expr → Bool} (hF : ∀ a ∈ al, F a.hole = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCoh V acval env φ cls F H τ)
    (hsem : AliasKeySem V acval env φ cls al H Good)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} e).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hnone : occRestrict (aliasOcc? al) F = fun _ => none := by
    funext x
    unfold occRestrict
    split
    · rename_i h n hx
      obtain ⟨a, ha, rfl, -⟩ := aliasOcc_spec hx
      simp [hF a ha]
    · rfl
  have h := aliasAbs_read_hole (V := V) (acval := acval) (env := env) (φ := φ) hwf (F := F)
    (Good := Good) (fun x h hx _ d' as2' as1' _ _ => ?_) e h2 h1
  · rwa [hnone, classAbsSpec_none] at h
  · rw [hnone, classAbsSpec_none]
    obtain ⟨a, ha, rfl, us, hfn, hle, hn, hlv, hps⟩ := aliasOcc_spec hx
    obtain ⟨i, ty, hi, hiH⟩ := hwf.hole a ha
    obtain ⟨ci, hci, hch, hkey⟩ := hsem a ha
    have hsem' : Expr.SemEq x (aliasKey a) := by
      have hlen : x.getAppArgs.length = a.nPc := by omega
      have hx' : x = Expr.mkAppN (.const a.ind us) (x.getAppArgs.take a.nPc) := by
        rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs]
      rw [hx']
      unfold aliasKey
      have hlvl := Level.evalEqList_of_isEquivList hlv
      have hps' : (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys
          = a.ps.map Expr.eraseFVarTys := by
        rw [hps, ← hps, List.map_map]
        apply List.map_congr_left
        intro p _
        exact (Expr.eraseFVarTys_idem p).symm
      obtain ⟨hl, hpw⟩ := semEq_of_map_erase hps'
      exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl hpw
    rw [hi]
    refine hole_agree_lift hacl hiH ty (hwf.keyScoped a ha).1 (hwf.keyScoped a ha).2 hsem'
      (hden a ha) (fun τ hτ r hr => ?_)
    have hchs : ci.hole.isSome := by rw [hch]; rfl
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (hhk ci hci hchs).2.2
    rw [hi] at hch
    rw [(hG τ hτ).1 ci hci i ty hch (by rw [← hi]; exact hF a ha) r' hr', hkey τ hτ r r' hr hr']

/-- Agreement at every `Good'` valuation is agreement at every `Good` one
when `Good ⊆ Good'`. -/
theorem optAgree_mono {Good Good' : (Nat → V) → Prop} (hG : ∀ τ, Good τ → Good' τ) {d : Nat}
    {o2 o1 : Option AnnotTerm} (h : OptAgree (ValAgree V Good' d) o2 o1) :
    OptAgree (ValAgree V Good d) o2 o1 := by
  cases o2 <;> cases o1 <;> simp_all [OptAgree]
  intro vals τ hvl hτ
  exact h vals τ hvl (hG τ hτ)

/-- **A crest's whole abstraction, read at stage values**: the syntactic
tier, then a defeq tier keeping no hole, reads as the syntactic tier
restricted to the kept holes `F` (P1 in hole form, `classAbs_read_stage`,
composed with `aliasAbs_read_stage`). -/
theorem crestAbs_read_stage
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) (hhk : HoleKeysOk acval env φ cls H)
    {F : Expr → Bool} (hFc : FClosed cls F)
    {al : List ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, F a.hole = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCoh V acval env φ cls F H τ)
    (hsem : AliasKeySem V acval env φ cls al H Good)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} (classAbs cls e)).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) :=
  optAgree_trans (aliasAbs_read_stage hacl hawf hden hhk hF hG hsem (classAbs cls e) h2 h1)
    (optAgree_mono hG (classAbs_read_stage hacl hwf hhk hFc e h1 h1))

end Alias

end ConLeche.Model
