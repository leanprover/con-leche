module

public import ConLeche.Model.Inductives.ClassSubst

public section

/-!
# A class fact's kept holes, and the coarser tier at stage values (P2d)

A container class `c`'s fact (PROOFPLAN §3) reads `c`'s abstracted
constructors at STAGE values: `c`'s group (the block mates of `c`'s
inductive at `c`'s instantiation) at the lfp variable, `c`'s cyclic inner
classes (younger inductives) free, every other class coherent — its hole
reads its key in hole form (`StageCoh`, `ClassSubst.lean` §7).  This file
fixes the KEPT holes of that fact and closes P2B's open item, the defeq
tier at stage values:

* `classKept` — the holes `c`'s fact keeps free: its group's and every
  class of an inductive not strictly older than `c`'s.  Closed under same keys (`classKept_fclosed`,
  given that a hole names one class).
* The defeq tier in a container class's crest identifies only with
  classes of a strictly OLDER inductive outside its block
  (`classAliasesFor`, the class check), so its holes are never kept
  (`classAliasesFor_notKept`): an alias hole reads its target's key in
  hole form, which the occurrence it replaced reads too — the
  per-component defeq, read (`AliasKeySem`).  So the whole abstraction —
  syntactic tier, then the defeq tier — reads as its restriction to the
  kept holes at every stage-coherent valuation (`crestAbs_read_stage`).

DESIGN record CLASSCHECK / P2D.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo ClassAlias aliasOcc? classAbs classAbsGo
  classAliasesFor classOwn classKeptBy)

universe w

/-! ## 1. The kept holes -/

/-- The holes class `c`'s fact keeps free. -/
@[expose] def classKept (age : Name → Nat) (mates : Name → List Name) (cls : List ClassInfo)
    (c : ClassInfo) : Expr → Bool := fun h =>
  cls.any fun d => d.hole == some h && classKeptBy age mates c d

/-- **A hole names one class.** -/
@[expose] def HolesUniq (cls : List ClassInfo) : Prop :=
  ∀ d ∈ cls, ∀ d' ∈ cls, ∀ h, d.hole = some h → d'.hole = some h → d = d'

theorem classKept_eq {age : Name → Nat} {mates : Name → List Name} {cls : List ClassInfo}
    (hu : HolesUniq cls) {c d : ClassInfo} (hd : d ∈ cls) {h : Expr} (hh : d.hole = some h) :
    classKept age mates cls c h = classKeptBy age mates c d := by
  unfold classKept
  cases hk : classKeptBy age mates c d
  · rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨d', hd', hp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hu d' hd' d hd h hp.1 hh] at hp
    rw [hk] at hp
    exact Bool.false_ne_true hp.2
  · exact List.any_eq_true.mpr ⟨d, hd, by simp [hh, hk]⟩

theorem lvEqL_of_zipAll {as bs : List Expr} (hl : as.length = bs.length)
    (h : ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true) : LvEqL as bs :=
  lvEqL_of_zip hl h

theorem zipAll_of_lvEqL {as bs : List Expr} (h : LvEqL as bs) :
    ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true :=
  zip_of_lvEqL h

theorem classOwn_iff {mates : Name → List Name} {c d : ClassInfo} :
    classOwn mates c d = true ↔ (mates c.key.ind).contains d.key.ind = true ∧
      d.key.lvls.map Level.canon = c.key.lvls.map Level.canon ∧ LvEqL d.dsA c.dsA := by
  unfold classOwn
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, lvEqL_of_zipAll h3 h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, h3.1⟩, zipAll_of_lvEqL h3⟩

/-- Group membership reads the class only up to same keys. -/
theorem classOwn_sameKey {mates : Name → List Name} {c d d' : ClassInfo} (hs : SameKey d d') :
    classOwn mates c d = classOwn mates c d' := by
  obtain ⟨hI, hlv, hps⟩ := hs
  apply Bool.eq_iff_iff.mpr
  rw [classOwn_iff, classOwn_iff, hI, hlv]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => hps.symm.trans h, fun h => hps.trans h⟩

theorem classKeptBy_sameKey {age : Name → Nat} {mates : Name → List Name} {c d d' : ClassInfo}
    (hs : SameKey d d') : classKeptBy age mates c d = classKeptBy age mates c d' := by
  unfold classKeptBy
  rw [classOwn_sameKey hs, hs.1]

/-- **The kept holes are closed under same keys.** -/
theorem classKept_fclosed {age : Name → Nat} {mates : Name → List Name} {cls : List ClassInfo}
    (hu : HolesUniq cls) (c : ClassInfo) : FClosed cls (classKept age mates cls c) := by
  intro d hd d' hd' h h' hh hh' hs
  rw [classKept_eq hu hd hh, classKept_eq hu hd' hh', classKeptBy_sameKey hs]

/-- **The defeq tier of a container class's crest keeps no hole**: its
aliases identify only with classes of strictly older inductives outside
the block, neither in the group nor cyclic. -/
theorem classAliasesFor_notKept {age : Name → Nat} {mates : Name → List Name}
    {cls : List ClassInfo} (hu : HolesUniq cls) {c : ClassInfo} (hc : c.member = none)
    {al : List ClassAlias}
    (hal : ∀ a ∈ al, ∃ ci ∈ cls, ci.hole = some a.hole ∧ ci.key.ind = a.ind) :
    ∀ a ∈ classAliasesFor age mates c al, classKept age mates cls c a.hole = false := by
  intro a ha
  unfold classAliasesFor at ha
  rw [hc] at ha
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ha
  obtain ⟨ha, hage, hmate⟩ := ha
  obtain ⟨ci, hci, hh, hI⟩ := hal a ha
  rw [classKept_eq hu hci hh]
  unfold classKeptBy classOwn
  rw [hI, hmate]
  simp [hage]

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
