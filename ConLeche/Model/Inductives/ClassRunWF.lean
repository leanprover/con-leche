module

public import ConLeche.Model.Inductives.ClassStage
public import ConLeche.Verify.Inductives.ClassInv

public section

/-!
# The class check's run: the recogniser's premises (P2d, item 1)

P2B's readings of the class abstraction take syntactic premises about
the classes (`ClassOccWF`, `AliasWF`, `HolesUniq`); here they come from
the run's check 1 (`ClassInfosD`, one `ClassKeyOk` per class) and the
defeq tier's inversion (`ClassAliasOk`):

* a container class's hole is `fvar (hiAt 0 + a)`, `a` the number of
  container classes before it — below the end of the holes, and a hole
  names one class (`HolesUniq`);
* its erased and member-abstracted parameters are as many as its
  container's parameter count, which one inductive fixes;
* an alias's hole is its target class's.

The key's scoping (`ClassOccWF.keyScoped`) is taken as a premise
(`KeysScoped`), its discharge from the annotation and the member
abstraction is the next step.
-/

namespace ConLeche.Model
open ConLeche (Expr Name ClassInfo ClassKey ClassAlias NestCtx ConstantVal ClassKeyOk
  ClassInfosD CheckerOps CheckM Env nestContainer)

/-! ## Check 1, read per position -/

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr}
  {ctorsAs : List (List (ConstantVal × Nat))}

/-- The number of container classes among `cs`. -/
@[expose] def nCont (cs : List ClassInfo) : Nat := (cs.filter (·.member.isNone)).length

theorem nCont_take_lt {cs : List ClassInfo} {i : Nat} {c : ClassInfo} (hc : cs[i]? = some c)
    (hm : c.member = none) : nCont (cs.take i) < nCont cs := by
  unfold nCont
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have e := List.take_append_drop i cs
  have e2 : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hi
  have : (cs.filter (·.member.isNone)).length
      = ((cs.take i).filter (·.member.isNone)).length + 1 +
        ((cs.drop (i + 1)).filter (·.member.isNone)).length := by
    calc (cs.filter (·.member.isNone)).length
        = ((cs.take i ++ cs.drop i).filter (·.member.isNone)).length := by rw [e]
      _ = _ := by
        rw [e2, List.filter_append, List.length_append,
          List.filter_cons_of_pos (by simp [hm]), List.length_cons]
        omega
  omega

theorem nCont_take_mono {cs : List ClassInfo} {i j : Nat} (h : i ≤ j) :
    nCont (cs.take i) ≤ nCont (cs.take j) := by
  unfold nCont
  have : cs.take i = (cs.take j).take i := by simp [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))

/-- **A container class's key, as check 1 built it.** -/
theorem classKeyOk_container {a : Nat} {key : ClassKey} {c : ClassInfo}
    (h : ClassKeyOk ops env ctx holes ctorsAs a key c) (hm : c.member = none) :
    ∃ hty, c.hole = some (.fvar (ctx.hiAt 0 + a) hty) ∧ c.dsE = c.dsA.map Expr.eraseFVarTys ∧
      c.dsA.length = c.nPc ∧ nestContainer ctx c.key.ind = some (c.nPc, c.ctors) := by
  cases h with
  | member => exact nomatch hm
  | container _ _ _ _ _ hC hlen _ _ _ _ _ _ =>
    exact ⟨_, rfl, rfl, by simp [hlen], hC⟩

/-- **Every container class's hole is below the end of the holes, at its
position's counter.** -/
theorem classInfosD_hole {ks : List ClassKey} {cls : List ClassInfo}
    (hD : ClassInfosD ops env ctx holes ctorsAs 0 ks cls) {i : Nat} {c : ClassInfo}
    (hc : cls[i]? = some c) (hm : c.member = none) :
    ∃ hty, c.hole = some (.fvar (ctx.hiAt 0 + nCont (cls.take i)) hty) ∧
      c.dsE = c.dsA.map Expr.eraseFVarTys ∧ c.dsA.length = c.nPc ∧
      nestContainer ctx c.key.ind = some (c.nPc, c.ctors) := by
  obtain ⟨-, hall⟩ := hD.getElem
  obtain ⟨k, -, hk⟩ := hall i c hc
  rw [Nat.zero_add] at hk
  exact classKeyOk_container hk hm

/-- A member class has no hole. -/
theorem classInfosD_member_hole {ks : List ClassKey} {cls : List ClassInfo}
    (hD : ClassInfosD ops env ctx holes ctorsAs 0 ks cls) {c : ClassInfo} (hc : c ∈ cls)
    (hm : c.member.isSome) : c.hole = none := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
  obtain ⟨-, hall⟩ := hD.getElem
  obtain ⟨k, -, hk⟩ := hall i c hi
  cases hk with
  | member => rfl
  | container => simp at hm

/-- A class has a hole exactly when it is a container class. -/
theorem classInfosD_hole_isSome {ks : List ClassKey} {cls : List ClassInfo}
    (hD : ClassInfosD ops env ctx holes ctorsAs 0 ks cls) {c : ClassInfo} (hc : c ∈ cls) :
    c.hole.isSome = c.member.isNone := by
  cases hm : c.member with
  | some t => rw [classInfosD_member_hole hD hc (by simp [hm])]; rfl
  | none =>
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    obtain ⟨hty, hh, -⟩ := classInfosD_hole hD hi hm
    rw [hh]; rfl

/-- **A hole names one class.** -/
theorem classInfosD_holesUniq {ks : List ClassKey} {cls : List ClassInfo}
    (hD : ClassInfosD ops env ctx holes ctorsAs 0 ks cls) : HolesUniq cls := by
  intro d hd d' hd' h hh hh'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hd
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hd'
  have hdm : d.member = none := by
    have := classInfosD_hole_isSome hD hd
    rw [hh] at this; simpa using this.symm
  have hdm' : d'.member = none := by
    have := classInfosD_hole_isSome hD hd'
    rw [hh'] at this; simpa using this.symm
  obtain ⟨t, ht, -⟩ := classInfosD_hole hD hi hdm
  obtain ⟨t', ht', -⟩ := classInfosD_hole hD hj hdm'
  rw [hh] at ht; rw [hh'] at ht'
  have heq0 : nCont (cls.take i) = nCont (cls.take j) := by
    have := ht.symm.trans ht'
    simp only [Option.some.injEq, Expr.fvar.injEq] at this
    omega
  -- same counter ⇒ same position
  have hij : i = j := by
    apply Classical.byContradiction
    intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := nCont_take_mono (cs := cls) (show i + 1 ≤ j by omega)
      have h2 : nCont (cls.take i) < nCont (cls.take (i + 1)) := by
        have := nCont_take_lt (cs := cls.take (i + 1)) (i := i) (c := d)
          (by rw [List.getElem?_take]; simp [hi]) hdm
        simpa [List.take_take] using this
      omega
    · have h1 := nCont_take_mono (cs := cls) (show j + 1 ≤ i by omega)
      have h2 : nCont (cls.take j) < nCont (cls.take (j + 1)) := by
        have := nCont_take_lt (cs := cls.take (j + 1)) (i := j) (c := d')
          (by rw [List.getElem?_take]; simp [hj]) hdm'
        simpa [List.take_take] using this
      omega
  subst hij
  rw [hi] at hj; exact Option.some.inj hj

/-- **The keys are frame-scoped and bound-closed** (the key half of
`ClassOccWF`, discharged separately). -/
@[expose] def KeysScoped (cls : List ClassInfo) (H : Nat) : Prop :=
  ∀ c ∈ cls, c.hole.isSome →
    Expr.WScoped H (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA) ∧
    (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA).looseBVarsBounded 0 = true

/-- **The recogniser's premises, from check 1.** -/
theorem classOccWF_of_infos {ks : List ClassKey} {cls : List ClassInfo}
    (hD : ClassInfosD ops env ctx holes ctorsAs 0 ks cls)
    (hks : KeysScoped cls (ctx.hiAt 0 + nCont cls)) :
    ClassOccWF cls (ctx.hiAt 0 + nCont cls) where
  hole := by
    intro c hc h hh
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    have hm : c.member = none := by
      have := classInfosD_hole_isSome hD hc
      rw [hh] at this; simpa using this.symm
    obtain ⟨hty, hh', -⟩ := classInfosD_hole hD hi hm
    rw [hh] at hh'
    cases hh'
    exact ⟨_, hty, rfl, by have := nCont_take_lt hi hm; omega⟩
  dsE := by
    intro c hc hs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    have hm : c.member = none := by
      have := classInfosD_hole_isSome hD hc
      rw [hs] at this; simpa using this.symm
    obtain ⟨-, -, h, -⟩ := classInfosD_hole hD hi hm
    exact h
  len := by
    intro c hc hs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    have hm : c.member = none := by
      have := classInfosD_hole_isSome hD hc
      rw [hs] at this; simpa using this.symm
    obtain ⟨-, -, -, h, -⟩ := classInfosD_hole hD hi hm
    exact h
  keyScoped := hks
  nPc := by
    intro c hc c' hc' hs hs' hI
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc'
    have hm : c.member = none := by
      have := classInfosD_hole_isSome hD hc
      rw [hs] at this; simpa using this.symm
    have hm' : c'.member = none := by
      have := classInfosD_hole_isSome hD hc'
      rw [hs'] at this; simpa using this.symm
    obtain ⟨-, -, -, -, h1⟩ := classInfosD_hole hD hi hm
    obtain ⟨-, -, -, -, h2⟩ := classInfosD_hole hD hj hm'
    rw [hI, h2] at h1
    exact (Prod.mk.inj (Option.some.inj h1)).1.symm

/-! ## The keys' scoping -/

section Scope



/-- Replacing every free variable (all below `n`) by a term scoped at `d`
gives a term scoped at `d`. -/
theorem wscoped_replaceFVars {f : Nat → Option Expr} {n d : Nat}
    (hf : ∀ i, i < n → ∃ s, f i = some s ∧ Expr.WScoped d s) :
    ∀ e : Expr, Expr.fvarsBelow n e → Expr.WScoped d (e.replaceFVars f) := by
  intro e
  induction e with
  | fvar i ty =>
    intro h
    obtain ⟨s, hs, hw⟩ := hf i h
    simp only [Expr.replaceFVars, hs, Option.getD_some]
    exact hw
  | app a b iha ihb => intro h; simp only [Expr.replaceFVars, Expr.WScoped]; exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb => intro h; simp only [Expr.replaceFVars, Expr.WScoped]; exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h; simp only [Expr.replaceFVars, Expr.WScoped]; exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h; simp only [Expr.replaceFVars, Expr.WScoped]; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj sn i x ih => intro h; simp only [Expr.replaceFVars, Expr.WScoped]; exact ih h
  | _ => intro _; simp [Expr.replaceFVars, Expr.WScoped]

/-- Replacing free variables by bound-closed terms keeps a bound. -/
theorem looseBVars_replaceFVars {f : Nat → Option Expr}
    (hf : ∀ i s, f i = some s → s.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceFVars f).looseBVarsBounded k = true := by
  intro e
  induction e with
  | fvar i ty =>
    intro k _
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => simp [Expr.looseBVarsBounded]
    | some s => exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf i s hi)
  | app a b iha ihb =>
    intro k h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b iht ihv ihb =>
    intro k h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj sn i x ih => intro k h; exact ih k h
  | _ => intro k h; simpa [Expr.replaceFVars] using h

end Scope

/-! ## The defeq tier -/

/-- **An alias's hole is its target class's**, the target of its
inductive. -/
theorem classAliasOk_target {hi : Nat} {cls : List ClassInfo} {a : ClassAlias}
    (h : ConLeche.ClassAliasOk ops env hi cls a) :
    ∃ ci ∈ cls, ci.hole = some a.hole ∧ ci.key.ind = a.ind := by
  obtain ⟨ci, hci, -, hI, -, hh, -⟩ := h
  exact ⟨ci, hci, hh, hI⟩

/-- **The alias recogniser's premises, from the defeq tier**: an alias's
hole is its target class's (below the frame), its parameters as many as
the target's parameter count; the alias keys' scoping is a premise. -/
theorem aliasWF_of_run {hi H : Nat} {cls : List ClassInfo} (hwf : ClassOccWF cls H)
    {al : List ClassAlias} (hal : ∀ a ∈ al, ConLeche.ClassAliasOk ops env hi cls a)
    (hks : ∀ a ∈ al, Expr.WScoped H (aliasKey a) ∧ (aliasKey a).looseBVarsBounded 0 = true) :
    AliasWF al H where
  hole := by
    intro a ha
    obtain ⟨ci, hci, -, -, -, hh, -⟩ := hal a ha
    obtain ⟨i, ty, he, hlt⟩ := hwf.hole ci hci a.hole hh
    exact ⟨i, ty, he, hlt⟩
  len := by
    intro a ha
    obtain ⟨ci, hci, ps, -, hN, hh, -, hps, hdef⟩ := hal a ha
    have hs : ci.hole.isSome := by rw [hh]; rfl
    obtain ⟨hl, -⟩ := ConLeche.classParamsDefEq_true hdef
    rw [hps, List.length_map, hl, ← hN]
    simp [ConLeche.ClassInfo.holeForm, hwf.len ci hci hs]
  keyScoped := hks

/-! ## At the run -/

section Run

open ConLeche (ClassRun classCtxOf classHi classAge classMates FEnv BlockParts ConstantInfo
  TargetMajor ClassCtor)

variable {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts} {block : List ConstantInfo}
  {cvTas : List ConstantVal} {out : List (ConstantVal × TargetMajor × List Expr)}
  {ctors : List (List ClassCtor)}

/-- A hole names one class, at the run. -/
theorem classRun_holesUniq (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors) :
    HolesUniq R.cls :=
  classInfosD_holesUniq R.hcls

/-- The recogniser's premises at the run (the keys' scoping a premise). -/
theorem classRun_classOccWF (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors)
    (hks : KeysScoped R.cls (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls)) :
    ClassOccWF R.cls (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls) :=
  classOccWF_of_infos R.hcls hks

/-- **At the run, a container class's crest's defeq tier keeps no hole**
of its class fact. -/
theorem classRun_aliases_notKept (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors)
    {c : ClassInfo} (hc : c.member = none) :
    ∀ a ∈ ConLeche.classAliasesFor (classAge fe₁) (classMates fe₁) c R.al,
      classKept (classAge fe₁) (classMates fe₁) R.cls c a.hole = false :=
  classAliasesFor_notKept (classRun_holesUniq R) hc fun a ha => classAliasOk_target (R.hal a ha)

end Run

end ConLeche.Model
