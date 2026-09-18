module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.FrontDoor
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.Inductives.NestedRestoreKit

public section

/-!
# The auxiliary recursors, read back (task #315 M7)

The nested route installs its auxiliary block with the MUTUAL
installer at the `auxRoute` grade and then reads the stored members
back out of the scratch environment (`auxStored?`).  `NestedAuxInv`
does this for the FORMERS and the CONSTRUCTORS; this module does it
for the **recursors**:

* the pre-annotated front door, restated keeping every guard AND the
  `inferTypeCore`/`ensureSortCore` run it made (`checkConstantValPre_shape`),
  and the restore's recursor types read positionally through it
  (`restoreRecTys_at`);
* the read-back's recursor record (`auxStored?_rec`), which the
  recursors' store put there (`storeMutualRecs_find?_recInfo`) and the
  projection tables carried through untouched
  (`mutualTables_find?_recInfo`, `mutualTables_find?_recInfo_inv`);
* hence **the auxiliary recursor IS the scratch install's generated
  one** (`auxStored_rec_eq`): its name `b.recName mIdx`, its level
  parameters `b.rlps`, and its type `mutualRecTy` at the formers' and
  constructors' stages' own data;
* and that generated type is a syntactic `∀`-telescope of
  `nP + k + n + nIdx + 1` binders, every binder carrying the
  elimination datum, over the conclusion `motive_m ı⃗ t`
  (`mutualRecTy_stripPis`) — a spine of bound variables, mentioning no
  constant;
* and the same at the **projection table** (task #315 M7-2): the
  read-back's `tbl` field (`auxStored?_tbl`) is what the scratch
  install's table stage consed at that member
  (`mutualTables_find?_projInfo_inv`, the stage's own fold), hence
  `auxStored_tbl_eq` — the nested route RE-USES that table, so its
  constructor, its offset `1` and its guards are the scratch stage's
  data and not a record the nested route checked.
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## The pre-annotated front door, in full -/

/-- The pre-annotated front door, in full: every guard, and the sort
inference it ran. -/
theorem checkConstantValPre_shape {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cvA = cv ∧ env.find? cv.name = none ∧ Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧ cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧ cv.type.constsResolve env = true ∧
    cv.type.projTablesOk env = true ∧
    ∃ (sty : Expr) (u : Level), inferTypeCore mode env F 0 cv.type = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u := by
  obtain ⟨rfl, hproj⟩ := checkConstantValPre_inv h
  have hd := FrontDoorFacts.ofPre h
  exact ⟨rfl, hd.fresh, hd.nodup, hd.bounded, hd.noFvar, by rw [← hd.lps]; exact hd.lpsOk,
    hd.resolve, hproj, hd.infer⟩

/-! ## The restored recursor types, positionally -/

/-- The restored recursor at position `i`: its level parameters are the
auxiliary's, its type is the restore of the auxiliary's, and the
pre-annotated door's guards and sort inference ran on it. -/
theorem restoreRecTys_at {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      ∀ (i : Nat) (a : AuxStored) (o : ConstantVal), as[i]? = some a → out[i]? = some o →
        o.levelParams = a.cvRa.levelParams ∧ restoreNested R a.cvRa.type = .ok o.type ∧
        o.type.looseBVarsBounded 0 = true ∧ o.type.hasFvar = false ∧
        o.type.allLevelParamsDefined o.levelParams = true ∧ o.type.constsResolve env = true ∧
        ∃ (sty : Expr) (u : Level), inferTypeCore mode env F 0 o.type = .ok sty ∧
          ensureSortCore mode env F 0 sty = .ok u := by
  intro names as
  induction as generalizing names with
  | nil =>
    intro out h i a o ha _
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    exact absurd ha (by simp)
  | cons a rest ih =>
    intro out h i a' o ha ho
    unfold restoreRecTys at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    have hty' := nestedLift_ok hty
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ho
      obtain rfl := ha
      obtain rfl := ho
      obtain ⟨hcv, -, -, hb, hfv, hlp, hres, -, hinf⟩ := checkConstantValPre_shape hpre
      rw [hcv]
      exact ⟨rfl, hty', hb, hfv, hlp, hres, hinf⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at ha ho
      exact ih hrest k a' o ha ho

/-- **THE RESTORED RECURSOR TYPES' PROJECTION SLOTS** (task #315 M7-2):
every `.proj` node of a restored recursor type sits at a table the
environment stores.

`restoreRecTys_at` reports the front door's scope guards and its sort
inference and DROPS this one, and the resolution predicate cannot
replace it: `constsResolve`'s `.proj s _ e` clause only asks that `s`
be stored, and at the restored environment every MEMBER is.  The
pre-annotated door checked the stronger guard (`projTablesOk`, K.13)
and `FrontDoorFacts.slots` is it as a proposition, so the report is
this projection of the same witness — the shape `restoreCtors_door`
already hands the constructors' side.

Consumer: the projection tables' face, through `NoProjEnv` at the
restored recursors' store. -/
theorem restoreRecTys_slots {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      ∀ (i : Nat) (o : ConstantVal), out[i]? = some o → Expr.ProjSlotsOk env o.type := by
  intro names as
  induction as generalizing names with
  | nil =>
    intro out h i o ho
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho
    exact absurd ho (by simp)
  | cons a rest ih =>
    intro out h i o ho
    unfold restoreRecTys at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
      obtain rfl := ho
      exact (FrontDoorFacts.ofPre hpre).slots
    | succ k =>
      simp only [List.getElem?_cons_succ] at ho
      exact ih hrest k o ho

/-! ## The read-back's recursor record -/

/-- The read-back's recursor: the scratch environment's `recInfo` at
the member's `.rec` name. -/
theorem auxStored?_rec {envAux : Env} {b : MutualBlock} {mIdx : Nat} {a : AuxStored}
    (h : auxStored? envAux b mIdx = some a) :
    ∃ cv : ConstantVal, b.formers[mIdx]? = some (cv, a.nIdx) ∧
      envAux.find? (cv.name.str "rec") = some (.recInfo a.cvRa a.mI a.rP a.rules) := by
  unfold auxStored? at h
  cases hfm : b.formers[mIdx]? with
  | none => rw [hfm] at h; exact absurd h (by simp [bind, Option.bind])
  | some p =>
    obtain ⟨cv, nIdx⟩ := p
    rw [hfm] at h
    simp only [bind, Option.bind] at h
    cases hfi : envAux.find? cv.name with
    | none => rw [hfi] at h; exact absurd h (by simp)
    | some ci =>
      rw [hfi] at h
      cases ci with
      | indInfo cvTa caps =>
        simp only [] at h
        cases hfr : envAux.find? (cv.name.str "rec") with
        | none => rw [hfr] at h; exact absurd h (by simp)
        | some cir =>
          rw [hfr] at h
          cases cir with
          | recInfo cvRa mI rP rules =>
            simp only [] at h
            split at h
            · exact absurd h (by simp)
            · simp only [pure, Option.some.injEq] at h
              obtain rfl := h
              exact ⟨cv, rfl, hfr⟩
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)

/-! ## The recursors' store, and the tables over it -/

/-- The recursors' store leaves every name it does not cons alone. -/
theorem storeMutualRecs_find?_of_ne {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {n : Name},
      (∀ p ∈ l, p.1.name ≠ n) →
      (storeMutualRecs env₂ b fms rulesOf l env).find? n = env.find? n := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons hd rest ih =>
    intro env n hne
    obtain ⟨cvRa, mIdx⟩ := hd
    show (storeMutualRecs env₂ b fms rulesOf rest ⟨_ :: env.consts⟩).find? n = _
    rw [ih (fun p hp => hne p (List.mem_cons_of_mem _ hp)), Env.find?_cons]
    exact if_neg (hne (cvRa, mIdx) List.mem_cons_self)

/-- `storeMutualRecs` conses one `recInfo` per entry; at pairwise
distinct names the record found under an entry's name is that entry's. -/
theorem storeMutualRecs_find?_recInfo {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ (l : List (ConstantVal × Nat)) {env : Env},
      (l.map (·.1.name)).Nodup →
      ∀ (cvRa : ConstantVal) (mIdx : Nat), (cvRa, mIdx) ∈ l →
        (storeMutualRecs env₂ b fms rulesOf l env).find? cvRa.name
          = some (.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
              (mutualRules env₂.find? cvRa.name b.nP (b.rulePrefix + (fms.getD mIdx default).nIdx)
                b.rulePrefix cvRa.type (rulesOf.getD mIdx []))) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ hmem; exact absurd hmem (by simp)
  | cons hd rest ih =>
    intro env hnd cvRa mIdx hmem
    obtain ⟨cvRa₀, mIdx₀⟩ := hd
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      show (storeMutualRecs env₂ b fms rulesOf rest ⟨_ :: env.consts⟩).find? cvRa.name = _
      rw [storeMutualRecs_find?_of_ne rest (fun p hp hn =>
        hnd.1 (by rw [← hn]; exact List.mem_map_of_mem hp))]
      exact Env.find?_cons_self _ _
    · show (storeMutualRecs env₂ b fms rulesOf rest ⟨_ :: env.consts⟩).find? cvRa.name = _
      exact ih hnd.2 cvRa mIdx hmem

/-- The projection tables keep a `recInfo` answer: a table is consed at
a name the stage's own guard found free. -/
theorem mutualTables_find?_recInfo {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) {env env' : Env} {n : Name} {cv : ConstantVal}
      {mI rP : Nat} {rules : List RecRule},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      env.find? n = some (.recInfo cv mI rP rules) →
      env'.find? n = some (.recInfo cv mI rP rules) := by
  intro l
  induction l with
  | nil =>
    intro env env' n cv mI rP rules h hf
    obtain rfl := mutualTables_nil_inv h
    exact hf
  | cons hd rest ih =>
    intro env env' n cv mI rP rules h hf
    obtain ⟨f, mIdx⟩ := hd
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    refine ih hrest ?_
    rcases mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact hf
    · obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := checkStructProjTable_inv htbl
      exact Env.find?_cons_of_fresh hfresh hf

/-- The projection tables cons only `projInfo`s, so a `recInfo` answer
at their output was already at their input. -/
theorem mutualTables_find?_recInfo_inv {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) {env env' : Env} {n : Name} {cv : ConstantVal}
      {mI rP : Nat} {rules : List RecRule},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      env'.find? n = some (.recInfo cv mI rP rules) →
      env.find? n = some (.recInfo cv mI rP rules) := by
  intro l
  induction l with
  | nil =>
    intro env env' n cv mI rP rules h hf
    obtain rfl := mutualTables_nil_inv h
    exact hf
  | cons hd rest ih =>
    intro env env' n cv mI rP rules h hf
    obtain ⟨f, mIdx⟩ := hd
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    have hfI := ih hrest hf
    rcases mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact hfI
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := checkStructProjTable_inv htbl
      rw [Env.find?_cons] at hfI
      split at hfI
      · exact nomatch hfI
      · exact hfI

/-! ## The generated recursor type's syntactic telescope -/

/-- A successful `replacePisPw` strips: the source has the `k`
binders. -/
theorem replacePisPw_some_stripPis {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr}, Expr.replacePisPw pw k e b = some r →
      ∃ (bs : List (Expr × BinderMeta)) (body : Expr), e.stripPis k = some (bs, body) := by
  intro k
  induction k with
  | zero => intro e _ _ _; exact ⟨[], e, rfl⟩
  | succ k ih =>
    intro e b r h
    match e, h with
    | .forallE ty rest mb, h =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', -⟩ := h
      obtain ⟨bs, body, hbs⟩ := ih hr'
      exact ⟨(ty, mb) :: bs, body, by simp only [Expr.stripPis, hbs, Option.map_some]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.replacePisPw] at h

/-- The motives' telescope's two steps, by `rfl`.  NOT `simp only
[mutualMotivesPis]`: unfolding through the equation lemmas realizes
`mutualMotivesPis.match_1.splitter` HERE, and this module sits below
every capstone in the import order, so the splitter's attribution moves
into it and the proof-term gate reads a door. -/
private theorem doorMotivesPis_nil {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {i : Nat} {body : Expr} : mutualMotivesPis lps nP ℓ pw [] i body = some body := rfl

private theorem doorMotivesPis_cons {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {f : MutualFormer} {fs : List MutualFormer} {i : Nat} {body : Expr} :
    mutualMotivesPis lps nP ℓ pw (f :: fs) i body
      = (mutualMotiveTy lps nP ℓ i f).bind fun mty =>
          (mutualMotivesPis lps nP ℓ pw fs (i + 1) body).map fun rest =>
            Expr.forallE mty rest ⟨pw⟩ := rfl

/-- The minors' telescope's two steps, by `rfl` (same reason). -/
private theorem doorMinorsPis_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body : Expr} : mutualMinorsPis lps nP pw [] o body = some body := rfl

private theorem doorMinorsPis_cons {lps : List Name} {nP : Nat} {pw : PropWhen}
    {c : MutualCtor4} {cs : List MutualCtor4} {o : Nat} {body : Expr} :
    mutualMinorsPis lps nP pw (c :: cs) o body
      = (mutualMinorTy lps nP o pw c).bind fun mty =>
          (mutualMinorsPis lps nP pw cs (o + 1) body).map fun rest =>
            Expr.forallE mty rest ⟨pw⟩ := rfl

/-- The motives' telescope: one `∀` per former, meta `⟨pw⟩`, the body
under them. -/
theorem mutualMotivesPis_stripPis {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} :
    ∀ (fs : List MutualFormer) {i : Nat} {body mots : Expr},
      mutualMotivesPis lps nP ℓ pw fs i body = some mots →
      ∃ bs : List (Expr × BinderMeta), mots.stripPis fs.length = some (bs, body) ∧
        ∀ x ∈ bs, x.2 = (⟨pw⟩ : BinderMeta) := by
  intro fs
  induction fs with
  | nil =>
    intro i body mots h
    rw [doorMotivesPis_nil, Option.some.injEq] at h
    exact ⟨[], by rw [← h]; rfl, by simp⟩
  | cons f fs ih =>
    intro i body mots h
    rw [doorMotivesPis_cons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, rest, hrest, rfl⟩ := h
    obtain ⟨bs, hbs, hmeta⟩ := ih hrest
    refine ⟨(mty, ⟨pw⟩) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, Expr.stripPis, hbs, Option.map_some]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hmeta x hx

/-- The minors' telescope: one `∀` per constructor, meta `⟨pw⟩`, the
body under them. -/
theorem mutualMinorsPis_stripPis {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ (cs : List MutualCtor4) {o : Nat} {body mins : Expr},
      mutualMinorsPis lps nP pw cs o body = some mins →
      ∃ bs : List (Expr × BinderMeta), mins.stripPis cs.length = some (bs, body) ∧
        ∀ x ∈ bs, x.2 = (⟨pw⟩ : BinderMeta) := by
  intro cs
  induction cs with
  | nil =>
    intro o body mins h
    rw [doorMinorsPis_nil, Option.some.injEq] at h
    exact ⟨[], by rw [← h]; rfl, by simp⟩
  | cons c cs ih =>
    intro o body mins h
    rw [doorMinorsPis_cons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, rest, hrest, rfl⟩ := h
    obtain ⟨bs, hbs, hmeta⟩ := ih hrest
    refine ⟨(mty, ⟨pw⟩) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, Expr.stripPis, hbs, Option.map_some]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hmeta x hx

/-- A spine mentions a constant only through its head or an argument
(the Verify copy of the Model tier's `mentionsConst_mkAppN_false`). -/
private theorem doorMentionsConst_mkAppN_false {n : Name} :
    ∀ (as : List Expr) (f : Expr), f.mentionsConst n = false →
      (∀ a ∈ as, a.mentionsConst n = false) → (Expr.mkAppN f as).mentionsConst n = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, has =>
    doorMentionsConst_mkAppN_false as (.app f a)
      (by simp only [Expr.mentionsConst, hf, has a List.mem_cons_self, Bool.or_self])
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

/-- **THE MAJOR PREMISE'S DOMAIN IS AN APPLICATION OF A CONSTANT**
(task #315, the crossing's premise): the generated recursor type of
member `mm`, stripped at its MAJOR INDEX — one binder short of
`mutualRecTy_stripPis`' strip — exposes the major premise itself, and
its domain is the member's own family application, whose head is a
`const`.

This is the unconditional form: no rule, no fire, no `.nested` guard —
the shape holds of the type the route GENERATES, and the stream's
record is only required to be defeq to it, so what is STORED is this
term.  `structFamI` is the family at the parameter and index openers,
so the head is `.const f.name (lps.map .param)` by construction. -/
theorem mutualRecTy_majorDom {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (bs : List (Expr × BinderMeta)) (dom body : Expr) (bm : BinderMeta),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx)
        = some (bs, .forallE dom body bm) ∧
      dom.getAppFn = .const f.name (lps.map .param) := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    obtain ⟨bs2, hbs2, -⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h2
    obtain ⟨bs3, hbs3, -⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + f.nIdx))
      = nP + formers.length + ctors.length + f.nIdx from by omega] at h8
    refine ⟨f, _, _, _, _, hf, h8, ?_⟩
    rw [structFamI, Expr.getAppFn_mkAppN]
    rfl
  · exact nomatch h

/-- **The generated recursor type of member `mm` is a syntactic
`∀`-telescope** of `nP + k + n + nIdx_m + 1` binders, every binder meta
the elimination datum, whose residual is the conclusion `motive_m ı⃗ t`
— an application of bound variables, mentioning no constant. -/
theorem mutualRecTy_stripPis {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (cbs : List (Expr × BinderMeta)),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx + 1)
        = some (cbs, Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
            (structPsAt 1 f.nIdx ++ [.bvar 0])) ∧
      (∀ x ∈ cbs, x.2 = (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)) ∧
      ∀ n : Name, (Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
        (structPsAt 1 f.nIdx ++ [.bvar 0])).mentionsConst n = false := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    -- the index telescope and the major, under the `f.nIdx + 1` binders
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    have h4 := stripPis_append f.nIdx h2 (m := 1) rfl
    -- the minors, then the motives
    obtain ⟨bs2, hbs2, hm2⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h4
    obtain ⟨bs3, hbs3, hm3⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    -- the parameters
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + (f.nIdx + 1)))
      = nP + formers.length + ctors.length + f.nIdx + 1 from by omega] at h8
    refine ⟨f, _, hf, h8, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
      rcases List.mem_append.mp hx with hx | hx
      · exact hm3 x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hm2 x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
      · rw [List.mem_singleton.mp hx]
    · intro n
      refine doorMentionsConst_mkAppN_false _ _ rfl ?_
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; rfl
      · rw [List.mem_singleton.mp ha]; rfl
  · exact nomatch h

/-- **THE GENERATED RECURSOR TYPE'S MAJOR BINDER, SYNTACTICALLY**
(task #315 M7-2): `mutualRecTy_stripPis` with the LAST binder named.
The telescope's binder `nP + k + n + nIdx_m` — the one the major
premise occupies — carries the domain `structFamI`, member `m`'s own
former applied to the block's parameters and the index binders, and
the elimination datum like every other.  The mimic recursors' fire
shape reads THIS binder through the restore, which is why it has to be
named. -/
theorem mutualRecTy_major {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (cbs₀ : List (Expr × BinderMeta)) (conc : Expr),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx + 1)
        = some (cbs₀ ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))], conc) ∧
      cbs₀.length = nP + formers.length + ctors.length + f.nIdx := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    have h4 := stripPis_append f.nIdx h2 (m := 1) rfl
    obtain ⟨bs2, hbs2, -⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h4
    obtain ⟨bs3, hbs3, -⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + (f.nIdx + 1)))
      = nP + formers.length + ctors.length + f.nIdx + 1 from by omega] at h8
    refine ⟨f, (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
        BinderMeta))) ++ (bs3 ++ (bs2 ++ (bs1.map fun x => (x.1,
          (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))))),
      Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
        (structPsAt 1 f.nIdx ++ [.bvar 0]), hf, ?_, ?_⟩
    · rw [show (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))) ++ (bs3 ++ (bs2 ++ (bs1.map fun x => (x.1,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)))))
          ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))]
        = (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
            BinderMeta))) ++ (bs3 ++ (bs2 ++ ((bs1.map fun x => (x.1,
              (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)))
            ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
              (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))]))) from by
          simp only [List.append_assoc]]
      exact h8
    · have e0 : (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))).length = nP := by
        rw [List.length_map]
        exact Expr.stripPis_length _ hbs0
      have e1 : (bs1.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))).length = f.nIdx := by
        rw [List.length_map]
        exact Expr.stripPis_length _ hbs1
      have e2 : bs2.length = ctors.length := Expr.stripPis_length _ hbs2
      have e3 : bs3.length = formers.length := Expr.stripPis_length _ hbs3
      simp only [List.length_append, e0, e1, e2, e3]
      omega
  · exact nomatch h

/-! ## The restore walk, per binder -/

/-- **The restore walk's telescope, per binder**: the walk of a
`∀`-telescope is the telescope of the walks — binder `i`'s domain is
the walk of the source's at depth `d + i`, its binder meta unchanged,
and the walk of the body is the body of the walk.
`rk_restoreWalk_stripPis` with the DOMAINS named. -/
theorem restoreWalk_stripPis_doms {R : RestoreTbl} :
    ∀ (n : Nat) {d : Nat} {e e' : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      restoreWalk R d e = .ok e' → e.stripPis n = some (bs, body) →
      ∃ (bs' : List (Expr × BinderMeta)) (body' : Expr),
        e'.stripPis n = some (bs', body') ∧ restoreWalk R (d + n) body = .ok body' ∧
          bs'.length = bs.length ∧ bs'.map (·.2) = bs.map (·.2) ∧
          ∀ (i : Nat) (x : Expr × BinderMeta), bs[i]? = some x →
            ∃ y : Expr × BinderMeta, bs'[i]? = some y ∧ restoreWalk R (d + i) x.1 = .ok y.1 := by
  intro n
  induction n with
  | zero =>
    intro d e e' bs body hw hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨[], e', rfl, hw, rfl, rfl, fun i x hx => by simp at hx⟩
  | succ n ih =>
    intro d e e' bs body hw hs
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at hs
      cases hb : b.stripPis n with
      | none => rw [hb] at hs; exact nomatch hs
      | some pr =>
        obtain ⟨bs₀, body₀⟩ := pr
        rw [hb] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ty', b', hty, hbw, rfl⟩ := restoreWalk_forallE_inv hw
        obtain ⟨bs', body', hs', hw', hlen, hmeta, hdom⟩ := ih hbw hb
        refine ⟨(ty', bm) :: bs', body', ?_, ?_, ?_, ?_, ?_⟩
        · rw [Expr.stripPis, hs']; rfl
        · rw [show d + (n + 1) = d + 1 + n by omega]; exact hw'
        · simp only [List.length_cons, hlen]
        · simp only [List.map_cons, hmeta]
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            exact ⟨(ty', bm), rfl, by rw [Nat.add_zero, ← hx]; exact hty⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hx ⊢
            obtain ⟨y, hy, hwy⟩ := hdom i x hx
            exact ⟨y, hy, by rw [show d + (i + 1) = d + 1 + i by omega]; exact hwy⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch hs

/-- **The restored type's telescope, per binder**: below the parameter
prefix the domains are the source's verbatim (the restore strips them
untouched); above it binder `nP + i`'s domain is the walk of the
source's at depth `i`.  `rk_restoreNested_stripPis` with the DOMAINS
named. -/
theorem restoreNested_stripPis_doms {R : RestoreTbl} {nP nF : Nat} (hnP : R.nP = nP)
    {tyA tyR : Expr} {cbs : List (Expr × BinderMeta)} {resid : Expr}
    (hstrip : tyA.stripPis (nP + nF) = some (cbs, resid))
    (hres : restoreNested R tyA = .ok tyR)
    (hfree : ∀ n ∈ R.auxNames, resid.mentionsConst n = false) :
    ∃ cbs' : List (Expr × BinderMeta), tyR.stripPis (nP + nF) = some (cbs', resid) ∧
      cbs'.length = cbs.length ∧ cbs'.map (·.2) = cbs.map (·.2) ∧
      (∀ i, i < nP → cbs'[i]? = cbs[i]?) ∧
      ∀ (i : Nat) (x : Expr × BinderMeta), cbs[nP + i]? = some x →
        ∃ y : Expr × BinderMeta, cbs'[nP + i]? = some y ∧ restoreWalk R i x.1 = .ok y.1 := by
  obtain ⟨mid, h1, h2⟩ := rk_stripPis_split nP nF hstrip
  have hcl : cbs.length = nP + nF := stripPis_length _ hstrip
  have htk : (cbs.take nP).length = nP := by rw [List.length_take, hcl]; omega
  have hs : tyA.stripPis R.nP = some (cbs.take nP, mid) := by rw [hnP]; exact h1
  have hpi : 0 < R.nP → ∃ ty b bm, tyA = Expr.forallE ty b bm := by
    intro hlt
    rw [hnP] at hlt
    obtain ⟨j, rfl⟩ : ∃ j, nP = j + 1 := ⟨nP - 1, by omega⟩
    cases tyA with
    | forallE ty b bm => exact ⟨ty, b, bm, rfl⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h1
  obtain ⟨body', hw, rfl⟩ := restoreNested_pis hs hpi hres
  obtain ⟨bs', body'', hsb, hw', hlen', hmeta, hdom⟩ := restoreWalk_stripPis_doms nF hw h2
  have hresid : restoreWalk R (0 + nF) resid = .ok resid :=
    restoreWalk_of_no_aux (0 + nF) resid hfree
  obtain rfl : body'' = resid := Except.ok.inj (hw'.symm.trans hresid)
  rw [mkPisB_eq_foldr]
  have hlenD : (cbs.drop nP).length = nF := by rw [List.length_drop, hcl]; omega
  refine ⟨cbs.take nP ++ bs', stripPis_append nP ?_ hsb, ?_, ?_, ?_, ?_⟩
  · have hmk := rk_mkPisB_stripPis (cbs.take nP) body'
    rw [htk] at hmk
    exact hmk
  · rw [List.length_append, htk, hlen', hlenD, hcl]
  · rw [List.map_append, hmeta, ← List.map_append, List.take_append_drop]
  · intro i hi
    rw [List.getElem?_append_left (by rw [htk]; exact hi), List.getElem?_take_of_lt hi]
  · intro i x hx
    have hx' : (cbs.drop nP)[i]? = some x := by rw [List.getElem?_drop]; exact hx
    obtain ⟨y, hy, hwy⟩ := hdom i x hx'
    refine ⟨y, ?_, by rw [Nat.zero_add] at hwy; exact hwy⟩
    rw [List.getElem?_append_right (by rw [htk]; omega), htk,
      show nP + i - nP = i from by omega]
    exact hy

/-- **An auxiliary-free binder is its own restoration**: at a domain
mentioning no auxiliary name the walk is the identity, so the restored
telescope carries the source's domain verbatim. -/
theorem restoreWalk_dom_id {R : RestoreTbl} {i : Nat} {x y : Expr}
    (hy : restoreWalk R i x = .ok y)
    (hfree : ∀ n ∈ R.auxNames, x.mentionsConst n = false) : y = x :=
  Except.ok.inj (hy.symm.trans (restoreWalk_of_no_aux i x hfree))

/-! ## The auxiliary recursor IS the scratch install's generated one -/

/-- The read-back's recursor at member `mIdx` is the scratch install's
generated recursor: its name `b.recName mIdx`, level parameters
`b.rlps`, its type `mutualRecTy` at the scratch formers'/constructors'
data, closed, fvar-free, resolving at the scratch constructors'
environment and with its level parameters defined. -/
theorem auxStored_rec_eq {env envAux : Env} {b : MutualBlock} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {stored : List AuxStored} (hst : auxStoredAll envAux b b.k = some stored)
    {mIdx : Nat} {a : AuxStored} (ha : stored[mIdx]? = some a) :
    a.cvRa.name = b.recName mIdx ∧ a.cvRa.levelParams = b.rlps ∧
    ∃ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat))),
      mutualFormers (fueledOps mode F) b.nP b.formers env true
        = .ok (consMutualFormers fms env, fms) ∧
      fms[0]? = some f₀ ∧
      checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms
        (Level.isEquiv f₀.s .zero == some true) true b.ctors = .ok (ctorsA, sortss) ∧
      classifyMutualKinds (m := CheckM) b.members3 b.lps b.nP ctorsA = .ok kinds ∧
      mutualRecTy b.lps b.elim b.large b.nP (mutualGenData b fms ctorsA kinds).1
        (mutualGenData b fms ctorsA kinds).2 mIdx = some a.cvRa.type ∧
      a.cvRa.type.allLevelParamsDefined b.rlps = true ∧
      a.cvRa.type.constsResolve (consMutualCtors b.nP ctorsA (consMutualFormers fms env)) = true ∧
      a.cvRa.type.looseBVarsBounded 0 = true ∧ a.cvRa.type.hasFvar = false := by
  obtain ⟨hnd0, -, -, -, env₁, fms, f₀, _tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas,
    rulesOf, hformers, hf₀, -, -, -, hctors, hkinds, -, hgd, hrectys, -, htables, -⟩ :=
    checkMutualCore_inv h
  obtain ⟨-, rfl⟩ := mutualFormers_inv hformers
  obtain ⟨hlenR, hallR⟩ := checkMutualRecTys_inv hrectys
  -- every generated recursor constant, positionally
  have hshape : ∀ t, t < b.k → ∃ (cvRa : ConstantVal) (recTy : Expr), cvRas[t]? = some cvRa ∧
      cvRa = ⟨b.recName t, b.rlps, recTy⟩ ∧
      mutualRecTy b.lps b.elim b.large b.nP formers4 ctors4 t = some recTy ∧
      recTy.allLevelParamsDefined b.rlps = true ∧
      recTy.constsResolve (consMutualCtors b.nP ctorsA (consMutualFormers fms env)) = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false := by
    intro t ht
    obtain ⟨cvRa, hget, hrun⟩ := hallR t ht
    obtain ⟨recTy, _sty, _u, hrt, hlp, hres, hbv, hfv, -, -, -, hcv⟩ :=
      checkMutualRecTy_shape hrun
    exact ⟨cvRa, recTy, hget, hcv, hrt, hlp, hres, hbv, hfv⟩
  -- the generated names are pairwise distinct: they are the block's own recursor names
  have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map, List.getElem?_map]
    by_cases ht : t < b.k
    · obtain ⟨cvRa, recTy, hget, hcv, -, -, -, -, -⟩ := hshape t ht
      rw [hget, List.getElem?_range ht]
      simp only [Option.map_some, Option.some.injEq]
      rw [hcv]
    · rw [List.getElem?_eq_none (by rw [hlenR]; omega),
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl
  have hndZ : ((cvRas.zipIdx).map (·.1.name)).Nodup := by
    rw [show (cvRas.zipIdx).map (fun x => x.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name)
            = (fun c : ConstantVal => c.name) ∘ Prod.fst from rfl,
        ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := hnd0
    unfold MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- the read-back at `mIdx`
  obtain ⟨hlenS, hgetS⟩ := auxStoredAll_get hst
  have hmk : mIdx < b.k := by
    have h1 := (List.getElem?_eq_some_iff.mp ha).1
    rw [hlenS] at h1
    exact h1
  obtain ⟨cv, hfm, hrec⟩ := auxStored?_rec (hgetS mIdx a ha)
  have hrn : b.recName mIdx = cv.name.str "rec" := by
    unfold MutualBlock.recName
    rw [List.getD_eq_getElem?_getD, hfm]
    rfl
  -- the answer travels back through the tables to the recursors' store
  have hstore := mutualTables_find?_recInfo_inv fms.zipIdx htables hrec
  obtain ⟨cvRa, recTy, hgetR, hcvR, hrt, hlp, hres, hbv, hfv⟩ := hshape mIdx hmk
  have hmem : (cvRa, mIdx) ∈ cvRas.zipIdx := by
    refine List.mem_of_getElem? (i := mIdx) ?_
    rw [List.getElem?_zipIdx, hgetR]
    simp
  have hfind := storeMutualRecs_find?_recInfo
    (env₂ := consMutualCtors b.nP ctorsA (consMutualFormers fms env)) (b := b) (fms := fms)
    (rulesOf := rulesOf) cvRas.zipIdx
    (env := consMutualCtors b.nP ctorsA (consMutualFormers fms env)) hndZ cvRa mIdx hmem
  have hname : cvRa.name = cv.name.str "rec" := by rw [hcvR, ← hrn]
  rw [hname, hstore, Option.some.injEq] at hfind
  have haq : a.cvRa = cvRa := (ConstantInfo.recInfo.inj hfind).1
  rw [haq, hcvR]
  refine ⟨rfl, rfl, fms, f₀, ctorsA, sortss, kinds, hformers, hf₀, hctors, hkinds, ?_,
    hlp, hres, hbv, hfv⟩
  rw [hgd]
  exact hrt

/-- **AND ITS RULES ARE THE SCRATCH INSTALL'S GENERATED ONES**
(`auxStored_rec_eq`'s twin at the RULES): the read-back's recursor
record carries the rule list the recursors' store consed there, which
is `mutualRules` of the member's own stage of `checkMutualAllRules`
(`storeMutualRecs_find?_recInfo` again, the projection tables carrying
the answer through, `mutualTables_find?_recInfo_inv`), together with
the two argument sums the store computed (`a.mI`, `a.rP`) and the
formers'/constructors'/kinds'/rules' runs, which the consumer
identifies with its own by determinism. -/
theorem auxStored_rules_eq {env envAux : Env} {b : MutualBlock} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {stored : List AuxStored} (hst : auxStoredAll envAux b b.k = some stored)
    {mIdx : Nat} {a : AuxStored} (ha : stored[mIdx]? = some a) :
    ∃ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (cvRas : List ConstantVal) (rulesOf : List (List (MutualCtor × Expr))),
      mutualFormers (fueledOps mode F) b.nP b.formers env true
        = .ok (consMutualFormers fms env, fms) ∧
      fms[0]? = some f₀ ∧
      checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms
        (Level.isEquiv f₀.s .zero == some true) true b.ctors = .ok (ctorsA, sortss) ∧
      classifyMutualKinds (m := CheckM) b.members3 b.lps b.nP ctorsA = .ok kinds ∧
      checkMutualAllRules (m := CheckM)
          (provisionMutualRecs b fms cvRas.zipIdx
            (consMutualCtors b.nP ctorsA (consMutualFormers fms env)))
          b (mutualGenData b fms ctorsA kinds).1 (mutualGenData b fms ctorsA kinds).2 none b.k
        = .ok rulesOf ∧
      a.mI = b.rulePrefix + (fms.getD mIdx default).nIdx ∧ a.rP = b.rulePrefix ∧
      a.rules = mutualRules
        (consMutualCtors b.nP ctorsA (consMutualFormers fms env)).find? a.cvRa.name b.nP
          a.mI a.rP a.cvRa.type (rulesOf.getD mIdx []) := by
  obtain ⟨hnd0, -, -, -, env₁, fms, f₀, _tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas,
    rulesOf, hformers, hf₀, -, -, -, hctors, hkinds, -, hgd, hrectys, hrules, htables, -⟩ :=
    checkMutualCore_inv h
  obtain ⟨-, rfl⟩ := mutualFormers_inv hformers
  obtain ⟨hlenR, hallR⟩ := checkMutualRecTys_inv hrectys
  -- the generated recursor constants' names, and their distinctness
  have hnames : ∀ t, t < b.k → ∃ cvRa : ConstantVal, cvRas[t]? = some cvRa ∧
      cvRa.name = b.recName t := by
    intro t ht
    obtain ⟨cvRa, hget, hrun⟩ := hallR t ht
    obtain ⟨recTy, _sty, _u, -, -, -, -, -, -, -, -, hcv⟩ := checkMutualRecTy_shape hrun
    exact ⟨cvRa, hget, by rw [hcv]⟩
  have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map, List.getElem?_map]
    by_cases ht : t < b.k
    · obtain ⟨cvRa, hget, hcv⟩ := hnames t ht
      rw [hget, List.getElem?_range ht]
      simp only [Option.map_some, Option.some.injEq]
      exact hcv
    · rw [List.getElem?_eq_none (by rw [hlenR]; omega),
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl
  have hndZ : ((cvRas.zipIdx).map (·.1.name)).Nodup := by
    rw [show (cvRas.zipIdx).map (fun x => x.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name)
            = (fun c : ConstantVal => c.name) ∘ Prod.fst from rfl,
        ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := hnd0
    unfold MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- the read-back at `mIdx`, and the record the store consed there
  obtain ⟨hlenS, hgetS⟩ := auxStoredAll_get hst
  have hmk : mIdx < b.k := by
    have h1 := (List.getElem?_eq_some_iff.mp ha).1
    rw [hlenS] at h1
    exact h1
  obtain ⟨cv, hfm, hrec⟩ := auxStored?_rec (hgetS mIdx a ha)
  have hrn : b.recName mIdx = cv.name.str "rec" := by
    unfold MutualBlock.recName
    rw [List.getD_eq_getElem?_getD, hfm]
    rfl
  have hstore := mutualTables_find?_recInfo_inv fms.zipIdx htables hrec
  obtain ⟨cvRa, hgetR, hcvn⟩ := hnames mIdx hmk
  have hmem : (cvRa, mIdx) ∈ cvRas.zipIdx := by
    refine List.mem_of_getElem? (i := mIdx) ?_
    rw [List.getElem?_zipIdx, hgetR]
    simp
  have hfind := storeMutualRecs_find?_recInfo
    (env₂ := consMutualCtors b.nP ctorsA (consMutualFormers fms env)) (b := b) (fms := fms)
    (rulesOf := rulesOf) cvRas.zipIdx
    (env := consMutualCtors b.nP ctorsA (consMutualFormers fms env)) hndZ cvRa mIdx hmem
  rw [show cvRa.name = cv.name.str "rec" from by rw [hcvn, ← hrn], hstore,
    Option.some.injEq] at hfind
  obtain ⟨haq, hmI, hrP, hrules'⟩ := ConstantInfo.recInfo.inj hfind
  refine ⟨fms, f₀, ctorsA, sortss, kinds, cvRas, rulesOf, hformers, hf₀, hctors, hkinds, ?_,
    hmI, hrP, ?_⟩
  · rw [hgd]; exact hrules
  · rw [hrules', haq, hmI, hrP, show cvRa.name = cv.name.str "rec" from by rw [hcvn, ← hrn]]


/-! ## The auxiliary member's PROJECTION TABLE, read back -/

/-- The formers' conses carry no projection table. -/
private theorem consMutualFormers_find?_projInfo :
    ∀ (l : List MutualFormerA) {env : Env} {n : Name} {tbl : ProjTable},
      (consMutualFormers l env).find? n = some (.projInfo tbl) →
      env.find? n = some (.projInfo tbl)
  | [], _, _, _, h => h
  | f :: rest, env, n, tbl, h => by
    have h' := consMutualFormers_find?_projInfo rest h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The constructors' conses carry no projection table. -/
private theorem consMutualCtors_find?_projInfo (nP : Nat) :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {n : Name} {tbl : ProjTable},
      (consMutualCtors nP l env).find? n = some (.projInfo tbl) →
      env.find? n = some (.projInfo tbl)
  | [], _, _, _, h => h
  | (cv, nF) :: rest, env, n, tbl, h => by
    have h' := consMutualCtors_find?_projInfo nP rest h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The recursors' store carries no projection table. -/
private theorem storeMutualRecs_find?_projInfo (env₂ : Env) (b : MutualBlock)
    (fms : List MutualFormerA) (rulesOf : List (List (MutualCtor × Expr))) :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {n : Name} {tbl : ProjTable},
      (storeMutualRecs env₂ b fms rulesOf l env).find? n = some (.projInfo tbl) →
      env.find? n = some (.projInfo tbl)
  | [], _, _, _, h => h
  | (cvRa, mIdx) :: rest, env, n, tbl, h => by
    have h' := storeMutualRecs_find?_projInfo env₂ b fms rulesOf rest h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- **The tables' stage conses a member's own table**: a `projInfo`
answer at the stage's output either stood at its input already or is
the table `mutualMemberTable` built at one of the members the stage
walked — its structure that member, its constructor the member's ONE
own constructor, its level parameters and parameter count the block's,
its result sort the member's, its offset `1` and its guards that
constructor's field sorts' `structProjGuards`. -/
theorem mutualTables_find?_projInfo_inv {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) {env env' : Env} {T : Name} {tbl : ProjTable},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      env'.find? (projTableName T) = some (.projInfo tbl) →
      env.find? (projTableName T) = some (.projInfo tbl) ∨
      ∃ (f : MutualFormerA) (mIdx J : Nat) (c : MutualCtor) (bodies : Array Expr),
        (f, mIdx) ∈ l ∧ f.cvTa.name = T ∧ b.ownCtors mIdx = [(J, c)] ∧ f.nIdx = 0 ∧
          structProjBodies T b.nP c.nF (ctorsA.getD J default).1.type = some bodies ∧
          tbl = ⟨T, b.lps, b.nP, c.cv.name, c.nF, f.s, bodies,
            structProjGuards (ctorsA.getD J default).1.type b.nP c.nF (sortss.getD J []), 1⟩ := by
  intro l
  induction l with
  | nil =>
    intro env env' T tbl h hf
    obtain rfl := mutualTables_nil_inv h
    exact Or.inl hf
  | cons hd rest ih =>
    intro env env' T tbl h hf
    obtain ⟨f, mIdx⟩ := hd
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    rcases ih hrest hf with hfI | ⟨f', mIdx', J, c, bodies, hmem, hname, hown, hnIdx, hbs, rfl⟩
    · rcases mutualMemberTable_inv hI with rfl | ⟨J, c, hown, hnIdx, htbl⟩
      · exact Or.inl hfI
      · obtain ⟨bodies, hbs, -, -, -, rfl⟩ := checkStructProjTable_inv htbl
        rw [Env.find?_cons] at hfI
        split at hfI
        · next heq =>
          obtain rfl : f.cvTa.name = T := projTableName_inj heq
          exact Or.inr ⟨f, mIdx, J, c, bodies, List.mem_cons_self .., rfl, hown, hnIdx, hbs,
            (ConstantInfo.projInfo.inj (Option.some.inj hfI)).symm⟩
        · exact Or.inl hfI
    · exact Or.inr ⟨f', mIdx', J, c, bodies, List.mem_cons_of_mem _ hmem, hname, hown, hnIdx,
        hbs, rfl⟩

/-- **The read-back at one member's projection table**: the record's
`tbl` field is the `projInfo` the scratch environment answers at the
member's `projTableName`. -/
theorem auxStored?_tbl {envAux : Env} {b : MutualBlock} {mIdx : Nat} {a : AuxStored}
    (h : auxStored? envAux b mIdx = some a) {tbl : ProjTable} (htbl : a.tbl = some tbl) :
    ∃ cv : ConstantVal, b.formers[mIdx]? = some (cv, a.nIdx) ∧
      envAux.find? (projTableName cv.name) = some (.projInfo tbl) := by
  unfold auxStored? at h
  cases hfm : b.formers[mIdx]? with
  | none => rw [hfm] at h; exact absurd h (by simp [bind, Option.bind])
  | some p =>
    obtain ⟨cv, nIdx⟩ := p
    rw [hfm] at h
    simp only [bind, Option.bind] at h
    cases hfi : envAux.find? cv.name with
    | none => rw [hfi] at h; exact absurd h (by simp)
    | some ci =>
      rw [hfi] at h
      cases ci with
      | indInfo cvTa caps =>
        simp only [] at h
        cases hfr : envAux.find? (cv.name.str "rec") with
        | none => rw [hfr] at h; exact absurd h (by simp)
        | some cir =>
          rw [hfr] at h
          cases cir with
          | recInfo cvRa mI rP rules =>
            simp only [] at h
            split at h
            · exact absurd h (by simp)
            · simp only [pure, Option.some.injEq] at h
              obtain rfl := h
              refine ⟨cv, rfl, ?_⟩
              simp only [] at htbl
              cases hpt : envAux.find? (projTableName cv.name) with
              | none => rw [hpt] at htbl; exact nomatch htbl
              | some cit =>
                rw [hpt] at htbl
                cases cit with
                | projInfo t =>
                  simp only [Option.some.injEq] at htbl
                  rw [htbl]
                | _ => exact nomatch htbl
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)

/-- **AND ITS PROJECTION TABLE IS THE SCRATCH INSTALL'S**
(`auxStored_rec_eq`'s twin at the TABLES): the read-back's `tbl` field
at member `mIdx` is what the scratch install's table stage
(`mutualMemberTable`) built there — the member's own structure, its ONE
own constructor, the block's level parameters and parameter count, the
member's result sort, the offset `1` and the guards
`structProjGuards` of that constructor's ANNOTATED type at the
constructor stage's field sorts.

The stage conses a table only at a STRUCTURE-LIKE member, so the
member's `ownCtors` is the singleton `[(J, c)]` and its index count is
`0`: a read-back table is the witness that the scratch member was
structure-like.

The left disjunct — the table stood at the PRE-BLOCK environment
already — is refuted by the nested route's own table stage, whose
`checkStructProjTable` found `projTableName` free at an environment
extending `env`; it is left to the consumer because the scratch
install's guard alone does not see `env`.

The member the stage walked is named by its own constant, not by its
position: `fms[t]? = some f` with `f.cvTa.name = cv.name`.  The
consumer identifies `t` with `mIdx` from the members' names being
distinct (`mutualMemberNames_eq`, the block record's `blockNames.Nodup`). -/
theorem auxStored_tbl_eq {env envAux : Env} {b : MutualBlock} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {stored : List AuxStored} (hst : auxStoredAll envAux b b.k = some stored)
    {mIdx : Nat} {a : AuxStored} (ha : stored[mIdx]? = some a)
    {tbl : ProjTable} (htbl : a.tbl = some tbl) :
    ∃ cv : ConstantVal, b.formers[mIdx]? = some (cv, a.nIdx) ∧
      (env.find? (projTableName cv.name) = some (.projInfo tbl) ∨
        ∃ (fms : List MutualFormerA) (f₀ f : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
          (sortss : List (List Level)) (t J : Nat) (c : MutualCtor) (bodies : Array Expr),
          mutualFormers (fueledOps mode F) b.nP b.formers env true
            = .ok (consMutualFormers fms env, fms) ∧
          fms[0]? = some f₀ ∧
          checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms
            (Level.isEquiv f₀.s .zero == some true) true b.ctors = .ok (ctorsA, sortss) ∧
          fms[t]? = some f ∧ f.cvTa.name = cv.name ∧
          b.ownCtors t = [(J, c)] ∧ f.nIdx = 0 ∧
          structProjBodies cv.name b.nP c.nF (ctorsA.getD J default).1.type = some bodies ∧
          tbl = ⟨cv.name, b.lps, b.nP, c.cv.name, c.nF, f.s, bodies,
            structProjGuards (ctorsA.getD J default).1.type b.nP c.nF (sortss.getD J []), 1⟩) := by
  obtain ⟨-, -, -, -, env₁, fms, f₀, _tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas,
    rulesOf, hformers, hf₀, -, -, -, hctors, -, -, -, -, -, htables, -⟩ := checkMutualCore_inv h
  obtain ⟨-, rfl⟩ := mutualFormers_inv hformers
  obtain ⟨-, hgetS⟩ := auxStoredAll_get hst
  obtain ⟨cv, hfm, hfind⟩ := auxStored?_tbl (hgetS mIdx a ha) htbl
  refine ⟨cv, hfm, ?_⟩
  rcases mutualTables_find?_projInfo_inv fms.zipIdx htables hfind with
    hleft | ⟨f, t, J, c, bodies, hmem, hname, hown, hnIdx, hbs, rfl⟩
  · exact Or.inl (consMutualFormers_find?_projInfo fms
      (consMutualCtors_find?_projInfo b.nP ctorsA
        (storeMutualRecs_find?_projInfo _ b fms rulesOf cvRas.zipIdx hleft)))
  · exact Or.inr ⟨fms, f₀, f, ctorsA, sortss, t, J, c, bodies, hformers, hf₀, hctors,
      List.mk_mem_zipIdx_iff_getElem?.mp hmem, hname, hown, hnIdx, hbs, rfl⟩

end ConLeche
