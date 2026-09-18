module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.FrontDoor
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.Inductives.FixRec
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
  constant.
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

/-- The recursive minors' telescope's two steps, by `rfl` (the reason is
`doorMinorsPis_nil`'s). -/
private theorem doorMinorsPisR_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body : Expr} : structMinorsPisR lps nP pw [] o body = some body := rfl

private theorem doorMinorsPisR_cons {lps : List Name} {nP : Nat} {pw : PropWhen}
    {c : Name × Nat × Expr × List Nat} {cs : List (Name × Nat × Expr × List Nat)}
    {o : Nat} {body : Expr} :
    structMinorsPisR lps nP pw (c :: cs) o body
      = (structMinorTyR c.1 lps nP c.2.1 o pw c.2.2.1 c.2.2.2).bind fun mty =>
          (structMinorsPisR lps nP pw cs (o + 1) body).map fun rest =>
            Expr.forallE mty rest ⟨pw⟩ := rfl

/-- The recursive minors' telescope: one `∀` per constructor, the body
under them. -/
theorem structMinorsPisR_stripPis {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ (cs : List (Name × Nat × Expr × List Nat)) {o : Nat} {body mins : Expr},
      structMinorsPisR lps nP pw cs o body = some mins →
      ∃ bs : List (Expr × BinderMeta), mins.stripPis cs.length = some (bs, body) := by
  intro cs
  induction cs with
  | nil =>
    intro o body mins h
    rw [doorMinorsPisR_nil, Option.some.injEq] at h
    exact ⟨[], by rw [← h]; rfl⟩
  | cons c cs ih =>
    intro o body mins h
    rw [doorMinorsPisR_cons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, rest, hrest, rfl⟩ := h
    obtain ⟨bs, hbs⟩ := ih hrest
    exact ⟨(mty, ⟨pw⟩) :: bs, by
      simp only [List.length_cons, Expr.stripPis, hbs, Option.map_some]⟩

/-- **THE FIXPOINT ROUTE'S MAJOR PREMISE IS AN APPLICATION OF A
CONSTANT** (task #315, the crossing's premise): `mutualRecTy_majorDom`'s
twin at `structRecTyR`, whose output is what `checkNativeRec` STORES
(the stream's record is only required to be defeq to it).  The strip is
the parameters, the motive, the minors and the indices — `majorIdx` —
and the domain exposed is `structFamI`'s family application. -/
theorem structRecTyR_majorDom {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr × List Nat)}
    (h : structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ (bs : List (Expr × BinderMeta)) (dom body : Expr) (bm : BinderMeta),
      recTy.stripPis (nP + 1 + ctors.length + nIdx)
        = some (bs, .forallE dom body bm) ∧
      dom.getAppFn = .const T (lps.map .param) := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hq, hmot, hmaj, hmin, hr⟩ :=
    structRecTyR_unfold h
  -- the indices, landing ON the major premise
  obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis nIdx hmaj
  have h2 := replacePisPw_stripPis nIdx hmaj hbs1
  -- the minors, the motive, the parameters
  obtain ⟨bs2, hbs2⟩ := structMinorsPisR_stripPis ctors hmin
  have h5 := stripPis_append ctors.length hbs2 h2
  have hmotive : (Expr.forallE motiveTy minors
      ⟨Level.zeronessOf (structElimLevel elim large)⟩).stripPis 1
        = some ([(motiveTy, ⟨Level.zeronessOf (structElimLevel elim large)⟩)], minors) := rfl
  have h6 := stripPis_append 1 hmotive h5
  obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
  have h7 := replacePisPw_stripPis nP hr hbs0
  have h8 := stripPis_append nP h7 h6
  rw [show nP + (1 + (ctors.length + nIdx)) = nP + 1 + ctors.length + nIdx from by omega] at h8
  refine ⟨_, _, _, _, h8, ?_⟩
  rw [structFamI, Expr.getAppFn_mkAppN]
  rfl

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

/-- **THE RESTORE KEEPS THE MAJOR PREMISE'S HEAD A CONSTANT** (task
#315, the crossing's premise at the NESTED route): the composition.
`restoreWalk_stripPis_doms` carries the `Π`-telescope positionally, so
the restored type strips at the same major index; `restoreWalk_forallE_inv`
exposes the restored major premise; and `restoreWalk_getAppFn_const`
keeps its domain's head a constant.

With `mutualRecTy_majorDom` on the AUXILIARY block's generated type as the
`hs`/`hdom` input, this is the nested route's half of the invariant's
clause — and the claim was MEASURED first, at 284 restored recursors of
which 184 are mimics (DESIGN, "THE RESTORE KEEPS THE HEAD A
CONSTANT"). -/
theorem restoreWalk_major {R : RestoreTbl} (hp : R.PinsHeaded) {d mI : Nat} {e e' : Expr}
    (hw : restoreWalk R d e = .ok e')
    {bs : List (Expr × BinderMeta)} {dom body : Expr} {bm : BinderMeta}
    (hs : e.stripPis mI = some (bs, .forallE dom body bm))
    {n : Name} {us : List Level} (hdom : dom.getAppFn = .const n us) :
    Expr.recMajorHeadOk e' mI = true := by
  obtain ⟨bs', body', hs', hw', -, -, -⟩ := restoreWalk_stripPis_doms mI hw hs
  obtain ⟨dom', b'', hdw, -, rfl⟩ := restoreWalk_forallE_inv hw'
  obtain ⟨q, ls, hq⟩ := restoreWalk_getAppFn_const hp dom hdw hdom
  rw [Expr.recMajorHeadOk, hs']
  simp only [hq]

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

end ConLeche
