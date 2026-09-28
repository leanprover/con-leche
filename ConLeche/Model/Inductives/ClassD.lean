module

public import ConLeche.Model.Inductives.ClassRunWF
import ConLeche.Verify.ExceptBind
import ConLeche.Model.Inductives.ClassSubst
import ConLeche.Verify.Cached.Erase

public section

/-!
# `ClassD`: positivity proven, declaratively

What the class-level proofs consume of a nested block's class check,
as ONE record: a checker that produces a `ClassD` for a block reuses
the whole class tower (the `ClassSys` instance, the identification of a
class's carrier with its container's, the class facts, `ClassPres`).
The class check's run produces one by one lemma (`ClassRun.toD`).

Per class, the record holds:

* **the key facts** — check 1 (`ClassInfosD`, one `ClassKeyOk` per
  class) and the group guard (`classMatesOk`);
* **the defeq tier** — the aliases, their candidates and their
  inversion (`ClassAliasOk`/`ClassAliasFrom`), and the same pairs;
* **the crests and their `FieldD` telescopes** — per constructor the
  abstracted crest (`classCrestInst`, `classAbs`, then the class's
  aliases) typed and walked (`ClassCtorRun`: the `FieldD` telescope,
  U4, the result, the member-side checks);
* **the free-set certificate, as propositions** (`ClassFreeCertD`),
  generalised where the proofs allow it: the free sets `Fl` ANY solution
  of the demand (not the least one), the commutation a `SemEq`-level
  statement (`ClassCommutesS`, not the kernel's `==` on erased terms),
  the rank any ranking function the coherent reads decrease;
* **R6** — the free-abstracted key typed at the holes' context (the
  source of its `Sat`);
* **check 5's kinds** — each walked constructor's output, its kinds
  re-pointed at its inductive hypotheses' classes (`ClassIhAgree`).

DESIGN record CLASSCHECK / P2D4.
-/

namespace ConLeche.Model
open ConLeche (Expr Name ClassInfo ClassKey ClassAlias ClassCtor ClassSlot NestCtx ConstantVal
  ClassInfosD CheckerOps CheckM Env ClassFreeV ClassCtorRun ClassAliasOk ClassAliasFrom ClassSameOk
  ClassIhAgree classHi classCrestInst classAliasAbs classAbs classHoleOf classSameIdx classDsF
  classMatesOk nestHoles)

/-! ## The commutation and the certificate, as propositions -/

/-- **The commutation, `SemEq`-level**: class `d`'s constructor `cv`,
instantiated at `d`'s parameters and abstracted at `c`'s free and own
classes, with the holes written back (`classGL`), agrees up to what the
reading does not read with the canonical text at `c`'s free-abstracted
parameters (`classGR`). -/
@[expose] def ClassCommutesS (cls : List ClassInfo) (mates : Name → List Name) (H : Nat)
    (isF isG : Expr → Bool) (c d : ClassInfo) (cv : ConstantVal) : Prop :=
  ∃ e0 A, ConLeche.instPisWith d.dsA (cv.type.instantiateLevelParams cv.levelParams d.key.lvls)
      = some e0 ∧ ConLeche.classCanonText (mates c.key.ind) c.nPc cv = some A ∧
    Expr.SemEq ((ConLeche.classAbsIf cls (fun h => isF h || isG h) e0).replaceFVars
        (ConLeche.classGL cls (mates c.key.ind) c H (c.dsA.map (ConLeche.classAbsIf cls isF))))
      ((A.instantiateLevelParams cv.levelParams c.key.lvls).replaceFVars
        (ConLeche.classGR c.nPc H (c.dsA.map (ConLeche.classAbsIf cls isF))))

theorem classCommutesS_of {cls : List ClassInfo} {mates : Name → List Name} {H : Nat}
    {isF isG : Expr → Bool} {c d : ClassInfo} {cv : ConstantVal}
    (h : ConLeche.classCommutes cls mates H isF isG c d cv = true) :
    ClassCommutesS cls mates H isF isG c d cv := by
  unfold ConLeche.classCommutes at h
  dsimp only at h
  cases he0 : ConLeche.instPisWith d.dsA (cv.type.instantiateLevelParams cv.levelParams d.key.lvls)
    with
  | none => rw [he0] at h; exact absurd h (by simp)
  | some e0 =>
    cases hA : ConLeche.classCanonText (mates c.key.ind) c.nPc cv with
    | none => rw [he0, hA] at h; exact absurd h (by simp)
    | some A =>
      rw [he0, hA] at h
      exact ⟨e0, A, he0, hA,
        Expr.semEq_of_erasedEq (Expr.erasedEq_of_eraseFVarTys (by simpa using h))⟩

/-- **The free-set certificate, as propositions** (`ClassFreeCert` with
the inner closure read as a closure and the commutation `SemEq`-level). -/
structure ClassFreeCertD (V : ClassFreeV) (hi : Nat) (aliasesOf : ClassInfo → List ClassAlias)
    (inn dep : Nat → List Nat) (rank : Nat → Nat) : Prop where
  /-- `inn x` contains the classes `x`'s key recognises and is closed under that step -/
  innClosed : ∀ x, x < V.cls.length →
    (∀ y ∈ ConLeche.classInner V.cls (V.cls.getD x default), y ∈ inn x) ∧
    ∀ y ∈ inn x, ∀ z ∈ ConLeche.classInner V.cls (V.cls.getD y default), z ∈ inn x
  /-- the free sets solve the demand -/
  demand : ∀ x, x < V.cls.length → ∀ y ∈ dep x, ∀ e ∈ inn y, V.stage x e = true →
    V.isFree y e = true
  commutes : ∀ c, c < V.cls.length → (V.cls.getD c default).member = none →
    ∀ j, j < V.cls.length → V.own c j = true → ∀ cv nF, (cv, nF) ∈ (V.cls.getD j default).ctors →
      ClassCommutesS V.cls V.mates hi (classHoleOf V.cls (V.isFree c))
        (classHoleOf V.cls (V.own c)) (V.cls.getD c default) (V.cls.getD j default) cv
  /-- no alias onto a stage class (free or own group) -/
  aliases : ∀ c, c < V.cls.length → (V.cls.getD c default).member = none →
    ∀ a ∈ aliasesOf (V.cls.getD c default), classStageHoles V c a.hole = false
  mentions : ∀ c, c < V.cls.length → (V.cls.getD c default).member = none →
    ∀ d ∈ V.mentions c, V.stage c d = true ∨ d ∈ dep c
  deps : ∀ c, c < V.cls.length → (V.cls.getD c default).member = none → ∀ d ∈ dep c,
    V.stage c d = false ∧ rank d < rank c ∧ ∀ e ∈ V.depStep c d, e ∈ dep c

/-! ## The record -/

/-- **`ClassD`: a nested block's positivity, proven** (see the module
docstring).  Everything is stated at the holes' context `ctx` and the
classes' hole bound `classHi ctx cls`. -/
structure ClassD (ops : CheckerOps CheckM) (env : Env) : Type where
  ctx : NestCtx
  holes : List Expr
  hholes : nestHoles ctx = some holes
  cls : List ClassInfo
  /-- each container's block mates -/
  mates : Name → List Name
  /-- check 1 -/
  ks : List ClassKey
  ctorsAs : List (List (ConstantVal × Nat))
  keys : ClassInfosD ops env ctx holes ctorsAs 0 ks cls
  hmates : classMatesOk cls mates = true
  /-- the defeq tier: the aliases, the ones each class's crests may use, their inversion -/
  al : List ClassAlias
  aliasesOf : ClassInfo → List ClassAlias
  aliasesOf_sub : ∀ c, ∀ a ∈ aliasesOf c, a ∈ al
  hal : ∀ a ∈ al, ClassAliasOk ops env (classHi ctx cls) cls a
  cands : List Expr
  hcand : ∀ e ∈ cands, ∃ I us nPc, e.getAppFn = .const I us ∧
    (cls.filterMap fun c => if c.member.isNone then some (c.key.ind, c.nPc) else none).lookup I
      = some nPc ∧ nPc ≤ e.getAppArgs.length ∧
    ∀ x ∈ e.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ classHi ctx cls
  halFrom : ∀ a ∈ al, ClassAliasFrom ops env (classHi ctx cls) cls cands a
  pairs : List (Nat × Nat)
  hpairs : ∀ q ∈ pairs, ClassSameOk ops env (classHi ctx cls) cls q.1 q.2 ∨
    ClassSameOk ops env (classHi ctx cls) cls q.2 q.1
  /-- the abstracted crests, per class and constructor -/
  crests : List (List Expr)
  hcrests : ∀ {c : Nat} {ci : ClassInfo} {j : Nat} {cv : ConstantVal} {nF : Nat} {e0 : Expr},
    cls[c]? = some ci → ci.ctors[j]? = some (cv, nF) → classCrestInst ctx holes ci cv = some e0 →
    (crests[c]?.bind (·[j]?)) = some (classAliasAbs (aliasesOf ci) (classAbs cls e0))
  /-- checks 3–5 per constructor: the crest typed and walked (the `FieldD`
  telescope), and check 5's output -/
  walked : List (List ClassCtor)
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  ctor : ∀ {c : Nat} {ci : ClassInfo} {j : Nat} {cv : ConstantVal} {nF : Nat},
    cls[c]? = some ci → ci.ctors[j]? = some (cv, nF) →
    ∃ e0 xs x xs' x', classCrestInst ctx holes ci cv = some e0 ∧
      walked[c]? = some xs ∧ xs[j]? = some x ∧
      ClassCtorRun ops env ctx holes cls (classHi ctx cls) ci cv nF
        (classAliasAbs (aliasesOf ci) (classAbs cls e0)) x ∧
      ctors[c]? = some xs' ∧ xs'[j]? = some x' ∧
      x'.cv = x.cv ∧ x'.nF = x.nF ∧ x'.tyN = x.tyN ∧
      ∃ (s : Nat) (ihs : List (Nat × Nat)), slots[s]? = some (ClassSlot.minor c cv.name ihs) ∧
        x'.kinds.length = x.kinds.length ∧
        ∀ (l : Nat) (k : ConLeche.ClassField), x.kinds[l]? = some k →
          ∃ k', x'.kinds[l]? = some k' ∧ ClassIhAgree (classSameIdx cls pairs) ihs l k k'
  /-- the free sets and their certificate -/
  Fl : Nat → List Nat
  inn : Nat → List Nat
  dep : Nat → List Nat
  rank : Nat → Nat
  cert : ClassFreeCertD (ClassFreeV.build cls mates crests Fl) (classHi ctx cls) aliasesOf
    inn dep rank
  /-- R6, at the free classes -/
  r6 : ∀ c, c < cls.length → (cls.getD c default).member = none →
    classDsF (ClassFreeV.build cls mates crests Fl) c ≠ (cls.getD c default).dsA →
    ∃ ty, ops.inferType env (classHi ctx cls)
      (Expr.mkAppN (.const (cls.getD c default).key.ind (cls.getD c default).key.lvls)
        (classDsF (ClassFreeV.build cls mates crests Fl) c)) = .ok ty

namespace ClassD

variable {ops : CheckerOps CheckM} {env : Env}

/-- The certificate's vocabulary. -/
@[expose] def V (D : ClassD ops env) : ClassFreeV :=
  ClassFreeV.build D.cls D.mates D.crests D.Fl

/-- The classes' hole bound. -/
@[expose] def H (D : ClassD ops env) : Nat := classHi D.ctx D.cls

/-- A hole names one class. -/
theorem holesUniq (D : ClassD ops env) : HolesUniq D.cls :=
  classInfosD_holesUniq D.keys

/-- The recogniser's premises (the keys' scoping a premise). -/
theorem classOccWF (D : ClassD ops env) (hks : KeysScoped D.cls D.H) : ClassOccWF D.cls D.H :=
  classOccWF_of_infos D.keys hks

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq] at hk
      simp only [Option.some.injEq] at h
      subst hk h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- Erasing the annotations keeps the variables and the loose bound
variables of a term the candidate guard admitted. -/
theorem erase_scoped {H : Nat} {x : Expr} (hx : x.bvarB = 0 ∧ x.fvarB ≤ H) :
    Expr.fvarsBelow H x.eraseFVarTys ∧ x.eraseFVarTys.looseBVarsBounded 0 = true :=
  ⟨fvarsBelow_replaceFVars (f := fun i => some (.fvar i (.sort .zero))) (fun i hi => ⟨_, rfl, (hi : i < H)⟩) x (ConLeche.Expr.fvarB_le hx.2),
    looseBVars_replaceFVars (fun i s hs => by simp only [Option.some.injEq] at hs; subst hs; rfl) x 0
      (ConLeche.Expr.bvarB_le (by omega))⟩

/-- **The alias keys are scoped** (the candidate guard). -/
theorem aliasKeysScoped (D : ClassD ops env) (hwf : ClassOccWF D.cls D.H) :
    ∀ a ∈ D.al, Expr.fvarsBelow D.H (aliasKey a) ∧ (aliasKey a).looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨e, he, us, hfn, -, hps, -⟩ := D.halFrom a ha
  obtain ⟨I, us', nPc, hfn', hl, -, hx⟩ := D.hcand e he
  rw [hfn] at hfn'
  simp only [Expr.const.injEq] at hfn'
  obtain ⟨rfl, -⟩ := hfn'
  obtain ⟨c, hc, hcm⟩ := List.mem_filterMap.mp (lookup_mem hl)
  split at hcm
  · rename_i hcn
    simp only [Option.some.injEq, Prod.mk.injEq] at hcm
    obtain ⟨hcI, hcN⟩ := hcm
    obtain ⟨ci, hci, -, hI, hN, hh, -⟩ := D.hal a ha
    have hcs : c.hole.isSome := by
      rw [classInfosD_hole_isSome D.keys hc]; exact hcn
    have hcis : ci.hole.isSome := by rw [hh]; rfl
    have : c.nPc = ci.nPc := hwf.nPc c hc ci hci hcs hcis (by rw [hcI, hI])
    have hn : a.nPc = nPc := by rw [← hN, ← this, hcN]
    rw [hn] at hps
    have hxs : ∀ y ∈ a.ps, Expr.fvarsBelow D.H y ∧ y.looseBVarsBounded 0 = true := by
      intro y hy
      rw [hps] at hy
      obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
      exact erase_scoped (hx x hx')
    exact ⟨fvarsBelow_mkAppN (by simp [Expr.fvarsBelow]) fun y hy => (hxs y hy).1,
      looseBVarsBounded_mkAppN' (by simp [Expr.looseBVarsBounded]) fun y hy => (hxs y hy).2⟩
  · exact nomatch hcm

/-- **The alias recogniser's premises.** -/
theorem aliasWF (D : ClassD ops env) (hwf : ClassOccWF D.cls D.H) : AliasWF D.al D.H :=
  aliasWF_of_run hwf D.hal (D.aliasKeysScoped hwf)

end ClassD

/-! ## The class check's run produces one -/

section Run

open ConLeche (FEnv BlockParts ConstantInfo TargetMajor ClassRun classCtxOf classAge classMates
  classAliasesFor classCrestsAl classFreeVOf)

variable {ops : CheckerOps CheckM} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts}
  {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {ctors : List (List ClassCtor)}

theorem classRun_crests (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors)
    {c : Nat} {ci : ClassInfo} {j : Nat} {cv : ConstantVal} {nF : Nat} {e0 : Expr}
    (hc : R.cls[c]? = some ci) (hj : ci.ctors[j]? = some (cv, nF))
    (he0 : classCrestInst (classCtxOf p fe₁ env₁ R.pq.1) R.holes ci cv = some e0) :
    ((classCrestsAl fe₁ R.cls R.al R.crests0)[c]?.bind (·[j]?)) =
      some (classAliasAbs (classAliasesFor (classAge fe₁) (classMates fe₁) ci R.al)
        (classAbs R.cls e0)) := by
  obtain ⟨-, hcr⟩ := ConLeche.except_mapM_ok R.hcrests
  obtain ⟨crs, hcrs, hcrsRun⟩ := hcr c ci hc
  obtain ⟨-, hce⟩ := ConLeche.except_mapM_ok hcrsRun
  obtain ⟨e, he, heRun⟩ := hce j (cv, nF) hj
  obtain ⟨e0', he0', rfl⟩ := ConLeche.classCrest_run heRun
  rw [he0] at he0'; cases he0'
  have hz : (R.cls.zip R.crests0)[c]? = some (ci, crs) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hcrs⟩
  simp [classCrestsAl, hz, he]

/-- **The class check's run is a `ClassD`.** -/
def ClassRun.toD (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors) :
    ClassD ops env₁ where
  ctx := classCtxOf p fe₁ env₁ R.pq.1
  holes := R.holes
  hholes := R.hholes
  cls := R.cls
  mates := classMates fe₁
  ks := R.rd.classes
  ctorsAs := ctorsAs
  keys := R.hcls
  hmates := R.hmates
  al := R.al
  aliasesOf c := classAliasesFor (classAge fe₁) (classMates fe₁) c R.al
  aliasesOf_sub c a ha := by
    unfold classAliasesFor at ha
    split at ha
    · exact ha
    · exact (List.mem_filter.mp ha).1
  hal := R.hal
  cands := R.cands
  hcand := R.hcand
  halFrom := R.halFrom
  pairs := R.pairs
  hpairs := R.hpairs
  crests := classCrestsAl fe₁ R.cls R.al R.crests0
  hcrests hc hj he0 := classRun_crests R hc hj he0
  walked := R.walked
  slots := R.rd.slots
  ctors := ctors
  ctor hc hj := R.ctor hc hj
  Fl := R.Fl
  inn := R.inn
  dep := R.dep
  rank := R.rank
  cert := by
    have h := ConLeche.classFreeOk_cert R.hfree
    refine ⟨fun x hx => ?_, h.demand, fun c hc hm j hj ho cv nF hcv =>
      classCommutesS_of (h.commutes c hc hm j hj ho cv nF hcv), fun c hc hm =>
      classAliasesFor_notStage (classInfosD_holesUniq R.hcls)
        (fun a ha => classAliasOk_target (R.hal a ha)) hm (h.aliases c hc hm), h.mentions, h.deps⟩
    have hi := h.innClosed
    unfold ConLeche.classClosedOk at hi
    have := List.all_eq_true.mp hi x (List.mem_range.mpr hx)
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at this
    exact this
  r6 c hc hm hne := R.r6 c (List.mem_range.mpr hc) hm hne

end Run

end ConLeche.Model
