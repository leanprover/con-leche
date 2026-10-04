module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecAssembly
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Abstract
import ConLeche.Verify.Extend.Inversions
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.GenRuleSyn
public import ConLeche.Model.Inductives.GenRuleFree
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Verify.CheckerF
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Levels
import ConLeche.Verify.Level
import ConLeche.Verify.Subst
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.BlockRecPreRun

public section

/-!
# The generated recursors' RULES (lane GENREC-C)

The rule side of the generated recursor stage (`genRecStage`,
`GenRecAssembly.lean`).  A stored rule is the ANNOTATION of the generated
rule (`ClassRuleRun.hann`): a λ-telescope over the shared prefix and the
constructor's declared fields whose body is the minor premise applied to
the fields and one `ih` λ per recursive field.  Everything here is read
off that run record:

* `genRuleAt`: the run at one stored `(recursor, constructor)` pair;
* `openLamsM`'s reading (`denoteMeta_openLamsM`): an opened λ-telescope
  reads as `mkLamsAV` of its binders' own bits and domains;
* **`htower`** (`genRuleTower`): every stored rule reads as a λ-tower of
  length `rP + nF` — the run strips exactly that many λs;
* **`hRaZ`** (`genRuleRaZ`): at `ℓ = 0` a stored rule reads as the point —
  its head λ carries the elimination level's datum (`ClassRuleRun.hpw`)
  and the prefix is never empty (the rule's own minor premise is in it).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassRuleRun ClassCtorRun ClassRecTyRun RecShape
  CheckMode)

universe w

/-! ## 1. An opened λ-telescope, read -/

section Open

variable {acv : Name → (Name → Nat) → AnnotTerm} {env : Env} {ψ : Name → Nat}

/-- `readLamBs` keeps one entry per binder. -/
theorem readLamBs_length :
    ∀ (j : Nat) (bs : List (Expr × ConLeche.BinderMeta)),
      (readLamBs acv env ψ j bs).length = bs.length
  | _, [] => rfl
  | j, _ :: bs => by simp [readLamBs, readLamBs_length (j + 1) bs]

/-- **An opened λ-telescope, read**: the reading of the term is the
λ-tower of the binders' own bits and domains (each read at its depth)
over the body's reading. -/
theorem denoteMeta_openLamsM :
    ∀ (n : Nat) {e : Expr} {j : Nat} {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr}
      {L : AnnotTerm},
      openLamsM n e j = some (bs, r) → denoteMeta acv env ψ j e = some L →
      ∃ C, denoteMeta acv env ψ (j + n) r = some C ∧
        L = mkLamsAV (readLamBs acv env ψ j bs) C ∧
        ∀ (k : Nat) (b : Expr × ConLeche.BinderMeta), bs[k]? = some b →
          ∃ a, denoteMeta acv env ψ (j + k) b.1 = some a
  | 0, e, j, bs, r, L, h, hL => by
    simp only [openLamsM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨L, by simpa using hL, rfl, fun k b hb => nomatch hb⟩
  | n + 1, .lam dom body m, j, bs, r, L, h, hL => by
    simp only [openLamsM] at h
    cases hi : openLamsM n (body.instantiate1 (.fvar j dom)) (j + 1) with
    | none => rw [hi] at h; exact nomatch h
    | some o =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv hL
      obtain ⟨C, hC, hbaE, hbs⟩ := denoteMeta_openLamsM n (bs := o.1) (r := o.2) (by rw [hi]) hba
      refine ⟨C, by rw [show j + (n + 1) = j + 1 + n by omega]; exact hC, ?_, ?_⟩
      · rw [hbaE]
        simp [readLamBs, mkLamsAV, hta]
      · intro k b hb
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
          subst hb
          exact ⟨ta, by simpa using hta⟩
        | succ k =>
          obtain ⟨a, ha⟩ := hbs k b (by simpa using hb)
          exact ⟨a, by rw [show j + (k + 1) = j + 1 + k by omega]; exact ha⟩
  | _ + 1, .bvar _, _, _, _, _, h, _ | _ + 1, .fvar _ _, _, _, _, _, h, _
  | _ + 1, .sort _, _, _, _, _, h, _ | _ + 1, .const _ _, _, _, _, _, h, _
  | _ + 1, .app _ _, _, _, _, _, h, _ | _ + 1, .forallE _ _ _, _, _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, _, _, h, _ | _ + 1, .lit _, _, _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, _, _, h, _ => nomatch h

/-- A term whose `n` leading binders are λs opens them. -/
theorem openLamsM_of_stripLams :
    ∀ (n : Nat) {e : Expr} (j : Nat) {bs : List (Expr × ConLeche.BinderMeta)} {b : Expr},
      e.stripLams n = some (bs, b) →
      ∃ bs' r, openLamsM n e j = some (bs', r)
  | 0, e, j, bs, b, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl⟩
  | n + 1, .lam dom body m, j, bs, b, h => by
    simp only [Expr.stripLams] at h
    cases hs : body.stripLams n with
    | none => rw [hs] at h; exact nomatch h
    | some q =>
      have hsome := Expr.stripLams_instantiate1_isSome (v := .fvar j dom) n 0
        (e := body) (by rw [hs]; rfl)
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨bs', r, ho⟩ := openLamsM_of_stripLams n (j + 1) (e := body.instantiate1
        (.fvar j dom)) (bs := q'.1) (b := q'.2) (by rw [show body.instantiate1 (.fvar j dom)
          = body.instantiate1 (.fvar j dom) 0 from rfl, hq'])
      exact ⟨(dom, m) :: bs', r, by simp [openLamsM, ho]⟩
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h
  | _ + 1, .forallE _ _ _, _, _, _, h | _ + 1, .letE _ _ _, _, _, _, h
  | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h => nomatch h

end Open

/-! ## 2. The run at one stored rule -/

section Run

variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **The generated stage at one stored `(recursor, constructor)` pair**:
the `j`-th recursor's record `rc`, class `c` and generated type run; the
class's `i`-th constructor `x` as the generator read it (declared fields
`cA.2`); the generated rule `gen` and its annotation run, whose output is
the stored rule. -/
theorem genRuleAt (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (rc : RecShape) (c : Nat) (x : ClassCtor) (gen : Expr),
      p.recs[j]? = some rc ∧ R.rd.recCls[j]? = some c ∧ R.cvGs[j]? = some r.1 ∧
      out[j]? = some (r.1, R.g.cls.getD c default, r.2.1) ∧
      r.2.2.2 = (R.g.cls.getD c default).ctors ∧
      c < R.Ms.length ∧
      (R.g.ctors.getD c [])[i]? = some x ∧
      Nonempty (ClassCtorRun mode F fe.env p (cvTas.map (·.type)) R.rd R.Ms c cA x) ∧
      Nonempty (ClassRecTyRun mode F fe R.g p.k rc c r.1) ∧
      x.nF = cA.2 ∧ x.cv = cA.1 ∧
      ConLeche.classGenRule R.g (ConLeche.classRecOf R.rd.recCls R.cvGs)
        (r.1.levelParams.map .param) c x = some gen ∧
      Nonempty (ClassRuleRun mode F .plain fe (ConLeche.classFeR p R.Ms R.cvGs R.rd.recCls fe)
        r.1 (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))
        (R.g.nP + R.g.slots.length + x.nF) gen rhs) := by
  obtain ⟨t, ho, rfl⟩ : ∃ t, out[j]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) := by
    simp only [tgtRs, List.getElem?_map] at hr
    cases ho : out[j]? with
    | none => rw [ho] at hr; exact nomatch hr
    | some t => rw [ho] at hr; exact ⟨t, rfl, (Option.some.inj hr).symm⟩
  have hjo : j < out.length := (List.getElem?_eq_some_iff.mp ho).1
  obtain ⟨hlenO, hallO⟩ := ConLeche.classRecsRulesOk_run R.hrules
  obtain ⟨hlenG, hallG⟩ := ConLeche.classRecTysOk_run R.hcvGs
  have hjr : j < p.recs.length := by
    have := Nat.min_le_left R.cvGs.length R.rd.recCls.length
    omega
  obtain ⟨c, cvG, hc, hcvG, ⟨TR⟩⟩ := hallG j p.recs[j] (List.getElem?_eq_getElem hjr)
  obtain ⟨rhss, ho', hrules⟩ := hallO j cvG c hcvG hc
  rw [ho] at ho'
  obtain rfl := Option.some.inj ho'
  simp only at hcA hrhs ⊢
  -- the class is one of the checked classes
  have hcM : c < R.Ms.length := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hd : R.g.cls.getD c default = default := by
      show R.Ms.getD c default = default
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [show (genRecGen p R.ctx.params R.Ms R.formerTysC R.rd R.ctors R.pre).cls.getD c default
      = R.g.cls.getD c default from rfl, hd] at hcA
    exact nomatch hcA
  obtain ⟨hlenC, hallC⟩ := ConLeche.classesCtors_run R.hctors
  obtain ⟨xs, hxs, hcs⟩ := hallC c R.Ms[c] (List.getElem?_eq_getElem hcM)
  rw [Nat.zero_add] at hcs
  obtain ⟨hlenX, hallX⟩ := ConLeche.classCtorsOf_run hcs
  have hMc : R.g.cls.getD c default = R.Ms[c] := by
    show R.Ms.getD c default = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcM]; rfl
  have hcA' : R.Ms[c].ctors[i]? = some cA := by
    rw [← hMc]; exact hcA
  obtain ⟨x, hx, ⟨CR⟩⟩ := hallX i cA hcA'
  have hgx : R.g.ctors.getD c [] = xs := by
    show R.ctors.getD c [] = xs
    rw [List.getD_eq_getElem?_getD, hxs]; rfl
  obtain ⟨-, hallR⟩ := ConLeche.classRulesOk_run hrules
  obtain ⟨gen, rhs', hrhs', hgen, ⟨RR⟩⟩ := hallR i x (by
    rw [show (genRecGen p R.ctx.params R.Ms R.formerTysC R.rd R.ctors R.pre).ctors.getD c []
      = R.g.ctors.getD c [] from rfl, hgx]; exact hx)
  obtain rfl : rhs = rhs' := Option.some.inj (hrhs.symm.trans hrhs')
  have hxe := CR.hx
  refine ⟨p.recs[j], c, x, gen, List.getElem?_eq_getElem hjr, hc, hcvG, ho, rfl, hcM,
    by rw [hgx]; exact hx, ⟨CR⟩, ⟨TR⟩, by rw [hxe], by rw [hxe], hgen, ⟨RR⟩⟩

end Run

/-! ## 3. `htower` and `hRaZ` -/

section Tower

variable {V : Type w} [SetTheory V]
variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The prefix is never empty: the rule's own minor premise is a slot. -/
theorem genRule_slots_pos {g : ClassGen} {recOf : Nat → Option Name} {rlvls : List Level}
    {c : Nat} {x : ClassCtor} {gen : Expr} (h : ConLeche.classGenRule g recOf rlvls c x = some gen) :
    0 < g.slots.length := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hnil : g.slots = [] := List.eq_nil_of_length_eq_zero h0
  simp [ConLeche.classGenRule, hnil] at h

/-- **`htower`, at any reading**: a stored rule reads as a λ-tower of
length `rP + nF` — the run strips exactly that many λs
(`ClassRuleRun.hstrip`). -/
theorem genRuleTower (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {ψ : Name → Nat} {Ra : AnnotTerm}
    (hRa : denoteMeta acv env₃ ψ 0 rhs = some Ra) :
    ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
      lds.length = p.rulePrefixAt j + cA.2 := by
  obtain ⟨rc, c, x, gen, hrc, -, -, -, -, -, -, -, ⟨TR⟩, hnF, -, -, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  obtain ⟨bs, b, ho⟩ := openLamsM_of_stripLams _ 0 RR.hstrip
  obtain ⟨C, -, hL, -⟩ := denoteMeta_openLamsM _ ho hRa
  refine ⟨_, C, hL, ?_⟩
  rw [readLamBs_length, openLamsM_length _ ho, BlockShape.rulePrefixAt,
    List.getD_eq_getElem?_getD, hrc, Option.getD_some, TR.hrP, hnF]

/-- **`hRaZ`, at any reading**: at `ℓ = 0` a stored rule reads as the
point — its head λ carries the elimination level's datum
(`ClassRuleRun.hpw`), whose bit is `0` there. -/
theorem genRuleRaZ (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {ψ : Name → Nat} {Ra : AnnotTerm}
    (hRa : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.elim p.large) = 0) (ρ : Nat → V) :
    interp V ρ Ra = pt := by
  obtain ⟨rc, c, x, gen, -, -, -, -, -, -, -, -, -, -, -, hgen, ⟨RR⟩⟩ := genRuleAt R hr hcA hrhs
  have hpos := genRule_slots_pos hgen
  obtain ⟨k, hk⟩ : ∃ k, R.g.nP + R.g.slots.length + x.nF = k + 1 :=
    ⟨R.g.nP + R.g.slots.length + x.nF - 1, by omega⟩
  obtain ⟨rbs, body, hstrip, hpw⟩ : ∃ rbs body, rhs.stripLams (k + 1) = some (rbs, body) ∧
      ∀ b ∈ rbs, b.2.pw = Level.zeronessOf (ConLeche.structElimLevel p.elim p.large) :=
    ⟨RR.rbs, RR.body, by rw [← hk]; exact RR.hstrip, RR.hpw⟩
  clear RR
  match rhs, hstrip with
  | .lam dom bd mb, hstrip =>
    simp only [Expr.stripLams] at hstrip
    cases hs : bd.stripLams k with
    | none => rw [hs] at hstrip; exact nomatch hstrip
    | some q =>
      rw [hs] at hstrip
      simp only [Option.map_some, Option.some.injEq] at hstrip
      have hmb : mb.pw = Level.zeronessOf (ConLeche.structElimLevel p.elim p.large) :=
        hpw (dom, mb) (by rw [← (Prod.mk.inj hstrip).1]; exact List.mem_cons_self)
      obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hRa
      have hb : pwBit ψ mb.pw = 0 := by rw [hmb]; exact (pwBit_zeronessOf ψ _).mpr hℓ
      rw [interp_lam, hb, ConLeche.SetModel.lamR_zero]

end Tower

/-! ## 4. `heqB`: the equations are bound

Every component of the generated family's equations is a reading of a
SCOPED term at its depth, or the default (`bvar 0`, below any positive
depth): the prefix is the recursor type's, the field domains, index
expressions and fired spine are readings of the constructor's declared
type at the class's parameters (`ClassGenScoped`), the `ih` data are
readings of pieces of the stored rule (closed), the residue is variables
only. -/

section Below

variable {V : Type w} [SetTheory V] {env : Env}

open ConLeche (ScB)

/-- An opened λ-telescope of a scoped term: its binders' domains are
scoped at their depths, its body at the extended depth. -/
theorem openLamsM_scoped :
    ∀ (n : Nat) {e : Expr} {j : Nat} {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr},
      openLamsM n e j = some (bs, r) → ScB j e →
      (∀ (k : Nat) (b : Expr × ConLeche.BinderMeta), bs[k]? = some b → ScB (j + k) b.1) ∧
        ScB (j + n) r
  | 0, e, j, bs, r, h, he => by
    simp only [openLamsM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun k b hb => nomatch hb), by simpa using he⟩
  | n + 1, .lam dom body m, j, bs, r, h, he => by
    simp only [openLamsM] at h
    cases hi : openLamsM n (body.instantiate1 (.fvar j dom)) (j + 1) with
    | none => rw [hi] at h; exact nomatch h
    | some o =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hw, hb⟩ := he
      simp only [Expr.WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hinst : ScB (j + 1) (body.instantiate1 (.fvar j dom)) :=
        ⟨Expr.WScoped.instantiate1 hw.1 0 hw.2, ConLeche.looseBVarsBounded_instantiate1 body 0 hb.2⟩
      obtain ⟨hbs, hr⟩ := openLamsM_scoped n (bs := o.1) (r := o.2) (by rw [hi]) hinst
      refine ⟨fun k b hk => ?_, by rw [show j + (n + 1) = j + 1 + n by omega]; exact hr⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk; exact ⟨by simpa using hw.1, hb.1⟩
      | succ k =>
        have := hbs k b (by simpa using hk)
        rwa [show j + (k + 1) = j + 1 + k by omega]
  | _ + 1, .bvar _, _, _, _, h, _ | _ + 1, .fvar _ _, _, _, _, h, _
  | _ + 1, .sort _, _, _, _, h, _ | _ + 1, .const _ _, _, _, _, h, _
  | _ + 1, .app _ _, _, _, _, h, _ | _ + 1, .forallE _ _ _, _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, _, h, _ | _ + 1, .lit _, _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

/-- A reading of a scoped term, or the default, is below any positive
depth it is read at. -/
theorem readD_below' (m : EnvModel V env) {φ : Name → Nat} {D : Nat} {e : Expr}
    (he : ScB D e ∨ e = default) (hD : 0 < D) :
    Term.bvarsBelow D ((denoteMeta m.acval env φ D e).getD default).erase := by
  rcases he with he | rfl
  · cases h : denoteMeta m.acval env φ D e with
    | none => exact hD
    | some a => exact bvarsBelow_of_reading (m := m) he.1 he.2 h
  · have : denoteMeta m.acval env φ D (default : Expr) = none := by
      show denoteMeta m.acval env φ D (.bvar 0) = none
      rw [denoteMeta] <;> simp
    rw [this]; exact hD

theorem readLamBs_below (m : EnvModel V env) {φ : Name → Nat} :
    ∀ (j : Nat) (bs : List (Expr × ConLeche.BinderMeta)),
      (∀ (k : Nat) (b : Expr × ConLeche.BinderMeta), bs[k]? = some b → ScB (j + k) b.1) →
      0 < j → LamDomsBelow j (readLamBs m.acval env φ j bs)
  | _, [], _, _ => trivial
  | j, b :: bs, h, hj => by
    refine ⟨readD_below' m (Or.inl (by simpa using h 0 b rfl)) hj,
      readLamBs_below m (j + 1) bs (fun k b' hk => ?_) (by omega)⟩
    have := h (k + 1) b' (by simpa using hk)
    rwa [show j + (k + 1) = j + 1 + k by omega] at this

theorem LamDomsBelow.mono : ∀ {ds : List (Nat × AnnotTerm)} {k k' : Nat}, k ≤ k' →
    LamDomsBelow k ds → LamDomsBelow k' ds
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hk, h => ⟨Term.bvarsBelow.mono hk h.1, LamDomsBelow.mono (by omega) h.2⟩

/-- **A generated `ih` term is below the chain and the frame**, when its
datum's telescope and arguments are below the frame. -/
theorem genIhAV_below {K rP D : Nat} {q : IhDatum} (hK : 0 < K) (hrP : rP ≤ D)
    (hT : LamDomsBelow D q.2.1)
    (hA : ∀ e ∈ q.2.2.1 ++ [q.2.2.2], Term.bvarsBelow (D + q.2.1.length) e.erase) :
    Term.bvarsBelow (K + D) (genIhAV K rP D q).erase := by
  unfold genIhAV
  refine mkLamsAV_below (LamDomsBelow.mono (by omega) hT) ?_
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by show _ < _; omega) fun a ha => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hl
    show _ < _
    omega
  · exact Term.bvarsBelow.mono (by omega) (hA b hb)

/-- **The `ih` data read off a closed stored rule are below the frame.** -/
theorem genIhdAV_below (m : EnvModel V env) {out : List (ConstantVal × TargetMajor × List Expr)}
    {g : ClassGen} {rd : ClassRead} {φ : Name → Nat} {c j : Nat}
    (hcl : ScB 0 (tgtRhsOf out c j)) (hD : 0 < g.pre.length + (genCtorAt g rd c j).nF) :
    ∀ q ∈ genIhdR m.acval env out g rd φ c j,
      LamDomsBelow (g.pre.length + (genCtorAt g rd c j).nF) q.2.1 ∧
      ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        Term.bvarsBelow (g.pre.length + (genCtorAt g rd c j).nF + q.2.1.length) e.erase := by
  intro q hq
  simp only [genIhdR, List.mem_map, List.mem_range] at hq
  obtain ⟨l, -, rfl⟩ := hq
  -- the stored rule's body arguments: scoped at the frame, or absent
  have hargs : ∀ k, ScB (g.pre.length + (genCtorAt g rd c j).nF)
      ((genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD k default) ∨
      (genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD k default = default := by
    intro k
    unfold genRuleArgs
    cases ho : openLamsM (g.pre.length + (genCtorAt g rd c j).nF) (tgtRhsOf out c j) 0 with
    | none =>
      right
      show (Expr.getAppArgs (default : Expr)).getD k default = default
      rfl
    | some o =>
      obtain ⟨-, hr⟩ := openLamsM_scoped _ (bs := o.1) (r := o.2) (by rw [ho]) hcl
      rw [Nat.zero_add] at hr
      simp only [Option.map_some, Option.getD_some]
      rw [List.getD_eq_getElem?_getD]
      cases hk : o.2.getAppArgs[k]? with
      | none => right; rfl
      | some a => left; exact ConLeche.ScB.getAppArgs hr a (List.mem_of_getElem? hk)
  -- the `ih` λ, opened
  generalize hA : (genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD
    ((genCtorAt g rd c j).nF + l) default = A at *
  have hAs := hargs ((genCtorAt g rd c j).nF + l)
  rw [hA] at hAs
  generalize hD' : g.pre.length + (genCtorAt g rd c j).nF = D at *
  generalize ((genCtorAt g rd c j).recs.getD l default).2.2 = tele
  -- the opened pieces: scoped at their depths, or absent
  have hopen : ∃ (bs : List (Expr × ConLeche.BinderMeta)) (call : Expr),
      (openLamsM tele A D).getD ([], default) = (bs, call) ∧
      (∀ (k : Nat) (b : Expr × ConLeche.BinderMeta), bs[k]? = some b → ScB (D + k) b.1) ∧
      (ScB (D + bs.length) call ∨ call = default) := by
    cases ho : openLamsM tele A D with
    | none => exact ⟨[], default, rfl, (fun k b hb => nomatch hb), Or.inr rfl⟩
    | some o =>
      rcases hAs with hAs | rfl
      · obtain ⟨hbs, hr⟩ := openLamsM_scoped tele (bs := o.1) (r := o.2) (by rw [ho]) hAs
        refine ⟨o.1, o.2, rfl, hbs, Or.inl ?_⟩
        rw [openLamsM_length tele (bs := o.1) (r := o.2) (by rw [ho])]; exact hr
      · -- the default opens nothing
        cases tele with
        | zero =>
          simp only [openLamsM, Option.some.injEq] at ho
          subst ho
          exact ⟨[], default, rfl, (fun k b hb => nomatch hb), Or.inr rfl⟩
        | succ t =>
          exact absurd ho (by show openLamsM (t + 1) (.bvar 0) D ≠ some o; simp [openLamsM])
  obtain ⟨bs, call, hbc, hbs, hcall⟩ := hopen
  simp only [hbc]
  have hcargs : ∀ e ∈ call.getAppArgs.drop g.pre.length, ScB (D + bs.length) e := by
    intro e he
    rcases hcall with hcall | rfl
    · exact ConLeche.ScB.getAppArgs hcall e (List.mem_of_mem_drop he)
    · have h0 : (default : Expr).getAppArgs = [] := rfl
      rw [h0] at he
      simp at he
  refine ⟨readLamBs_below m D bs hbs (by omega), fun e he => ?_⟩
  rw [readLamBs_length]
  rcases List.mem_append.mp he with he | he
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact readD_below' m (Or.inl (hcargs a ((List.dropLast_sublist _).subset ha))) (by omega)
  · simp only [List.mem_singleton] at he
    subst he
    refine readD_below' m ?_ (by omega)
    cases hl : (call.getAppArgs.drop g.pre.length).getLast? with
    | none =>
      right
      rw [List.getLastD_eq_getLast?, hl]; rfl
    | some a =>
      left
      rw [List.getLastD_eq_getLast?, hl]
      exact hcargs a (List.mem_of_getLast? hl)

end Below

/-! ## 5. The generated rule's frame is the target frame -/

section Frame

variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

/-- The generated rule opens the constructor's declared fields at the
prefix. -/
theorem classGenRule_open {g : ClassGen} {recOf : Nat → Option Name} {rlvls : List Level}
    {c : Nat} {x : ClassCtor} {gen : Expr} (h : ConLeche.classGenRule g recOf rlvls c x = some gen) :
    ∃ fvs res, ConLeche.openPisAtFvars x.nF x.tyD g.pre.length = some (fvs, res) := by
  unfold ConLeche.classGenRule at h
  obtain ⟨⟨s, sl⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨fvs, res⟩, hop, -⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨fvs, res, hop⟩

/-- **The generated rule's frame IS the target frame** (`tgtCrest`,
`tgtFieldFvs`, `tgtCbody` — official's `mk_rec_rules` binds the
declared fields at the class's instantiation), and the prefix is the
generator's. -/
theorem genFrameAt (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (cls : Nat) (x : ClassCtor) (fvs : List Expr) (res : Expr),
      R.rd.recCls[j]? = some cls ∧
      p.rulePrefixAt j = R.g.pre.length ∧ tgtRP p j = R.g.pre.length ∧
      tgtMajor out j = R.g.cls.getD cls default ∧ tgtCtorOf out j i = cA ∧
      tgtCrest out j i = x.tyD ∧
      ConLeche.openPisAtFvars cA.2 x.tyD R.g.pre.length = some (fvs, res) ∧
      tgtFieldFvs p out j i = fvs ∧ tgtCbody p out j i = res ∧
      tgtB p out j i = R.g.pre.length + cA.2 ∧
      genCtorAt R.g R.rd j i = x ∧ x.nF = cA.2 ∧ x ∈ R.g.ctors.getD cls [] ∧
      tgtRhsOf out j i = rhs ∧ ScB 0 rhs ∧
      ScB R.g.pre.length x.tyD ∧
      (∀ e ∈ (R.g.cls.getD cls default).ds, ScB R.g.pre.length e) ∧
      0 < R.g.slots.length := by
  obtain ⟨rc, cls, x, gen, hrc, hc, -, ho, hctors, -, hx, ⟨CR⟩, ⟨TR⟩, hnF, -, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  obtain ⟨hpl, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  have hrP : p.rulePrefixAt j = R.g.pre.length := by
    rw [BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some, TR.hrP, hpl]
  have hMaj : tgtMajor out j = R.g.cls.getD cls default := by
    rw [tgtMajor, List.getD_eq_getElem?_getD, ho]; rfl
  have hCt : tgtCtorOf out j i = cA := tgtCtorOf_at hr hcA
  have hxmem : x ∈ R.g.ctors.getD cls [] := List.mem_of_getElem? hx
  have hCrest : tgtCrest out j i = x.tyD := by
    rw [tgtCrest, hMaj, hCt]
    have hD := CR.hD
    rw [show (R.g.cls.getD cls default) = R.Ms.getD cls default from rfl, hD]; rfl
  obtain ⟨fvs, res, hop⟩ := classGenRule_open hgen
  rw [hnF] at hop
  have hRP : tgtRP p j = R.g.pre.length := hrP
  have hB : tgtB p out j i = R.g.pre.length + cA.2 := by rw [tgtB_at hr hcA, hrP]
  have hcx : genCtorAt R.g R.rd j i = x := by
    have h1 : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
    rw [genCtorAt, h1, List.getD_eq_getElem?_getD, hx]; rfl
  have hrhsE : tgtRhsOf out j i = rhs := by
    simp only [tgtRhsOf, List.getD_eq_getElem?_getD, ho, Option.getD_some, hrhs]
  have hcl : ScB 0 rhs := by
    rw [RR.hout]
    exact ⟨Expr.WScoped.of_not_hasFvar RR.hfv, RR.hbv⟩
  have hsl := genRule_slots_pos hgen
  refine ⟨cls, x, fvs, res, hc, hrP, hRP, hMaj, hCt, hCrest, hop, ?_, ?_, hB, hcx, hnF, hxmem,
    hrhsE, hcl, (hg.tyD cls x hxmem).mono (by omega),
    fun e he => (hg.ds cls e he).mono (by omega), hsl⟩
  · rw [tgtFieldFvs, hCt, hCrest, hRP, hop]; rfl
  · rw [tgtCbody, hCt, hCrest, hRP, hop]; rfl

end Frame

/-! ## 6. `heqB`, assembled -/

section EqsB

variable {V : Type w} [SetTheory V] {env : Env}
variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

/-- Opened variables' domains, read, are below their depths. -/
theorem readOpenedDoms_below' (m : EnvModel V env) {φ : Name → Nat} :
    ∀ (d : Nat) (fvs : List Expr),
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = .fvar (d + k) ty ∧ ScB (d + k) ty) →
      0 < d → FieldsBelow d (readOpenedDoms m.acval env φ d fvs)
  | _, [], _, _ => trivial
  | d, x :: fvs, h, hd => by
    obtain ⟨ty, rfl, hty⟩ := h 0 x rfl
    refine ⟨readD_below' m (Or.inl (by simpa [Expr.fvarTypeD] using hty)) hd,
      readOpenedDoms_below' m (d + 1) fvs (fun k x' hk => ?_) (by omega)⟩
    obtain ⟨ty', hx', hty'⟩ := h (k + 1) x' (by simpa using hk)
    exact ⟨ty', by rw [hx']; congr 1; omega, by rwa [show d + (k + 1) = d + 1 + k by omega] at hty'⟩

/-- The generated residue is variables only: below the frame and the
`ih`s as soon as the prefix is not empty. -/
theorem genRb0_below {nPre minPos nF nIh : Nat} (hn : 0 < nPre) :
    Term.bvarsBelow (nPre + nF + nIh) (genRb0 nPre minPos nF nIh).erase := by
  unfold genRb0
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by show _ < _; omega) fun a ha => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp hb with hb | hb <;>
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hl
    show _ < _
    omega

omit [SetTheory V] in
theorem genIhdAV_length {acval : Name → (Name → Nat) → AnnotTerm} {g : ClassGen} {rd : ClassRead}
    {φ : Name → Nat} {c j : Nat} :
    (genIhdR acval env out g rd φ c j).length = (genCtorAt g rd c j).recs.length := by
  simp [genIhdR]

/-- **`heqB`'s rows at the generated family**: the field domains, index
expressions and fired spine (the target frame, `genFrameAt`: the
constructor's declared type at the class's parameters, scoped), the
`ih` terms (read off the closed stored rule) and the residue are bound
by their frames. -/
theorem genRowB (m : EnvModel V env)
    (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g) :
    ∀ (ψ : Name → Nat) (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsBelow (p.rulePrefixAt c) (tgtFdomsAV p out m.acval env ψ c j) ∧
        (∀ e ∈ tgtEsAV p out m.acval env ψ c j, Term.bvarsBelow
          (p.rulePrefixAt c + (tgtFdomsAV p out m.acval env ψ c j).length) e.erase) ∧
        Term.bvarsBelow (p.rulePrefixAt c + (tgtFdomsAV p out m.acval env ψ c j).length)
          (tgtMkAV p out m.acval env ψ c j).erase ∧
        (∀ v ∈ genIhsR m.acval env (tgtRs out).length out R.g R.rd ψ c j, Term.bvarsBelow
          ((tgtRs out).length + p.rulePrefixAt c
            + (tgtFdomsAV p out m.acval env ψ c j).length) v.erase) ∧
        Term.bvarsBelow (p.rulePrefixAt c + (tgtFdomsAV p out m.acval env ψ c j).length
            + (genIhsR m.acval env (tgtRs out).length out R.g R.rd ψ c j).length)
          (genRbAV R.g R.rd c j).erase := by
  intro ψ c r hr j cA rhs hcA hrhs
  obtain ⟨cls, x, fvs, res, -, hrP, hRP, hMaj, hCt, -, hop, hFld, hCb, hB, hcx, hnF, -, hrhsE,
    hcl, hsx, hds, hsl⟩ := genFrameAt R hg hr hcA hrhs
  obtain ⟨hpl, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  have hpos : 0 < R.g.pre.length := by omega
  obtain ⟨hfl, hfvs, hres⟩ := ConLeche.ScB.openPis hop hsx
  have hFlen : (tgtFdomsAV p out m.acval env ψ c j).length = cA.2 := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, hFld, hfl]
  have hK : 0 < (tgtRs out).length := by
    have := (List.getElem?_eq_some_iff.mp hr).1; omega
  rw [hFlen, hrP]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tgtFdomsAV, hRP, hFld]
    exact readOpenedDoms_below' m _ fvs hfvs hpos
  · intro e he
    rw [tgtEsAV, hCb, hB] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact readD_below' m (Or.inl (ConLeche.ScB.getAppArgs hres a (List.mem_of_mem_drop ha)))
      (by omega)
  · rw [tgtMkAV, hB, hMaj, hCt, hFld]
    refine readD_below' m (Or.inl (ConLeche.ScB.mkAppN (ConLeche.ScB.const _ _ _) fun a ha => ?_))
      (by omega)
    rcases List.mem_append.mp ha with ha | ha
    · exact (hds a ha).mono (by omega)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]
      exact ConLeche.ScB.fvar (by rw [hfl] at hk; omega) hty
  · intro v hv
    rw [genIhsR, hcx, List.mem_map] at hv
    obtain ⟨q, hq, rfl⟩ := hv
    rw [← hrhsE] at hcl
    have hq' := genIhdAV_below m (g := R.g) (rd := R.rd) (φ := ψ) (c := c) (j := j) hcl
      (by rw [hcx]; omega) q hq
    rw [hcx, hnF] at hq'
    have := genIhAV_below (K := (tgtRs out).length) (rP := R.g.pre.length) hK (by omega) hq'.1
      hq'.2
    rw [hnF]
    simpa [Nat.add_assoc] using this
  · rw [genIhsR, List.length_map, genIhdAV_length, genRbAV, hcx, hnF]
    exact genRb0_below hpos

end EqsB

/-! ## 8. `heqP`: the `ih` data are level-parametric

The `ih` data are readings of pieces of the stored rule, whose level
footprint is the recursor's (`ClassRuleRun.hlp`); a reading, and a
binder's bit, depend on the valuation only there. -/

section Params

variable {V : Type w} [SetTheory V] {env : Env}

theorem lpDefF_getAppArgs {ps : List Name} {e : Expr} (h : lpDefF ps e = true) :
    ∀ a ∈ e.getAppArgs, lpDefF ps a = true :=
  (lpDefF_mkAppN_args e.getAppArgs (f := e.getAppFn) (by rw [Expr.mkAppN_getApp]; exact h)).2

/-- An opened λ-telescope keeps the footprint: in its domains, its binders'
data and its body. -/
theorem openLamsM_lp {ps : List Name} :
    ∀ (n : Nat) {e : Expr} {j : Nat} {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr},
      openLamsM n e j = some (bs, r) → lpDefF ps e = true →
      (∀ b ∈ bs, lpDefF ps b.1 = true ∧ b.2.pw.paramsDefined ps = true) ∧ lpDefF ps r = true
  | 0, e, j, bs, r, h, he => by
    simp only [openLamsM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun b hb => nomatch hb), he⟩
  | n + 1, .lam dom body m, j, bs, r, h, he => by
    simp only [openLamsM] at h
    cases hi : openLamsM n (body.instantiate1 (.fvar j dom)) (j + 1) with
    | none => rw [hi] at h; exact nomatch h
    | some o =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [lpDefF, Bool.and_eq_true] at he
      obtain ⟨hbs, hr⟩ := openLamsM_lp n (bs := o.1) (r := o.2) (by rw [hi])
        (lpDefF_instantiate1 rfl _ 0 he.1.2)
      refine ⟨fun b hb => ?_, hr⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨he.1.1, he.2⟩
      · exact hbs b hb
  | _ + 1, .bvar _, _, _, _, h, _ | _ + 1, .fvar _ _, _, _, _, h, _
  | _ + 1, .sort _, _, _, _, h, _ | _ + 1, .const _ _, _, _, _, h, _
  | _ + 1, .app _ _, _, _, _, h, _ | _ + 1, .forallE _ _ _, _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, _, h, _ | _ + 1, .lit _, _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

theorem readLamBs_params (m : EnvModel V env) {ps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ ps, ψ₁ q = ψ₂ q) :
    ∀ (j : Nat) (bs : List (Expr × ConLeche.BinderMeta)),
      (∀ b ∈ bs, lpDefF ps b.1 = true ∧ b.2.pw.paramsDefined ps = true) →
      readLamBs m.acval env ψ₁ j bs = readLamBs m.acval env ψ₂ j bs
  | _, [], _ => rfl
  | j, b :: bs, h => by
    obtain ⟨h1, h2⟩ := h b List.mem_cons_self
    have hpw : pwBit ψ₁ b.2.pw = pwBit ψ₂ b.2.pw := by
      unfold pwBit; rw [ConLeche.PropWhen.holds_ext h2 hq]
    simp only [readLamBs]
    rw [hpw, denoteMeta_params_extF m hq _ _ h1,
      readLamBs_params m hq (j + 1) bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- **The `ih` terms are level-parametric** at the stored rule's
footprint. -/
theorem genIhsAV_params (m : EnvModel V env) {out : List (ConstantVal × TargetMajor × List Expr)}
    {g : ClassGen} {rd : ClassRead} {K c j : Nat} {ps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ ps, ψ₁ q = ψ₂ q) (hlp : lpDefF ps (tgtRhsOf out c j) = true) :
    genIhsR m.acval env K out g rd ψ₁ c j = genIhsR m.acval env K out g rd ψ₂ c j := by
  unfold genIhsR genIhdR
  simp only [List.map_map]
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply]
  -- the pieces carry the footprint
  have hargs : ∀ k, lpDefF ps ((genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD
      k default) = true := by
    intro k
    unfold genRuleArgs
    cases ho : openLamsM (g.pre.length + (genCtorAt g rd c j).nF) (tgtRhsOf out c j) 0 with
    | none => rfl
    | some o =>
      obtain ⟨-, hr⟩ := openLamsM_lp _ (bs := o.1) (r := o.2) (by rw [ho]) hlp
      simp only [Option.map_some, Option.getD_some]
      rw [List.getD_eq_getElem?_getD]
      cases hk : o.2.getAppArgs[k]? with
      | none => rfl
      | some a => exact lpDefF_getAppArgs hr a (List.mem_of_getElem? hk)
  have hA := hargs ((genCtorAt g rd c j).nF + l)
  generalize (genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD
    ((genCtorAt g rd c j).nF + l) default = A at hA ⊢
  generalize ((genCtorAt g rd c j).recs.getD l default).2.2 = tele
  obtain ⟨bs, call, hbc, hbs, hcall⟩ : ∃ (bs : List (Expr × ConLeche.BinderMeta)) (call : Expr),
      (openLamsM tele A (g.pre.length + (genCtorAt g rd c j).nF)).getD ([], default)
        = (bs, call) ∧
      (∀ b ∈ bs, lpDefF ps b.1 = true ∧ b.2.pw.paramsDefined ps = true) ∧
      lpDefF ps call = true := by
    cases ho : openLamsM tele A (g.pre.length + (genCtorAt g rd c j).nF) with
    | none => exact ⟨[], default, rfl, (fun b hb => nomatch hb), rfl⟩
    | some o =>
      obtain ⟨h1, h2⟩ := openLamsM_lp tele (bs := o.1) (r := o.2) (by rw [ho]) hA
      exact ⟨o.1, o.2, rfl, h1, h2⟩
  have hcargs : ∀ a ∈ call.getAppArgs.drop g.pre.length, lpDefF ps a = true :=
    fun a ha => lpDefF_getAppArgs hcall a (List.mem_of_mem_drop ha)
  simp only [hbc]
  rw [readLamBs_params m hq _ bs hbs]
  congr 3
  congr 1
  · refine List.map_congr_left fun a ha => ?_
    rw [denoteMeta_params_extF m hq _ _ (hcargs a ((List.dropLast_sublist _).subset ha))]
  · refine congrArg (·.getD default) (denoteMeta_params_extF m hq _ _ ?_)
    cases hl : (call.getAppArgs.drop g.pre.length).getLast? with
    | none => rw [List.getLastD_eq_getLast?, hl]; rfl
    | some a =>
      rw [List.getLastD_eq_getLast?, hl]
      exact hcargs a (List.mem_of_getLast? hl)

end Params

/-! ## 9. The residue: the stored rule's body at the `ih` values

At a frame of prefix and field values, the stored rule's body reads as
the minor premise applied to the fields and to its `ih` λs, and each
`ih` λ — its callee's recursor constant read as the callee's leaf — reads
as the generated `ih` term `genIhAV` at the chain frame whose components
are the leaves: the same telescope and arguments, the head a variable
of the same value. -/

section Residue

variable {V : Type w} [SetTheory V]

theorem denoteMetaSpine_map {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      vs = as.map (fun a => (denoteMeta acval env φ d a).getD default)
  | _, _, .nil => rfl
  | _, _, .cons ha hs => by rw [denoteMetaSpine_map hs, List.map_cons, ha]; rfl

/-- **Two λ-towers over the same telescope and arguments**, their heads
of the same value along every spine of the telescope's length, read
alike at frames agreeing below the telescope's base. -/
theorem interp_lamsApp_congr {h1 h2 : AnnotTerm} {args : List AnnotTerm} :
    ∀ (tele : List (Nat × AnnotTerm)) {D : Nat} {σ σ' : Nat → V},
      LamDomsBelow D tele → (∀ e ∈ args, Term.bvarsBelow (D + tele.length) e.erase) →
      (∀ i, i < D → σ i = σ' i) →
      (∀ bs : List V, bs.length = tele.length →
        interp V (consList bs σ) h1 = interp V (consList bs σ') h2) →
      interp V σ (mkLamsAV tele (AnnotTerm.mkAppN h1 args))
        = interp V σ' (mkLamsAV tele (AnnotTerm.mkAppN h2 args))
  | [], D, σ, σ', _, hargs, hag, hh => by
    simp only [mkLamsAV, interp_mkAppN]
    have h0 := hh [] rfl
    simp only [consList_nil] at h0
    rw [h0]
    have hmap : args.map (interp V σ) = args.map (interp V σ') :=
      List.map_congr_left fun e he =>
        interp_congr_below V e D σ σ' (by simpa using hargs e he) hag
    rw [← List.foldl_map, ← List.foldl_map (f := interp V σ'), hmap]
  | (v, A) :: tele, D, σ, σ', hT, hargs, hag, hh => by
    show lamR v (interp V σ A) (fun x => interp V (cons x σ) _)
      = lamR v (interp V σ' A) (fun x => interp V (cons x σ') _)
    rw [← interp_congr_below V A D σ σ' hT.1 hag]
    refine lamR_congr fun x _ => ?_
    refine interp_lamsApp_congr tele (D := D + 1) hT.2 (fun e he => ?_) (fun i hi => ?_)
      (fun bs hbs => ?_)
    · have := hargs e he
      simpa [Nat.add_assoc, Nat.add_comm 1 tele.length] using this
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have := hh (x :: bs) (by simp [hbs])
      simpa [consList_cons] using this

theorem map_dropLast_getLastD {α β : Type} (f : α → β) (d : α) (l : List α) (hne : l ≠ []) :
    l.dropLast.map f ++ [f (l.getLastD d)] = l.map f := by
  have h1 := List.dropLast_concat_getLast hne
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  conv => rhs; rw [← h1]
  simp

theorem denoteMeta_const_depth {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} (d : Nat) (n : Name) (us : List Level) :
    denoteMeta acval env φ d (.const n us) = denoteMeta acval env φ 0 (.const n us) := by
  simp only [denoteMeta]

theorem readLamBs_cross {env₁ env₂ : Env} {acv₁ acv₂ : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {P : Expr → Prop}
    (hcross : ∀ (d : Nat) (e : Expr), P e →
      denoteMeta acv₁ env₁ ψ d e = denoteMeta acv₂ env₂ ψ d e) :
    ∀ (j : Nat) (bs : List (Expr × ConLeche.BinderMeta)), (∀ b ∈ bs, P b.1) →
      readLamBs acv₁ env₁ ψ j bs = readLamBs acv₂ env₂ ψ j bs
  | _, [], _ => rfl
  | j, b :: bs, h => by
    simp only [readLamBs]
    rw [hcross j b.1 (h b List.mem_cons_self),
      readLamBs_cross hcross (j + 1) bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

open ConLeche (ScB) in
/-- **One `ih` λ of the stored rule, valued**: read with its callee's
recursor constant as a closed term of value `a t'`, it has the value of
the generated `ih` term `genIhAV` at a chain frame agreeing below the
rule's frame and holding `a t'` at the callee's chain position. -/
theorem genIh_value {envC : Env} (m : EnvModel V envC) {acv : Name → (Name → Nat) → AnnotTerm}
    {env₃ : Env} {ψ : Name → Nat}
    (hcross : ∀ (d : Nat) (e : Expr), CBNF envC e →
      denoteMeta m.acval envC ψ d e = denoteMeta acv env₃ ψ d e)
    {D rP tele K t' : Nat} {a : Nat → V} {argE : Expr}
    {bl : List (Expr × ConLeche.BinderMeta)} {call : Expr}
    (hop : openLamsM tele argE D = some (bl, call)) (hsc : ScB D argE)
    (hfreeL : (∀ b ∈ bl, CBNF envC b.1) ∧
      ∀ e ∈ call.getAppArgs.drop rP, CBNF envC e)
    {rn : Name} {rlvls : List Level} (hfn : call.getAppFn = .const rn rlvls)
    (hlenc : rP < call.getAppArgs.length)
    (hpv : ∀ k, k < rP → ∃ T, call.getAppArgs[k]? = some (.fvar k T)) (hrPD : rP ≤ D)
    (hD : 0 < D) {L0 : AnnotTerm} (hL0 : denoteMeta acv env₃ ψ 0 (.const rn rlvls) = some L0)
    (hL0v : ∀ ρ' : Nat → V, interp V ρ' L0 = a t')
    {L : AnnotTerm} (hL : denoteMeta acv env₃ ψ D argE = some L)
    {σ σc : Nat → V} (hag : ∀ i, i < D → σ i = σc i) (hσc : σc (D + (K - 1 - t')) = a t') :
    interp V σ L = interp V σc (genIhAV K rP D (t', readLamBs m.acval envC ψ D bl,
      (call.getAppArgs.drop rP).dropLast.map
        (fun e => (denoteMeta m.acval envC ψ (D + bl.length) e).getD default),
      (denoteMeta m.acval envC ψ (D + bl.length) ((call.getAppArgs.drop rP).getLastD default)).getD
        default)) := by
  obtain ⟨C, hC, rfl, -⟩ := denoteMeta_openLamsM tele hop hL
  obtain ⟨hbsS, hcallS⟩ := openLamsM_scoped tele hop hsc
  have hbl := openLamsM_length tele hop
  rw [← hbl] at hcallS
  rw [readLamBs_cross hcross D bl hfreeL.1]
  -- the call, read
  have hcallE : call = Expr.mkAppN (.const rn rlvls) call.getAppArgs := by
    rw [← hfn]; exact (Expr.mkAppN_getApp call).symm
  rw [hcallE] at hC
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hC
  rw [denoteMeta_const_depth, hL0] at hfa
  obtain rfl := Option.some.inj hfa.symm
  have hvsE := denoteMetaSpine_map hvs
  -- the arguments: the prefix variables, then the rest
  have hsplit : call.getAppArgs = call.getAppArgs.take rP ++ call.getAppArgs.drop rP := (List.take_append_drop rP call.getAppArgs).symm
  have hpref : (call.getAppArgs.take rP).map
      (fun e => (denoteMeta acv env₃ ψ (D + tele) e).getD default)
      = prefVarsAV rP (D - rP + (readLamBs acv env₃ ψ D bl).length) := by
    rw [readLamBs_length, hbl]
    refine List.ext_getElem (by simp [prefVarsAV]; omega) fun k hk hk' => ?_
    simp only [List.length_map, List.length_take] at hk
    obtain ⟨T, hT⟩ := hpv k (by omega)
    simp only [List.getElem_map, List.getElem_take, prefVarsAV, List.getElem_range]
    have : call.getAppArgs[k] = .fvar k T := by
      rw [List.getElem?_eq_some_iff] at hT; exact hT.2
    rw [this]
    simp only [denoteMeta, Option.getD_some, AnnotTerm.bvar.injEq]
    omega
  have hrest : (call.getAppArgs.drop rP).map
      (fun e => (denoteMeta acv env₃ ψ (D + tele) e).getD default)
      = (call.getAppArgs.drop rP).map
      (fun e => (denoteMeta m.acval envC ψ (D + bl.length) e).getD default) := by
    rw [hbl]
    exact List.map_congr_left fun e he => by rw [hcross _ e (hfreeL.2 e he)]
  have hne : call.getAppArgs.drop rP ≠ [] := by
    intro h0; have := congrArg List.length h0; simp at this; omega
  have hargsE : vs = prefVarsAV rP (D - rP + (readLamBs acv env₃ ψ D bl).length) ++
      ((call.getAppArgs.drop rP).dropLast.map
        (fun e => (denoteMeta m.acval envC ψ (D + bl.length) e).getD default) ++
      [(denoteMeta m.acval envC ψ (D + bl.length) ((call.getAppArgs.drop rP).getLastD default)).getD
        default]) := by
    rw [hvsE, hsplit, List.map_append, hpref, hrest, List.take_append_drop,
      map_dropLast_getLastD _ _ _ hne]
  rw [hargsE]
  simp only [genIhAV]
  refine interp_lamsApp_congr _ (D := D) ?_ ?_ hag ?_
  · rw [← readLamBs_cross hcross D bl hfreeL.1]
    exact readLamBs_below m D bl hbsS hD
  · intro e he
    simp only [readLamBs_length] at he ⊢
    rcases List.mem_append.mp he with he | he
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      rw [List.mem_range] at hl
      show _ < _
      omega
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
        exact readD_below' m (Or.inl (ConLeche.ScB.getAppArgs hcallS b
          (List.mem_of_mem_drop ((List.dropLast_sublist _).subset hb)))) (by omega)
      · simp only [List.mem_singleton] at he
        subst he
        refine readD_below' m ?_ (by omega)
        cases hl : (call.getAppArgs.drop rP).getLast? with
        | none => right; rw [List.getLastD_eq_getLast?, hl]; rfl
        | some b =>
          left
          rw [List.getLastD_eq_getLast?, hl]
          exact ConLeche.ScB.getAppArgs hcallS b (List.mem_of_mem_drop (List.mem_of_getLast? hl))
  · intro bs hbs
    simp only [readLamBs_length] at hbs ⊢
    rw [hL0v, interp_bvar,
      show D + bl.length + (K - 1 - t') = (D + (K - 1 - t')) + bs.length by omega,
      consList_apply_add, hσc]

theorem denoteMetaSpine_some {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      ∀ a ∈ as, ∃ v, denoteMeta acval env φ d a = some v
  | _, _, .nil => fun a ha => nomatch ha
  | _, _, .cons ha hs => fun a' ha' => by
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨_, ha⟩
    · exact denoteMetaSpine_some hs a' ha'

/-- **The stored rule's `ih` pieces name no recursor**: the telescope
domains and the call's arguments past the prefix of every `ih` λ of the
stored rule resolve at the constructors' environment. -/
@[expose] def GenIhFree (env : Env) (out : List (ConstantVal × TargetMajor × List Expr))
    (g : ClassGen) (rd : ClassRead) (c j : Nat) : Prop :=
  ∀ l, l < (genCtorAt g rd c j).recs.length →
    ∀ (bl : List (Expr × ConLeche.BinderMeta)) (call : Expr),
      openLamsM ((genCtorAt g rd c j).recs.getD l default).2.2
          ((genRuleArgs out (g.pre.length + (genCtorAt g rd c j).nF) c j).getD
            ((genCtorAt g rd c j).nF + l) default)
          (g.pre.length + (genCtorAt g rd c j).nF) = some (bl, call) →
        (∀ b ∈ bl, CBNF env b.1) ∧
          ∀ e ∈ call.getAppArgs.drop g.pre.length, CBNF env e

end Residue

section ResidueRun

variable {V : Type w} [SetTheory V]
variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

set_option maxHeartbeats 2000000 in
/-- **The residue at the generated rule**: at a frame of prefix and field
values, the body of the stored rule's reading is the generated residue
`genRbAV` at the generated `ih` terms' values at the chain frame whose
components are the callees' values — given that every callee's recursor
constant reads as a closed term of its chain component's value
(`hcallee`), the readings of the constructors' environment cross to the
reading's (`hcross`) and the `ih` pieces name no recursor (`hfree`). -/
theorem genRule_residue {envC : Env} (m : EnvModel V envC)
    (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {ψ : Name → Nat}
    (hcross : ∀ (d : Nat) (e : Expr), CBNF envC e →
      denoteMeta m.acval envC ψ d e = denoteMeta acv env₃ ψ d e)
    (hfree : GenIhFree envC out R.g R.rd j i)
    {K : Nat} {a : Nat → V}
    (hcallee : ∀ (t : Nat) (rn : Name), ConLeche.classRecOf R.rd.recCls R.cvGs t = some rn →
      genRecIdx R.rd t < K ∧ ∃ L0, denoteMeta acv env₃ ψ 0 (.const rn (r.1.levelParams.map .param))
        = some L0 ∧ ∀ ρ' : Nat → V, interp V ρ' L0 = a (genRecIdx R.rd t))
    {Ra : AnnotTerm} (hRa : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    {lds : List (Nat × AnnotTerm)} {A : AnnotTerm} (hlam : Ra = mkLamsAV lds A)
    (hlen : lds.length = p.rulePrefixAt j + cA.2)
    {ρ : Nat → V} {pref fields : List V} (hpl : pref.length = p.rulePrefixAt j)
    (hfl : fields.length = cA.2) :
    interp V (consList (pref ++ fields) ρ) A
      = interp V (consList ((genIhsR m.acval envC K out R.g R.rd ψ j i).map
          (interp V (consList (pref ++ fields) (chainFrame K a ρ))))
          (consList (pref ++ fields) ρ)) (genRbAV R.g R.rd j i) := by
  obtain ⟨cls, x, -, -, hc, hrP, -, -, -, -, -, -, -, -, hcx, hnF, hxmem, hrhsE, hcl, -, -,
    hsl0⟩ := genFrameAt R hg hr hcA hrhs
  obtain ⟨-, cls2, x2, gen, -, hc2, -, -, -, -, hx2, -, -, -, -, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hc)
  subst cls2
  have hgc : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
  have hxx : x2 = x := by
    rw [← hcx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  obtain ⟨hpl0, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  obtain ⟨_fvs, _res, _ws, s, bs, body, -, -, hslot, hsl, hop, -, ⟨T, hfn⟩, hlenB, hfields, hihs⟩ :=
    genRule_shapeD hg hxmem hgen RR.hout
  -- the frame's depth
  have hD : R.g.pre.length + x.nF = p.rulePrefixAt j + cA.2 := by rw [hrP, hnF]
  have hDpos : 0 < R.g.pre.length := by omega
  obtain ⟨C, hC, hRaE, -⟩ := denoteMeta_openLamsM _ hop hRa
  obtain ⟨-, rfl⟩ : lds = readLamBs acv env₃ ψ 0 bs ∧ A = C :=
    mkLamsAV_length_inj (by rw [hlen, readLamBs_length, openLamsM_length _ hop, hD])
      (hlam ▸ hRaE)
  rw [Nat.zero_add] at hC
  have hbE : body = Expr.mkAppN (.fvar (R.g.nP + s) T) body.getAppArgs := by
    rw [← hfn]; exact (Expr.mkAppN_getApp body).symm
  rw [hbE] at hC
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hC
  simp only [denoteMeta, Option.some.injEq] at hfa
  subst hfa
  have hvsE := denoteMetaSpine_map hvs
  have hvsS := denoteMetaSpine_some hvs
  -- the body scoped (the stored rule is closed)
  obtain ⟨-, hbodyS⟩ := openLamsM_scoped _ hop hcl
  rw [Nat.zero_add] at hbodyS
  -- the frames
  have hspl : (pref ++ fields).length = R.g.pre.length + x.nF := by
    rw [List.length_append, hpl, hfl, hrP, hnF]
  have hag : ∀ k, k < R.g.pre.length + x.nF →
      consList (pref ++ fields) ρ k = consList (pref ++ fields) (chainFrame K a ρ) k := by
    intro k hk
    rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]
  -- the minor's position
  have hms : genMinorSlot R.g R.rd j i = s := by
    have h1 : genMinorSlot R.g R.rd j i = (genSlotOf R.g cls x.cv.name).getD 0 := by
      unfold genMinorSlot genSlotOf
      rw [hgc, hcx]
      congr 1
    rw [h1, hslot]; rfl
  have hRb : genRbAV R.g R.rd j i = genRb0 pref.length (R.g.nP + s) fields.length
      ((genIhsR m.acval envC K out R.g R.rd ψ j i).map
        (interp V (consList (pref ++ fields) (chainFrame K a ρ)))).length := by
    rw [genRbAV, hms, hcx, List.length_map, genIhsR, List.length_map, genIhdAV_length, hcx,
      hpl, hfl, hrP, hnF]
  rw [hRb, interp_genRb0 (by rw [hpl, hrP]; omega)]
  rw [interp_mkAppN, ← List.foldl_map]
  -- the head: the minor
  have hhead : interp V (consList (pref ++ fields) ρ)
      (.bvar (R.g.pre.length + x.nF - 1 - (R.g.nP + s))) = pref.getD (R.g.nP + s) pt := by
    rw [interp_bvar, consList_getD_of_lt _ _ _ (by rw [hspl]; omega), hspl,
      show R.g.pre.length + x.nF - 1 - (R.g.pre.length + x.nF - 1 - (R.g.nP + s)) = R.g.nP + s
        by omega, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hpl, hrP]; omega),
      ← List.getD_eq_getElem?_getD]
  rw [hhead]
  congr 1
  -- the arguments: the fields, then the `ih` values
  rw [hvsE, List.map_map]
  refine List.ext_getElem (by simp [hlenB, hfl, genIhsR, genIhdAV_length, hcx, hnF])
    fun k hk hk' => ?_
  simp only [List.length_map] at hk
  rw [hlenB] at hk
  simp only [List.getElem_map, Function.comp_apply]
  rcases Nat.lt_or_ge k x.nF with hkF | hkF
  · -- a field
    obtain ⟨T', hT'⟩ := hfields k hkF
    have hbk : body.getAppArgs[k] = .fvar (R.g.pre.length + k) T' :=
      (List.getElem?_eq_some_iff.mp hT').2
    rw [hbk, List.getElem_append_left (by rw [hfl, ← hnF]; exact hkF)]
    simp only [denoteMeta, Option.getD_some, interp_bvar]
    rw [consList_getD_of_lt _ _ _ (by rw [hspl]; omega), hspl,
      show R.g.pre.length + x.nF - 1 - (R.g.pre.length + x.nF - 1 - (R.g.pre.length + k))
        = pref.length + k by rw [hpl, hrP]; omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem (by rw [hfl, ← hnF]; exact hkF)]
    rfl
  · -- an `ih`
    obtain ⟨l, rfl⟩ : ∃ l, k = x.nF + l := ⟨k - x.nF, by omega⟩
    have hl : l < x.recs.length := by have := hlenB; omega
    obtain ⟨q, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
    obtain ⟨rn, -, -, bl, call, hrn, -, hop2, hfn2, hlenc, hpv, -⟩ := hihs l q hq
    have hargE : body.getAppArgs.getD (x.nF + l) default = body.getAppArgs[x.nF + l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    rw [hargE] at hop2
    obtain ⟨L, hL⟩ := hvsS _ (List.getElem_mem (by rw [hlenB]; omega))
    rw [hL, Option.getD_some]
    -- the generated rule's arguments are the stored rule's
    have hgra : genRuleArgs out (R.g.pre.length + x.nF) j i = body.getAppArgs := by
      rw [genRuleArgs, hrhsE, hop]; rfl
    have hqd : x.recs.getD l default = q := by
      rw [List.getD_eq_getElem?_getD, hq]; rfl
    obtain ⟨hK, L0, hL0, hL0v⟩ := hcallee q.2.1 rn hrn
    have hfreeL := hfree l (by rw [hcx]; exact hl) bl call (by
      rw [hcx, hgra, hqd, hargE]; exact hop2)
    have hsc : ScB (R.g.pre.length + x.nF) body.getAppArgs[x.nF + l] :=
      ConLeche.ScB.getAppArgs hbodyS _ (List.getElem_mem _)
    have hv := genIh_value m hcross (K := K) (t' := genRecIdx R.rd q.2.1) (a := a) hop2 hsc
      hfreeL hfn2 hlenc hpv (by omega) (by omega) hL0 hL0v hL hag (by
        rw [show R.g.pre.length + x.nF + (K - 1 - genRecIdx R.rd q.2.1)
          = (K - 1 - genRecIdx R.rd q.2.1) + (pref ++ fields).length by rw [hspl]; omega,
          consList_apply_add, chainFrame_apply hK])
    rw [hv, List.getElem_append_right (by rw [hfl, ← hnF]; omega)]
    simp only [genIhsR, List.getElem_map, genIhdR, List.getElem_range, hcx, hfl, ← hnF,
      Nat.add_sub_cancel_left, hgra, hqd, hargE, hop2, Option.getD_some]
end ResidueRun

/-! ## 10. `hdataS`: the rule contract at every fired pair -/

section DataS

variable {V : Type w} [SetTheory V]

theorem stripLams_length' :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {b : Expr},
      e.stripLams n = some (bs, b) → bs.length = n
  | 0, e, bs, b, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, .lam dom body m, bs, b, h => by
    simp only [Expr.stripLams] at h
    cases hs : body.stripLams n with
    | none => rw [hs] at h; exact nomatch h
    | some q =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← (Prod.mk.inj h).1, List.length_cons, stripLams_length' n (bs := q.1) (b := q.2)
        (by rw [hs])]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .forallE _ _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripLams] at h

/-- The opened domains of a λ-telescope whose stripped domains name only
constants of `env` name only constants of `env`. -/
theorem openLamsM_constsBound {env : Env} :
    ∀ (n : Nat) {e : Expr} {j : Nat} {rbs bs : List (Expr × ConLeche.BinderMeta)} {b r : Expr},
      e.stripLams n = some (rbs, b) → (∀ q ∈ rbs, ConstsBound env q.1) →
      openLamsM n e j = some (bs, r) → ∀ q ∈ bs, ConstsBound env q.1
  | 0, e, j, rbs, bs, b, r, _, _, ho, q, hq => by
    simp only [openLamsM, Option.some.injEq, Prod.mk.injEq] at ho
    rw [← ho.1] at hq; exact nomatch hq
  | n + 1, .lam dom body m, j, rbs, bs, b, r, hs, hrbs, ho, q, hq => by
    simp only [Expr.stripLams] at hs
    cases hs' : body.stripLams n with
    | none => rw [hs'] at hs; exact nomatch hs
    | some p =>
      rw [hs'] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      simp only [openLamsM] at ho
      cases hi : openLamsM n (body.instantiate1 (.fvar j dom)) (j + 1) with
      | none => rw [hi] at ho; exact nomatch ho
      | some o =>
        rw [hi] at ho
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ho
        rw [← ho.1] at hq
        have hdom : ConstsBound env dom := hrbs (dom, m) List.mem_cons_self
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hdom
        · have hsome := Expr.stripLams_instantiate1_isSome (v := .fvar j dom) n 0 (e := body)
            (by rw [hs']; rfl)
          obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp hsome
          have heq := Expr.stripLams_instantiate1_eq n 0 hs' hp'
          refine openLamsM_constsBound n (e := body.instantiate1 (.fvar j dom))
            (rbs := p'.1) (b := p'.2) hp' (fun q' hq' => ?_) (by rw [hi]) q hq
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq'
          obtain ⟨b0, hb0⟩ : ∃ b0, p.1[k]? = some b0 := ⟨_, List.getElem?_eq_getElem (by
            have h1 := stripLams_length' _ hs'
            have h2 := stripLams_length' _ hp'
            omega)⟩
          rw [heq.2 k b0 p'.1[k] hb0 (List.getElem?_eq_getElem hk)]
          exact ConstsBound.instantiate1 (by simpa using hdom) _ _
            (hrbs b0 (List.mem_cons_of_mem _ (List.mem_of_getElem? hb0)))
  | _ + 1, .bvar _, _, _, _, _, _, h, _, _, _, _ | _ + 1, .fvar _ _, _, _, _, _, _, h, _, _, _, _
  | _ + 1, .sort _, _, _, _, _, _, h, _, _, _, _ | _ + 1, .const _ _, _, _, _, _, _, h, _, _, _, _
  | _ + 1, .app _ _, _, _, _, _, _, h, _, _, _, _
  | _ + 1, .forallE _ _ _, _, _, _, _, _, h, _, _, _, _
  | _ + 1, .letE _ _ _, _, _, _, _, _, h, _, _, _, _ | _ + 1, .lit _, _, _, _, _, _, h, _, _, _, _
  | _ + 1, .proj _ _ _, _, _, _, _, _, h, _, _, _, _ => by simp [Expr.stripLams] at h

theorem find?_range_extend {q : Nat → Bool} {n m r0 : Nat} (hnm : n ≤ m)
    (h : (List.range n).find? q = some r0) : (List.range m).find? q = some r0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [List.range_add, List.find?_append, h]; rfl

section Callee

variable {μ : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {pp : BlockParts}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

/-- **The callees' recursor constants read as their leaves**: the
constant a generated rule calls at class `t` (`classRecOf`) is the
family's recursor at position `genRecIdx rd t`, stored at the cons, read
by the family's valuation as that position's leaf. -/
theorem genHcallee
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block ctorsAs
      out)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hnd : ((tgtRs out).map (·.1.name)).Nodup)
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r)
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC (tgtRs out) s eqs ψ q).erase))
    {ψ : Name → Nat} {ρ : Nat → V} {a : Nat → V}
    (hleaf : ∀ c', c' < (tgtRs out).length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC (tgtRs out) s eqs ψ c') = a c') :
    ∀ (t : Nat) (rn : Name), ConLeche.classRecOf R.rd.recCls R.cvGs t = some rn →
      genRecIdx R.rd t < (tgtRs out).length ∧
        ∃ L0, denoteMeta (blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs)
            (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) ψ 0
            (.const rn (r.1.levelParams.map .param)) = some L0 ∧
          ∀ ρ' : Nat → V, interp V ρ' L0 = a (genRecIdx R.rd t) := by
  intro t rn hrn
  unfold ConLeche.classRecOf at hrn
  obtain ⟨r0, hf, rfl⟩ := Option.map_eq_some_iff.mp hrn
  have hr0 : r0 < R.cvGs.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
  obtain ⟨hlenO, hallO⟩ := ConLeche.classRecsRulesOk_run R.hrules
  obtain ⟨hlenG, hallG⟩ := ConLeche.classRecTysOk_run R.hcvGs
  have hRC : R.cvGs.length ≤ R.rd.recCls.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    obtain ⟨c, -, hc, -, -⟩ := hallG R.rd.recCls.length _
      (List.getElem?_eq_getElem (by omega))
    have := (List.getElem?_eq_some_iff.mp hc).1
    omega
  have hK : (tgtRs out).length = R.cvGs.length := by
    simp only [tgtRs, List.length_map, hlenO]; omega
  have hidx : genRecIdx R.rd t = r0 := by
    unfold genRecIdx
    rw [find?_range_extend hRC hf]; rfl
  rw [hidx]
  refine ⟨by omega, ?_⟩
  -- the stored recursor at `r0`
  obtain ⟨c, hc⟩ : ∃ c, R.rd.recCls[r0]? = some c :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rhss, ho, -⟩ := hallO r0 R.cvGs[r0] c (List.getElem?_eq_getElem hr0) hc
  have hr' : (tgtRs out)[r0]? = some (R.cvGs[r0], rhss, (R.g.cls.getD c default).nIdx,
      (R.g.cls.getD c default).ctors) := by
    simp only [tgtRs, List.getElem?_map, ho]; rfl
  have hcv := ConLeche.recStage_cvFacts h
  have hfind := find?_consBlockRecsR_at (R := Rr) (q := pp.toBlockShape) (m := 0) hnd
    (fun r₀ hr₀ => (hcv r₀ hr₀).1) hr'
  have hlps : R.cvGs[r0].levelParams = r.1.levelParams := recStage_lps h hr' hr
  have hname : (R.cvGs.getD r0 default).name = R.cvGs[r0].name := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0]; rfl
  rw [hname]
  have hread : denoteMeta (blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs)
      (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) ψ 0
      (.const R.cvGs[r0].name (r.1.levelParams.map .param))
      = some (blockRecLeafAV mpC.base2.acval envC (tgtRs out) s eqs ψ r0) := by
    simp only [denoteMeta, hfind, ConstantInfo.toConstantVal, List.length_map, hlps, ite_true,
      Level.substFn_param_self, blockRecAcv]
    rw [blockRecAcvOf_at hnd (by rw [List.getElem?_map, hr']; rfl)]
  refine ⟨_, hread, fun ρ' => ?_⟩
  rw [interp_closed (V := V) (hleafCl _ r0) _ ρ]
  exact hleaf r0 (by omega)

end Callee

/-! ### The named premises of `hdataS` -/

/-- **Bridge, prefix half**: at every stored rule and valuation, the
stored rule's first `rP` λ-domains (opened) read as the recursor type's
prefix domains (`blockRulePdomsAV`) — the rule and the type annotate the
same generated prefix. -/
@[expose] def GenRulePrefRead (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) : Prop :=
  ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
    r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
    ∀ (ψ : Name → Nat) (bs : List (Expr × ConLeche.BinderMeta)) (body : Expr),
      openLamsM (p.rulePrefixAt j + cA.2) rhs 0 = some (bs, body) →
      ((readLamBs acval envC ψ 0 bs).map (·.2)).take (p.rulePrefixAt j)
        = blockRulePdomsAV acval envC p (tgtRs out) ψ j

/-- **Bridge, field half**: at every stored rule and valuation, the
stored rule's field λ-domains (opened at the rule frame) read as the
target frame's field domains `tgtFdomsAV` — the rule binds the declared
fields at the class's instantiation, annotated as generated. -/
@[expose] def GenRuleFieldRead (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) : Prop :=
  ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
    r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
    ∀ (ψ : Name → Nat) (bs : List (Expr × ConLeche.BinderMeta)) (body : Expr),
      openLamsM (p.rulePrefixAt j + cA.2) rhs 0 = some (bs, body) →
      ((readLamBs acval envC ψ 0 bs).map (·.2)).drop (p.rulePrefixAt j)
        = tgtFdomsAV p out acval envC ψ j i

/-- **`BlockRuleDataB`'s three DATA conjuncts** (the class side's rows:
the frame's fit, the index readings, the fired spine) at one pair, under
the contract's premises. -/
@[expose] def BlockRuleRows3 {μ : CheckMode} {envC : Env} (mpC : EnvModelM V μ envC)
    (p : BlockParts) (nP : Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) : Prop :=
  ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j →
        ys.length = nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
          ∀ q, q < nP → ∀ vpa : AnnotTerm,
            denoteMeta mpC.base2.acval envC φ (p.toBlockShape.rulePrefixAt j)
              (openRev 0 (p.toBlockShape.rulePrefixAt j)
                ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
              = some vpa →
            interp V ρ (ys.getD q default)
              = interp V ρ (AnnotTerm.instRevChain
                  (xs.take (p.toBlockShape.rulePrefixAt j)) vpa)) →
        IotaIndexPin (V := V) ρ restC nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
        ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ∧
      (es0 (Level.substFn φ r.1.levelParams us) j i).map
          (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ))
        = (xs.drop (p.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
      interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ρ)
          (mk0 (Level.substFn φ r.1.levelParams us) j i)
        = interp V ρ (AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)

end DataS

/-! ## 11. `heqV`: the `ih` terms and the residue are bit-valid -/

section Valid

variable {V : Type w} [SetTheory V]

/-- **A λ-tower over a variable-headed spine is valid** at a frame
agreeing below its base with one where its telescope is valid, fitted
at every step, and its arguments valid at every fitting spine. -/
theorem annotValid_lamsApp {h : AnnotTerm} (hh : ∀ ρ' : Nat → V, AnnotValid V ρ' h)
    {args : List AnnotTerm} :
    ∀ (tele : List (Nat × AnnotTerm)) {D : Nat} {σ σc : Nat → V},
      LamDomsBelow D tele → (∀ e ∈ args, Term.bvarsBelow (D + tele.length) e.erase) →
      (∀ i, i < D → σ i = σc i) →
      FieldsValid σ (tele.map (·.2)) →
      (∀ bs : List V, SpineFit σ (tele.map (·.2)) bs →
        ∀ e ∈ args, AnnotValid V (consList bs σ) e) →
      AnnotValid V σc (mkLamsAV tele (AnnotTerm.mkAppN h args))
  | [], D, σ, σc, _, hargs, hag, _, hv => by
    refine annotValid_mkAppN (hh _) fun e he => ?_
    exact (AnnotValid_congr_below e D σ σc (by simpa using hargs e he) hag).mp
      (by simpa using hv [] trivial e he)
  | (v, A) :: tele, D, σ, σc, hT, hargs, hag, hF, hv => by
    show AnnotValid V σc (.lam v A _)
    rw [AnnotValid_lam]
    have hA := (AnnotValid_congr_below A D σ σc hT.1 hag).mp hF.1
    refine ⟨hA, fun x hx => ?_⟩
    rw [← interp_congr_below V A D σ σc hT.1 hag] at hx
    refine annotValid_lamsApp hh tele (D := D + 1) (σ := cons x σ) hT.2 (fun e he => ?_)
      (fun i hi => ?_) (hF.2 x hx) (fun bs hbs e he => ?_)
    · have := hargs e he
      simpa [Nat.add_assoc, Nat.add_comm 1 tele.length] using this
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have := hv (x :: bs) ⟨hx, hbs⟩ e he
      simpa [consList_cons] using this

/-- The generated residue is bit-valid anywhere: variables applied. -/
theorem genRb0_valid (ρ : Nat → V) (nPre minPos nF nIh : Nat) :
    AnnotValid V ρ (genRb0 nPre minPos nF nIh) := by
  unfold genRb0
  refine annotValid_mkAppN (by simp) fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha <;>
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    simp

/-- **The stored rule's `ih` pieces are bit-valid** at every stored rule,
at a frame of prefix and field values fitting the rule frame: every `ih` datum's telescope,
fitted step by step, and its arguments at every fitting spine. -/
@[expose] def GenIhPiecesValid {envC : Env} (acval : Name → (Name → Nat) → AnnotTerm)
    (out : List (ConstantVal × TargetMajor × List Expr)) (g : ClassGen) (rd : ClassRead)
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 : (Name → Nat) → Nat → Nat → List AnnotTerm) : Prop :=
  ∀ (ψ : Name → Nat) (ρ : Nat → V) (c j : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
    (rhs : Expr), (tgtRs out)[c]? = some r → r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
    ∀ ys : List V, SpineFit ρ (pdoms0 ψ c ++ fdoms0 ψ c j) ys →
    ∀ q ∈ genIhdR acval envC out g rd ψ c j,
      FieldsValid (consList ys ρ) (q.2.1.map (·.2)) ∧
        ∀ bs : List V, SpineFit (consList ys ρ) (q.2.1.map (·.2)) bs →
          ∀ e ∈ q.2.2.1 ++ [q.2.2.2], AnnotValid V (consList bs (consList ys ρ)) e

end Valid

/-! ## 12. The skeleton's `ih` data ARE the stored rule's (kernel D1) -/

section IhEq

variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

theorem readLamBs_eq_readOpened {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {ψ : Name → Nat} {m : ConLeche.BinderMeta} :
    ∀ (j : Nat) (bl : List (Expr × ConLeche.BinderMeta)) (xs : List Expr),
      bl.length = xs.length →
      (∀ (k : Nat) (b : Expr × ConLeche.BinderMeta) (y : Expr), bl[k]? = some b → xs[k]? = some y →
        Expr.ErasedEq b.1 y.fvarTypeD ∧ b.2 = m) →
      readLamBs acval env ψ j bl = (readOpenedDoms acval env ψ j xs).map fun a => (pwBit ψ m.pw, a)
  | _, [], [], _, _ => rfl
  | j, b :: bl, y :: xs, hl, h => by
    obtain ⟨h1, h2⟩ := h 0 b y rfl rfl
    simp only [readLamBs, readOpenedDoms, List.map_cons, h2, denoteMeta_erasedEq h1]
    rw [readLamBs_eq_readOpened (j + 1) bl xs (by simpa using hl) (fun k b' y' hb hy =>
      h (k + 1) b' y' (by simpa using hb) (by simpa using hy))]
  | _, [], _ :: _, hl, _ => nomatch hl
  | _, _ :: _, [], hl, _ => nomatch hl

/-- **The skeleton's `ih` data (read off the generator's pieces) are the
stored rule's** (`genIhdR`): the rule is stored as generated (kernel
D1), its `ih` λs open to the generator's pieces up to the annotations of
free variables, and the λ binders carry the family's elimination
datum. -/
theorem genIhdAV_eq_R (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) :
    genIhdAV acval env R.g R.rd (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
        ψ j i
      = genIhdR acval env out R.g R.rd ψ j i := by
  obtain ⟨cls, x, -, -, hc, -, -, -, -, -, -, -, -, -, hcx, hnF, hxmem, hrhsE, -, -, -, -⟩ :=
    genFrameAt R hg hr hcA hrhs
  obtain ⟨_rc2, cls2, x2, gen, -, hc2, -, -, -, -, hx2, -, -, -, -, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hc)
  subst cls2
  have hgc : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
  have hxx : x2 = x := by
    rw [← hcx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  obtain ⟨fvs, res, ws, s, bs, body, hop0, hws, -, -, hop, -, -, hlenB, -, hihs⟩ :=
    genRule_shapeD hg hxmem hgen RR.hout
  have hgra : genRuleArgs out (R.g.pre.length + x.nF) j i = body.getAppArgs := by
    rw [genRuleArgs, hrhsE, hop]; rfl
  unfold genIhdAV genIhdR
  simp only [hcx, hgra, hop0, hws, Option.map_some, Option.getD_some]
  refine List.ext_getElem (by simp) fun l hl hl' => ?_
  simp only [List.length_map, List.length_range] at hl hl'
  obtain ⟨q, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
  have hqE : x.recs[l] = q := (List.getElem?_eq_some_iff.mp hq).2
  have hqd : x.recs.getD l default = q := by rw [List.getD_eq_getElem?_getD, hq]; rfl
  obtain ⟨rn, xs, idx, bl, call, -, hparts, hop2, -, -, -, hbll, hbl, hdl, hpt⟩ := hihs l q hq
  simp only [List.getElem_map, List.getElem_range, hqE, hqd, hparts, hop2, Option.getD_some]
  have hbits : pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))
      = pwBit ψ R.g.bm.pw := rfl
  rw [hbits, ← readLamBs_eq_readOpened _ bl xs hbll hbl, hbll]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · -- the index arguments
    refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_dropLast, hdl]; rfl)
      fun k hk hk' => ?_
    simp only [List.length_map] at hk
    simp only [List.getElem_map, List.getElem_dropLast]
    have hz := hpt k _ idx[k] (List.getElem?_eq_getElem (by rw [hdl]; omega))
      (by rw [List.getElem?_append_left hk]; exact List.getElem?_eq_getElem hk)
    rw [denoteMeta_erasedEq hz]
  · -- the applied field
    obtain ⟨z, hz0⟩ : ∃ z, (call.getAppArgs.drop R.g.pre.length)[idx.length]? = some z :=
      ⟨_, List.getElem?_eq_getElem (by rw [hdl]; omega)⟩
    have hlast : (call.getAppArgs.drop R.g.pre.length).getLastD default = z := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hdl,
        show idx.length + 1 - 1 = idx.length by omega, hz0]; rfl
    have hz := hpt idx.length z (Expr.mkAppN (fvs.getD q.1 default) xs) hz0
      (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    rw [hlast, denoteMeta_erasedEq hz]

theorem genIhsAV_eq_R (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (K : Nat) (ψ : Name → Nat) :
    genIhsAV acval env K R.g R.rd (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
        ψ j i
      = genIhsR acval env K out R.g R.rd ψ j i := by
  unfold genIhsAV genIhsR
  rw [genIhdAV_eq_R R hg hr hcA hrhs]

end IhEq

/-! ## 13. The bridges, under D1 -/

section Bridges

variable {V : Type w} [SetTheory V] {μ : CheckMode}
variable {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {pp : BlockParts} {nb : Bool}
  {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

theorem closeTelescope_append' :
    ∀ (A B : List (Expr × ConLeche.BinderMeta)) (i : Nat) (body : Expr),
      ConLeche.closeTelescope (A ++ B) i body
        = ConLeche.closeTelescope A i (ConLeche.closeTelescope B (i + A.length) body)
  | [], B, i, body => by simp [ConLeche.closeTelescope]
  | (d, bm) :: A, B, i, body => by
    simp only [List.cons_append, ConLeche.closeTelescope]
    rw [closeTelescope_append' A B (i + 1) body,
      show i + 1 + A.length = i + (A.length + 1) by omega]
    rfl

theorem readLamBs_getElem {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {ψ : Name → Nat} :
    ∀ (j : Nat) (bs : List (Expr × ConLeche.BinderMeta)) (k : Nat) (hk : k < bs.length),
      ((readLamBs acval env ψ j bs).map (·.2))[k]'(by simp [readLamBs_length]; exact hk)
        = (denoteMeta acval env ψ (j + k) bs[k].1).getD default
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | j, b :: bs, 0, _ => by simp [readLamBs]
  | j, b :: bs, k + 1, hk => by
    have := readLamBs_getElem (acval := acval) (env := env) (ψ := ψ) (j + 1) bs k
      (by simpa using hk)
    simp only [readLamBs, List.map_cons, List.getElem_cons_succ, List.getElem_cons_succ] at this ⊢
    rw [this, show j + 1 + k = j + (k + 1) by omega]

theorem readOpenedDoms_getElem {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {ψ : Name → Nat} :
    ∀ (j : Nat) (xs : List Expr) (k : Nat) (hk : k < xs.length),
      (readOpenedDoms acval env ψ j xs)[k]'(by simp; exact hk)
        = (denoteMeta acval env ψ (j + k) xs[k].fvarTypeD).getD default
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | j, x :: xs, 0, _ => by simp [readOpenedDoms]
  | j, x :: xs, k + 1, hk => by
    have := readOpenedDoms_getElem (acval := acval) (env := env) (ψ := ψ) (j + 1) xs k
      (by simpa using hk)
    simp only [readOpenedDoms, List.getElem_cons_succ] at this ⊢
    rw [this, show j + 1 + k = j + (k + 1) by omega]

/-- **The field bridge, under D1**: the stored rule's field λ-domains
read as the target frame's field domains. -/
theorem genRuleFieldRead
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g) (acval : Name → (Name → Nat) → AnnotTerm) :
    GenRuleFieldRead acval envC pp.toBlockShape out := by
  intro j r hr i cA rhs hcA hrhs ψ bs body hop
  obtain ⟨cls, x, fvs0, res0, hc, hrP, hRP, -, -, -, hop0, hFld, -, -, hcx, hnF, hxmem, -, -, -,
    -, -⟩ := genFrameAt R hg hr hcA hrhs
  obtain ⟨_rc2, cls2, x2, gen, -, hc2, -, -, -, -, hx2, -, -, -, -, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hc)
  subst cls2
  have hgc : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
  have hxx : x2 = x := by
    rw [← hcx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  obtain ⟨fvs, res, ws, s, bs', body', hopF, -, -, -, hop', hbs, -⟩ :=
    genRule_shapeD hg hxmem hgen RR.hout
  rw [hnF] at hopF
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop0.symm.trans hopF))
  rw [hrP, ← hnF] at hop
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hop'))
  have hfl : fvs0.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hbl : bs.length = R.g.pre.length + cA.2 := by rw [openLamsM_length _ hop', hnF]
  rw [tgtFdomsAV, hRP, hFld, hrP]
  refine List.ext_getElem (by simp [readLamBs_length, hbl, hfl]) fun k hk hk' => ?_
  rw [List.getElem_drop, readLamBs_getElem 0 bs _ (by simp [readLamBs_length] at hk; omega),
    readOpenedDoms_getElem]
  obtain ⟨nd, hnd⟩ : ∃ nd, (R.g.pre ++ fvs0.map R.g.binder)[R.g.pre.length + k]? = some nd :=
    ⟨_, by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk')]; rfl⟩
  have hkb : R.g.pre.length + k < bs.length := by simp [readLamBs_length] at hk; omega
  have hE := (hbs (R.g.pre.length + k) bs[R.g.pre.length + k] nd
    (List.getElem?_eq_getElem hkb) hnd).1
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hk')] at hnd
  obtain rfl := (Option.some.inj hnd).symm
  rw [Nat.zero_add, denoteMeta_erasedEq hE]
  rfl

/-- **The prefix bridge, under D1**: the stored rule's prefix λ-domains
read as the stored recursor type's prefix domains — both are the
generated prefix `g.pre`, stored as generated. -/
theorem genRulePrefRead (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) :
    GenRulePrefRead mpC.base2.acval envC pp.toBlockShape out := by
  intro j r hr i cA rhs hcA hrhs ψ bs body hop
  obtain ⟨cls, x, fvs0, res0, hc, hrP, -, -, -, -, hop0, -, -, -, hcx, hnF, hxmem, -, -, -,
    -, -⟩ := genFrameAt R hg hr hcA hrhs
  obtain ⟨rc, cls2, x2, gen, hrc, hc2, -, -, -, -, hx2, -, ⟨TR⟩, -, -, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hc)
  subst cls2
  have hgc : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
  have hxx : x2 = x := by
    rw [← hcx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  obtain ⟨fvs, res, ws, s, bs', body', -, -, -, -, hop', hbs, -⟩ :=
    genRule_shapeD hg hxmem hgen RR.hout
  rw [hrP, ← hnF] at hop
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hop'))
  -- the stored recursor type is the generated one
  obtain ⟨-, -, -, -, -, -, -, -, _st, _u, -, -, hcvE⟩ := ConLeche.classConstOk_inv TR.hcv
  have hty : r.1.type = TR.gty := congrArg ConstantVal.type hcvE
  obtain ⟨ifs, maj, -, -, hgty, hbnd, hbody⟩ := ConLeche.classGenRecTy_spec hg TR.hgty
  have hpreB : ∀ q ∈ R.g.pre, q.1.looseBVarsBounded 0 = true := fun q hq =>
    hbnd q (List.mem_append_left _ (List.mem_append_left _ hq))
  have hrestB : ∀ q ∈ ifs.map R.g.binder ++ [(maj, R.g.bm)], q.1.looseBVarsBounded 0 = true :=
    fun q hq => hbnd q (by rw [List.append_assoc]; exact List.mem_append_right _ hq)
  rw [List.append_assoc, closeTelescope_append'] at hgty
  have hEq0 : Expr.ErasedEq r.1.type (ConLeche.closeTelescope R.g.pre 0
      (ConLeche.closeTelescope (ifs.map R.g.binder ++ [(maj, R.g.bm)]) (0 + R.g.pre.length)
        (Expr.mkAppN (R.g.motVar cls) (ifs ++ [.fvar (R.g.pre.length + ifs.length) maj])))) := by
    rw [hty, hgty]
    exact Expr.ErasedEq.rfl _
  obtain ⟨xsT, restT, hopT, -, hdomsT⟩ := open_of_erasedEq_closeTelescope R.g.pre 0 _ r.1.type
    hpreB (ConLeche.closeTelescope_bounded _ _ _ hrestB hbody) hEq0
  have hrP' : pp.toBlockShape.rulePrefixAt j = R.g.pre.length := hrP
  have hreads := blockRulePdomsAV_reads hμ mpC h hr ψ (by rw [hrP']; exact hopT)
  have hxT : xsT.length = R.g.pre.length := ConLeche.Verify.openPisAtFvars_length _ hopT
  have hbl : bs.length = R.g.pre.length + x.nF := openLamsM_length _ hop'
  rw [hrP']
  refine List.ext_getElem (by
    rw [List.length_take, List.length_map, readLamBs_length, blockRulePdomsAV_length hμ mpC h hr,
      hrP', hbl]; omega) fun k hk hk' => ?_
  have hkP : k < R.g.pre.length := by simp at hk; omega
  rw [List.getElem_take, readLamBs_getElem 0 bs k (by omega), Nat.zero_add]
  obtain ⟨nd, hnd⟩ : ∃ nd, (R.g.pre ++ fvs.map R.g.binder)[k]? = some nd :=
    ⟨_, by rw [List.getElem?_append_left hkP]; exact List.getElem?_eq_getElem hkP⟩
  have hE := (hbs k bs[k] nd (List.getElem?_eq_getElem (by omega)) hnd).1
  rw [List.getElem?_append_left hkP] at hnd
  have hT := hdomsT k xsT[k] nd.1 (List.getElem?_eq_getElem (by omega)) (by rw [hnd]; rfl)
  have hr' := hreads k xsT[k] (List.getElem?_eq_getElem (by omega))
  rw [denoteMeta_erasedEq hE, ← denoteMeta_erasedEq hT, hr', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  rfl

end Bridges

/-! ## 14. `GenIhFree`, from the stored recursor TYPE -/

section Free

variable {mode : CheckMode} {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {p : BlockShape}
  {nb : Bool} {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

open ConLeche (ScB ClassGenScoped)

/-- Every constructor the generator read at a checked class has its run. -/
theorem genClassCtorAt (R : GenRecRun mode F fe₁ env₁ (ConLeche.mkFEnv envC) p nb pos cvTas block
      ctorsAs out) {cls : Nat} (hcls : cls < R.Ms.length) {i : Nat} {x : ClassCtor}
    (hx : (R.g.ctors.getD cls [])[i]? = some x) :
    ∃ cA, (R.Ms.getD cls default).ctors[i]? = some cA ∧
      Nonempty (ClassCtorRun mode F envC p (cvTas.map (·.type)) R.rd R.Ms cls cA x) := by
  obtain ⟨-, hallC⟩ := ConLeche.classesCtors_run R.hctors
  obtain ⟨xs, hxs, hcs⟩ := hallC cls R.Ms[cls] (List.getElem?_eq_getElem hcls)
  rw [Nat.zero_add] at hcs
  obtain ⟨hlenX, hallX⟩ := ConLeche.classCtorsOf_run hcs
  have hgx : R.g.ctors.getD cls [] = xs := by
    show R.ctors.getD cls [] = xs
    rw [List.getD_eq_getElem?_getD, hxs]; rfl
  rw [hgx] at hx
  have hi : i < R.Ms[cls].ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hx).1; omega
  obtain ⟨x', hx', ⟨CR⟩⟩ := hallX i _ (List.getElem?_eq_getElem hi)
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  refine ⟨_, ?_, ⟨CR⟩⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcls, Option.getD_some,
    List.getElem?_eq_getElem hi]

set_option maxHeartbeats 4000000 in
/-- **`GenIhFree`, from the stored recursor TYPE** (kernel D1): the rule's
`ih` pieces are, up to their free variables, the pieces of the minor
premise's inductive hypothesis inside the stored generated type, whose
constants resolve at the constructors' environment (`classConstOk`).
`hfind`: the class's constructors are stored under their names (lane E's
`genRecCtor_find`), which pins the minor premise's constructor. -/
theorem genIhFree_run
    (R : GenRecRun mode F fe₁ env₁ (ConLeche.mkFEnv envC) p nb pos cvTas block ctorsAs out)
    (hg : ClassGenScoped R.g)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    GenIhFree envC out R.g R.rd j i := by
  obtain ⟨cls, x, -, -, hc, hrP, -, -, -, -, -, -, -, -, hcx, hnF, hxmem, hrhsE, -, -, -,
    -⟩ := genFrameAt R hg hr hcA hrhs
  obtain ⟨rc, cls2, x2, gen, -, hc2, -, -, hctors, hclsM, hx2, ⟨CR⟩, ⟨TR⟩, -, hxcv, hgen, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hc)
  subst cls2
  have hgc : genClsOf R.rd j = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hc]
  have hxx : x2 = x := by
    rw [← hcx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  intro l hl bl call hopI
  rw [hcx] at hl hopI
  obtain ⟨fvs, res, ws, s, bs, body, hopF, hws, hslot, hsl, hop, -, -, -, -, hihs⟩ :=
    genRule_shapeD hg hxmem hgen RR.hout
  have hgra : genRuleArgs out (R.g.pre.length + x.nF) j i = body.getAppArgs := by
    rw [genRuleArgs, hrhsE, hop]; rfl
  obtain ⟨q, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
  have hqd : x.recs.getD l default = q := by rw [List.getD_eq_getElem?_getD, hq]; rfl
  rw [hgra, hqd] at hopI
  obtain ⟨rn, xs, idx, bl', call', -, hparts, hop2, -, -, -, hbll, hblE, hdl, hpt⟩ :=
    hihs l q hq
  rw [hopI] at hop2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop2)
  -- the stored type: its constants resolve at the constructors' environment
  obtain ⟨-, -, -, -, -, -, -, hres, _st, _u, -, -, hcvE⟩ := ConLeche.classConstOk_inv TR.hcv
  have hgtyC : CBNF envC TR.gty :=
    constsBound_eraseFVars _ (constsBound_of_constsResolve _ hres)
  obtain ⟨ifs, maj, -, -, hgty, -, -⟩ := ConLeche.classGenRecTy_spec hg TR.hgty
  rw [hgty] at hgtyC
  obtain ⟨hpreC, -⟩ := CBNF_closeTelescope _ _ _ hgtyC
  -- the minor premise's slot, and its constructor
  have hsS : R.g.slots[s]? = some (.minor cls x.cv.name
      (match R.g.slots.getD s default with | .minor _ _ ihs0 => ihs0 | _ => [])) := by
    unfold genSlotOf at hslot
    have hpr := List.find?_some hslot
    rw [List.getElem?_eq_getElem hsl]
    have hgd : R.g.slots.getD s default = R.g.slots[s] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsl]; rfl
    rw [hgd] at hpr ⊢
    revert hpr
    cases R.g.slots[s] with
    | minor c' C' ihs0 =>
      intro hpr
      simp only [Bool.and_eq_true, beq_iff_eq] at hpr
      obtain ⟨rfl, rfl⟩ := hpr
      rfl
    | motive _ => intro hpr; exact nomatch hpr
  obtain ⟨x', T, hfx, hmin, hpreT⟩ := ConLeche.ClassGen.prefixBinders_minor hg hsS
  -- the constructor found by name is `x`
  have hx'x : x' = x := by
    have hmem := List.mem_of_find?_eq_some hfx
    have hname : x'.cv.name = x.cv.name := by simpa using List.find?_some hfx
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨cA', hcA', ⟨CR'⟩⟩ := genClassCtorAt R hclsM (List.getElem?_eq_getElem hi')
    have hcA'r : r.2.2.2[i']? = some cA' := by
      rw [hctors]; exact hcA'
    have hf1 := hfind j r hr i' cA' hcA'r
    have hf2 := hfind j r hr i cA hcA
    have hn1 : cA'.1.name = cA.1.name := by
      have h1 := congrArg (fun y => y.cv.name) CR'.hx
      simp only at h1
      rw [← h1, hname, hxcv]
    rw [hn1, hf2] at hf1
    have hinj := Option.some.inj hf1
    injection hinj with h1 h2 h3
    have hcAeq : cA' = cA := Prod.ext h1.symm h3.symm
    subst hcAeq
    exact classCtorRun_unique CR' CR
  rw [hx'x] at hmin
  have hTC : CBNF envC T := hpreC _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_of_getElem? hpreT)))
  obtain ⟨fvs', res', ws', ihs', concl, hop', hws', hT, -, hih'⟩ := minorTy_spec' hmin
  rw [hT] at hTC
  obtain ⟨hTn, -⟩ := CBNF_closeTelescope _ _ _ hTC
  obtain ⟨xs', idx', hparts', hihl⟩ := hih' l q hq
  have hihC := hTn _ (List.mem_append_right _ (List.mem_of_getElem? hihl))
  obtain ⟨hxsC, hcallC⟩ := CBNF_closeTelescope _ _ _ hihC
  rw [CBNF_mkAppN] at hcallC
  -- the two openings agree after erasure
  have hF := (openPis_erase x.nF (e := x.tyD) rfl hopF hop').2
  have hfvsV : ∀ y ∈ fvs, ∃ i T, y = Expr.fvar i T := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    exact ⟨_, ConLeche.openPisAtFvars_index _ _ _ hopF k _ (List.getElem?_eq_getElem hk)⟩
  have hfvsV' : ∀ y ∈ fvs', ∃ i T, y = Expr.fvar i T := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    exact ⟨_, ConLeche.openPisAtFvars_index _ _ _ hop' k _ (List.getElem?_eq_getElem hk)⟩
  have hfl : fvs.length = fvs'.length := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hopF, ConLeche.Verify.openPisAtFvars_length _ hop']
  have hW := targetPiDomsWith_erase fvs fvs' hfvsV hfvsV' hfl rfl hws hws'
  have hwq : eraseFVars (ws.getD q.1 default) = eraseFVars (ws'.getD q.1 default) := by
    have h1 := congrArg (fun L => L[q.1]?) hW
    simp only [List.getElem?_map] at h1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    cases hw1 : ws[q.1]? <;> cases hw2 : ws'[q.1]? <;> simp_all
  obtain ⟨hxs, hidx⟩ := ihParts_erase hwq hparts hparts'
  refine ⟨fun b hb => ?_, fun e he => ?_⟩
  · -- a telescope domain
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have hkx : k < xs.length := by rw [← hbll]; exact hk
    have hE := (hblE k bl[k] xs[k] (List.getElem?_eq_getElem hk)
      (List.getElem?_eq_getElem hkx)).1
    rw [CBNF_of_erasedEq hE]
    have hk' : k < xs'.length := by
      have := congrArg List.length hxs; simp at this; omega
    have hy := hxsC _ (List.mem_of_getElem? (show (xs'.map R.g.binder)[k]? = some
      (R.g.binder xs'[k]) by rw [List.getElem?_map, List.getElem?_eq_getElem hk']; rfl))
    have hmap := congrArg (fun L => L[k]?) hxs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hkx, List.getElem?_eq_getElem hk',
      Option.map_some, Option.some.injEq] at hmap
    unfold CBNF; rw [hmap]
    exact hy
  · -- a call argument past the prefix
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have hk2 : k < idx.length + 1 := by rw [← hdl]; exact hk
    obtain ⟨a, ha⟩ : ∃ a, (idx ++ [Expr.mkAppN (fvs.getD q.1 default) xs])[k]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    have hE := hpt k _ a (List.getElem?_eq_getElem hk) ha
    rw [CBNF_of_erasedEq hE]
    have hil : idx.length = idx'.length := by
      have := congrArg List.length hidx; simpa using this
    rcases Nat.lt_or_ge k idx.length with hki | hki
    · rw [List.getElem?_append_left hki] at ha
      obtain rfl := (Option.some.inj ((List.getElem?_eq_getElem hki).symm.trans ha))
      have hc' := hcallC.2 idx'[k] (List.mem_append_left _ (List.getElem_mem (by omega)))
      have hmap := congrArg (fun L => L[k]?) hidx
      simp only [List.getElem?_map, List.getElem?_eq_getElem hki,
        List.getElem?_eq_getElem (show k < idx'.length by omega), Option.map_some,
        Option.some.injEq] at hmap
      unfold CBNF; rw [hmap]; exact hc'
    · have hk0 : k = idx.length := by omega
      subst hk0
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at ha
      obtain rfl := (Option.some.inj ha).symm
      have hc' := hcallC.2 _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      have hxl : xs.length = xs'.length := by
        have := congrArg List.length hxs; simpa using this
      have hvars : ∀ {w : Expr} {d : Nat} {ys id : List Expr},
          R.g.ihParts q.2.1 q.2.2 w d = some (ys, id) → ys.map eraseFVars = ys.map fun _ => F0 := by
        intro w d ys id hp
        unfold ConLeche.ClassGen.ihParts at hp
        obtain ⟨⟨ys', leaf⟩, hop0, hp⟩ := Option.bind_eq_some_iff.mp hp
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        refine List.map_congr_left fun y hy => ?_
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        obtain ⟨T, hT⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 k _ (List.getElem?_eq_getElem hk)
        rw [hT]; rfl
      have hq1 : q.1 < x.nF := (ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)).1
      have hfv1 : eraseFVars (fvs.getD q.1 default) = F0 := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length _ hopF]; exact hq1)]
        obtain ⟨T, hT⟩ := ConLeche.openPisAtFvars_index _ _ _ hopF q.1 _
          (List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length _ hopF]; exact hq1))
        simp only [Option.getD_some]; rw [hT]; rfl
      have hfv2 : eraseFVars (fvs'.getD q.1 default) = F0 := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length _ hop']; exact hq1)]
        obtain ⟨T, hT⟩ := ConLeche.openPisAtFvars_index _ _ _ hop' q.1 _
          (List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length _ hop']; exact hq1))
        simp only [Option.getD_some]; rw [hT]; rfl
      unfold CBNF at hc' ⊢
      rw [eraseFVars_mkAppN, hfv1, hvars hparts]
      rw [eraseFVars_mkAppN, hfv2, hvars hparts'] at hc'
      have hrep : (xs.map fun _ => F0) = xs'.map fun _ => F0 := by
        rw [List.map_const', List.map_const', hxl]
      rw [hrep]; exact hc'

end Free

/-! ## 7. The skeleton's obligations, in its spelling -/

section Obligations

variable {V : Type w} [SetTheory V] {μ : CheckMode}
variable {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {pp : BlockParts} {nb : Bool}
  {pos : ConLeche.NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

open ConLeche (ScB ClassGenScoped)

/-- **`heqB`** (the skeleton's goal): every equation of the generated
family is bound below the family. -/
theorem genRecHeqB_R (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) :
    ∀ (ψ : Name → Nat) (e : AnnotTerm),
      e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsR mpC.base2.acval envC (tgtRs out).length out R.g R.rd ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd) ψ →
        Term.bvarsBelow (tgtRs out).length e.erase :=
  fun ψ e he => blockRecEqs_below_rows hμ h (genRowB mpC.base2 R hg) ψ e he

/-- **`htower`** (the skeleton's goal, at any environment's reading). -/
theorem genRecHtower
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out) {env₃ : Env} :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r →
        ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
          r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
            ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
                (ConLeche.tgtMajorsOf out) j r ≠ ConLeche.RecRuleFire.inert →
              ∀ (acv : Name → (Name → Nat) → AnnotTerm) (ψ : Name → Nat) (Ra : AnnotTerm),
                denoteMeta acv env₃ ψ 0 rhs = some Ra →
                  ∃ lds A, Ra = mkLamsAV lds A ∧ lds.length = pp.rulePrefixAt j + cA.2 :=
  fun _ _ hr _ _ _ hcA hrhs _ _ _ _ hRa => genRuleTower R hr hcA hrhs hRa

/-- **`hRaZ`** (the skeleton's goal, at any environment's reading). -/
theorem genRecHRaZ
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out) {env₃ : Env} {acv : Name → (Name → Nat) → AnnotTerm} :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r →
        ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
          r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
            ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
                (ConLeche.tgtMajorsOf out) j r ≠ ConLeche.RecRuleFire.inert →
              ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
                denoteMeta acv env₃ ψ 0 rhs = some Ra →
                  Level.eval ψ (ConLeche.structElimLevel pp.elim pp.large) = 0 →
                    ∀ (ρ : Nat → V), interp V ρ Ra = pt :=
  fun _ _ hr _ _ _ hcA hrhs _ _ _ hRa hℓ ρ => genRuleRaZ R hr hcA hrhs hRa hℓ ρ

/-- **`heqP`** (the skeleton's goal), given the family level's
parametricity (`blockRecLevel_run`'s `hsP`) and the CLASS SIDE's
parametricity rows — the field domains, index expressions and fired
spine at the target frame (`tgtRow_params`'s conclusion, at the
generated run: the constructor's declared type at the class's
instantiation names only the recursor's level parameters).  The `ih`
terms are parametric at the stored rule's footprint
(`genIhsAV_params`, `ClassRuleRun.hlp`), the residue is ψ-free. -/
theorem genRecHeqP_R (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {s : (Name → Nat) → Nat}
    (hsP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r → ∀ (ψ₁ ψ₂ : Name → Nat),
        (∀ (q : Name), q ∈ r.1.levelParams → ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂)
    (hrowP : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → ∀ (ψ₁ ψ₂ : Name → Nat),
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r →
        ∀ (ψ₁ ψ₂ : Name → Nat), (∀ (q : Name), q ∈ r.1.levelParams → ψ₁ q = ψ₂ q) →
          s ψ₁ = s ψ₂ ∧
            blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
                (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
                (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun ψ => genIhsR mpC.base2.acval envC (tgtRs out).length out R.g R.rd ψ)
                (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun _ => genRbAV R.g R.rd) ψ₁ =
              blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
                (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
                (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun ψ => genIhsR mpC.base2.acval envC (tgtRs out).length out R.g R.rd ψ)
                (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
                (fun _ => genRbAV R.g R.rd) ψ₂ := by
  intro i₀ r₀ hr₀ ψ₁₀ ψ₂₀ hq₀
  refine ⟨hsP i₀ r₀ hr₀ ψ₁₀ ψ₂₀ hq₀, blockRecEqs_params_rows hμ h ?_ i₀ r₀ hr₀ ψ₁₀ ψ₂₀ hq₀⟩
  intro c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq
  obtain ⟨e1, e2, e3⟩ := hrowP c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq
  obtain ⟨_rc, _cls, _x, _gen, -, -, -, -, -, -, -, -, -, -, -, -, ⟨RR⟩⟩ :=
    genRuleAt R hr hcA hrhs
  have hRlp := RR.hlp
  have hrhsE : tgtRhsOf out c j = rhs := by
    obtain ⟨t, ho, rfl⟩ : ∃ t, out[c]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) := by
      simp only [tgtRs, List.getElem?_map] at hr
      cases ho : out[c]? with
      | none => rw [ho] at hr; exact nomatch hr
      | some t => rw [ho] at hr; exact ⟨t, rfl, (Option.some.inj hr).symm⟩
    simp only at hrhs
    simp only [tgtRhsOf, List.getD_eq_getElem?_getD, ho, Option.getD_some, hrhs]
  have hlp : lpDefF r.1.levelParams (tgtRhsOf out c j) = true := by
    rw [hrhsE]; exact lpDefF_of_allLevelParamsDefined _ hRlp
  exact ⟨e1, e2, genIhsAV_params mpC.base2 hq hlp, e3, rfl⟩


/-- **The environment crossing at `CBNF`**: a term whose constants
(free variables forgotten) are the constructors' environment's reads
alike there and at the recursors' cons. -/
theorem blockRecDenote_cross_CBNF {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {mpC : EnvModelM V μ envC} {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : CBNF envC e) :
    denoteMeta mpC.base2.acval envC ψ d e
      = denoteMeta (blockRecAcv mpC.base2.acval envC rs s eqs)
          (ConLeche.consBlockRecsR R pp.toBlockShape 0 rs envC) ψ d e := by
  rw [denoteMeta_erasedEq (erasedEq_eraseFVarTys e), denoteMeta_erasedEq (erasedEq_eraseFVarTys e)]
  exact blockRecDenote_cross_eq h ψ d _ (constsBound_eraseFVarTys_of_CBNF e hcb)

set_option maxHeartbeats 4000000 in
/-- **`hdataS`** (the skeleton's goal): the rule contract at every fired
pair of the generated family.  Its conjuncts: the three DATA rows (the
class side, `hrow3`); the λ-tower's fit — the stored rule's λ-domains
read as the recursor's prefix and the target frame's field domains
(`hpref`, `hfield`), so the first conjunct's fit is theirs; the residue —
BY CONSTRUCTION (`genRule_residue`): the stored rule's body at the frame
is the minor premise applied to the fields and to its `ih` λs, each of
which, its callee's recursor constant read as the callee's leaf
(`genHcallee`), is the generated `ih` term at the chain frame of the
leaves' values; `hfind`: the stored constructors are installed (the `ih` pieces then name no recursor, `genIhFree_run`).  The family's
leaf facts come from the equations' `heqB`/`heqV`/`heqP` and the family
premise `hpre` (as at the target check, `tgtRecDataB`). -/
theorem genRecHdataS (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hndM : pp.toBlockShape.memberNames.Nodup)
    {s : (Name → Nat) → Nat}
    (heqB : ∀ (ψ : Name → Nat), ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ, Term.bvarsBelow (tgtRs out).length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ mm, mm < (tgtRs out).length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
      ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ, AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ₁ = (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ) ρ)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (hpref : GenRulePrefRead mpC.base2.acval envC pp.toBlockShape out)
    (hfield : GenRuleFieldRead mpC.base2.acval envC pp.toBlockShape out)
    (hrow3 : ∀ (φ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
          (ConLeche.tgtMajorsOf out) j r ≠ ConLeche.RecRuleFire.inert →
      BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
        (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA
        (ConLeche.recRuleBits envC.find? r.1.name
          { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
            fire := ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
              (ConLeche.tgtMajorsOf out) j r, rhs := rhs, paramsBlind := true })) :
    AtStoredRules mpC (ConLeche.tgtRulesR envC.find? (fun x => Expr.constsResolve envC x)
        pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd))
      (fun j => (ConLeche.tgtMajorsOf out j).nPc)
      (ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
        (ConLeche.tgtMajorsOf out))
      fun _ φ j r i cA rhs rl =>
        ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
            (ConLeche.tgtMajorsOf out) j r ≠ ConLeche.RecRuleFire.inert →
          BlockRuleDataB mpC pp (ConLeche.tgtMajorsOf out j).nPc
            (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find?
              (fun x => Expr.constsResolve envC x) pp.toBlockShape (ConLeche.tgtMajorsOf out))
              pp.toBlockShape 0 (tgtRs out) envC)
            (tgtRs out) s (blockRecNCt (tgtRs out))
            (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
            (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
            (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
            (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
            (fun _ => genRbAV R.g R.rd)
            (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA rl rhs := by
  intro m₃ hac φ j r hr i cA rhs hcA hrhs hfire
  have hnd := ConLeche.recStageG_nodup h hndM
  have hleaf := blockRecLeafOk_of hμ mpC h heqB heqV heqP hpre
  obtain ⟨hreadR, hokR⟩ := blockRuleRhs_read_run hμ mpC h hnd hleaf m₃ hac r
    (List.mem_of_getElem? hr) rhs (List.mem_of_getElem? hrhs)
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hnest hidx hfitR hfitC
  obtain ⟨h1, h2, h3⟩ := hrow3 φ j r hr i cA rhs hcA hrhs hfire us hus hℓ usj ρ xs ys restR restC
    hxl hyl husjl hψ hnest hidx hfitR hfitC
  -- the rule's reading at the family's valuation
  have hread' : denoteMeta (blockRecAcv mpC.base2.acval envC (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)))
      (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (fun x => Expr.constsResolve envC x)
        pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC)
      (Level.substFn φ r.1.levelParams us) 0 rhs
      = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)))
        (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find?
          (fun x => Expr.constsResolve envC x) pp.toBlockShape (ConLeche.tgtMajorsOf out))
          pp.toBlockShape 0 (tgtRs out) envC) rhs (Level.substFn φ r.1.levelParams us)) := by
    rw [← hac, ← denoteMeta_instLevels (acvalParamsAt_of_core m₃) (ks := r.1.levelParams)
      (us := us) φ]
    exact hreadR φ us
  have hok : ∀ ρ' : Nat → V, WellDenotedV V ρ' (blockRuleRaOf
      (blockRecAcv mpC.base2.acval envC (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)))
      (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find?
        (fun x => Expr.constsResolve envC x) pp.toBlockShape (ConLeche.tgtMajorsOf out))
        pp.toBlockShape 0 (tgtRs out) envC) rhs (Level.substFn φ r.1.levelParams us)) := by
    intro ρ'; rw [← hac]; exact hokR _ ρ'
  -- lengths
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hle := blockRecHrPle (p := pp) h hj
  have hpl : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).length
      = pp.toBlockShape.rulePrefixAt j := by simp [hxl]; omega
  have hfl : ((ys.drop (ConLeche.tgtMajorsOf out j).nPc).map (interp V ρ)).length = cA.2 := by
    simp [hyl]
  -- the λ-tower's fit (the bridges)
  have hfit5 : ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm),
      blockRuleRaOf (blockRecAcv mpC.base2.acval envC (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)))
          (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find?
            (fun x => Expr.constsResolve envC x) pp.toBlockShape (ConLeche.tgtMajorsOf out))
            pp.toBlockShape 0 (tgtRs out) envC) rhs (Level.substFn φ r.1.levelParams us)
        = mkLamsAV lds A →
      lds.length = pp.toBlockShape.rulePrefixAt j + cA.2 →
      SpineFit ρ (lds.map (·.2))
        ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop (ConLeche.tgtMajorsOf out j).nPc).map (interp V ρ)) := by
    intro lds A hlam hlen
    obtain ⟨cls, x, -, -, -, hrP, -, -, -, -, -, -, -, -, -, hnF, -, -, -, -, -, -⟩ :=
      genFrameAt R hg hr hcA hrhs
    obtain ⟨_rc2, _cls2, x2, _gen2, -, -, -, -, -, -, -, -, -, hnF2, -, -, ⟨RR⟩⟩ :=
      genRuleAt R hr hcA hrhs
    obtain ⟨hpl0, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
    have hn : R.g.nP + R.g.slots.length + x2.nF = pp.toBlockShape.rulePrefixAt j + cA.2 := by
      rw [hrP, hnF2, hpl0]
    have hstrip : rhs.stripLams (pp.toBlockShape.rulePrefixAt j + cA.2) = some (RR.rbs, RR.body) := by
      rw [← hn]; exact RR.hstrip
    obtain ⟨bs, body, hop⟩ := openLamsM_of_stripLams _ 0 hstrip
    obtain ⟨C, -, hRaE, -⟩ := denoteMeta_openLamsM _ hop hread'
    obtain ⟨rfl, -⟩ := mkLamsAV_length_inj
      (by rw [readLamBs_length, openLamsM_length _ hop]; exact hlen) (hlam.symm.trans hRaE)
    have hcb : ∀ q ∈ bs, ConstsBound envC q.1 :=
      openLamsM_constsBound _ hstrip (fun q hq => by
        have hres := RR.hdoms q hq
        simp only [ConLeche.StructWalkers.plain] at hres
        rw [ConLeche.constsResolveF_eq] at hres
        exact constsBound_of_constsResolve _ hres) hop
    rw [← readLamBs_cross (fun d e hcbe => blockRecDenote_cross_eq h _ d e hcbe) 0 bs hcb,
      ← List.take_append_drop (pp.toBlockShape.rulePrefixAt j)
        ((readLamBs mpC.base2.acval envC (Level.substFn φ r.1.levelParams us) 0 bs).map (·.2)),
      hpref j r hr i cA rhs hcA hrhs _ bs body hop, hfield j r hr i cA rhs hcA hrhs _ bs body hop]
    exact h1
  refine ⟨h1, h2, h3, fun a hleafA => ?_, hfit5⟩
  obtain ⟨lds, A, hlam, hlen⟩ := genRuleTower R hr hcA hrhs hread'
  have hlam' : blockRuleRaOf (blockRecAcv mpC.base2.acval envC (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)))
      (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find?
        (fun x => Expr.constsResolve envC x) pp.toBlockShape (ConLeche.tgtMajorsOf out))
        pp.toBlockShape 0 (tgtRs out) envC) rhs (Level.substFn φ r.1.levelParams us)
      = mkLamsAV lds A := hlam
  refine blockRuleHRa_val hlam' (hok ρ).1 (hfit5 lds A hlam' hlen) ?_
  simp only [genBit]
  rw [genIhsAV_eq_R R hg hr hcA hrhs]
  exact genRule_residue mpC.base2 R hg hr hcA hrhs
    (fun d e hcbe => blockRecDenote_cross_CBNF h _ d e hcbe)
    (genIhFree_run R hg hfind hr hcA hrhs)
    (genHcallee R h hnd hr hleaf.closed hleafA) hread' hlam' hlen hpl hfl

/-- The equations at the skeleton's `ih` terms ARE the equations at the
stored rule's (`genIhsAV_eq_R` at every stored pair). -/
theorem genEqs_eq_R
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (ψ : Name → Nat) :
    (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ = (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsR mpC.base2.acval envC (tgtRs out).length out R.g R.rd ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ := by
  show blockIotaEqsAV _ _ _ _ _ _ _ _ = blockIotaEqsAV _ _ _ _ _ _ _ _
  refine blockIotaEqsAV_congr (fun c hc => rfl) fun c hc j hj => ?_
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  exact ⟨rfl, rfl, genIhsAV_eq_R R hg (List.getElem?_eq_getElem hc) hcA hrhs _ _ _ ψ, rfl, rfl⟩

/-- **`heqB`** (the skeleton's goal, at its `ih` terms). -/
theorem genRecHeqB (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) :
    ∀ (ψ : Name → Nat) (e : AnnotTerm), e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ →
        Term.bvarsBelow (tgtRs out).length e.erase := fun ψ e he =>
  genRecHeqB_R (mpC := mpC) hμ R hg h ψ e (by rw [← genEqs_eq_R (mpC := mpC) R hg h ψ]; exact he)

/-- **`heqV`** (the skeleton's goal): the equations are bit-valid at every
tuple (the typing of the tuple is not needed).  The frame, index
expressions and fired spine are the class side's (`hrowV`, the target
frame's grading); the `ih` terms are valid from their pieces'
validity at the base frame (`GenIhPiecesValid`) — the chain frame agrees
below the rule frame, the head is a variable; the residue is variables
only. -/
theorem genRecHeqV_R (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hrowV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsValid ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ∧
        ∀ ys : List V, SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
            (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
          (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
            AnnotValid V (consList ys ρ) e) ∧
          AnnotValid V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (hihV : GenIhPiecesValid (V := V) (envC := envC) mpC.base2.acval out R.g R.rd
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V),
      tup.length = (tgtRs out).length →
        (∀ (mm : Nat), mm < (tgtRs out).length →
          tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
          ∀ (e : AnnotTerm), e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsR mpC.base2.acval envC (tgtRs out).length out R.g R.rd ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ → AnnotValid V (consList tup ρ) e := by
  intro ψ ρ tup hlen _ e he
  rw [consList_eq_chainFrame hlen ρ]
  refine annotValid_blockIotaEqsAV (a := fun c => tup.getD c pt) (ρ := ρ)
    (fun c hc j hj => ?_) (fun c hc j hj ys hys => ?_) e he
  all_goals
    obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
    have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  · exact (hrowV ψ ρ c _ hr j cA rhs hcA hrhs).1
  · dsimp only at hys ⊢
    obtain ⟨hE, hM⟩ := (hrowV ψ ρ c _ hr j cA rhs hcA hrhs).2 ys hys
    refine ⟨hE, hM, fun v hv => ?_, genRb0_valid _ _ _ _ _⟩
    obtain ⟨cls, x, fvs, res, -, hrP, hRP, -, -, -, hop, hFld, -, -, hcx, hnF, -, hrhsE, hcl, -, -,
      hsl0⟩ := genFrameAt R hg hr hcA hrhs
    obtain ⟨hpl0, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
    have hfl : fvs.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ hop
    have hys' : ys.length = R.g.pre.length + x.nF := by
      have := hys.length_eq
      rw [List.length_append, blockRulePdomsAV_length hμ mpC h hr ψ, tgtFdomsAV,
        readOpenedDoms_length_eq, hFld, hfl] at this
      rw [this, hrP, hnF]
    rw [genIhsR, List.mem_map] at hv
    obtain ⟨q, hq, rfl⟩ := hv
    obtain ⟨hF, hA⟩ := hihV ψ ρ c j _ cA rhs hr hcA hrhs ys hys q hq
    rw [← hrhsE] at hcl
    have hb := genIhdAV_below mpC.base2 (g := R.g) (rd := R.rd) (φ := ψ) (c := c) (j := j) hcl
      (by rw [hcx]; omega) q hq
    rw [hcx] at hb ⊢
    unfold genIhAV
    refine annotValid_lamsApp (fun _ => by simp) q.2.1 (D := R.g.pre.length + x.nF)
      (σ := consList ys ρ) hb.1 (fun e he => ?_) (fun i hi => ?_) hF (fun bs hbs e he => ?_)
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
        rw [List.mem_range] at hl
        show _ < _
        omega
      · exact hb.2 e he
    · rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
        simp
      · exact hA bs hbs e he

/-- **`heqP`** (the skeleton's goal, at its `ih` terms). -/
theorem genRecHeqP (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {s : (Name → Nat) → Nat}
    (hsP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r → ∀ (ψ₁ ψ₂ : Name → Nat),
        (∀ (q : Name), q ∈ r.1.levelParams → ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂)
    (hrowP : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → ∀ (ψ₁ ψ₂ : Name → Nat),
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r →
        ∀ (ψ₁ ψ₂ : Name → Nat), (∀ (q : Name), q ∈ r.1.levelParams → ψ₁ q = ψ₂ q) →
          s ψ₁ = s ψ₂ ∧ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ₁ = (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ₂ := by
  intro i r hr ψ₁ ψ₂ hq
  obtain ⟨h1, h2⟩ := genRecHeqP_R (mpC := mpC) hμ R h hsP hrowP i r hr ψ₁ ψ₂ hq
  refine ⟨h1, ?_⟩
  rw [genEqs_eq_R (mpC := mpC) R hg h ψ₁, genEqs_eq_R (mpC := mpC) R hg h ψ₂]
  exact h2

/-- **`heqV`** (the skeleton's goal, at its `ih` terms). -/
theorem genRecHeqV (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F fe₁ env₁ (ConLeche.mkFEnv envC) pp.toBlockShape nb pos cvTas block
      ctorsAs out)
    (hg : ClassGenScoped R.g)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hrowV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsValid ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ∧
        ∀ ys : List V, SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
            (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
          (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
            AnnotValid V (consList ys ρ) e) ∧
          AnnotValid V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (hihV : GenIhPiecesValid (V := V) (envC := envC) mpC.base2.acval out R.g R.rd
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V),
      tup.length = (tgtRs out).length →
        (∀ (mm : Nat), mm < (tgtRs out).length →
          tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
          ∀ (e : AnnotTerm), e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) ψ → AnnotValid V (consList tup ρ) e := by
  intro ψ ρ tup hl ht e he
  rw [genEqs_eq_R (mpC := mpC) R hg h ψ] at he
  exact genRecHeqV_R hμ R hg h hrowV hihV ψ ρ tup hl ht e he

end Obligations

end ConLeche.Model
