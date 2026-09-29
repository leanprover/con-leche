module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Abstract
import ConLeche.Verify.Extend.Inversions
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Inductives.TargetResidue

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

theorem openLamsM_length :
    ∀ (n : Nat) {e : Expr} {j : Nat} {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr},
      openLamsM n e j = some (bs, r) → bs.length = n
  | 0, e, j, bs, r, h => by
    simp only [openLamsM, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, .lam dom body m, j, bs, r, h => by
    simp only [openLamsM] at h
    cases hi : openLamsM n (body.instantiate1 (.fvar j dom)) (j + 1) with
    | none => rw [hi] at h; exact nomatch h
    | some o =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, List.length_cons, openLamsM_length n (bs := o.1) (r := o.2) (by rw [hi])]
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h
  | _ + 1, .forallE _ _ _, _, _, _, h | _ + 1, .letE _ _ _, _, _, _, h
  | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h => nomatch h

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
        (R.g.nP + R.g.slots.length + x.nF) gen.resetMeta rhs) := by
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
theorem readD_below (m : EnvModel V env) {φ : Name → Nat} {D : Nat} {e : Expr}
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
    refine ⟨readD_below m (Or.inl (by simpa using h 0 b rfl)) hj,
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
    ∀ q ∈ genIhdAV m.acval env out g rd φ c j,
      LamDomsBelow (g.pre.length + (genCtorAt g rd c j).nF) q.2.1 ∧
      ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        Term.bvarsBelow (g.pre.length + (genCtorAt g rd c j).nF + q.2.1.length) e.erase := by
  intro q hq
  simp only [genIhdAV, List.mem_map, List.mem_range] at hq
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
    exact readD_below m (Or.inl (hcargs a ((List.dropLast_sublist _).subset ha))) (by omega)
  · simp only [List.mem_singleton] at he
    subst he
    refine readD_below m ?_ (by omega)
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
    obtain ⟨hf, hb⟩ := annotate_syntax (by
      rw [← ConLeche.fueledOps_annotate]; exact RR.hann) RR.hfv RR.hbv
    exact ⟨Expr.WScoped.of_not_hasFvar hf, hb⟩
  have hsl := genRule_slots_pos hgen
  refine ⟨cls, x, fvs, res, hc, hrP, hRP, hMaj, hCt, hCrest, hop, ?_, ?_, hB, hcx, hnF, hxmem,
    hrhsE, hcl, (hg.tyD cls x hxmem).mono (by omega),
    fun e he => (hg.ds cls e he).mono (by omega), hsl⟩
  · rw [tgtFieldFvs, hCt, hCrest, hRP, hop]; rfl
  · rw [tgtCbody, hCt, hCrest, hRP, hop]; rfl

end Frame

end ConLeche.Model
