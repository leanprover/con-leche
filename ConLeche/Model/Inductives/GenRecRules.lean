module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecAssembly

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

end ConLeche.Model
