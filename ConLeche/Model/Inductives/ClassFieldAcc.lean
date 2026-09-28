module

public import ConLeche.Model.Inductives.ClassFieldMono
public import ConLeche.Model.Inductives.HoleAccKit
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.Valid

public section

/-!
# The class check's flat derivation is accessible in the holes (PROOFPLAN T4, acc)

The twin of `ClassFieldMono.lean` for the closure witness (W): the flat
arms of the old positivity derivation's accessibility (`posD_acc`:
`const`, `pi`, `hole`, `teleNil`, `teleCons`), ported to the class
check's derivation `FieldD`.  The relation (`ClassHoleRelA`) relates
comparable frames — they satisfy the context and agree off the holes
`nP ..< hi` — and is symmetric with RICH holes at their full arity
(`ClassHoleQ`: the member holes and the container classes' holes of
`ClassHoleAr`).  Every hole is FREE here (PROOFPLAN §2.3: all holes of
the abstracted crest range over their whole spaces), so richness is the
free-hole one the consumers already prove (`accRel_rich`); no hole is
ever pinned to a fixed value and no frame-blindness is asked.

* `fieldD_acc` — every judgment reads accessibly (`ClassAccJ`): a
  field's reading is in the type regime and accessible with a bound of
  the level that reads only the non-hole positions its walk's output
  mentions (`ClassAccConcl`, the U4 uniformity the consumers need); a
  telescope's fields each so under the earlier ones, their values small
  (`PiAccThenC`), the result read at the relation;
* `classCtorWalk_acc` — one constructor of a class, the result's indices
  hole-free (`ResultIdxConst`).

The kits are reused unchanged (`Semantics/Inductives/HoleAcc.lean`,
`MentP`/`TeleSmall` of `NestPosAcc.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name CheckM NestCtx ClassInfo ClassField ClassJ FieldD fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The admissible items and the relation -/

/-- **The admissible items at depth `d`**: every hole of `ClassHoleAr`
at its full arity, seen as a bound position. -/
@[expose] def ClassHoleQ (ctx : NestCtx) (cls : List ClassInfo) (hi d : Nat) : Nat → Nat → Prop :=
  fun j n => ∃ i, i < d ∧ j = d - 1 - i ∧ ClassHoleAr ctx cls hi i n

/-- One binder down, the admissible items are the same holes. -/
theorem shiftQ_classHoleQ {ctx : NestCtx} {cls : List ClassInfo} {hi d : Nat} (hd : hi ≤ d)
    (j n : Nat) : shiftQ (ClassHoleQ ctx cls hi d) j n ↔ ClassHoleQ ctx cls hi (d + 1) j n := by
  cases j with
  | zero =>
    simp only [shiftQ, false_iff]
    rintro ⟨i, hi', hj, har⟩
    have := har.2.1
    omega
  | succ j =>
    simp only [shiftQ]
    constructor
    · rintro ⟨i, hi', rfl, har⟩
      exact ⟨i, by omega, by omega, har⟩
    · rintro ⟨i, hi', hj, har⟩
      exact ⟨i, by omega, by omega, har⟩

/-- **The class hole relation for accessibility** at depth `d`: related
frames satisfy the context and agree off the holes; the relation is
symmetric and its holes rich at their full arity. -/
structure ClassHoleRelA (ctx : NestCtx) (cls : List ClassInfo) (hi d : Nat) (Δa : List AnnotTerm)
    (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP hi)
  symm : R.Symm
  rich : RichOn (ClassHoleQ ctx cls hi d) R

/-- **Under a binder** whose domain carries its values to every larger
related frame: the relation one level deeper. -/
theorem ClassHoleRelA.underBoth {ctx : NestCtx} {cls : List ClassInfo} {hi d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (h : ClassHoleRelA ctx cls hi d Δa R) (hd : hi ≤ d)
    (ta : AnnotTerm)
    (htr : ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe (ClassHoleQ ctx cls hi d) ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta) :
    ClassHoleRelA ctx cls hi (d + 1) (ta :: Δa) (R.underBoth ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 hx'⟩
  agree := by
    intro σ σ' hr i hi'
    exact (h.agree.underBoth ta) σ σ' hr i fun hs => hi' (holeP_succ i hs)
  symm := h.symm.underBoth ta
  rich := RichOn.congrQ (shiftQ_classHoleQ hd) (h.rich.underBoth htr)

/-! ## What a field and a telescope prove -/

/-- **What a field proves of its reading**: the type regime, and
accessibility with a bound of the level reading only the non-hole
positions its walk's output `nf` mentions (or a parameter position). -/
@[expose] def ClassAccConcl (w : Nat) (ctx : NestCtx) (cls : List ClassInfo) (hi dep : Nat)
    (nf : Expr) (R : FrameRel V) (ea : AnnotTerm) : Prop :=
  TypeReg R ea ∧ ∃ A, AccOn w (ClassHoleQ ctx cls hi dep) R A ea ∧ SizeOn w R A ∧
    InvOn (MentP ctx.nP hi dep nf) A

/-- **The first `n` Π-domains of a reading accessible**, each under the
earlier ones (`underBoth`), with a bound of the level reading only the
non-hole positions of its walk's output (`nds`, one per field, at their
depths from `d`), and `Q` of the relation and the reading below them. -/
@[expose] def PiAccThenC (w : Nat) (ctx : NestCtx) (cls : List ClassInfo) (hi : Nat)
    (Q : FrameRel V → AnnotTerm → Prop) :
    Nat → Nat → List Expr → FrameRel V → AnnotTerm → Prop
  | 0, _, _, R, r => Q R r
  | n + 1, d, nd :: nds, R, .pi _ _ A B =>
    (∃ Af, AccOn w (ClassHoleQ ctx cls hi d) R Af A ∧ SizeOn w R Af ∧
      InvOn (MentP ctx.nP hi d nd) Af) ∧
      PiAccThenC w ctx cls hi Q n (d + 1) nds (R.underBoth A) B
  | _ + 1, _, _, _, _ => False

theorem PiAccThenC.mono {w : Nat} {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat}
    {Q Q' : FrameRel V → AnnotTerm → Prop} (hQ : ∀ R r, Q R r → Q' R r) :
    ∀ (n d : Nat) (nds : List Expr) (R : FrameRel V) (r : AnnotTerm),
      PiAccThenC w ctx cls hi Q n d nds R r → PiAccThenC w ctx cls hi Q' n d nds R r
  | 0, _, _, R, r, h => hQ R r h
  | n + 1, d, _ :: nds, _, .pi _ _ _ B, h => ⟨h.1, PiAccThenC.mono hQ n (d + 1) nds _ B h.2⟩
  | _ + 1, _, [], _, _, h => h.elim
  | _ + 1, _, _ :: _, _, .bvar _, h | _ + 1, _, _ :: _, _, .sort _, h
  | _ + 1, _, _ :: _, _, .const _ _, h | _ + 1, _, _ :: _, _, .app _ _, h
  | _ + 1, _, _ :: _, _, .lam _ _ _, h | _ + 1, _, _ :: _, _, .eqE _ _, h
  | _ + 1, _, _ :: _, _, .fst _, h | _ + 1, _, _ :: _, _, .snd _, h
  | _ + 1, _, _ :: _, _, .prf, h => h.elim

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (w : Nat)
  (ctx : NestCtx) (cls : List ClassInfo) (hi : Nat)

/-- **What a class-check derivation proves** of its judgment's reading,
for accessibility. -/
@[expose] def ClassAccJ : ClassJ → Prop
  | .field dep _ e _ nf =>
    hi ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → ClassHoleRelA ctx cls hi dep Δa R → ClassAccConcl w ctx cls hi dep nf R ea
  | .tele base nF j cur _ nds res =>
    hi ≤ base + j → Frame (base + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (base + j) Δa cur →
      denoteMeta mp.base2.acval env φ (base + j) cur = some ca → Graded V Δa ca →
      ClassHoleRelA ctx cls hi (base + j) Δa R → TeleSmall w nF R ca →
      PiAccThenC w ctx cls hi (ResultAt mp.base2 φ ctx.nP hi (base + j + nF) res)
        nF (base + j) (nds.map (·.1)) R ca

end Motive

variable {φ : Name → Nat}

/-! ## The whnf step and a hole leaf -/

/-- **The whnf step** of every field rule: the reduct reads as the term,
so it is enough to prove the reduct's reading accessible. -/
theorem classAcc_of_whnf {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e wt : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok wt) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denoteMeta mp.base2.acval env φ dep e = some ea)
    (hgr : Graded V Δa ea) (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    {w : Nat} {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat} {nf : Expr}
    (kont : Frame dep wt → CtxOkP mp.base2 φ dep Δa wt → ∀ wa,
      denoteMeta mp.base2.acval env φ dep wt = some wa → Graded V Δa wa →
      ClassAccConcl w ctx cls hi dep nf R wa) :
    ClassAccConcl w ctx cls hi dep nf R ea := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok wt := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  obtain ⟨hTR, A, hA, hsz, hinv⟩ := kont hfrw (hC.of_subset hsub) wa hwa hgw
  exact ⟨TypeReg.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) hTR,
    A, AccOn.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) hA, hsz, hinv⟩

/-- **A hole leaf is accessible** (the bound `{pt}`) and in the type
regime (richness). -/
theorem classAcc_holeLeaf {w : Nat} {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    {ctx : NestCtx} {cls : List ClassInfo} {hi dep : Nat} {wt nf : Expr} {i : Nat} {ty : Expr}
    (hhi : hi ≤ dep) (hfn : wt.getAppFn = .fvar i ty)
    (har : ClassHoleAr ctx cls hi i wt.getAppArgs.length)
    (hfree : ∀ x ∈ wt.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false)
    (hws : Expr.WScoped dep wt)
    {Δa : List AnnotTerm} {wa : AnnotTerm} {R : FrameRel V}
    (hwa : denoteMeta mp.base2.acval env φ dep wt = some wa)
    (hR : ClassHoleRelA ctx cls hi dep Δa R) :
    ClassAccConcl w ctx cls hi dep nf R wa := by
  have hspine := Expr.mkAppN_getApp wt
  rw [hfn] at hspine
  rw [← hspine] at hwa hws
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
  rw [denoteMeta_fvar] at hfa
  cases hfa
  have hwsargs := (wScoped_mkAppN _ hws).2
  have hlenv := DenoteMetaSpine.length_eq hsp
  have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
  have hQ : ClassHoleQ ctx cls hi dep (dep - 1 - i) vs.length := by
    refine ⟨i, ?_, rfl, by rw [← hlenv]; exact har⟩
    have := har.2.1
    omega
  exact ⟨TypeReg.holeApp hR.rich hR.symm hQ hvs, _, AccOn.holeApp hQ hvs,
    SizeOn.const (unitSet_mem_univ w), InvOn.const _ _⟩

/-! ## THE INDUCTION -/

/-- **THE FLAT DERIVATION IS ACCESSIBLE** (PROOFPLAN T4): every judgment
of a class-check derivation reads accessibly in ALL the holes, at a
positive level, by induction on the derivation. -/
theorem fieldD_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx}
    {cls : List ClassInfo} {hi F : Nat}
    (hparL : ctx.params.length = ctx.nP)
    (hparF : ∀ x ∈ ctx.params, x.nestOcc ctx.names ctx.nP hi = false) :
    ∀ {j : ClassJ}, FieldD (fueledOps .verified F) env ctx cls hi j →
      ClassAccJ mp φ w ctx cls hi j := by
  intro j h
  induction h with
  | @const dep kb e wt hw' hocc =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classAcc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ => ?_
    have hco : ConstOn R wa := ConstOn.of_noBVar hR.agree
      (denoteMeta_noBVar_of_nestOcc dep wt hfrw.1 hhi hocc hwa)
    exact ⟨hco.typeReg, _, hco.accOn, SizeOn.const (empty_mem_univ w), InvOn.const _ _⟩
  | @pi dep kb e a b bm k nb hw' hocc ha hb ihb =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classAcc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hholes : NoBVar (holeP dep ctx.nP hi) ta :=
      denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi ha hta
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree hholes
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    obtain ⟨hTRb, Ab, hAb, hszb, hinvb⟩ := ihb (by omega)
      (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd) hCop hba hgB
      (hR.underBoth hhi ta (transfer_of_constOn hA))
    -- at a `Prop` codomain the body is truth-valued (the grading)
    have hB0 : pwBit φ bm.pw = 0 → ∀ σ σ', R.underBoth ta σ σ' →
        interp V σ ba ∈ˢ (univZero : V) ∧ interp V σ' ba ∈ˢ (univZero : V) := by
      rintro hv0 _ _ ⟨x, ρ, ρ', rfl, rfl, hRr, hx, hx'⟩
      have hval : ∀ σ, Sat V Δa σ → x ∈ˢ interp V σ ta →
          interp V (cons x σ) ba ∈ˢ (univZero : V) := by
        intro σ hσ hxσ
        have := (hgw σ hσ).2
        rw [AnnotValid_pi] at this
        exact this.2.2 hv0 x hxσ
      exact ⟨hval ρ (hR.dom ρ ρ' hRr).1 hx, hval ρ' (hR.dom ρ ρ' hRr).2 hx'⟩
    refine ⟨TypeReg.pi 0 _ hA hTRb hB0, ?_⟩
    by_cases hv0 : pwBit φ bm.pw = 0
    · -- hole-free: the body is
      have hco : ConstOn R (.pi 0 (pwBit φ bm.pw) ta ba) := ConstOn.pi 0 _ hA (hTRb (hB0 hv0))
      exact ⟨_, hco.accOn, SizeOn.const (empty_mem_univ w), InvOn.const _ _⟩
    · refine ⟨_, AccOn.pi hw 0 hv0 hA
        (AccOn.congrQ (fun i n => (shiftQ_classHoleQ hhi i n).symm) hAb),
        SizeOn.pi hw hA hszb, InvOn.pi ?_ (InvOn.mono hinvb fun i hi' => mentP_body i hi')⟩
      refine NoBVar.mono (fun i hi' hn => hi' (Or.inl hn))
        (noBVar_not_mentNH hws.1 hbb.1 hholes (fun s _ hs => ?_) hta)
      simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hs
      exact hs.1
  | @memberHole dep kb e wt i ty c ci hw' hocc hfn hlo hhi' hc hmem hpar hlen hfree =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classAcc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ => ?_
    have hall := memberHole_args hparL hparF hpar hfree
    exact classAcc_holeLeaf hhi hfn
      (memberHole_ar hocc hfn hhi' hc hmem hlen hall.1 hall.2) hall.2 hfrw.1 hwa hR
  | @classHole dep kb e wt i ty hty c ci hw' hocc hfn hout hc hhole hlen hfree =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classAcc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ => ?_
    exact classAcc_holeLeaf hhi hfn (classHole_ar hocc hfn hout hc hhole hlen hfree) hfree
      hfrw.1 hwa hR
  | teleNil =>
    intro _ hfr Δa ca R _ hca _ hR _
    exact ⟨hR.agree, hca, hfr.1⟩
  | @teleCons base nF j a b bm k nd ks nds res ha hb iha ihb =>
    intro hhi hfr Δa ca R hC hca hgr hR hsm
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    obtain ⟨-, Af, hAf, hszf, hinvf⟩ :=
      iha hhi ⟨hws.1, hbb.1, hLa⟩ hC.forallE_ty hta hgA hR
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    have hR' := hR.underBoth hhi ta (transfer_of_accOn hAf hsm.1)
    have hPi := ihb (by omega) hfr' hCop hba hgB
      (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR') hsm.2
    rw [show base + (j + 1) + nF = base + j + (nF + 1) by omega,
      show base + (j + 1) = base + j + 1 by omega] at hPi
    exact ⟨⟨Af, hAf, hszf, hinvf⟩, hPi⟩

/-! ## One constructor of a class -/

/-- **One constructor of a class is accessible** (at a positive level):
every field's reading accessible under the earlier ones along the
accessibility relation (the fields' values small), each bound reading
only its field's output's non-hole positions, the result's indices
(after the parameters, at a member's constructor) hole-free. -/
theorem classCtorWalk_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {holes : List Expr}
    {cls : List ClassInfo} {hi F nF : Nat} {c : ClassInfo} {cv : ConLeche.ConstantVal}
    {crest cur : Expr} {ks : List ClassField} {nds : List (Expr × ConLeche.BinderMeta)}
    (hwk : ConLeche.ClassCtorWalk (fueledOps .verified F) env ctx holes cls hi c cv nF crest ks nds
      cur)
    (hparL : ctx.params.length = ctx.nP)
    (hparF : ∀ x ∈ ctx.params, x.nestOcc ctx.names ctx.nP hi = false)
    (hfr : Frame hi crest) {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ hi Δa crest)
    (hca : denoteMeta mp.base2.acval env φ hi crest = some ca) (hgr : Graded V Δa ca)
    (hR : ClassHoleRelA ctx cls hi hi Δa R) (hsm : TeleSmall w nF R ca) :
    PiAccThenC w ctx cls hi (ResultIdxConst (if c.member.isSome then ctx.nP else 0)) nF hi
      (nds.map (·.1)) R ca := by
  have hhead : ∃ i ty, cur.getAppFn = .fvar i ty := by
    rcases hwk.res with ⟨t, ty, -, h⟩ | ⟨-, h, hty, ty, -, h'⟩
    · exact ⟨_, ty, h⟩
    · exact ⟨h, ty, h'⟩
  have hPi := fieldD_acc mp hin hw hparL hparF hwk.tele (by simp) hfr hC hca hgr hR hsm
  simp only [Nat.add_zero] at hPi
  exact PiAccThenC.mono (fun _ _ h => resultIdxConst_of_resultAtC (Nat.le_add_right _ _) hhead
    hwk.resIdx h) nF hi _ R ca hPi

end ConLeche.Model
