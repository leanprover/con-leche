module

public import ConLeche.Model.Inductives.HoleKit
public import ConLeche.Verify.Inductives.ClassInv
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The class check's flat derivation is monotone in the holes (PROOFPLAN T4, mono)

The flat arms of the old positivity derivation's monotonicity
(`posD_mono`: `const`, `pi`, `hole`, `teleNil`, `teleCons`), ported to
the class check's derivation `FieldD` (`Verify/Inductives/ClassInv.lean`).
No frames, no containers: every class occurrence is a HOLE when the whnf
runs (R1), so a field's reading is monotone along ONE relation in which
every hole — the members' (`nP ..< hiAt 0`, applied to the parameters
then the indices) and the classes' (`hiAt 0 ..< hi`, applied to the
indices) — grows at its full arity (`ClassHoleRel`).  Which class a hole
belongs to and its arity are read off the class list (`ClassHoleAr`),
exactly as the derivation's `memberHole`/`classHole` rules record them.

* `fieldD_mono` — every judgment reads monotonically (`ClassMonoJ`):
  a field's reading is `MonoOn` the relation, a telescope's fields are
  each monotone under the earlier ones (`PiPosThen`), the result read at
  the relation;
* `classCtorWalk_mono` — one constructor of a class (a member's or a
  container instance's) as the class facts consume it: every field
  monotone under the earlier ones, the result's indices hole-free
  (`ResultIdxConst`, after the parameters at a member's constructor).

The kits are reused unchanged (`Semantics/Inductives/HoleMono.lean`);
the whnf step is `red_sound`, legal because the whnf'd term is the
abstracted one and typed in the holes' context (T1).
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

/-! ## The holes and the relation -/

/-- **Hole variable `i` has full arity `n`** (`hi` the end of the holes):
a member's hole (`nP ≤ i < hiAt 0`, the member of some class) at the
parameters plus that class's indices, or a container class's hole (at or
above `hiAt 0`) at its indices — the two hole rules of `FieldD`. -/
@[expose] def ClassHoleAr (ctx : NestCtx) (cls : List ClassInfo) (hi i n : Nat) : Prop :=
  ctx.nP ≤ i ∧ i < hi ∧ ∃ (c : Nat) (ci : ClassInfo), cls[c]? = some ci ∧
    ((i < ctx.hiAt 0 ∧ ci.member = some (i - ctx.nP) ∧ n = ctx.nP + ci.nIdx) ∨
      (ctx.hiAt 0 ≤ i ∧ (∃ hty, ci.hole = some (.fvar i hty)) ∧ n = ci.nIdx))

/-- **The class hole relation** at depth `d`: related frames satisfy the
context, agree off the hole positions `nP ..< hi`, and every hole grows
at its full arity. -/
structure ClassHoleRel (ctx : NestCtx) (cls : List ClassInfo) (hi d : Nat) (Δa : List AnnotTerm)
    (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP hi)
  hole : ∀ i n, ClassHoleAr ctx cls hi i n → HoleOn R (d - 1 - i) n

/-- **Under a positive binder** the relation is the same one level
deeper. -/
theorem ClassHoleRel.under {ctx : NestCtx} {cls : List ClassInfo} {hi d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (h : ClassHoleRel ctx cls hi d Δa R) (hd : hi ≤ d)
    {ta : AnnotTerm} (hA : MonoOn R ta) :
    ClassHoleRel ctx cls hi (d + 1) (ta :: Δa) (R.under ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 (hA ρ ρ' hR x hx)⟩
  agree := by
    intro σ σ' hr i hi'
    exact (h.agree.under ta) σ σ' hr i fun hs => hi' (holeP_succ i hs)
  hole := by
    intro i n har
    have hlt : i < d := by have := har.2.1; omega
    rw [show d + 1 - 1 - i = d - 1 - i + 1 by omega]
    exact (h.hole i n har).under ta

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (ctx : NestCtx)
  (cls : List ClassInfo) (hi : Nat)

/-- **What a class-check derivation proves** of its judgment's reading. -/
@[expose] def ClassMonoJ : ClassJ → Prop
  | .field dep _ e _ _ =>
    hi ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → ClassHoleRel ctx cls hi dep Δa R → MonoOn R ea
  | .tele base nF j cur _ _ res =>
    hi ≤ base + j → Frame (base + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (base + j) Δa cur → denoteMeta mp.base2.acval env φ (base + j) cur = some ca →
      Graded V Δa ca → ClassHoleRel ctx cls hi (base + j) Δa R →
      PiPosThen (ResultAt mp.base2 φ ctx.nP hi (base + j + nF) res) nF R ca

end Motive

variable {φ : Name → Nat}

/-! ## The whnf step -/

/-- **The whnf step** of every field rule: the reduct reads as the term,
so it is enough to prove the reduct's reading monotone. -/
theorem classMono_of_whnf {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e w : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok w) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denoteMeta mp.base2.acval env φ dep e = some ea)
    (hgr : Graded V Δa ea) (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (k : Frame dep w → CtxOkP mp.base2 φ dep Δa w → ∀ wa,
      denoteMeta mp.base2.acval env φ dep w = some wa → Graded V Δa wa → MonoOn R wa) :
    MonoOn R ea := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok w := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  exact MonoOn.of_eqOn (Q := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ)
    (k hfrw (hC.of_subset hsub) wa hwa hgw)

/-! ## The hole rules' leaves -/

theorem classNestOcc_mkAppN {names : List Name} {lo hi : Nat} :
    ∀ (as : List Expr) (f : Expr),
      (Expr.mkAppN f as).nestOcc names lo hi = (f.nestOcc names lo hi || as.any (·.nestOcc names lo hi))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).nestOcc names lo hi = _
    rw [classNestOcc_mkAppN as (.app f a)]
    simp [Expr.nestOcc, Bool.or_assoc]

/-- An occurrence at a variable-headed spine with occurrence-free
arguments is the head: a hole variable. -/
theorem holeHead_bounds {names : List Name} {lo hi : Nat} {w : Expr} {i : Nat} {ty : Expr}
    (hocc : w.nestOcc names lo hi = true) (hfn : w.getAppFn = .fvar i ty)
    (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc names lo hi = false) : lo ≤ i ∧ i < hi := by
  have hspine := Expr.mkAppN_getApp w
  rw [hfn] at hspine
  rw [← hspine, classNestOcc_mkAppN] at hocc
  have hany : w.getAppArgs.any (·.nestOcc names lo hi) = false :=
    List.any_eq_false.mpr fun x hx => by simp [hfree x hx]
  rw [hany, Bool.or_false] at hocc
  simpa [Expr.nestOcc] using hocc

/-- A member hole's arguments: the parameters (`nP` many, hole-free) and
hole-free indices. -/
theorem memberHole_args {ctx : NestCtx} {hi : Nat} {w : Expr}
    (hparL : ctx.params.length = ctx.nP)
    (hparF : ∀ x ∈ ctx.params, x.nestOcc ctx.names ctx.nP hi = false)
    (hpar : w.getAppArgs.take ctx.nP = ctx.params)
    (hfree : ∀ x ∈ w.getAppArgs.drop ctx.nP, x.nestOcc ctx.names ctx.nP hi = false) :
    ctx.nP ≤ w.getAppArgs.length ∧ ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 := congrArg List.length hpar
    rw [List.length_take, hparL] at h1
    omega
  · rw [← List.take_append_drop ctx.nP w.getAppArgs, hpar] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hparF x hx
    · exact hfree x hx

/-- **The member-hole rule's leaf** is a hole of its full arity. -/
theorem memberHole_ar {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat} {w : Expr} {i : Nat}
    {ty : Expr} {c : Nat} {ci : ClassInfo}
    (hocc : w.nestOcc ctx.names ctx.nP hi = true) (hfn : w.getAppFn = .fvar i ty)
    (hhi' : i < ctx.hiAt 0) (hc : cls[c]? = some ci) (hmem : ci.member = some (i - ctx.nP))
    (hlen : (w.getAppArgs.drop ctx.nP).length = ci.nIdx)
    (hle : ctx.nP ≤ w.getAppArgs.length)
    (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false) :
    ClassHoleAr ctx cls hi i w.getAppArgs.length := by
  obtain ⟨hlo, hhi⟩ := holeHead_bounds hocc hfn hfree
  refine ⟨hlo, hhi, c, ci, hc, Or.inl ⟨hhi', hmem, ?_⟩⟩
  rw [← hlen, List.length_drop]
  omega

/-- **The class-hole rule's leaf** is a hole of its full arity. -/
theorem classHole_ar {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat} {w : Expr} {i : Nat}
    {ty hty : Expr} {c : Nat} {ci : ClassInfo}
    (hocc : w.nestOcc ctx.names ctx.nP hi = true) (hfn : w.getAppFn = .fvar i ty)
    (hout : ¬(ctx.nP ≤ i ∧ i < ctx.hiAt 0)) (hc : cls[c]? = some ci)
    (hhole : ci.hole = some (.fvar i hty)) (hlen : w.getAppArgs.length = ci.nIdx)
    (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false) :
    ClassHoleAr ctx cls hi i w.getAppArgs.length := by
  obtain ⟨hlo, hhi⟩ := holeHead_bounds hocc hfn hfree
  exact ⟨hlo, hhi, c, ci, hc, Or.inr ⟨by omega, ⟨hty, hhole⟩, hlen⟩⟩

/-! ## A hole leaf -/

/-- **A hole leaf reads monotonically**: the whnf'd term is a hole
variable of full arity `n` applied to hole-free arguments. -/
theorem classMono_holeLeaf {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env} {ctx : NestCtx}
    {cls : List ClassInfo} {hi dep : Nat} {w : Expr} {i : Nat} {ty : Expr}
    (hhi : hi ≤ dep) (hfn : w.getAppFn = .fvar i ty) (har : ClassHoleAr ctx cls hi i w.getAppArgs.length)
    (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false) (hws : Expr.WScoped dep w)
    {Δa : List AnnotTerm} {wa : AnnotTerm} {R : FrameRel V}
    (hwa : denoteMeta mp.base2.acval env φ dep w = some wa) (hR : ClassHoleRel ctx cls hi dep Δa R) :
    MonoOn R wa := by
  have hspine := Expr.mkAppN_getApp w
  rw [hfn] at hspine
  rw [← hspine] at hwa hws
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
  rw [denoteMeta_fvar] at hfa
  cases hfa
  have hwsargs := (wScoped_mkAppN _ hws).2
  have hlenv := DenoteMetaSpine.length_eq hsp
  have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
  have hh := hR.hole i _ har
  rw [hlenv] at hh
  exact MonoOn.holeApp hh hvs

/-! ## THE INDUCTION -/

/-- **THE FLAT DERIVATION IS MONOTONE** (PROOFPLAN T4): every judgment of
a class-check derivation reads monotonically in ALL the holes, by
induction on the derivation.  `hparL`/`hparF`: the block's parameter
terms (a member hole's first arguments) are `nP` many and mention no
hole. -/
theorem fieldD_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {cls : List ClassInfo} {hi F : Nat}
    (hparL : ctx.params.length = ctx.nP)
    (hparF : ∀ x ∈ ctx.params, x.nestOcc ctx.names ctx.nP hi = false) :
    ∀ {j : ClassJ}, FieldD (fueledOps .verified F) env ctx cls hi j →
      ClassMonoJ mp φ ctx cls hi j := by
  intro j h
  induction h with
  | @const dep kb e w hw hocc =>
    intro hhi hfr Δa ea R hC hea hgr hR
    exact classMono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ =>
      (ConstOn.of_noBVar hR.agree (denoteMeta_noBVar_of_nestOcc dep w hfrw.1 hhi hocc hwa)).monoOn
  | @pi dep kb e a b bm k nb hw hocc ha hb ihb =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classMono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree
      (denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi ha hta)
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    exact MonoOn.pi 0 _ hA (ihb (by omega) (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd)
      hCop hba hgB (hR.under hhi hA.monoOn))
  | @memberHole dep kb e w i ty c ci hw hocc hfn hlo hhi' hc hmem hpar hlen hfree =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classMono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ => ?_
    have hall := memberHole_args hparL hparF hpar hfree
    exact classMono_holeLeaf hhi hfn
      (memberHole_ar hocc hfn hhi' hc hmem hlen hall.1 hall.2) hall.2 hfrw.1 hwa hR
  | @classHole dep kb e w i ty hty c ci hw hocc hfn hout hc hhole hlen hfree =>
    intro hhi hfr Δa ea R hC hea hgr hR
    refine classMono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ => ?_
    exact classMono_holeLeaf hhi hfn (classHole_ar hocc hfn hout hc hhole hlen hfree) hfree
      hfrw.1 hwa hR
  | teleNil =>
    intro _ hfr Δa ca R _ hca _ hR
    exact ⟨hR.agree, hca, hfr.1⟩
  | @teleCons base nF j a b bm k nd ks nds res ha hb iha ihb =>
    intro hhi hfr Δa ca R hC hca hgr hR
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    have hA := iha hhi ⟨hws.1, hbb.1, hLa⟩ hC.forallE_ty hta hgA hR
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    have hrest := ihb (by omega) hfr' hCop hba hgB
      (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR.under hhi hA)
    rw [show base + j + (nF + 1) = base + (j + 1) + nF by omega]
    exact ⟨hA, hrest⟩


/-! ## One constructor of a class -/

/-- **The result's reading, its indices constant** along the relation: a
variable-headed result whose arguments after the first `n` are
hole-free, read at a depth above the holes. -/
theorem resultIdxConst_of_resultAtC {m : EnvModel V env} {lo hi D n : Nat} {names : List Name}
    {res : Expr} (hD : hi ≤ D) (hhead : ∃ i ty, res.getAppFn = .fvar i ty)
    (hok : (res.getAppArgs.drop n).all (fun a => !a.nestOcc names lo hi) = true)
    {R : FrameRel V} {r : AnnotTerm} (hres : ResultAt m φ lo hi D res R r) :
    ResultIdxConst n R r := by
  obtain ⟨hag, hrd, hws⟩ := hres
  obtain ⟨i0, ty0, hfn⟩ := hhead
  have hspine := Expr.mkAppN_getApp res
  rw [← hspine, hfn] at hrd hws
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hrd
  rw [denoteMeta_fvar] at hfa
  cases hfa
  rw [← List.take_append_drop n res.getAppArgs] at hsp
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
  refine ⟨_, vs₁ ++ vs₂, rfl, ?_⟩
  have hl₁ : vs₁.length ≤ n := by
    rw [← DenoteMetaSpine.length_eq hsp₁, List.length_take]; omega
  intro v hv
  simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
  have hdrop : (vs₁ ++ vs₂).drop n ⊆ vs₂ := by
    intro x hx
    rw [List.drop_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.drop_eq_nil_of_le hl₁] at hx; exact nomatch hx
    · exact List.mem_of_mem_drop hx
  have hwsargs := (wScoped_mkAppN _ hws).2
  refine constOn_spine hag hD hsp₂ (fun a ha => ⟨?_, hok a ha⟩) v (hdrop hv)
  exact hwsargs a (List.mem_of_mem_drop ha)

/-- **One constructor of a class is positive** (the class facts'
premise, in the constructor type's own Π-form): every field's reading
monotone under the earlier ones along the class hole relation, the
result's indices (after the parameters, at a member's constructor)
hole-free. -/
theorem classCtorWalk_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {holes : List Expr} {cls : List ClassInfo}
    {hi F nF : Nat} {c : ClassInfo} {cv : ConLeche.ConstantVal} {crest cur : Expr}
    {ks : List ClassField} {nds : List (Expr × ConLeche.BinderMeta)}
    (hwk : ConLeche.ClassCtorWalk (fueledOps .verified F) env ctx holes cls hi c cv nF crest ks nds
      cur)
    (hparL : ctx.params.length = ctx.nP)
    (hparF : ∀ x ∈ ctx.params, x.nestOcc ctx.names ctx.nP hi = false)
    (hfr : Frame hi crest) {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ hi Δa crest)
    (hca : denoteMeta mp.base2.acval env φ hi crest = some ca) (hgr : Graded V Δa ca)
    (hR : ClassHoleRel ctx cls hi hi Δa R) :
    PiPosThen (ResultIdxConst (if c.member.isSome then ctx.nP else 0)) nF R ca := by
  have hhead : ∃ i ty, cur.getAppFn = .fvar i ty := by
    rcases hwk.res with ⟨t, ty, -, h⟩ | ⟨-, h, hty, ty, -, h'⟩
    · exact ⟨_, ty, h⟩
    · exact ⟨h, ty, h'⟩
  have hPi := fieldD_mono mp hin hparL hparF hwk.tele (by simp) hfr hC hca hgr hR
  simp only [Nat.add_zero] at hPi
  exact PiPosThen.mono (fun _ _ h => resultIdxConst_of_resultAtC (Nat.le_add_right _ _) hhead
    hwk.resIdx h) nF R ca hPi

end ConLeche.Model
