module

import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndDomGrade
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Abstract
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.InstList
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.BlockRecInv
public import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.StructFrame
import ConLeche.Verify.BetaGate

public section

/-!
# The target call's kit (lane RECLIB, B3 (e))

Generic facts the call's typing (`TargetCallCore.lean`) is read with:

* `targetWhnfPis_sem` — a field's telescope read through whnf
  (`targetWhnfPis`) keeps the reading's value at every satisfying
  valuation, is framed, reads and is graded;
* `interp_mkPisAV_congr` — a Π-tower's value reads only the bits and
  the domains of its binder data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A Π-tower reads only its bits and domains -/

theorem interp_mkPisAV_congr {X : AnnotTerm} :
    ∀ {ds ds' : List (Nat × Nat × AnnotTerm)}, ds.map (·.2) = ds'.map (·.2) →
      ∀ ρ : Nat → V, interp V ρ (mkPisAV ds X) = interp V ρ (mkPisAV ds' X)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | d :: ds, d' :: ds', h, ρ => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    show interp V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV ds X))
      = interp V ρ (.pi d'.1 d'.2.1 d'.2.2 (mkPisAV ds' X))
    rw [interp_pi, interp_pi, show d.2 = d'.2 from h1]
    exact piR_congr fun x _ => interp_mkPisAV_congr h2 _

/-! ## Scoping of an opened binder body -/

/-- Every `fvar d` node of `e` carries `ty` when every leaf at `d` does. -/
theorem fvarConsistent_of_leaves {d : Nat} {ty : Expr} :
    ∀ (e : Expr), (∀ l ∈ e.fvarLeaves, l.1 = d → l.2 = ty) → Expr.fvarConsistent d ty e := by
  intro e
  induction e with
  | fvar idx ty' _ =>
    intro h
    simp only [Expr.fvarConsistent]
    intro hidx
    exact h (idx, ty') (by simp [Expr.fvarLeaves]) hidx
  | app f a ihf iha =>
    intro h
    simp only [Expr.fvarConsistent]
    exact ⟨ihf fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      iha fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | lam t b _ iht ihb =>
    intro h
    simp only [Expr.fvarConsistent]
    exact ⟨iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | forallE t b _ iht ihb =>
    intro h
    simp only [Expr.fvarConsistent]
    exact ⟨iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.fvarConsistent]
    exact ⟨iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihv fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.fvarConsistent]
    exact ih fun l hl => h l (by simpa [Expr.fvarLeaves] using hl)
  | bvar => intro _; simp [Expr.fvarConsistent]
  | sort => intro _; simp [Expr.fvarConsistent]
  | const => intro _; simp [Expr.fvarConsistent]
  | lit => intro _; simp [Expr.fvarConsistent]

/-! ## Syntax helpers -/

theorem annot_inst_mkAppN (a : AnnotTerm) (k : Nat) :
    ∀ (as : List AnnotTerm) (f : AnnotTerm),
      (AnnotTerm.mkAppN f as).inst a k = AnnotTerm.mkAppN (f.inst a k) (as.map (·.inst a k))
  | [], _ => rfl
  | b :: as, f => by
    rw [AnnotTerm.mkAppN_cons, annot_inst_mkAppN a k as (.app f b), AnnotTerm.inst_app]
    rfl

theorem annot_instSeq_mkAppN :
    ∀ (ws : List AnnotTerm) (t : Nat) (f : AnnotTerm) (as : List AnnotTerm),
      ConLeche.Model.AnnotTerm.instSeq ws t (AnnotTerm.mkAppN f as)
        = AnnotTerm.mkAppN (ConLeche.Model.AnnotTerm.instSeq ws t f)
            (as.map (ConLeche.Model.AnnotTerm.instSeq ws t))
  | [], _, f, as => by simp [ConLeche.Model.AnnotTerm.instSeq]
  | w :: ws, t, f, as => by
    rw [AnnotTerm.instSeq_cons, annot_inst_mkAppN, annot_instSeq_mkAppN ws, List.map_map]
    rfl

theorem annot_instSeq_of_inst_self {f : AnnotTerm} (h : ∀ (y : AnnotTerm) (k : Nat), f.inst y k = f) :
    ∀ (ws : List AnnotTerm) (t : Nat), ConLeche.Model.AnnotTerm.instSeq ws t f = f
  | [], _ => rfl
  | w :: ws, t => by rw [AnnotTerm.instSeq_cons, h, annot_instSeq_of_inst_self h ws]

theorem looseBVarsBounded_mkAppN_args {k : Nat} :
    ∀ {as : List Expr} {f : Expr}, (Expr.mkAppN f as).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ a ∈ as, a.looseBVarsBounded k = true
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | b :: as, f, h => by
    obtain ⟨h1, h2⟩ := looseBVarsBounded_mkAppN_args (as := as) (f := .app f b) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h1.2
    · exact h2 a ha

theorem looseBVarsBounded_mkLamsOf_body :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) (X : Expr) (k : Nat),
      (Expr.mkLamsOf bs X).looseBVarsBounded k = true → X.looseBVarsBounded (k + bs.length) = true
  | [], X, k, h => by simpa [Expr.mkLamsOf] using h
  | (ty, mt) :: bs, X, k, h => by
    simp only [Expr.mkLamsOf, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := looseBVarsBounded_mkLamsOf_body bs X (k + 1) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- The peel commutes with an opening by bvar-closed terms. -/
theorem instPisAtLift_instantiateList {os : List Expr}
    (hcl : ∀ s ∈ os, s.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) {ty rest : Expr}, (∀ a ∈ args, a.looseBVarsBounded os.length = true) →
      ty.looseBVarsBounded 0 = true →
      Expr.instPisAtLift args ty = some rest →
      Expr.instPisAtLift (args.map (·.instantiateList os 0)) ty = some (rest.instantiateList os 0) := by
  intro args ty rest hargs hty h
  cases os with
  | nil => simpa [ConLeche.Expr.instantiateList_nil] using h
  | cons o os' =>
    have hne : (o :: os') ≠ [] := by simp
    have hlen : (o :: os').reverse.length = ((o :: os').length - 1) + 1 := by simp
    have hcl' : ∀ s ∈ (o :: os').reverse, s.looseBVarsBounded 0 = true :=
      fun s hs => hcl s (List.mem_reverse.mp hs)
    have h2 := instPisAtLift_instSeq hcl' hlen args
      (fun a ha => by rw [show (o :: os').length - 1 + 1 = (o :: os').length from by simp]; exact hargs a ha) h
    rw [← ConLeche.instantiateList_eq_instSeq hne, ← ConLeche.instantiateList_eq_instSeq hne,
      ConLeche.Expr.instantiateList_eq_self hty] at h2
    rw [← h2]
    congr 1
    exact List.map_congr_left fun a _ => ConLeche.instantiateList_eq_instSeq hne a

/-! ## A graph's domain is rigid -/

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) : f ≠ (pt : V) := by
  intro h
  have hm : (ptTag : V) ∈ˢ f := h ▸ ptTag_mem_pt
  obtain ⟨x, -, y, -, hp⟩ := mem_sigmaPairs.mp ((mem_piSet.mp hf).1 _ hm)
  exact ptTag_ne_kpair x y hp

theorem mem_dom_of_mem_piSet_two {A A' f x : V} {B B' : V → V} (hf : f ∈ˢ piSet A B)
    (hf' : f ∈ˢ piSet A' B') (hx : x ∈ˢ A') : x ∈ˢ A := by
  obtain ⟨y, hy, -⟩ := (mem_piSet.mp hf').2 x hx
  obtain ⟨x', hx', y', -, hp⟩ := mem_sigmaPairs.mp ((mem_piSet.mp hf).1 _ hy)
  rw [(kpair_inj hp).1]
  exact hx'

theorem WellDenoted_mkAppN_head {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {g : AnnotTerm},
      WellDenoted V ρ (AnnotTerm.mkAppN g as) → WellDenoted V ρ g
  | [], _, h => h
  | a :: as, g, h => by
    have h1 := WellDenoted_mkAppN_head as (g := .app g a) h
    exact ((WellDenoted_app V ρ g a) ▸ h1).1

/-- **A graded application spine of a value of a nonzero-bit Π-tower fits
the tower**: each application node's package puts its argument in a
domain the head inhabits as a graph, and a graph's domain is rigid. -/
theorem spineFit_of_wellDenoted_mkAppN_pi {R : AnnotTerm} :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {h : AnnotTerm} {args : List AnnotTerm}
      {τ σ : Nat → V},
      (∀ d ∈ pds, d.2.1 ≠ 0) →
      WellDenoted V τ (AnnotTerm.mkAppN h args) →
      interp V τ h ∈ˢ interp V σ (mkPisAV pds R) →
      args.length = pds.length →
      SpineFit σ (pds.map (·.2.2)) (args.map (interp V τ))
  | [], _, [], _, _, _, _, _, _ => trivial
  | [], _, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, _, [], _, _, _, _, _, hlen => by simp at hlen
  | d :: pds, h, a :: args, τ, σ, hnz, hwd, hmem, hlen => by
    simp only [List.map_cons, SpineFit]
    rw [AnnotTerm.mkAppN_cons] at hwd
    have hwdA := WellDenoted_mkAppN_head args hwd
    obtain ⟨-, -, v, A, Bf, hf, ha, -⟩ := (WellDenoted_app V τ h a) ▸ hwdA
    have hd : d.2.1 ≠ 0 := hnz d List.mem_cons_self
    have hmem' : interp V τ h ∈ˢ piSet (interp V σ d.2.2)
        (fun x => interp V (cons x σ) (mkPisAV pds R)) := by
      have := hmem
      simp only [mkPisAV, interp_pi] at this
      rwa [piR_pos hd] at this
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0, piR_zero] at hf
      exact ne_pt_of_mem_piSet hmem' (eq_pt_of_mem_truthVal hf)
    rw [piR_pos hv] at hf
    have hx : interp V τ a ∈ˢ interp V σ d.2.2 := mem_dom_of_mem_piSet_two hmem' hf ha
    refine ⟨hx, ?_⟩
    refine spineFit_of_wellDenoted_mkAppN_pi (R := R) (h := .app h a)
      (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd')) hwd ?_ (by simpa using hlen)
    rw [interp_app]
    exact app_mem_of_mem_piSet hmem' hx

/-- The member abstraction commutes with an opening by free variables
(the holes are free variables too). -/
theorem targetAbs_instantiateList {names : List Name} {lvls : List Level} {holes : List Expr}
    (hh : ∀ h ∈ holes, ∃ i ty, h = Expr.fvar i ty) {os : List Expr}
    (ho : ∀ o ∈ os, ∃ i ty, o = Expr.fvar i ty) :
    ∀ (e : Expr) (k : Nat),
      ConLeche.targetAbs names lvls holes (e.instantiateList os k)
        = (ConLeche.targetAbs names lvls holes e).instantiateList os k := by
  intro e
  induction e with
  | bvar j =>
    intro k
    simp only [ConLeche.targetAbs, Expr.instantiateList]
    split
    · rfl
    · split
      · rename_i hj
        obtain ⟨i, ty, hi⟩ := ho _ (List.getElem_mem hj)
        rw [hi]
        simp [Expr.instantiateList, ConLeche.targetAbs]
      · rfl
  | fvar i ty _ => intro k; simp [Expr.instantiateList, ConLeche.targetAbs]
  | sort => intro k; simp [Expr.instantiateList, ConLeche.targetAbs]
  | lit => intro k; simp [Expr.instantiateList, ConLeche.targetAbs]
  | const n us =>
    intro k
    simp only [Expr.instantiateList, ConLeche.targetAbs]
    split
    · split
      · rename_i t ht
        rcases Nat.lt_or_ge t holes.length with hlt | hge
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          obtain ⟨i, ty, hi⟩ := hh _ (List.getElem_mem hlt)
          rw [hi]; simp [Expr.instantiateList]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
          simp [Expr.instantiateList]
      · simp [Expr.instantiateList]
    · simp [Expr.instantiateList]
  | app f a ihf iha => intro k; simp [Expr.instantiateList, ConLeche.targetAbs, ihf, iha]
  | lam t b _ iht ihb => intro k; simp [Expr.instantiateList, ConLeche.targetAbs, iht, ihb]
  | forallE t b _ iht ihb => intro k; simp [Expr.instantiateList, ConLeche.targetAbs, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro k; simp [Expr.instantiateList, ConLeche.targetAbs, iht, ihv, ihb]
  | proj s i e ih => intro k; simp [Expr.instantiateList, ConLeche.targetAbs, ih]

/-! ## Replacing free variables by terms -/

/-- Replace `fvar i` by `g i` where given (annotations not entered). -/
@[expose] def replF (g : Nat → Option Expr) : Expr → Expr
  | .fvar i ty => (g i).getD (.fvar i ty)
  | .bvar j => .bvar j
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (replF g f) (replF g a)
  | .lam ty b bi => .lam (replF g ty) (replF g b) bi
  | .forallE ty b bi => .forallE (replF g ty) (replF g b) bi
  | .letE ty v b => .letE (replF g ty) (replF g v) (replF g b)
  | .proj s i e => .proj s i (replF g e)

theorem replF_of_not_hasFvar (g : Nat → Option Expr) :
    ∀ e : Expr, e.hasFvar = false → replF g e = e := by
  intro e
  induction e <;> intro h <;> simp_all [replF, Expr.hasFvar]

theorem replF_mkAppN (g : Nat → Option Expr) :
    ∀ (as : List Expr) (f : Expr), replF g (Expr.mkAppN f as) = Expr.mkAppN (replF g f) (as.map (replF g))
  | [], _ => rfl
  | a :: as, f => by
    show replF g (Expr.mkAppN (.app f a) as) = _
    rw [replF_mkAppN g as (.app f a)]
    rfl

theorem replF_instantiate1 {g : Nat → Option Expr}
    (hg : ∀ i x, g i = some x → x.looseBVarsBounded 0 = true) :
    ∀ (e v : Expr) (k : Nat), replF g (e.instantiate1 v k) = (replF g e).instantiate1 (replF g v) k := by
  intro e
  induction e with
  | bvar j =>
    intro v k
    simp only [replF, Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | fvar i ty _ =>
    intro v k
    simp only [Expr.instantiate1, replF]
    cases hgi : g i with
    | none => rfl
    | some x =>
      simp only [Option.getD_some]
      exact (ConLeche.Expr.instantiate1_eq_self
        (ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) (hg i x hgi))).symm
  | sort => intro v k; rfl
  | const => intro v k; rfl
  | lit => intro v k; rfl
  | app f a ihf iha => intro v k; simp [Expr.instantiate1, replF, ihf, iha]
  | lam t b _ iht ihb => intro v k; simp [Expr.instantiate1, replF, iht, ihb]
  | forallE t b _ iht ihb => intro v k; simp [Expr.instantiate1, replF, iht, ihb]
  | letE t v' b iht ihv ihb => intro v k; simp [Expr.instantiate1, replF, iht, ihv, ihb]
  | proj s i e ih => intro v k; simp [Expr.instantiate1, replF, ih]

/-- **A peel at free variables, replaced, is the peel at the terms.** -/
theorem instPisAt_replF {g : Nat → Option Expr}
    (hg : ∀ i x, g i = some x → x.looseBVarsBounded 0 = true) :
    ∀ (fs as : List Expr) (e : Expr) {ds : List Expr} {r : Expr},
      Expr.instPisAt fs e = some (ds, r) → fs.length = as.length →
      (∀ (j : Nat) (hj : j < fs.length) (hj' : j < as.length), replF g fs[j] = as[j]) →
      Expr.instPisAt as (replF g e) = some (ds.map (replF g), replF g r)
  | [], [], e, ds, r, h, _, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | f :: fs, a :: as, e, ds, r, h, hl, hrep => by
    match e, h with
    | .forallE dom body bm, h =>
      simp only [Expr.instPisAt] at h
      cases hq : Expr.instPisAt fs (body.instantiate1 f) with
      | none => rw [hq] at h; exact nomatch h
      | some q =>
        rw [hq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hf : replF g f = a := hrep 0 (by simp) (by simp)
        have ih := instPisAt_replF hg fs as (body.instantiate1 f) hq (by simpa using hl)
          (fun j hj hj' => hrep (j + 1) (by simpa using hj) (by simpa using hj'))
        rw [replF_instantiate1 hg, hf] at ih
        simp only [replF, Expr.instPisAt, ih, Option.map_some, List.map_cons]

/-! ## A field's telescope read through whnf -/

section Whnf

variable {μ : CheckMode} {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **`targetWhnfPis` keeps the value.**  At a framed, readable,
graded subject: the result is framed, adds no leaf, reads, is graded,
and has the subject's value at every satisfying valuation — the whnf
steps' own soundness (`Rules.red_sound`), and at each opened binder
the recursion under the binder's domain. -/
theorem targetWhnfPis_sem (hμ : μ.verifiedChecks = true) (hin : Rules.RulesInputs V m φ)
    {F : Nat} :
    ∀ (fuel d : Nat) (e r : Expr),
      ConLeche.targetWhnfPis (ConLeche.fueledOps μ F) env d fuel e = .ok r →
      Rules.Frame d e →
      ∀ {Δ : List AnnotTerm} {ea : AnnotTerm}, CtxOk m φ d Δ e →
        denoteMeta m.acval env φ d e = some ea → Rules.Graded V Δ ea →
        Rules.Frame d r ∧ Rules.LeavesSub r e ∧
          ∃ ra, denoteMeta m.acval env φ d r = some ra ∧ Rules.Graded V Δ ra ∧
            ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ ea = interp V ρ ra
  | 0, d, e, r, h, _, _, _, _, _, _ => by
    simp [ConLeche.targetWhnfPis, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, e, r, h, hFr, Δ, ea, hC, hea, hG => by
    have hver : μ = .verified := CheckMode.eq_verified hμ
    simp only [ConLeche.targetWhnfPis] at h
    obtain ⟨w, hwr, h⟩ := ConLeche.exceptBind_ok h
    have hwr0 : ConLeche.whnf μ env F d e = .ok w := hwr
    have hwr' : ConLeche.whnf .verified env F d e = .ok w := hver ▸ hwr0
    obtain ⟨hFw, hLw, wa, hwa, hGw, hEw⟩ :=
      Rules.red_sound hin (Rules.whnf_bridge hwr') hFr hC hea hG
    split at h
    · rename_i dom body bm
      obtain ⟨body', hb', h⟩ := ConLeche.exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hwsW, hlbW, hLBW⟩ := hFw
      unfold Expr.WScoped at hwsW
      obtain ⟨hwsD, hwsB⟩ := hwsW
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbW
      obtain ⟨hlbD, hlbB⟩ := hlbW
      obtain ⟨doma, ba, hdoma, hba, rfl⟩ := denoteMeta_forallE_inv hwa
      have hCw : CtxOk m φ d Δ (.forallE dom body bm) := hC.of_subset hLw
      have hGd : Rules.Graded V Δ doma := fun ρ hρ => WellDenotedV_pi_dom (hGw ρ hρ)
      -- the opened body: framed, in context, graded
      have hFb : Rules.Frame (d + 1) (body.instantiate1 (.fvar d dom)) := by
        refine ⟨Expr.WScoped.instantiate1 hwsD 0 hwsB, ConLeche.looseBVarsBounded_instantiate1 _ 0 hlbB,
          fun l hl => ?_⟩
        rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with h1 | h1
        · exact hLBW l (by simp [Expr.fvarLeaves, h1])
        · simp only [Expr.fvarLeaves, List.mem_cons] at h1
          rcases h1 with rfl | h1
          · exact hlbD
          · exact hLBW l (by simp [Expr.fvarLeaves, h1])
      have hCb : CtxOk m φ (d + 1) (doma :: Δ) (body.instantiate1 (.fvar d dom)) :=
        CtxOk.open hCw.forallE_body hCw.forallE_ty hdoma hGd
      have hGb : Rules.Graded V (doma :: Δ) ba := by
        intro σ hσ
        obtain ⟨hx, hs⟩ := Sat_cons_inv hσ
        have h1 := WellDenotedV_pi_body (hGw _ hs) hx
        rwa [cons_eta] at h1
      obtain ⟨hFb', hLb', rb, hrb, hGrb, hErb⟩ :=
        targetWhnfPis_sem hμ hin fuel (d + 1) _ body' hb' hFb hCb hba hGb
      obtain ⟨hwsb', hlbb', hLBb'⟩ := hFb'
      -- every leaf of the new body at `d` is the opener
      have hcons : Expr.fvarConsistent d dom body' := by
        refine fvarConsistent_of_leaves body' fun l hl hld => ?_
        rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 (hLb' l hl) with h1 | h1
        · exfalso
          have := ConLeche.Expr.fvarLeaves_lt_of_wscoped hwsB l h1
          omega
        · simp only [Expr.fvarLeaves, List.mem_cons] at h1
          rcases h1 with rfl | h1
          · rfl
          · exfalso
            have := ConLeche.Expr.fvarLeaves_lt_of_wscoped hwsD l h1
            omega
      have hround : (body'.abstract1 d 0).instantiate1 (.fvar d dom) 0 = body' :=
        ConLeche.abstract1_instantiate1 body' 0 hcons hlbb'
      have hleafR : ∀ l ∈ (Expr.forallE dom (body'.abstract1 d 0) bm).fvarLeaves,
          l ∈ e.fvarLeaves := by
        intro l hl
        simp only [Expr.fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLw l (by simp [Expr.fvarLeaves, hl])
        · obtain ⟨hl1, hne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne body' 0 hwsb' l hl
          rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 (hLb' l hl1) with h1 | h1
          · exact hLw l (by simp [Expr.fvarLeaves, h1])
          · simp only [Expr.fvarLeaves, List.mem_cons] at h1
            rcases h1 with rfl | h1
            · exact absurd rfl hne
            · exact hLw l (by simp [Expr.fvarLeaves, h1])
      refine ⟨⟨by unfold Expr.WScoped; exact ⟨hwsD, ConLeche.WScoped.abstract1 0 hwsb'⟩,
          by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
             exact ⟨hlbD, ConLeche.looseBVarsBounded_abstract1 body' 0 hlbb'⟩,
          fun l hl => hLBW l ?_⟩, hleafR, ?_⟩
      · simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
        rcases hl with hl | hl
        · exact Or.inl hl
        · obtain ⟨hl1, hne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne body' 0 hwsb' l hl
          rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 (hLb' l hl1) with h1 | h1
          · exact Or.inr h1
          · simp only [Expr.fvarLeaves, List.mem_cons] at h1
            rcases h1 with rfl | h1
            · exact absurd rfl hne
            · exact Or.inl h1
      · refine ⟨.pi 0 (pwBit φ bm.pw) doma rb, ?_, ?_, ?_⟩
        · rw [denoteMeta_forallE, hdoma]
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [hround, hrb]
          rfl
        · intro ρ hρ
          have hW := hGw ρ hρ
          refine ⟨?_, ?_⟩
          · rw [WellDenoted_pi]
            refine ⟨(hGd ρ hρ).1, fun x hx => ?_⟩
            exact (hGrb _ (Sat_cons V hρ hx)).1
          · rw [AnnotValid_pi]
            have hWv := hW.2
            rw [AnnotValid_pi] at hWv
            refine ⟨hWv.1, fun x hx => (hGrb _ (Sat_cons V hρ hx)).2, fun hv0 x hx => ?_⟩
            rw [← hErb _ (Sat_cons V hρ hx)]
            exact hWv.2.2 hv0 x hx
        · intro ρ hρ
          rw [hEw ρ hρ, interp_pi, interp_pi]
          exact piR_congr fun x hx => hErb _ (Sat_cons V hρ hx)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨hFr, fun l hl => hl, ea, hea, hG, fun _ _ => rfl⟩

end Whnf

/-! ## The member abstraction, read at the members' own values -/

/-- Two optional readings agree: both absent, or both present and
related. -/
@[expose] def ReadAgree (P : AnnotTerm → AnnotTerm → Prop) : Option AnnotTerm → Option AnnotTerm → Prop
  | some a2, some a1 => P a2 a1
  | none, none => True
  | _, _ => False

/-- A projection spelling keeps a value and a truthfulness transfer. -/
theorem projAV_agree {ρ : Nat → V} :
    ∀ (n : Nat) {e2 e1 : AnnotTerm}, interp V ρ e2 = interp V ρ e1 →
      (WellDenoted V ρ e2 → WellDenoted V ρ e1) →
      interp V ρ (projAV n e2) = interp V ρ (projAV n e1) ∧
        (WellDenoted V ρ (projAV n e2) → WellDenoted V ρ (projAV n e1))
  | 0, e2, e1, hv, hw => by
    refine ⟨by simp [projAV, hv], fun h => ?_⟩
    simp only [projAV, WellDenoted_fst] at h ⊢
    obtain ⟨h1, u, v, A, Bf, h2, h3, h4⟩ := h
    exact ⟨hw h1, u, v, A, Bf, hv ▸ h2, h3, h4⟩
  | n + 1, e2, e1, hv, hw => by
    refine projAV_agree n (e2 := .snd e2) (e1 := .snd e1) (by simp [hv]) fun h => ?_
    simp only [WellDenoted_snd] at h ⊢
    obtain ⟨h1, u, v, A, Bf, h2, h3, h4⟩ := h
    exact ⟨hw h1, u, v, A, Bf, hv ▸ h2, h3, h4⟩

section Abs

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}
  {names : List Name} {lvls : List Level} {formerTys : List Expr} {B : Nat} {hvC : Nat → V}

/-- The relation `targetAbs_read` concludes: at every valuation whose
hole slots carry the members' values, the abstract reading has the
concrete one's value, and its truthfulness gives the concrete one's. -/
@[expose] def AbsAgree (V : Type w) [SetTheory V] (k d : Nat) (hvC : Nat → V)
    (a2 a1 : AnnotTerm) : Prop :=
  ∀ (vals : List V) (τ : Nat → V), vals.length = d → (∀ t, t < k → τ (k - 1 - t) = hvC t) →
    interp V (consList vals τ) a2 = interp V (consList vals τ) a1 ∧
      (WellDenoted V (consList vals τ) a2 → WellDenoted V (consList vals τ) a1)

theorem readAgree_refl {k d : Nat} (o : Option AnnotTerm) :
    ReadAgree (AbsAgree V k d hvC) o o := by
  cases o with
  | none => trivial
  | some a => exact fun _ _ _ _ => ⟨rfl, id⟩

set_option maxHeartbeats 1600000 in
/-- **The member abstraction read at the members' own values is the
concrete term**: `targetAbs` replaces a member constant (at the block's
levels) by its hole; at a valuation carrying, at every hole's slot,
the member constant's own value, the two readings agree — the same
reading everywhere else. -/
theorem targetAbs_read
    (hnames : ∀ (n : Name) (t : Nat), names.findIdx? (· == n) = some t →
      t < formerTys.length ∧ ∃ ci : ConLeche.ConstantInfo, env.find? n = some ci ∧
        lvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (m.acval n (Level.substFn φ ci.toConstantVal.levelParams lvls))
          = hvC t) :
    ∀ (e : Expr) (d : Nat) (as2 as1 : List Expr),
      LocList (B + formerTys.length) d as2 → LocList (B + formerTys.length) d as1 →
      ReadAgree (AbsAgree V formerTys.length d hvC)
        (denoteMeta m.acval env φ (B + formerTys.length + d)
          ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) e).instantiateList
            as2 0))
        (denoteMeta m.acval env φ (B + formerTys.length + d) (e.instantiateList as1 0))
  | .bvar j, d, as2, as1, h2, h1 => by
    simp only [ConLeche.targetAbs]
    rcases Nat.lt_or_ge j d with hjd | hjd
    · obtain ⟨ty1, he1⟩ := h1.bvar_lt hjd
      obtain ⟨ty2, he2⟩ := h2.bvar_lt hjd
      rw [he1, he2, denoteMeta_fvar, denoteMeta_fvar]
      exact readAgree_refl (V := V) _
    · rw [h1.bvar_ge hjd, h2.bvar_ge hjd]
      exact readAgree_refl (V := V) _
  | .fvar i ty, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta_fvar]
    exact readAgree_refl (V := V) _
  | .sort u, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList]
    exact readAgree_refl (V := V) _
  | .lit l, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList]
    exact readAgree_refl (V := V) _
  | .letE ty v b, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta]
    trivial
  | .const n us, d, as2, as1, _, _ => by
    simp only [ConLeche.targetAbs]
    split
    · rename_i hus
      split
      · rename_i t ht
        obtain ⟨htk, ci, hfind, hlen, hval⟩ := hnames n t ht
        have hus' : us = lvls := by simpa using hus
        subst hus'
        rw [List.getD_eq_getElem?_getD, ConLeche.targetHoles, List.getElem?_map,
          List.getElem?_range htk, Option.map_some, Option.getD_some]
        simp only [Expr.instantiateList, denoteMeta_fvar]
        rw [denoteMeta_const hfind hlen]
        intro vals τ hvl hτ
        rw [interp_bvar, show B + formerTys.length + d - 1 - (B + t)
            = (formerTys.length - 1 - t) + vals.length from by omega, consList_apply_add,
          hτ t htk, hval]
        exact ⟨rfl, fun _ => m.acval_wellDenoted _ _ _⟩
      · simp only [Expr.instantiateList]; exact readAgree_refl (V := V) _
    · simp only [Expr.instantiateList]; exact readAgree_refl (V := V) _
  | .app f a, d, as2, as1, h2, h1 => by
    have ihf := targetAbs_read hnames f d as2 as1 h2 h1
    have iha := targetAbs_read hnames a d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta]
    revert ihf iha
    cases denoteMeta m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) f).instantiateList as2 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + d) (f.instantiateList as1 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) a).instantiateList as2 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + d) (a.instantiateList as1 0)
      <;> simp [ReadAgree]
    intro hf ha vals τ hvl hτ
    obtain ⟨hfv, hfw⟩ := hf vals τ hvl hτ
    obtain ⟨hav, haw⟩ := ha vals τ hvl hτ
    refine ⟨by simp [hfv, hav], fun hw => ?_⟩
    rw [WellDenoted_app] at hw ⊢
    obtain ⟨w1, w2, v, A, Bf, h3, h4, h5⟩ := hw
    exact ⟨hfw w1, haw w2, v, A, Bf, hfv ▸ h3, hav ▸ h4, h5⟩
  | .proj sn i e, d, as2, as1, h2, h1 => by
    have ihe := targetAbs_read hnames e d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta]
    revert ihe
    cases denoteMeta m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) e).instantiateList as2 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + d) (e.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? sn i with
    | some entry =>
      intro vals τ hvl hτ
      obtain ⟨hv, hw⟩ := he vals τ hvl hτ
      exact projAV_agree (i + entry.off) hv hw
    | none =>
      rcases i with _ | _ | i
      · intro vals τ hvl hτ
        obtain ⟨hv, hw⟩ := he vals τ hvl hτ
        exact projAV_agree 0 hv hw
      · intro vals τ hvl hτ
        obtain ⟨hv, hw⟩ := he vals τ hvl hτ
        refine ⟨by simp [hv], fun h => ?_⟩
        simp only [WellDenoted_snd] at h ⊢
        obtain ⟨h1, u, v, A, Bf, h2, h3, h4⟩ := h
        exact ⟨hw h1, u, v, A, Bf, hv ▸ h2, h3, h4⟩
      · trivial
  | .lam ty b bi, d, as2, as1, h2, h1 => by
    have iht := targetAbs_read hnames ty d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta]
    revert iht
    cases hA2 : denoteMeta m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList as2 0)
      <;> cases hA1 : denoteMeta m.acval env φ (B + formerTys.length + d) (ty.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
      show B + formerTys.length + d + 1 = B + formerTys.length + (d + 1) from by omega]
    have ihb := targetAbs_read hnames b (d + 1)
      (Expr.fvar (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
          as2 0) :: as2)
      (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1)
      (h2.cons _) (h1.cons _)
    revert ihb
    cases denoteMeta m.acval env φ (B + formerTys.length + (d + 1))
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) b).instantiateList
          (Expr.fvar (B + formerTys.length + d)
            ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
              as2 0) :: as2) 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + (d + 1))
        (b.instantiateList (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1) 0)
      <;> simp [ReadAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    obtain ⟨hAv, hAw⟩ := hA vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2 = interp V (cons x (consList vals τ)) b1 ∧
        (WellDenoted V (cons x (consList vals τ)) b2 → WellDenoted V (cons x (consList vals τ)) b1) := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    refine ⟨?_, fun hw => ?_⟩
    · rw [interp_lam, interp_lam, hAv]
      exact lamR_congr fun x _ => (hbx x).1
    · rw [WellDenoted_lam] at hw ⊢
      obtain ⟨w1, w2, Bf, w3, w4⟩ := hw
      refine ⟨hAw w1, fun x hx => (hbx x).2 (w2 x (hAv ▸ hx)), Bf, fun x hx => ?_,
        fun hv0 x hx => w4 hv0 x (hAv ▸ hx)⟩
      rw [← (hbx x).1]
      exact w3 x (hAv ▸ hx)
  | .forallE ty b bi, d, as2, as1, h2, h1 => by
    have iht := targetAbs_read hnames ty d as2 as1 h2 h1
    simp only [ConLeche.targetAbs, Expr.instantiateList, denoteMeta]
    revert iht
    cases hA2 : denoteMeta m.acval env φ (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList as2 0)
      <;> cases hA1 : denoteMeta m.acval env φ (B + formerTys.length + d) (ty.instantiateList as1 0)
      <;> simp [ReadAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
      show B + formerTys.length + d + 1 = B + formerTys.length + (d + 1) from by omega]
    have ihb := targetAbs_read hnames b (d + 1)
      (Expr.fvar (B + formerTys.length + d)
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
          as2 0) :: as2)
      (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1)
      (h2.cons _) (h1.cons _)
    revert ihb
    cases denoteMeta m.acval env φ (B + formerTys.length + (d + 1))
        ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) b).instantiateList
          (Expr.fvar (B + formerTys.length + d)
            ((ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys B) ty).instantiateList
              as2 0) :: as2) 0)
      <;> cases denoteMeta m.acval env φ (B + formerTys.length + (d + 1))
        (b.instantiateList (Expr.fvar (B + formerTys.length + d) (ty.instantiateList as1 0) :: as1) 0)
      <;> simp [ReadAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    obtain ⟨hAv, hAw⟩ := hA vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2 = interp V (cons x (consList vals τ)) b1 ∧
        (WellDenoted V (cons x (consList vals τ)) b2 → WellDenoted V (cons x (consList vals τ)) b1) := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    refine ⟨?_, fun hw => ?_⟩
    · rw [interp_pi, interp_pi, hAv]
      exact piR_congr fun x _ => (hbx x).1
    · rw [WellDenoted_pi] at hw ⊢
      obtain ⟨w1, w2⟩ := hw
      exact ⟨hAw w1, fun x hx => (hbx x).2 (w2 x (hAv ▸ hx))⟩

end Abs

end ConLeche.Model
