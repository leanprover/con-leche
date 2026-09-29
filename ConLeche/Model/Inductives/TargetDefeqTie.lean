module

public import ConLeche.Model.Inductives.TargetCallKit
public import ConLeche.Model.Inductives.ContN2
public import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Rules.Sound
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Semantics.Tower.SumTower
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Shift

public section

/-!
# The defeq tie: a class match reads alike

The recursor check matches a recursor class against an instantiation the
positivity check recorded PER COMPONENT (`targetClassMatch`, ruling
2026-09-27): levels by `Level.isEquivList`, every parameter by the
kernel's defeq — over the class's recursor prefix `pfvs`, with the
block's members abstracted to holes on top.  At a `Prop`-valued class the
class induction reads DECODINGS (the hole fits at the class's parameter
FRAME), not merely readings of types: two instances whose majors read
alike need not share a frame (`P Nat`, `P Bool`: both `{pt}`), which is
why the match is per component and not one defeq of the two majors.

What the model needs is that the FRAMES agree: every parameter pair
reads alike at every valuation of the prefix.  The defeq ran over the
holes, so its soundness (`Rules.defeq_sound`) equates the two readings
at every valuation of the holes that carries values of the formers'
types — in particular at the members' own values, where the abstraction
reads as the concrete term (`targetAbs_read`); the holes sit above the
prefix, so the concrete readings are the prefix-depth ones lifted
(`denoteMeta_lift`).  A syntactically equal pair needs no defeq: the
abstraction read at the members' values gives it directly.

* `walkCtx_holes` — the prefix's walk context extended by the holes at
  values of the formers' types;
* `param_read_eq` — one matched pair (`ParamMatch`) reads alike at the
  prefix (the port of the parked `TargetDefeqTie.param_read_eq`);
* `params_read_eq` — a matched parameter spine's readings, mapped;
* `keyFrame_eq_of_params` — spines reading alike give one key frame
  (whence one fit, one carrier, one index set: the parked `tie_fits`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term ConLeche.Verify
open ConLeche (Env Expr Name Level CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The canonical move, syntactically -/

/-- A frame list read backwards has the variable `i` at position `i`. -/
theorem fvarList_rev_getElem {E : Nat} {L : List Expr} (hL : FvarList E L.reverse) {i : Nat}
    {x : Expr} (hx : L[i]? = some x) : ∃ ty, x = .fvar i ty := by
  have hlen : L.length = E := by rw [← List.length_reverse]; exact hL.1
  have hi : i < E := by have := (List.getElem?_eq_some_iff.mp hx).1; omega
  obtain ⟨ty, hty⟩ := hL.2.1 (E - 1 - i) (by omega)
  rw [List.getElem?_reverse (by omega), show L.length - 1 - (E - 1 - i) = i by omega, hx,
    Option.some.injEq] at hty
  exact ⟨ty, by rw [hty]; congr 1; omega⟩

/-- Moving to openers at their own indices is invisible to erasure. -/
theorem canon_erasedEq {pfvs : List Expr}
    (hp : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x → ∃ ty, x = .fvar i ty) :
    ∀ (a : Expr), a.fvarsBelow pfvs.length →
      Expr.ErasedEq (ConLeche.targetCanonParams pfvs a) a := by
  intro a
  induction a with
  | bvar i => intro _; exact Expr.ErasedEq.rfl _
  | fvar i ty =>
    intro h
    simp only [Expr.fvarsBelow] at h
    obtain ⟨ty', hty'⟩ := hp i _ (List.getElem?_eq_getElem h)
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, List.getElem?_eq_getElem h,
      Option.getD_some]
    rw [hty']
    simp [Expr.ErasedEq]
  | sort u => intro _; exact Expr.ErasedEq.rfl _
  | const n us => intro _; exact Expr.ErasedEq.rfl _
  | lit l => intro _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := ihf h.1
    have h2 := iha h.2
    simp only [ConLeche.targetCanonParams] at h1 h2 ⊢
    simp only [ConLeche.Expr.replaceFVars, Expr.ErasedEq]
    exact ⟨h1, h2⟩
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [ConLeche.targetCanonParams] at h1 h2 ⊢
    simp only [ConLeche.Expr.replaceFVars, Expr.ErasedEq]
    exact ⟨trivial, h1, h2⟩
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [ConLeche.targetCanonParams] at h1 h2 ⊢
    simp only [ConLeche.Expr.replaceFVars, Expr.ErasedEq]
    exact ⟨trivial, h1, h2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihv h.2.1
    have h3 := ihb h.2.2
    simp only [ConLeche.targetCanonParams] at h1 h2 h3 ⊢
    simp only [ConLeche.Expr.replaceFVars, Expr.ErasedEq]
    exact ⟨h1, h2, h3⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := ih h
    simp only [ConLeche.targetCanonParams] at h1 ⊢
    simp only [ConLeche.Expr.replaceFVars, Expr.ErasedEq]
    exact ⟨trivial, trivial, h1⟩

/-- The canonical move's leaves are the openers'. -/
theorem canon_leaves {pfvs : List Expr} :
    ∀ (a : Expr), a.fvarsBelow pfvs.length →
      ∀ l ∈ (ConLeche.targetCanonParams pfvs a).fvarLeaves, ∃ x ∈ pfvs, l ∈ x.fvarLeaves := by
  intro a
  induction a with
  | bvar i => intro _ l hl; simp [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars,
      ConLeche.Expr.fvarLeaves] at hl
  | fvar i ty =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, List.getElem?_eq_getElem h,
      Option.getD_some] at hl
    exact ⟨_, List.getElem_mem h, hl⟩
  | sort u => intro _ l hl; simp [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars,
      ConLeche.Expr.fvarLeaves] at hl
  | const n us => intro _ l hl; simp [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars,
      ConLeche.Expr.fvarLeaves] at hl
  | lit v => intro _ l hl; simp [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars,
      ConLeche.Expr.fvarLeaves] at hl
  | app f a ihf iha =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, ConLeche.Expr.fvarLeaves,
      List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf h.1 l hl
    · exact iha h.2 l hl
  | lam t b m iht ihb =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, ConLeche.Expr.fvarLeaves,
      List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | forallE t b m iht ihb =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, ConLeche.Expr.fvarLeaves,
      List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | letE t v b iht ihv ihb =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars, ConLeche.Expr.fvarLeaves,
      List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1 l hl
    · exact ihv h.2.1 l hl
    · exact ihb h.2.2 l hl
  | proj s i e ih =>
    intro h l hl
    simp only [Expr.fvarsBelow] at h
    simp only [ConLeche.targetCanonParams, ConLeche.Expr.replaceFVars,
      ConLeche.Expr.fvarLeaves] at hl
    exact ih h l hl

/-! ## The prefix extended by the holes -/

section Walk

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

/-- The holes' valuation slots: hole `t` of `k` sits at `k - 1 - t`. -/
theorem consList_hole {hv : List V} {σ : Nat → V} {t : Nat} (ht : t < hv.length) :
    consList hv σ (hv.length - 1 - t) = hv.getD t pt := by
  rw [consList_getD_of_lt _ _ _ (by omega), show hv.length - 1 - (hv.length - 1 - t) = t by omega]

/-- **The prefix's walk context extended by the holes**, at values `hv`
of the formers' (closed) types. -/
theorem walkCtx_holes
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    {D : Nat} {L : List Expr} (hL : FvarList D L) {σ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ D σ Δ L) {formerTys : List Expr} {hv : List V}
    (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T) :
    ∃ Δ', FvarList (D + formerTys.length) ((ConLeche.targetHoles formerTys D).reverse ++ L) ∧
      WalkCtx V mT φ (D + formerTys.length) (consList hv σ) Δ'
        ((ConLeche.targetHoles formerTys D).reverse ++ L) := by
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  generalize hk : formerTys.length = k at *
  let Ts : List AnnotTerm := (List.range k).map fun t =>
    (denoteMeta mT.acval envT φ 0 (formerTys.getD t default)).getD default
  have hTsLen : Ts.length = k := by simp [Ts]
  have hTsGet : ∀ t, t < k → ∃ T, Ts.getD t default = T ∧
      denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
      Term.bvarsBelow 0 T.erase ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
      ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T := by
    intro t ht
    obtain ⟨hf, hb, -, T, hT, hG, hvT⟩ := hformer t ht
    refine ⟨T, ?_, hT, bvarsBelow_of_reading (m := mT) (Expr.WScoped.of_not_hasFvar hf) hb hT,
      hG, hvT⟩
    have hT' := hT
    rw [List.getD_eq_getElem?_getD] at hT'
    simp [Ts, List.getD_eq_getElem?_getD, List.getElem?_range ht, hT']
  have hL0 : FvarList (D + k) ((ConLeche.targetHoles formerTys D).reverse ++ L) := by
    have h := fvarList_ihs hL formerTys (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      have := (hformer i (by omega)).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
      exact Expr.WScoped.of_not_hasFvar this)
    rw [hk] at h
    exact h
  have h := walkCtx_ihs hacl hL hW formerTys Ts hv (by rw [hTsLen, hk]) (by rw [hvl, hTsLen])
    (fun t ht => by
      rw [hTsLen] at ht
      obtain ⟨T, hTe, hT, hcl, hG, hvT⟩ := hTsGet t ht
      obtain ⟨hf, hb, hcb, -⟩ := hformer t ht
      have hnl : ∀ l ∈ (formerTys.getD t default).fvarLeaves, Expr.fvar l.1 l.2 ∈ L := by
        intro l hl
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf] at hl
        exact nomatch hl
      refine ⟨hnl, hb, hcb, ?_, fun σ _ => by rw [hTe]; exact hG σ, ?_⟩
      · rw [hTe]
        exact denoteMeta_depth_of_closed hacl1 hf (fun j => liftN_eq_self_of_closed hcl j 1) hT D
      · rw [hTe]
        exact hvT _)
  rw [hTsLen] at h
  exact ⟨_, hL0, h⟩

/-! ## One matched pair reads alike -/

/-- The concrete side of an abstraction read at the members' values. -/
theorem readAgree_lift
    (hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    {D k : Nat} {hvC : Nat → V} {o : Option AnnotTerm} {A : Expr} (hA : Expr.WScoped D A)
    (h : ReadAgree (AbsAgree V k 0 hvC) o (denoteMeta mT.acval envT φ (D + k) A))
    {hv : List V} (hvl : hv.length = k) (hvget : ∀ t, t < k → hv.getD t pt = hvC t)
    (σ : Nat → V) :
    o.map (interp V (consList hv σ)) = (denoteMeta mT.acval envT φ D A).map (interp V σ) := by
  rw [denoteMeta_lift hacl1 hA (D + k) (by omega), show D + k - D = k by omega] at h
  cases ho : o with
  | none =>
    rw [ho] at h
    cases hd : denoteMeta mT.acval envT φ D A with
    | none => rfl
    | some a => rw [hd] at h; exact nomatch h
  | some x =>
    rw [ho] at h
    cases hd : denoteMeta mT.acval envT φ D A with
    | none => rw [hd] at h; exact nomatch h
    | some a =>
      rw [hd] at h
      obtain ⟨hval, -⟩ := h [] (consList hv σ) rfl (fun t ht => by
        rw [← hvl] at ht ⊢
        rw [consList_hole ht, hvget t (by omega)])
      simp only [Option.map_some, Option.some.injEq]
      rw [consList_nil] at hval
      rw [hval, ← hvl, interp_liftN_consList]

set_option maxHeartbeats 4000000 in
/-- **One matched parameter pair reads alike at the prefix** (the port of
the parked `param_read_eq`): at a prefix walk context over the openers
`pfvs`, with the holes valued at the members' own values `hv` (values of
the formers' types, `hformer`; the abstraction read back, `hnames`), a
pair the class match passed (`ParamMatch`) has one reading at the
prefix's valuation. -/
theorem param_read_eq {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F D : Nat} {pfvs : List Expr}
    (hL : FvarList D pfvs.reverse) {σ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ D σ Δ pfvs.reverse)
    {names : List Name} {lvls : List Level} {formerTys : List Expr} {hv : List V}
    (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    (hnames : ∀ (n : Name) (t : Nat), names.findIdx? (· == n) = some t →
      t < formerTys.length ∧ ∃ ci : ConLeche.ConstantInfo, envT.find? n = some ci ∧
        lvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mT.acval n (Level.substFn φ ci.toConstantVal.levelParams lvls))
          = hv.getD t pt)
    {a b : Expr}
    (hm : ConLeche.ParamMatch (ConLeche.fueledOps μ F) envT (D + formerTys.length)
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)) pfvs a b) :
    (denoteMeta mT.acval envT φ D a).map (interp V σ)
      = (denoteMeta mT.acval envT φ D b).map (interp V σ) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  obtain ⟨-, -, haf, hbf, hcase⟩ := hm
  have hpl : pfvs.length = D := by rw [← List.length_reverse]; exact hL.1
  have hp := fun i x (hx : pfvs[i]? = some x) => fvarList_rev_getElem hL hx
  have haB : a.fvarsBelow pfvs.length := ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq a ▸ haf)
  have hbB : b.fvarsBelow pfvs.length := ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq b ▸ hbf)
  -- the canonical sides read as the parameters
  have hpW : ∀ x ∈ pfvs, Expr.WScoped D x := fun x hx => hL.2.2 x (List.mem_reverse.mpr hx)
  have hAW := ConLeche.targetCanonParams_WScoped hpW a haB
  have hBW := ConLeche.targetCanonParams_WScoped hpW b hbB
  have hAe := denoteMeta_erasedEq (acval := mT.acval) (env := envT) (φ := φ)
    (canon_erasedEq hp a haB) D
  have hBe := denoteMeta_erasedEq (acval := mT.acval) (env := envT) (φ := φ)
    (canon_erasedEq hp b hbB) D
  rw [← hAe, ← hBe]
  -- the abstraction read at the members' values
  generalize hA : ConLeche.targetCanonParams pfvs a = A at *
  generalize hB : ConLeche.targetCanonParams pfvs b = B at *
  have hread := fun (X : Expr) => targetAbs_read (m := mT) (env := envT) (φ := φ) (names := names)
    (lvls := lvls) (formerTys := formerTys) (B := D) (hvC := fun t => hv.getD t pt) hnames X 0
    [] [] (LocList.nil _) (LocList.nil _)
  simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero] at hread
  have hrA := readAgree_lift (φ := φ) hacl1 hAW (hread A) hvl (fun t _ => rfl) σ
  have hrB := readAgree_lift (φ := φ) hacl1 hBW (hread B) hvl (fun t _ => rfl) σ
  rw [← hrA, ← hrB]
  rcases hcase with heq | ⟨⟨ta, hta⟩, ⟨tb, htb⟩, hd⟩
  · rw [heq]
  -- the defeq branch: both sides read over the holes, and alike
  obtain ⟨Δ', hL0, hW0⟩ := walkCtx_holes (σ := σ) hacl hL hW hvl hformer
  have habsL : ∀ e : Expr, e.fvarsBelow pfvs.length →
      ∀ l ∈ (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)
        (ConLeche.targetCanonParams pfvs e)).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ (ConLeche.targetHoles formerTys D).reverse ++ pfvs.reverse := by
    intro e he l hl
    rcases ConLeche.targetAbs_fvarLeaves _ l hl with h1 | ⟨h, hh, h1⟩
    · obtain ⟨x, hx, hlx⟩ := canon_leaves e he l h1
      refine List.mem_append_right _ (List.mem_reverse.mpr ?_)
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hp i x hi
      simp only [ConLeche.Expr.fvarLeaves, List.mem_cons] at hlx
      rcases hlx with rfl | hlx
      · exact hx
      · exact List.mem_reverse.mp (hW.2.2.2.2.2.2 _ (List.mem_reverse.mpr hx) l hlx)
    · have hh' := hh
      simp only [ConLeche.targetHoles, List.mem_map, List.mem_range] at hh'
      obtain ⟨t', ht', rfl⟩ := hh'
      have hcl := (hformer t' ht').1
      simp only [ConLeche.Expr.fvarLeaves, List.mem_cons,
        ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl, List.not_mem_nil, or_false] at h1
      subst h1
      exact List.mem_append_left _ (List.mem_reverse.mpr hh)
  rw [← hA] at hta hd
  rw [← hB] at htb hd
  have hAL := habsL a haB
  have hBL := habsL b hbB
  have hWS0 := hW0.2.2.2.2.1
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hta)
  have hBb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge htb)
  obtain ⟨aa, haa⟩ := acceptedReads_of mT φ hta (wscoped_of_leaves_mem hL0 _ hAL) hAb
    (fun l hl => hWS0 _ (hAL l hl))
  obtain ⟨ba, hba⟩ := acceptedReads_of mT φ htb (wscoped_of_leaves_mem hL0 _ hBL) hBb
    (fun l hl => hWS0 _ (hBL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hAL hAb haa
    ⟨_, Rules.inferTypeCore_bridge hta⟩
  obtain ⟨hFrB, hCB, hGB⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hBL hBb hba
    ⟨_, Rules.inferTypeCore_bridge htb⟩
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge hd) hFrA hFrB hCA hCB haa hba
    hGA hGB _ hW0.2.1
  rw [hA] at haa
  rw [hB] at hba
  rw [haa, hba]
  simp only [Option.map_some, heq]

/-- **A matched parameter spine reads alike at the prefix**: the class
match's parameter run (`targetParamsDefEq`) passed, every pair reads
alike (`param_read_eq`), so the two spines' readings agree. -/
theorem params_read_eq {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F D : Nat} {pfvs : List Expr}
    (hL : FvarList D pfvs.reverse) {σ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ D σ Δ pfvs.reverse)
    {names : List Name} {lvls : List Level} {formerTys : List Expr} {hv : List V}
    (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    (hnames : ∀ (n : Name) (t : Nat), names.findIdx? (· == n) = some t →
      t < formerTys.length ∧ ∃ ci : ConLeche.ConstantInfo, envT.find? n = some ci ∧
        lvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mT.acval n (Level.substFn φ ci.toConstantVal.levelParams lvls))
          = hv.getD t pt)
    {ds eds : List Expr}
    (hm : ConLeche.targetParamsDefEq (ConLeche.fueledOps μ F) envT (D + formerTys.length)
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)) pfvs ds eds = .ok true) :
    ds.map (fun x => interp V σ ((denoteMeta mT.acval envT φ D x).getD default))
      = eds.map (fun x => interp V σ ((denoteMeta mT.acval envT φ D x).getD default)) := by
  obtain ⟨hl, hall⟩ := ConLeche.targetParamsDefEq_true hm
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map]
  cases hx : ds[i]? with
  | none =>
    have : eds[i]? = none := List.getElem?_eq_none (by
      have := List.getElem?_eq_none_iff.mp hx; omega)
    rw [this]
  | some a =>
    obtain ⟨b, hb⟩ : ∃ b, eds[i]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hx).1; omega)⟩
    rw [hb]
    have h := param_read_eq hμ hacl hin hL hW hvl hformer hnames (hall i a b hx hb)
    simp only [Option.map_some, Option.some.injEq]
    cases h1 : denoteMeta mT.acval envT φ D a with
    | none =>
      rw [h1] at h
      cases h2 : denoteMeta mT.acval envT φ D b with
      | none => rfl
      | some _ => rw [h2] at h; exact nomatch h
    | some x =>
      rw [h1] at h
      cases h2 : denoteMeta mT.acval envT φ D b with
      | none => rw [h2] at h; exact nomatch h
      | some y =>
        rw [h2] at h
        simpa using h

end Walk

/-! ## One key frame -/

/-- Key frames of spines reading alike agree (whence one hole fit, one
carrier, one index set — the parked `tie_fits`). -/
theorem keyFrame_eq_of_params {dsa₁ dsa₂ : List AnnotTerm} {hi : Nat} {ρ : Nat → V}
    (h : dsa₁.map (interp V ρ) = dsa₂.map (interp V ρ)) :
    keyFrame dsa₁ hi ρ = keyFrame dsa₂ hi ρ := by
  unfold keyFrame; rw [h]

end ConLeche.Model
