module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.ClassGenUniq
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Rules.InferSoundKit

public section

/-!
# The family premise at the GENERATED recursor stage (`hpre`, lane GENREC-B1)

The skeleton's `hpre` obligation (`GenRecAssembly.lean`, `genRecStage`) —
the recursor model's family premise `BlockRecPre` at every level
assignment and base frame — at the generated family's equation
components (`blockRulePdomsAV`, `tgtFdomsAV`, `tgtEsAV`, `genIhsAV`,
`tgtMkAV`, `genRbAV`).  Its three halves:

* `hTy` — the recursor types' level (`blockRecLevel_run`), passed in;
* `hEq` — the equations are truth values (by their shape,
  `iotaEqAV_univZero`) and graded at every typed tuple (a row);
* `hCand` — the candidate, through the graph producer over a step
  premise (`graphRecPre_coreR`, `ClassRecKit.lean`) at the OLD class data
  (`tgtClsIs`/`tgtClsCr`/`tgtClsInj`/`tgtClsU`/`tgtClsNIdx`/`tgtClsTup`/
  `tgtClsFit`, `TargetClasses.lean`), the generated calls (`genCallT`) and
  the class induction in the interface form `GenClassInd` (lane B2).

The graph's `ih` values are the generated `ih` terms read at the chain
valuation of the graph (`genIhvT`: every recursor the graph-regime
λ-tower over its stored type's domains reading the graph at the
tagged major).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockShape TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 1. The graph's `ih` values -/

section Ihv

private theorem defFun_mkTower_ofFn {p : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin p → V) → V), (∀ i, DefFun p (As i)) →
      DefFun p fun v => ConLeche.SetTheory.Tower.mkTower (List.ofFn fun i => As i v)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [ConLeche.SetTheory.Tower.mkTower]
  | _ + 1, As, hAs =>
    (DefFun.spair_apply (hAs 0)
      (defFun_mkTower_ofFn (fun i => As i.succ) (fun i => hAs i.succ))).congr fun v => by
      simp [List.ofFn_succ, ConLeche.SetTheory.Tower.mkTower]

private theorem defFun_tupW_ofFn (u : Nat) {p r : Nat}
    (As : Fin r → (Fin p → V) → V) (hAs : ∀ i, DefFun p (As i)) :
    DefFun p fun v => tupW u (List.ofFn fun i => As i v) := by
  by_cases hu : u = 0
  · subst hu; exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn As hAs).congr fun _ => (tupW_pos hu _).symm

theorem defFun_majOf_revList : ∀ n : Nat,
    DefFun (V := V) n fun xs : Fin n → V => majOf (revList xs)
  | 0 => DefFun.pt.congr fun _ => by simp [majOf, revList]
  | n + 1 => (DefFun.proj ⟨0, Nat.zero_lt_succ n⟩).congr fun xs => by
    have hrev : (revList xs).reverse = List.ofFn xs := by
      apply List.ext_getElem (by simp [revList])
      intro i h1 h2
      simp only [List.length_ofFn] at h2
      simp only [List.getElem_reverse, List.getElem_ofFn, revList, List.length_ofFn]
      exact congrArg xs (Fin.ext (by dsimp; omega))
    simp only [majOf, hrev]
    rw [List.ofFn_succ, List.headD_cons]
    rfl

private noncomputable def lamTowerSubG (ρ0 : Nat → V) (G : V → List V → (Nat → V) → V) :
    ∀ (p : Nat) (ds : List Term),
      DefFun ((p + ds.length) + 1)
        (fun w : Fin ((p + ds.length) + 1) → V =>
          G (w ⟨p + ds.length, Nat.lt_succ_self _⟩)
            (revList (ftake (k := p + ds.length) (p := 1) w))
            (Semantics.prepend (ftake (k := p + ds.length) (p := 1) w) ρ0)) →
      { F : (Fin (p + 1) → V) → V // DefFun (p + 1) F }
  | p, [], hg =>
    ⟨fun xs =>
      G (xs ⟨p, Nat.lt_succ_self _⟩)
        (revList (ftake (k := p) (p := 1) xs))
        (Semantics.prepend (ftake (k := p) (p := 1) xs) ρ0),
      hg⟩
  | p, d :: ds, hg =>
    have hg' : DefFun (((p + 1) + ds.length) + 1) fun w =>
        G (w ⟨(p + 1) + ds.length, Nat.lt_succ_self _⟩)
          (revList (ftake (k := (p + 1) + ds.length) (p := 1) w))
          (Semantics.prepend (ftake (k := (p + 1) + ds.length) (p := 1) w) ρ0) :=
      (hg.reIndex (n := ((p + 1) + ds.length) + 1)
        fun i : Fin ((p + (d :: ds).length) + 1) =>
          ⟨i.val, by simp only [List.length_cons] at *; omega⟩).congr fun w => by
        congr 1
        · exact congrArg w (Fin.ext (by simp [List.length_cons]; omega))
        · apply List.ext_getElem (by simp [revList, List.length_cons]; omega)
          intro i h1 h2
          simp only [revList, List.length_ofFn] at h2
          simp only [revList, List.getElem_ofFn, ftake]
          exact congrArg w (Fin.ext (by dsimp; omega))
        · funext j
          by_cases hj : j < (p + 1) + ds.length
          · have hj' : j < p + (d :: ds).length := by simp [List.length_cons]; omega
            simp only [Semantics.prepend, hj, hj', ↓reduceDIte, ftake]
          · have hj' : ¬ (j < p + (d :: ds).length) := by simp [List.length_cons]; omega
            simp only [Semantics.prepend, hj, hj', ↓reduceDIte]
            congr 1; simp [List.length_cons]; omega
    let sub := lamTowerSubG ρ0 G (p + 1) ds hg'
    let hA : DefFun (p + 1) fun xs => interp V (Semantics.prepend (ftake (k := p) (p := 1) xs) ρ0) d :=
      ((interp_defFun_prepend ρ0 p d).comp fun i => DefFun.proj ⟨i.val, by omega⟩).congr fun _ => rfl
    let hB : DefFun ((p + 1) + 1) fun v => sub.val (fcons (v 0) (ftail v)) :=
      sub.property.congr fun v => congrArg sub.val (fcons_zero_ftail v).symm
    ⟨fun xs => lamV (interp V (Semantics.prepend (ftake (k := p) (p := 1) xs) ρ0) d)
        (fun a => sub.val (fcons a xs))
        (hasGraph_of_defFun1 (defFun1_fcons sub.property xs)),
      DefFun.lamV_apply_curry hB hA⟩

private theorem lamTowerSubG_eq (ρ0 : Nat → V) (G : V → List V → (Nat → V) → V) :
    ∀ (p : Nat) (ds : List Term)
      (hg : DefFun ((p + ds.length) + 1) fun w =>
        G (w ⟨p + ds.length, Nat.lt_succ_self _⟩)
          (revList (ftake (k := p + ds.length) (p := 1) w))
          (Semantics.prepend (ftake (k := p + ds.length) (p := 1) w) ρ0))
      (xs : Fin (p + 1) → V)
      (hgp : DefFun (p + ds.length) fun w =>
        G (xs ⟨p, Nat.lt_succ_self _⟩) (revList w) (Semantics.prepend w ρ0)),
      (lamTowerSubG ρ0 G p ds hg).val xs =
        (lamTowerSub ρ0 (G (xs ⟨p, Nat.lt_succ_self _⟩)) p ds hgp).val
          (ftake (k := p) (p := 1) xs)
  | _, [], _, _, _ => by simp only [lamTowerSubG, lamTowerSub]
  | p, d :: ds, hg, xs, hgp => by
    simp only [lamTowerSubG, lamTowerSub]
    refine lamV_ext (V := V) rfl _ _ fun a _ => ?_
    have hg_eq : (fcons a xs) ⟨p + 1, Nat.lt_succ_self _⟩ = xs ⟨p, Nat.lt_succ_self _⟩ := by
      change (ftail (fcons a xs)) ⟨p, Nat.lt_succ_self _⟩ = _
      rw [ftail_fcons]
    have hgp' : DefFun ((p + 1) + ds.length) fun w =>
        G ((fcons a xs) ⟨p + 1, Nat.lt_succ_self _⟩) (revList w) (Semantics.prepend w ρ0) := by
      rw [hg_eq]
      exact (defFun_revList_shift hgp).congr fun w => rfl
    have hft_eq : ftake (k := p + 1) (p := 1) (fcons a xs) =
        fcons a (ftake (k := p) (p := 1) xs) := by
      funext ⟨i, hi⟩
      cases i with
      | zero => simp [ftake, fcons_zero]
      | succ i =>
        change (ftail (fcons a xs)) ⟨i, by omega⟩ = (ftail (fcons a (ftake (k := p) (p := 1) xs))) ⟨i, by omega⟩
        rw [ftail_fcons, ftail_fcons]; rfl
    rw [lamTowerSubG_eq ρ0 G (p + 1) ds _ (fcons a xs) hgp', hft_eq]
    simp only [hg_eq]

private theorem defFun_lamTowerA_app (ρ : Nat → V) (ds : List Term) (B : List V → V)
    (hB : DefFun ds.length fun xs : Fin ds.length → V => B (revList xs)) :
    DefFun 1 fun w : Fin 1 → V =>
      lamTowerA ρ ds (fun sp _ => app (w 0) (B sp))
        (DefFun.app_apply (DefFun.const (w 0)) hB) := by
  let G : V → List V → (Nat → V) → V := fun g sp _ => app g (B sp)
  have hB' : DefFun ((0 + ds.length) + 1) fun w =>
      B (revList (ftake (k := 0 + ds.length) (p := 1) w)) := by
    refine (hB.reIndex (n := (0 + ds.length) + 1) fun i => ⟨i.val, by omega⟩).congr fun w => ?_
    congr 1
    apply List.ext_getElem (by simp [revList])
    intro i h1 h2
    simp only [revList, List.length_ofFn] at h2
    simp only [revList, List.getElem_ofFn, ftake]
    exact congrArg w (Fin.ext (by dsimp; omega))
  have hG : DefFun ((0 + ds.length) + 1) fun w =>
      G (w ⟨0 + ds.length, Nat.lt_succ_self _⟩)
        (revList (ftake (k := 0 + ds.length) (p := 1) w))
        (Semantics.prepend (ftake (k := 0 + ds.length) (p := 1) w) ρ) :=
    DefFun.app_apply (DefFun.proj ⟨0 + ds.length, Nat.lt_succ_self _⟩) hB'
  refine (lamTowerSubG ρ G 0 ds hG).property.congr fun w => ?_
  have heq := lamTowerSubG_eq ρ G 0 ds hG w
    ((Nat.zero_add ds.length).symm ▸ (DefFun.app_apply (DefFun.const (w 0)) hB))
  have hft : ftake (k := 0) (p := 1) w = Fin.elim0 := funext fun i => Fin.elim0 i
  rw [hft] at heq
  exact heq

/-- **The chain valuation of a graph** at the stored domains `rds`:
recursor `t` is the graph-regime λ-tower over its domains reading
`g` at the tagged major (`genF` over any domains and tuple
function). -/
@[expose] noncomputable def genFT (ρ : Nat → V) (rP : Nat → Nat)
    (rds : Nat → List Term) (tup : Nat → List V → V)
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (g : V) (t : Nat) : V :=
  lamTowerA ρ (rds t)
    (fun sp _ => app g (tagged t (tup t (idxOf (rP t) sp)) (majOf sp)))
    (DefFun.app_apply (DefFun.const g)
      (DefFun.tagged_apply t (htup t) (defFun_majOf_revList (rds t).length)))

private theorem defFun_genFT (ρ : Nat → V) (rP : Nat → Nat) (rds : Nat → List Term)
    (tup : Nat → List V → V)
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (t : Nat) :
    DefFun 1 fun w => genFT ρ rP rds tup htup (w 0) t :=
  (defFun_lamTowerA_app ρ (rds t) (fun sp => tagged t (tup t (idxOf (rP t) sp)) (majOf sp))
    (DefFun.tagged_apply t (htup t) (defFun_majOf_revList (rds t).length))).congr fun _ => rfl

/-- **The graph's `ih` values**: the `ih` terms read at the chain
valuation of the graph. -/
@[expose] noncomputable def genIhvT (K : Nat) (ρ : Nat → V) (rP : Nat → Nat)
    (rds : Nat → List Term) (tup : Nat → List V → V)
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (ihs : Nat → Nat → List Term) (xs : List V) (c j : Nat) (fs : List V) (g : V) :
    List V :=
  (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup htup g) ρ)))

end Ihv

/-! ## 2. The equation list at the chain spelling -/

section Eqs

variable {F : Nat} {envC : Env} {pp : BlockShape} {formers : List ConstantVal}
  {memberCtors : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC}

/-- **The generated equation list, at the chain spelling** (`tgtClsEqs_eq`
at any `ih` terms and residue): the prefix domains are closed
(`blockRecPdomsK_run`), and the chain lifts keep the field domains'
lengths. -/
theorem genClsEqs_eq
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (ihs : (Name → Nat) → Nat → Nat → List Term)
    (Rb0 : (Name → Nat) → Nat → Nat → Term) (ψ : Name → Nat) :
    iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ)
        (fun c j => liftEsK (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
            + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
          (tgtEsAV pp out mpC.base2.acval envC ψ c j))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
            + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c
              j).length
            + (ihs ψ c j).length))
      = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp out mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => tgtMkAV pp out mpC.base2.acval envC ψ')
          Rb0 ψ := by
  show _ = iotaEqsAV _ _ _ _ _ _ _ _
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c _ j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) mpC h (List.getElem?_eq_getElem hc) ψ _).symm
  · simp only [tgtFdomsK, liftDomsK_length]

/-- Every member of the family's equation list is a truth value. -/
theorem blockRecEqs_univZero (nCt : Nat → Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (pdoms0 : (Name → Nat) → Nat → List Term)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List Term)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → Term) (ψ : Name → Nat) (σ : Nat → V) :
    ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
      interp V σ e ∈ˢ (univZero : V) :=
  forall_iotaEqsAV fun _ _ _ _ => iotaEqAV_univZero

end Eqs

/-! ## 2.5 Definability and separation helpers for `graphRecPre_coreR` -/

section DefHelpers

private theorem consList_ofFn_prepend {k m : Nat} (bsVec : Fin k → V) (ps : Fin m → V)
    (tail : Nat → V) :
    consList (List.ofFn bsVec) (Semantics.prepend ps tail) =
      Semantics.prepend (fun l : Fin (k + m) =>
        if hl : l.val < k then bsVec ⟨k - 1 - l.val, by omega⟩
        else ps ⟨l.val - k, by omega⟩) tail := by
  funext q
  by_cases hq1 : q < k
  · rw [consList_getD_of_lt _ _ _ (by simp; exact hq1)]
    simp only [List.length_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show k - 1 - q < (List.ofFn bsVec).length by simp; omega),
      Option.getD_some, List.getElem_ofFn, Semantics.prepend, show q < k + m by omega, hq1,
      ↓reduceDIte]
  · have hqeq : q = (q - k) + (List.ofFn bsVec).length := by simp; omega
    rw [hqeq, consList_apply_add]
    by_cases hq2 : q < k + m
    · have hm : q - k < m := by omega
      simp only [Semantics.prepend, hm, ↓reduceDIte, List.length_ofFn,
        show q - k + k < k + m by omega, show ¬ (q - k + k < k) by omega]
      congr 1; ext; dsimp; omega
    · have hm : ¬ (q - k < m) := by omega
      simp only [Semantics.prepend, hm, ↓reduceDIte, List.length_ofFn,
        show ¬ (q - k + k < k + m) by omega]
      congr 1; omega

private theorem consList_revList_prepend {n m : Nat} (xsVec : Fin n → V) (ps : Fin m → V)
    (tail : Nat → V) :
    consList (revList xsVec) (Semantics.prepend ps tail) =
      Semantics.prepend (fun l : Fin (n + m) =>
        if hl : l.val < n then xsVec ⟨l.val, hl⟩
        else ps ⟨l.val - n, by omega⟩) tail := by
  rw [revList, consList_ofFn_prepend]
  congr 1
  funext l
  by_cases hl : l.val < n
  · simp only [hl, ↓reduceDIte]
    congr 1; ext; dsimp; omega
  · simp only [hl, ↓reduceDIte]

private theorem consList_append_ofFn_prepend {n m : Nat} (xsVec : Fin n → V) (fsVec : Fin m → V)
    (ρ : Nat → V) :
    consList (revList xsVec ++ List.ofFn fsVec) ρ =
      Semantics.prepend (fun l : Fin (m + n) =>
        if hl : l.val < m then fsVec ⟨m - 1 - l.val, by omega⟩
        else xsVec ⟨l.val - m, by omega⟩) ρ := by
  rw [consList_append]
  have h1 : consList (revList xsVec) ρ = Semantics.prepend xsVec ρ := by
    have hp0 : Semantics.prepend Fin.elim0 ρ = ρ := funext fun j => by simp [Semantics.prepend]
    calc consList (revList xsVec) ρ
        = consList (revList xsVec) (Semantics.prepend Fin.elim0 ρ) := by rw [hp0]
      _ = Semantics.prepend xsVec ρ := by
          rw [consList_revList_prepend]
          congr 1; funext ⟨i, hi⟩; simp only [Nat.add_zero] at hi; simp [hi]
  rw [h1, consList_ofFn_prepend]

private theorem defRel_exists_spineFit_prepend {d : Nat} (tail : Nat → V) :
    ∀ (Ts : List Term) {m : Nat} (Xs : Fin m → (Fin d → V) → V), (∀ i, DefFun d (Xs i)) →
      DefRel d fun v => ∃ is : List V, SpineFit (Semantics.prepend (fun i => Xs i v) tail) Ts is
  | [], _, _, _ => DefRel.true.congr fun _ => ⟨fun _ => ⟨[], trivial⟩, fun _ => trivial⟩
  | F :: Ts, m, Xs, hXs => by
    let Xs' : Fin (m + 1) → (Fin (d + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (d + 1) (Xs' i) := fun ⟨i, _⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    have ih := defRel_exists_spineFit_prepend tail Ts Xs' hXs'
    have hF : DefFun (d + 1) fun w =>
        interp V (Semantics.prepend (fun i => Xs i (ftail w)) tail) F :=
      ((interp_defFun_prepend tail m F).comp hXs).weaken
    let R_body : V → (Fin d → V) → Prop := fun a v =>
      a ∈ˢ interp V (Semantics.prepend (fun i => Xs i v) tail) F ∧
        ∃ is : List V, SpineFit (Semantics.prepend (fun i => Xs' i (fcons a v)) tail) Ts is
    have hBody : DefRel (d + 1) fun w => R_body (w 0) (ftail w) := by
      refine (DefRel.and (DefRel.mem_apply (DefFun.proj 0) hF) ih).congr fun w => ?_
      dsimp only [R_body]
      have hfw : fcons (w 0) (ftail w) = w := fcons_zero_ftail w
      rw [hfw]
    refine (DefRel.exists_curry (R := R_body) hBody).congr fun v => ?_
    constructor
    · rintro ⟨a, ha, vs, hvs⟩
      refine ⟨a :: vs, ha, ?_⟩
      have hp : Semantics.prepend (fun i => Xs' i (fcons a v)) tail =
          cons a (Semantics.prepend (fun i => Xs i v) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs', fcons_zero]
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      rwa [← hp]
    · rintro ⟨(_ | ⟨a, vs⟩), hsp⟩
      · exact hsp.elim
      · refine ⟨a, hsp.1, vs, ?_⟩
        have hp : Semantics.prepend (fun i => Xs' i (fcons a v)) tail =
            cons a (Semantics.prepend (fun i => Xs i v) tail) := by
          funext j
          cases j with
          | zero => simp [Semantics.prepend, Xs', fcons_zero]
          | succ j =>
            by_cases hj : j < m
            · have hj1 : j + 1 < m + 1 := by omega
              simp [Semantics.prepend, hj, hj1, Xs', cons]
            · have hj1 : ¬ (j + 1 < m + 1) := by omega
              simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
              congr 1; omega
        rw [hp]
        exact hsp.2

private theorem defRel_sat_prepend {d m : Nat} (tail : Nat → V)
    (Xs : Fin m → (Fin d → V) → V) (hXs : ∀ i, DefFun d (Xs i))
    (Δ : List Term) :
    DefRel d fun v => Sat V Δ (Semantics.prepend (fun i => Xs i v) tail) := by
  refine (DefRel.finForall (R := fun (idx : Fin Δ.length) (v : Fin d → V) =>
      Semantics.prepend (fun i => Xs i v) tail idx.val ∈ˢ
        interp V (fun j => Semantics.prepend (fun i => Xs i v) tail (j + idx.val + 1)) Δ[idx.val])
    fun idx => ?_).congr fun v => ?_
  · have hhead : DefFun d fun v => Semantics.prepend (fun i => Xs i v) tail idx.val := by
      by_cases hi : idx.val < m
      · exact (hXs ⟨idx.val, hi⟩).congr fun v => by simp [Semantics.prepend, hi]
      · exact (DefFun.const (tail (idx.val - m))).congr fun v => by simp [Semantics.prepend, hi]
    let m' := m - (idx.val + 1)
    let tail' : Nat → V := fun j =>
      if _ : idx.val + 1 ≤ m then tail j else tail (j + (idx.val + 1 - m))
    let Xs' : Fin m' → (Fin d → V) → V := fun k v =>
      Xs ⟨k.val + idx.val + 1, by dsimp [m'] at k; omega⟩ v
    have hXs' : ∀ k, DefFun d (Xs' k) := fun k => hXs _
    have harg : DefFun d fun v =>
        interp V (fun j => Semantics.prepend (fun i => Xs i v) tail (j + idx.val + 1)) Δ[idx.val] := by
      refine ((interp_defFun_prepend tail' m' Δ[idx.val]).comp hXs').congr fun v => ?_
      congr 1
      funext j
      by_cases hm : idx.val + 1 ≤ m
      · by_cases hj : j < m'
        · have hj' : j + idx.val + 1 < m := by dsimp [m'] at hj; omega
          simp only [Semantics.prepend, hj, hj', ↓reduceDIte, Xs']
        · have hj' : ¬ (j + idx.val + 1 < m) := by dsimp [m'] at hj; omega
          simp only [Semantics.prepend, hj, hj', ↓reduceDIte, tail', hm]
          congr 1; dsimp [m']; omega
      · have hj1 : ¬ (j < m') := by dsimp [m']; omega
        have hj2 : ¬ (j + idx.val + 1 < m) := by omega
        simp only [Semantics.prepend, hj1, hj2, ↓reduceDIte, tail', hm]
        congr 1; dsimp [m']; omega
    exact DefRel.mem_apply hhead harg
  · unfold Sat
    constructor
    · intro h i Aa hi
      have hil : i < Δ.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_eq_getElem hil, Option.some.injEq] at hi
      subst hi
      exact h ⟨i, hil⟩
    · intro h idx
      exact h idx.val _ (List.getElem?_eq_getElem idx.isLt)

private theorem defRel_spineFit_listOfFn {p : Nat} (tail : Nat → V) :
    ∀ (Ts : List Term) {m : Nat} (ps : Fin m → (Fin p → V) → V), (∀ i, DefFun p (ps i)) →
      (Xs : Fin Ts.length → (Fin p → V) → V) → (∀ i, DefFun p (Xs i)) →
      DefRel p fun v => SpineFit (Semantics.prepend (fun i => ps i v) tail) Ts
        (List.ofFn fun i => Xs i v)
  | [], _, _, _, _, _ => DefRel.true.congr fun _ => by simp [SpineFit]
  | T :: Ts, m, ps, hps, Xs, hXs => by
    let ps' : Fin (m + 1) → (Fin p → V) → V := fun i v =>
      if h0 : i.val = 0 then Xs 0 v else ps ⟨i.val - 1, by omega⟩ v
    have hps' : ∀ i, DefFun p (ps' i) := fun ⟨i, _⟩ => by
      dsimp only [ps']
      split
      · exact hXs 0
      · exact hps _
    have hhead : DefRel p fun v =>
        Xs 0 v ∈ˢ interp V (Semantics.prepend (fun i => ps i v) tail) T :=
      DefRel.mem_apply (hXs 0) ((interp_defFun_prepend tail m T).comp hps)
    have htail := defRel_spineFit_listOfFn tail Ts ps' hps' (fun i => Xs i.succ)
      (fun i => hXs i.succ)
    refine (hhead.and htail).congr fun v => ?_
    rw [List.ofFn_succ, SpineFit]
    have hprep : cons (Xs 0 v) (Semantics.prepend (fun i => ps i v) tail) =
        Semantics.prepend (fun i => ps' i v) tail := by
      funext j
      cases j with
      | zero => simp [Semantics.prepend, ps', cons]
      | succ j =>
        by_cases hj : j < m
        · have hj1 : j + 1 < m + 1 := by omega
          simp [Semantics.prepend, hj, hj1, cons]
          simp [ps']
        · have hj1 : ¬ (j + 1 < m + 1) := by omega
          simp [Semantics.prepend, hj, hj1, cons]
    rw [hprep]

private theorem defFun_holeFam_param {d : Nat} (tail : Nat → V) (Fs : List Term)
    (G : (Fin d → V) → List V → V)
    (hGd : ∀ xs : Fin d → V, DefHoleFn Fs.length (G xs))
    (hG : DefFun (d + Fs.length) fun w =>
      G (ftake (k := d) (p := Fs.length) w) (List.ofFn (fdrop (k := d) (p := Fs.length) w))) :
    DefFun d fun xs => holeFam (Semantics.prepend xs tail) Fs (G xs) (hGd xs) := by
  refine (holeFamDef d tail Fs _ hG).property.congr fun xs => ?_
  rw [holeFamDef_prepend Fs d xs tail]
  unfold holeFam
  refine holeFamDef_congr 0 (Semantics.prepend xs tail) Fs _ _ (fun bs => ?_) Fin.elim0
  congr 1
  · funext ⟨i, hi⟩
    simp [ftake, hi]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, fdrop]
    have hnot : ¬ (d + i < d) := by omega
    simp [hnot]

private theorem defFun_holeVal_param (D : LfpDatum V) (hN : D.k ≤ D.N) (ψ : Name → Nat)
    (tail : Nat → V) (d m : Nat) (hm : m < D.k) :
    DefFun d fun ps =>
      D.holeVal ψ (Semantics.prepend ps tail) (D.carrier ψ (Semantics.prepend ps tail)) m := by
  unfold LfpDatum.holeVal
  have hmN : m < D.N := Nat.lt_of_lt_of_le hm hN
  let Fs := D.ids m ψ
  let G : (Fin d → V) → List V → V := fun ps vs =>
    app (D.carrier ψ (Semantics.prepend ps tail) m) (tupW (D.u m ψ) vs)
  have hGd : ∀ ps : Fin d → V, DefHoleFn Fs.length (G ps) := fun ps =>
    DefHoleFn.of_app_tupW (D.carrier ψ (Semantics.prepend ps tail) m) (D.u m ψ) Fs.length
  have hG : DefFun (d + Fs.length) fun w =>
      G (ftake (k := d) (p := Fs.length) w)
        (List.ofFn (fdrop (k := d) (p := Fs.length) w)) := by
    have hcar : DefFun (d + Fs.length) fun w =>
        D.carrier ψ (Semantics.prepend (ftake (k := d) (p := Fs.length) w) tail) m :=
      ((D.defFun_carrier ψ tail d m hmN).comp fun i => DefFun.ftake_proj i).congr fun _ => rfl
    have htup : DefFun (d + Fs.length) fun w =>
        tupW (D.u m ψ) (List.ofFn (fdrop (k := d) (p := Fs.length) w)) :=
      defFun_tupW_ofFn (D.u m ψ) (fun i w => (fdrop (k := d) (p := Fs.length) w) i)
        (fun i => DefFun.fdrop_proj (V := V) i)
    exact DefFun.app_apply hcar htup
  exact defFun_holeFam_param tail Fs G hGd hG

private theorem tgtClsFr_eq_prepend (d : BlockData V)
    (acval : Name → (Name → Nat) → Term) (envC : Env) (pp : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (ρ : Nat → V)
    (m n : Nat) :
    ∃ (tail_fr : Nat → V) (len_fr : Nat) (ps_fr : Fin len_fr → (Fin n → V) → V),
      (∀ l, DefFun n (ps_fr l)) ∧
      ∀ xsVec : Fin n → V,
        tgtClsFr d acval envC pp out ψ ρ (revList xsVec) m =
          Semantics.prepend (fun l => ps_fr l xsVec) tail_fr := by
  by_cases hm : (tgtMajor out m).member.isSome = true
  · let k₁ := min d.nP n
    refine ⟨ρ, k₁, fun l xsVec => xsVec ⟨n - k₁ + l.val, by omega⟩,
      fun _ => DefFun.proj _, fun xsVec => ?_⟩
    rw [tgtClsFr, ite_eq_left hm]
    funext q
    have htake : ((revList xsVec).take d.nP).length = k₁ := by simp [k₁, revList]
    by_cases hq : q < k₁
    · rw [consList_getD_of_lt _ _ _ (by rw [htake]; exact hq)]
      simp only [Semantics.prepend, hq, ↓reduceDIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by rw [htake]; omega), Option.getD_some,
        List.getElem_take]
      simp only [revList, List.getElem_ofFn]
      exact congrArg xsVec (Fin.ext (by simp [k₁]; omega))
    · have hqeq : consList ((revList xsVec).take d.nP) ρ q = ρ (q - k₁) := by
        have h1 : q = (q - k₁) + ((revList xsVec).take d.nP).length := by omega
        calc consList ((revList xsVec).take d.nP) ρ q
            = consList ((revList xsVec).take d.nP) ρ
                ((q - k₁) + ((revList xsVec).take d.nP).length) := by rw [← h1]
          _ = ρ (q - k₁) := consList_apply_add _ _ _
      rw [hqeq]
      simp only [Semantics.prepend, hq, ↓reduceDIte]
  · let dsa := tgtOutDsa acval envC pp out ψ m
    let hi := tgtRP pp m
    let nrest := n - hi
    refine ⟨fun q => ρ (q + (hi - n)), dsa.length + nrest, fun l xsVec =>
      if hl : l.val < dsa.length then
        interp V (Semantics.prepend xsVec ρ) dsa[dsa.length - 1 - l.val]
      else xsVec ⟨hi + (l.val - dsa.length), by dsimp [nrest] at l hl; omega⟩,
      fun l => by
        dsimp only
        split
        · exact interp_defFun_prepend ρ n _
        · exact DefFun.proj _,
      fun xsVec => ?_⟩
    rw [tgtClsFr, ite_eq_right hm, keyFrame]
    have hxs : consList (revList xsVec) ρ = Semantics.prepend xsVec ρ := by
      have hp0 : Semantics.prepend Fin.elim0 ρ = ρ := funext fun j => by simp [Semantics.prepend]
      calc consList (revList xsVec) ρ
          = consList (revList xsVec) (Semantics.prepend Fin.elim0 ρ) := by rw [hp0]
        _ = Semantics.prepend xsVec ρ := by
            rw [consList_revList_prepend]
            congr 1; funext ⟨i, hi'⟩; simp only [Nat.add_zero] at hi'; simp [hi']
    rw [hxs]
    let tailFn : Fin nrest → V := fun l => xsVec ⟨hi + l.val, by dsimp [nrest] at l; omega⟩
    have htail_eq : (fun j => Semantics.prepend xsVec ρ (j + hi)) =
        Semantics.prepend tailFn (fun q => ρ (q + (hi - n))) := by
      funext j
      by_cases hj : j < nrest
      · have hj' : j + hi < n := by dsimp [nrest] at hj; omega
        simp only [Semantics.prepend, hj, hj', ↓reduceDIte, tailFn]
        congr 1; ext; dsimp; omega
      · have hj' : ¬ (j + hi < n) := by dsimp [nrest] at hj; omega
        simp only [Semantics.prepend, hj, hj', ↓reduceDIte]
        congr 1; dsimp [nrest] at hj ⊢; omega
    have hmap : (tgtOutDsa acval envC pp out ψ m).map (interp V (Semantics.prepend xsVec ρ)) =
        List.ofFn fun i : Fin dsa.length =>
          interp V (Semantics.prepend xsVec ρ) dsa[i.val] := by
      apply List.ext_getElem (by simp [dsa])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_ofFn, dsa]
    dsimp only [hi]
    rw [htail_eq, hmap, consList_ofFn_prepend]

private theorem defFun_tgtClsCr_param (d : BlockData V) (Dc : Nat → LfpDatum V) (mc : Nat → Nat)
    (cvc : Nat → ConstantVal) (acval : Name → (Name → Nat) → Term) (envC : Env)
    (pp : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (ρ : Nat → V) {n m : Nat} (hmN : tgtClsM mc pp out m < (tgtClsD d Dc out m).N) :
    DefFun n fun xsVec : Fin n → V =>
      tgtClsCr d Dc mc cvc acval envC pp out ψ ρ (revList xsVec) m := by
  obtain ⟨tail_fr, len_fr, ps_fr, hps_fr, hfr⟩ :=
    tgtClsFr_eq_prepend d acval envC pp out ψ ρ m n
  let D := tgtClsD d Dc out m
  let ψm := tgtClsψ cvc out ψ m
  let mm := tgtClsM mc pp out m
  refine ((D.defFun_carrier ψm tail_fr len_fr mm hmN).comp hps_fr).congr fun xsVec => ?_
  rw [tgtClsCr, hfr xsVec]

private theorem defFun_tgtClsIs_param (d : BlockData V) (Dc : Nat → LfpDatum V) (mc : Nat → Nat)
    (cvc : Nat → ConstantVal) (acval : Name → (Name → Nat) → Term) (envC : Env)
    (pp : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (ρ : Nat → V) (n m : Nat) :
    DefFun n fun xsVec : Fin n → V =>
      tgtClsIs d Dc mc cvc acval envC pp out ψ ρ (revList xsVec) m := by
  obtain ⟨tail_fr, len_fr, ps_fr, hps_fr, hfr⟩ :=
    tgtClsFr_eq_prepend d acval envC pp out ψ ρ m n
  let D := tgtClsD d Dc out m
  let ψm := tgtClsψ cvc out ψ m
  let mm := tgtClsM mc pp out m
  have hIdx : DefFun n fun xsVec =>
      D.idx ψm (tgtClsFr d acval envC pp out ψ ρ (revList xsVec) m) mm :=
    ((D.defFun_idx ψm tail_fr len_fr mm).comp hps_fr).congr fun xsVec => by
      rw [hfr xsVec]
  have hG_pdom : DefRel n fun xsVec : Fin n → V =>
      SpineFit ρ (blockRulePdomsAV acval envC pp (tgtRs out) ψ m) (revList xsVec) := by
    let pds := blockRulePdomsAV acval envC pp (tgtRs out) ψ m
    by_cases hlen : pds.length = n
    · have hp := defRel_spineFit_listOfFn (p := n) ρ pds
        (fun i (_ : Fin n → V) => i.elim0) (fun i => i.elim0)
        (fun i xsVec => xsVec ⟨n - 1 - i.val, by omega⟩) (fun _ => DefFun.proj _)
      refine hp.congr fun xsVec => ?_
      have h0 : Semantics.prepend (fun i : Fin 0 => (Fin.elim0 i : V)) ρ = ρ := by
        funext q; simp [Semantics.prepend]
      have hl : (List.ofFn fun i : Fin pds.length => xsVec ⟨n - 1 - i.val, by omega⟩) =
          revList xsVec := by
        apply List.ext_getElem (by simp [revList, hlen])
        intro i h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, revList]
      rw [h0, hl]
    · exact (DefRel.false (V := V)).congr fun xsVec =>
        ⟨False.elim, fun hsp => absurd (by simpa [revList] using hsp.length_eq.symm) hlen⟩
  have hG_par : DefRel n fun xsVec : Fin n → V =>
      SpineFit ρ (d.params ψ) ((revList xsVec).take d.nP) := by
    let pars := d.params ψ
    by_cases hlen : pars.length = min d.nP n
    · have hp := defRel_spineFit_listOfFn (p := n) ρ pars
        (fun i (_ : Fin n → V) => i.elim0) (fun i => i.elim0)
        (fun i xsVec => xsVec ⟨n - 1 - i.val, by omega⟩) (fun _ => DefFun.proj _)
      refine hp.congr fun xsVec => ?_
      have h0 : Semantics.prepend (fun i : Fin 0 => (Fin.elim0 i : V)) ρ = ρ := by
        funext q; simp [Semantics.prepend]
      have hl : (List.ofFn fun i : Fin pars.length => xsVec ⟨n - 1 - i.val, by omega⟩) =
          (revList xsVec).take d.nP := by
        apply List.ext_getElem (by simp [revList, hlen])
        intro i h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, List.getElem_take, revList]
      rw [h0, hl]
    · exact (DefRel.false (V := V)).congr fun xsVec =>
        ⟨False.elim, fun hsp => absurd (by simpa [revList] using hsp.length_eq.symm) hlen⟩
  have hG : DefRel n fun xsVec => tgtClsG d acval envC pp out ψ ρ (revList xsVec) m := by
    by_cases hm : (tgtMajor out m).member.isSome = true
    · exact (hG_par.and hG_pdom).congr fun xsVec => by
        simp [tgtClsG, hm]
    · exact hG_pdom.congr fun xsVec => by
        simp [tgtClsG, hm]
  have hLive : DefRel n fun xsVec => tgtClsLive d Dc cvc acval envC pp out ψ ρ (revList xsVec) m := by
    by_cases hm : (tgtMajor out m).member.isSome = true
    · exact DefRel.true.congr fun xsVec => by simp [tgtClsLive, hm]
    · have hsat : DefRel n fun xsVec =>
          Sat V (D.params ψm).reverse (Semantics.prepend (fun l => ps_fr l xsVec) tail_fr) :=
        defRel_sat_prepend tail_fr ps_fr hps_fr (D.params ψm).reverse
      have hex : DefRel n fun xsVec => ∃ mm < D.k, ∃ is : List V,
          SpineFit (Semantics.prepend (fun l => ps_fr l xsVec) tail_fr) (D.ids mm ψm) is :=
        DefRel.finExists_lt fun mm _ =>
          defRel_exists_spineFit_prepend tail_fr (D.ids mm ψm) ps_fr hps_fr
      refine (hsat.and hex).congr fun xsVec => ?_
      simp only [tgtClsLive, hm, LfpDatum.FrFit, hfr xsVec]
      rfl
  exact (DefFun.ite (hG.and hLive) hIdx DefFun.empty).congr fun xsVec => by
    by_cases h1 : tgtClsG d acval envC pp out ψ ρ (revList xsVec) m <;>
      by_cases h2 : tgtClsLive d Dc cvc acval envC pp out ψ ρ (revList xsVec) m <;>
      simp [tgtClsIs, h1, h2, D, ψm, mm]

theorem defFun_tgtClsTup_param (d : BlockData V) (Dc : Nat → LfpDatum V) (mc : Nat → Nat)
    (cvc : Nat → ConstantVal) (pp : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (rP : Nat → Nat) (rds : Nat → List Term) (c₀ : Nat) :
    DefFun (rds c₀).length fun vs : Fin (rds c₀).length → V =>
      tgtClsTup d Dc mc cvc pp out ψ c₀ (idxOf (rP c₀) (revList vs)) := by
  let len := (rds c₀).length
  by_cases hle : rP c₀ + 1 ≤ len
  · let nIdx := len - rP c₀ - 1
    refine (defFun_tupW_ofFn (r := nIdx) (tgtClsU d Dc mc cvc pp out ψ c₀)
      (fun l (vs : Fin len → V) => vs ⟨len - 1 - (rP c₀ + l.val), by dsimp [nIdx] at l; omega⟩)
      (fun l => DefFun.proj ⟨len - 1 - (rP c₀ + l.val), by dsimp [nIdx] at l; omega⟩)).congr
      fun vs => ?_
    rw [tgtClsTup]
    congr 1
    apply List.ext_getElem
    · simp [idxOf, revList, nIdx]; omega
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      simp only [List.getElem_ofFn, idxOf, List.getElem_dropLast, List.getElem_drop,
        revList]
      exact congrArg vs (Fin.ext rfl)
  · refine (DefFun.const (tgtClsTup d Dc mc cvc pp out ψ c₀ [])).congr fun vs => ?_
    have hidx : idxOf (rP c₀) (revList vs) = [] := by
      rw [idxOf]
      apply List.eq_nil_of_length_eq_zero
      simp [revList]
      omega
    rw [hidx]

private theorem defRel_tgtClsFit_param (d : BlockData V) (Dc : Nat → LfpDatum V)
    (mc : Nat → Nat) (cvc : Nat → ConstantVal) (acval : Name → (Name → Nat) → Term)
    (envC : Env) (mpC : EnvModelM V envC) (pp : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr))
    (ψ : Name → Nat) (ρ : Nat → V)
    {K : Nat} {fdoms : Nat → Nat → List Term}
    (hDin : ∀ c, c < K → tgtClsD d Dc out c ∈ mpC.lfpBlocks)
    (n c j : Nat) (hc : c < K)
    (hfitLen : ((tgtClsD d Dc out c).fields (tgtClsψ cvc out ψ c) (tgtClsM mc pp out c) j).length =
      (fdoms c j).length) :
    DefRel ((fdoms c j).length + 1 + n) fun v =>
      tgtClsFit d Dc mc cvc acval envC pp out ψ ρ
        (revList (fdrop (k := (fdoms c j).length + 1) (p := n) v)) c
        ((ftake (k := (fdoms c j).length + 1) (p := n) v) 0) j
        (List.ofFn (ftail (ftake (k := (fdoms c j).length + 1) (p := n) v))) := by
  let m := (fdoms c j).length
  let p := m + 1 + n
  let D := tgtClsD d Dc out c
  let ψc := tgtClsψ cvc out ψ c
  let mc₀ := tgtClsM mc pp out c
  have hC := (mpC.lfp_ok D (hDin c hc)).1
  obtain ⟨tail_fr, len_fr, ps_fr, hps_fr, hfr⟩ :=
    tgtClsFr_eq_prepend d acval envC pp out ψ ρ c n
  let ps_fr_v : Fin len_fr → (Fin p → V) → V := fun l v =>
    ps_fr l (fdrop (k := m + 1) (p := n) v)
  have hps_fr_v : ∀ l, DefFun p (ps_fr_v l) := fun l =>
    (hps_fr l).comp fun i => DefFun.fdrop_proj i
  let hole_v : Fin D.k → (Fin p → V) → V := fun mm v =>
    D.holeVal ψc (Semantics.prepend (fun l => ps_fr_v l v) tail_fr)
      (D.carrier ψc (Semantics.prepend (fun l => ps_fr_v l v) tail_fr)) mm.val
  have hhole_v : ∀ mm, DefFun p (hole_v mm) := fun mm =>
    ((defFun_holeVal_param D hC.kN ψc tail_fr len_fr mm.val mm.isLt).comp hps_fr_v).congr
      fun _ => rfl
  let frame_ps : Fin (D.k + len_fr) → (Fin p → V) → V := fun l v =>
    if hl : l.val < D.k then hole_v ⟨D.k - 1 - l.val, by omega⟩ v
    else ps_fr_v ⟨l.val - D.k, by omega⟩ v
  have hframe_ps : ∀ l, DefFun p (frame_ps l) := fun l => by
    dsimp only [frame_ps]
    split
    · exact hhole_v _
    · exact hps_fr_v _
  have hframe_eq : ∀ v : Fin p → V,
      D.frame ψc (tgtClsFr d acval envC pp out ψ ρ
          (revList (fdrop (k := m + 1) (p := n) v)) c)
        (D.carrier ψc (tgtClsFr d acval envC pp out ψ ρ
          (revList (fdrop (k := m + 1) (p := n) v)) c)) =
      Semantics.prepend (fun l => frame_ps l v) tail_fr := fun v => by
    rw [hfr (fdrop (k := m + 1) (p := n) v)]
    unfold LfpDatum.frame
    have hmap : (List.range D.k).map (D.holeVal ψc
        (Semantics.prepend (fun l => ps_fr l (fdrop (k := m + 1) (p := n) v)) tail_fr)
        (D.carrier ψc (Semantics.prepend (fun l => ps_fr l (fdrop (k := m + 1) (p := n) v))
          tail_fr))) =
        List.ofFn fun mm : Fin D.k => hole_v mm v := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      rfl
    rw [hmap, consList_ofFn_prepend]
  have hC1 : DefRel (V := V) p fun _ => j < D.nctors mc₀ := by
    by_cases hj : j < D.nctors mc₀
    · exact DefRel.true.congr fun _ => ⟨fun _ => hj, fun _ => trivial⟩
    · exact DefRel.false.congr fun _ => ⟨False.elim, fun h => absurd h hj⟩
  have hflen : (D.fields ψc mc₀ j).length = m := hfitLen
  let fs_v : Fin (D.fields ψc mc₀ j).length → (Fin p → V) → V := fun i v =>
    (ftail (ftake (k := m + 1) (p := n) v)) ⟨i.val, Nat.lt_of_lt_of_eq i.isLt hflen⟩
  have hfs_v : ∀ i, DefFun p (fs_v i) := fun i =>
    (DefFun.proj ⟨i.val + 1, by
      have := Nat.lt_of_lt_of_eq i.isLt hflen
      dsimp [p]
      omega⟩).congr fun _ => rfl
  have hC2 : DefRel p fun v =>
      SpineFit (D.frame ψc (tgtClsFr d acval envC pp out ψ ρ
          (revList (fdrop (k := m + 1) (p := n) v)) c)
        (D.carrier ψc (tgtClsFr d acval envC pp out ψ ρ
          (revList (fdrop (k := m + 1) (p := n) v)) c)))
        (D.fields ψc mc₀ j)
        (List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) := by
    refine (defRel_spineFit_listOfFn tail_fr (D.fields ψc mc₀ j) frame_ps hframe_ps fs_v hfs_v).congr
      fun v => ?_
    rw [hframe_eq v]
    have hlo : (List.ofFn fun i => fs_v i v) =
        List.ofFn (ftail (ftake (k := m + 1) (p := n) v)) := by
      apply List.ext_getElem (by simp [hflen])
      intro i h1 h2
      simp only [List.length_ofFn] at h1
      simp only [List.getElem_ofFn, fs_v]
    rw [hlo]
  let fs_full_ps : Fin (m + (D.k + len_fr)) → (Fin p → V) → V := fun l v =>
    if hl : l.val < m then
      (ftail (ftake (k := m + 1) (p := n) v)) ⟨m - 1 - l.val, by omega⟩
    else frame_ps ⟨l.val - m, by omega⟩ v
  have hfs_full_ps : ∀ l, DefFun p (fs_full_ps l) := fun l => by
    dsimp only [fs_full_ps]
    split
    · exact DefFun.proj _
    · exact hframe_ps _
  have hC3 : DefRel p fun v =>
      ∀ l, l < (D.ids mc₀ ψc).length → ∃ e, (D.resIdx ψc mc₀ j)[l]? = some e ∧
        interp V (consList (List.ofFn (ftail (ftake (k := m + 1) (p := n) v)))
          (D.frame ψc (tgtClsFr d acval envC pp out ψ ρ
              (revList (fdrop (k := m + 1) (p := n) v)) c)
            (D.carrier ψc (tgtClsFr d acval envC pp out ψ ρ
              (revList (fdrop (k := m + 1) (p := n) v)) c)))) e =
          ConLeche.SetTheory.Tower.projS l ((ftake (k := m + 1) (p := n) v) 0) := by
    refine (DefRel.finForall (R := fun (l : Fin (D.ids mc₀ ψc).length) (v : Fin p → V) =>
        match (D.resIdx ψc mc₀ j)[l.val]? with
        | none => False
        | some e =>
          interp V (Semantics.prepend (fun i => fs_full_ps i v) tail_fr) e =
            ConLeche.SetTheory.Tower.projS l.val ((ftake (k := m + 1) (p := n) v) 0)) fun l => ?_).congr fun v => ?_
    · cases hres : (D.resIdx ψc mc₀ j)[l.val]? with
      | none => exact DefRel.false.congr fun _ => by simp
      | some e =>
        exact (DefRel.eq_apply ((interp_defFun_prepend tail_fr (m + (D.k + len_fr)) e).comp hfs_full_ps)
          (DefFun.projS_apply l.val (DefFun.proj 0))).congr fun _ => by dsimp; exact Iff.rfl
    · have hcon : ∀ v : Fin p → V,
          consList (List.ofFn (ftail (ftake (k := m + 1) (p := n) v)))
            (D.frame ψc (tgtClsFr d acval envC pp out ψ ρ
                (revList (fdrop (k := m + 1) (p := n) v)) c)
              (D.carrier ψc (tgtClsFr d acval envC pp out ψ ρ
                (revList (fdrop (k := m + 1) (p := n) v)) c))) =
          Semantics.prepend (fun i => fs_full_ps i v) tail_fr := fun v => by
        rw [hframe_eq v, consList_ofFn_prepend]
      constructor
      · intro h l' hl'
        have hl'' := h ⟨l', hl'⟩
        cases hres : (D.resIdx ψc mc₀ j)[l']? with
        | none => simp [hres] at hl''
        | some e =>
          simp only [hres] at hl''
          exact ⟨e, rfl, by rw [hcon v]; exact hl''⟩
      · rintro h ⟨l', hl'⟩
        obtain ⟨e, he, heq⟩ := h l' hl'
        simp only [he]
        rw [← hcon v]
        exact heq
  exact (hC1.and (hC2.and hC3)).congr fun _ => Iff.rfl

private theorem defRel_genCallT_list (tup : Nat → List V → V) (ρ : Nat → V)
    (htup : ∀ c, ∃ u : Nat, ∀ is, tup c is = tupW u is)
    {m n : Nat} : ∀ (qs : List IhDatum),
    DefRel (m + 1 + n) fun v =>
      ∃ q ∈ qs, ∃ bs : List V,
        SpineFit (consList (revList (fdrop (k := m + 1) (p := n) v) ++
            List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ) q.2.1 bs ∧
          (ftake (k := m + 1) (p := n) v) 0 =
            tagged q.1 (tup q.1 (q.2.2.1.map (interp V (consList bs
                (consList (revList (fdrop (k := m + 1) (p := n) v) ++
                  List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ)))))
              (interp V (consList bs
                (consList (revList (fdrop (k := m + 1) (p := n) v) ++
                  List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ)) q.2.2.2)
  | [] => (DefRel.false (V := V)).congr fun _ => ⟨False.elim, by rintro ⟨q, hq, _⟩; exact nomatch hq⟩
  | q :: qs => by
    let p := m + 1 + n
    let k := q.2.1.length
    let rest_xs_fs : Fin (m + n) → (Fin (k + p) → V) → V := fun l w =>
      let r := fdrop (k := k) (p := p) w
      if hl : l.val < m then
        (ftail (ftake (k := m + 1) (p := n) r)) ⟨m - 1 - l.val, by omega⟩
      else (fdrop (k := m + 1) (p := n) r) ⟨l.val - m, by omega⟩
    have hrest_xs_fs : ∀ l, DefFun (k + p) (rest_xs_fs l) := fun l => by
      dsimp only [rest_xs_fs]
      split
      · exact DefFun.proj _
      · exact DefFun.proj _
    let bs_xs_fs : Fin (k + (m + n)) → (Fin (k + p) → V) → V := fun l w =>
      if hl : l.val < k then (ftake (k := k) (p := p) w) ⟨k - 1 - l.val, by omega⟩
      else rest_xs_fs ⟨l.val - k, by omega⟩ w
    have hbs_xs_fs : ∀ l, DefFun (k + p) (bs_xs_fs l) := fun l => by
      dsimp only [bs_xs_fs]
      split
      · exact DefFun.proj _
      · exact hrest_xs_fs _
    have hsp : DefRel (k + p) fun w =>
        SpineFit (consList (revList (fdrop (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)) ++
            List.ofFn (ftail (ftake (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)))) ρ)
          q.2.1 (List.ofFn (ftake (k := k) (p := p) w)) := by
      refine (defRel_spineFit_listOfFn ρ q.2.1 rest_xs_fs hrest_xs_fs
        (fun i w => (ftake (k := k) (p := p) w) i) (fun _ => DefFun.proj _)).congr fun w => ?_
      rw [consList_append_ofFn_prepend]
    obtain ⟨u, hu⟩ := htup q.1
    have htag : DefRel (k + p) fun w =>
        (ftake (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)) 0 =
          tagged q.1 (tup q.1 (q.2.2.1.map (interp V (consList (List.ofFn (ftake (k := k) (p := p) w))
              (consList (revList (fdrop (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)) ++
                List.ofFn (ftail (ftake (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)))) ρ)))))
            (interp V (consList (List.ofFn (ftake (k := k) (p := p) w))
              (consList (revList (fdrop (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)) ++
                List.ofFn (ftail (ftake (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)))) ρ))
              q.2.2.2) := by
      let idxFuns : Fin q.2.2.1.length → (Fin (k + p) → V) → V := fun i w =>
        interp V (Semantics.prepend (fun l => bs_xs_fs l w) ρ) q.2.2.1[i.val]
      have hidxFuns : ∀ i, DefFun (k + p) (idxFuns i) := fun i =>
        (interp_defFun_prepend ρ (k + (m + n)) _).comp hbs_xs_fs
      have hbody : DefFun (k + p) fun w =>
          interp V (Semantics.prepend (fun l => bs_xs_fs l w) ρ) q.2.2.2 :=
        (interp_defFun_prepend ρ (k + (m + n)) _).comp hbs_xs_fs
      refine (DefRel.eq_apply (DefFun.proj ⟨k, by omega⟩)
        (DefFun.tagged_apply q.1 (defFun_tupW_ofFn u idxFuns hidxFuns) hbody)).congr fun w => ?_
      have hcon : consList (List.ofFn (ftake (k := k) (p := p) w))
          (consList (revList (fdrop (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)) ++
            List.ofFn (ftail (ftake (k := m + 1) (p := n) (fdrop (k := k) (p := p) w)))) ρ) =
          Semantics.prepend (fun l => bs_xs_fs l w) ρ := by
        rw [consList_append_ofFn_prepend, consList_ofFn_prepend]
      rw [hcon, hu]
      have hmap : q.2.2.1.map (interp V (Semantics.prepend (fun l => bs_xs_fs l w) ρ)) =
          List.ofFn fun i => idxFuns i w := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_ofFn, idxFuns]
      rw [hmap]
      exact Iff.rfl
    have hex : DefRel p fun v => ∃ bs : List V,
        SpineFit (consList (revList (fdrop (k := m + 1) (p := n) v) ++
            List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ) q.2.1 bs ∧
          (ftake (k := m + 1) (p := n) v) 0 =
            tagged q.1 (tup q.1 (q.2.2.1.map (interp V (consList bs
                (consList (revList (fdrop (k := m + 1) (p := n) v) ++
                  List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ)))))
              (interp V (consList bs
                (consList (revList (fdrop (k := m + 1) (p := n) v) ++
                  List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ)) q.2.2.2) := by
      refine (DefRel.exists_fin (k := k) (p := p) (hsp.and htag)).congr fun v => ?_
      constructor
      · rintro ⟨bsVec, h1, h2⟩
        rw [ftake_fappend, fdrop_fappend] at h1 h2
        exact ⟨List.ofFn bsVec, h1, h2⟩
      · rintro ⟨bs, h1, h2⟩
        have hbl : bs.length = k := h1.length_eq
        let bsVec : Fin k → V := fun i => bs[i.val]'(by omega)
        have hbsEq : List.ofFn bsVec = bs := by
          apply List.ext_getElem (by simp [hbl])
          intro i _ _
          simp only [List.getElem_ofFn, bsVec]
        refine ⟨bsVec, ?_⟩
        rw [ftake_fappend, fdrop_fappend, hbsEq]
        exact ⟨h1, h2⟩
    refine (hex.or (defRel_genCallT_list tup ρ htup qs)).congr fun v => ?_
    constructor
    · rintro (⟨bs, h1, h2⟩ | ⟨q', hq', bs, h1, h2⟩)
      · exact ⟨q, List.Mem.head _, bs, h1, h2⟩
      · exact ⟨q', List.Mem.tail _ hq', bs, h1, h2⟩
    · rintro ⟨q', hq', bs, h1, h2⟩
      rcases List.mem_cons.mp hq' with rfl | hq''
      · exact Or.inl ⟨bs, h1, h2⟩
      · exact Or.inr ⟨q', hq'', bs, h1, h2⟩

private theorem defRel_genCallT_param (tup : Nat → List V → V) (ρ : Nat → V)
    (htup : ∀ c, ∃ u : Nat, ∀ is, tup c is = tupW u is)
    (ihd : Nat → Nat → List IhDatum) (m n c j : Nat) :
    DefRel (m + 1 + n) fun v =>
      genCallT tup ρ ihd (revList (fdrop (k := m + 1) (p := n) v)) c j
        (List.ofFn (ftail (ftake (k := m + 1) (p := n) v)))
        ((ftake (k := m + 1) (p := n) v) 0) :=
  (defRel_genCallT_list tup ρ htup (ihd c j)).congr fun _ => Iff.rfl

theorem hasSep_genCallT (tup : Nat → List V → V) (ρ : Nat → V)
    (htup : ∀ c, ∃ u : Nat, ∀ is, tup c is = tupW u is)
    (ihd : Nat → Nat → List IhDatum) (U : V) (xs : List V) (c j : Nat) (fs : List V) :
    HasSep U (genCallT tup ρ ihd xs c j fs) := by
  let p := fs.length + 1 + xs.length
  let Gs : Fin p → (Fin 1 → V) → V := fun l w =>
    if hl0 : l.val = 0 then w 0
    else if hl1 : l.val < fs.length + 1 then fs[l.val - 1]'(by omega)
    else xs.reverse[l.val - (fs.length + 1)]'(by simp; omega)
  have hGs : ∀ l, DefFun 1 (Gs l) := fun l => by
    dsimp only [Gs]
    split
    · exact DefFun.proj 0
    · split <;> exact DefFun.const _
  have hR : DefRel 1 fun w => genCallT tup ρ ihd xs c j fs (w 0) := by
    refine ((defRel_genCallT_param tup ρ htup ihd fs.length xs.length c j).comp hGs).congr
      fun w => ?_
    have hxs : revList (fdrop (k := fs.length + 1) (p := xs.length) fun l => Gs l w) = xs := by
      apply List.ext_getElem (by simp [revList])
      intro i h1 h2
      simp only [revList, fdrop, List.getElem_ofFn, Gs]
      have h1' : ¬ ((fs.length + 1) + (xs.length - 1 - i) = 0) := by omega
      have h2' : ¬ ((fs.length + 1) + (xs.length - 1 - i) < fs.length + 1) := by omega
      simp only [h1', ↓reduceDIte, h2', List.getElem_reverse]
      congr 1; omega
    have hfs : List.ofFn (ftail (ftake (k := fs.length + 1) (p := xs.length) fun l => Gs l w)) = fs := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.length_ofFn] at h1
      simp only [List.getElem_ofFn, ftail, ftake, Gs, Fin.val_succ]
      have h1' : ¬ (i + 1 = 0) := by omega
      have h2' : i + 1 < fs.length + 1 := by omega
      simp only [h1', ↓reduceDIte, h2']
      congr 1
    have h0 : ftake (k := fs.length + 1) (p := xs.length) (fun l => Gs l w) 0 = w 0 := rfl
    rw [hxs, hfs, h0]
  exact hasSep_of_defPred hR

private theorem defFun_blockGraphStep_param (K : Nat) (ρ : Nat → V) (rP : Nat → Nat)
    (rds : Nat → List Term) (tup : Nat → List V → V)
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (ihs : Nat → Nat → List Term) (Rb0 : Nat → Nat → Term) (m n c j : Nat) :
    DefFun (m + 1 + n) fun v =>
      blockGraphStep ρ Rb0 (genIhvT K ρ rP rds tup htup ihs)
        (revList (fdrop (k := m + 1) (p := n) v))
        (c, j, List.ofFn (ftail (ftake (k := m + 1) (p := n) v)))
        ((ftake (k := m + 1) (p := n) v) 0) := by
  let p := m + 1 + n
  let chainPs : Fin (m + (n + K)) → (Fin p → V) → V := fun l v =>
    if hl1 : l.val < m then
      (ftail (ftake (k := m + 1) (p := n) v)) ⟨m - 1 - l.val, by omega⟩
    else if hl2 : l.val < m + n then
      (fdrop (k := m + 1) (p := n) v) ⟨l.val - m, by omega⟩
    else genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) (K - 1 - (l.val - (m + n)))
  have hchainPs : ∀ l, DefFun p (chainPs l) := fun l => by
    dsimp only [chainPs]
    split
    · exact DefFun.proj _
    · split
      · exact DefFun.proj _
      · exact ((defFun_genFT ρ rP rds tup htup (K - 1 - (l.val - (m + n)))).comp
          (fun (_ : Fin 1) => DefFun.proj (V := V) (⟨0, by omega⟩ : Fin p))).congr fun _ => rfl
  let ihPs : Fin ((ihs c j).length + (m + n)) → (Fin p → V) → V := fun l v =>
    if hl1 : l.val < (ihs c j).length then
      interp V (Semantics.prepend (fun i => chainPs i v) ρ)
        (ihs c j)[(ihs c j).length - 1 - l.val]
    else if hl2 : l.val < (ihs c j).length + m then
      (ftail (ftake (k := m + 1) (p := n) v)) ⟨m - 1 - (l.val - (ihs c j).length), by omega⟩
    else (fdrop (k := m + 1) (p := n) v) ⟨l.val - ((ihs c j).length + m), by omega⟩
  have hihPs : ∀ l, DefFun p (ihPs l) := fun l => by
    dsimp only [ihPs]
    split
    · exact (interp_defFun_prepend ρ (m + (n + K)) _).comp hchainPs
    · split <;> exact DefFun.proj _
  refine ((interp_defFun_prepend ρ ((ihs c j).length + (m + n)) (Rb0 c j)).comp hihPs).congr
    fun v => ?_
  dsimp only [blockGraphStep, genIhvT]
  have hch_eq : consList (revList (fdrop (k := m + 1) (p := n) v) ++
        List.ofFn (ftail (ftake (k := m + 1) (p := n) v)))
      (chainFrame K (genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0)) ρ) =
      Semantics.prepend (fun l => chainPs l v) ρ := by
    have hcf : chainFrame K (genFT ρ rP rds tup htup
          ((ftake (k := m + 1) (p := n) v) 0)) ρ =
        Semantics.prepend (fun i : Fin K =>
          genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) (K - 1 - i.val)) ρ := by
      rw [chainFrame]
      have hrg : (List.range K).map (genFT ρ rP rds tup htup
          ((ftake (k := m + 1) (p := n) v) 0)) =
          List.ofFn fun i : Fin K =>
            genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) i.val := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      have hp0 : Semantics.prepend Fin.elim0 ρ = ρ := funext fun j => by simp [Semantics.prepend]
      calc consList ((List.range K).map (genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0))) ρ
          = consList (List.ofFn fun i : Fin K =>
              genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) i.val)
              (Semantics.prepend Fin.elim0 ρ) := by
            rw [hrg, hp0]
        _ = Semantics.prepend (fun i : Fin K =>
              genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) (K - 1 - i.val)) ρ := by
            rw [consList_ofFn_prepend]
            congr 1; funext ⟨i, hi⟩; simp only [Nat.add_zero] at hi; simp [hi]
    have hinner : consList (revList (fdrop (k := m + 1) (p := n) v))
          (chainFrame K (genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0)) ρ) =
        Semantics.prepend (fun l : Fin (n + K) =>
          if hl : l.val < n then (fdrop (k := m + 1) (p := n) v) ⟨l.val, hl⟩
          else genFT ρ rP rds tup htup ((ftake (k := m + 1) (p := n) v) 0) (K - 1 - (l.val - n))) ρ := by
      rw [hcf, consList_revList_prepend]
    rw [consList_append, hinner, consList_ofFn_prepend]
    congr 1
    funext l
    by_cases hl1 : l.val < m
    · simp only [hl1, ↓reduceDIte, chainPs]
    · by_cases hl2 : l.val < m + n
      · have hl3 : l.val - m < n := by omega
        simp only [hl1, ↓reduceDIte, hl2, hl3, chainPs]
      · have hl3 : ¬ (l.val - m < n) := by omega
        simp only [hl1, ↓reduceDIte, hl2, hl3, chainPs]
        congr 1; omega
  have hih_eq : consList ((ihs c j).map (interp V (Semantics.prepend (fun l => chainPs l v) ρ)))
      (consList (revList (fdrop (k := m + 1) (p := n) v) ++
        List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ) =
      Semantics.prepend (fun l => ihPs l v) ρ := by
    have hmap : (ihs c j).map (interp V (Semantics.prepend (fun l => chainPs l v) ρ)) =
        List.ofFn fun i : Fin (ihs c j).length =>
          interp V (Semantics.prepend (fun l => chainPs l v) ρ) (ihs c j)[i.val] := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_ofFn]
    rw [hmap, consList_append_ofFn_prepend, consList_ofFn_prepend]
    congr 1
    funext l
    by_cases hl1 : l.val < (ihs c j).length
    · simp only [hl1, ↓reduceDIte, ihPs]
    · by_cases hl2 : l.val < (ihs c j).length + m
      · have hl3 : l.val - (ihs c j).length < m := by omega
        simp only [hl1, ↓reduceDIte, hl2, hl3, ihPs]
      · have hl3 : ¬ (l.val - (ihs c j).length < m) := by omega
        simp only [hl1, ↓reduceDIte, hl2, hl3, ihPs]
        exact congrArg (fdrop (k := m + 1) (p := n) v) (Fin.ext (by dsimp; omega))
  rw [hch_eq]
  rw [show consList (List.map (interp V (Semantics.prepend (fun l => chainPs l v) ρ)) (ihs c j))
        (consList (revList (fdrop (k := m + 1) (p := n) v) ++
          List.ofFn (ftail (ftake (k := m + 1) (p := n) v))) ρ) =
      Semantics.prepend (fun l => ihPs l v) ρ from hih_eq]

end DefHelpers



/-! ## 3. The candidate, from the rows

`graphRecPre_coreR` at the old class data, the generated calls and the
graph's `ih` values `genIhvT`.  The type half of the producer
(`hTyP`) and the prefix lengths (`hpl`) are the stage record's; every other row is a premise,
stated exactly as the producer consumes it (§4 discharges them). -/

section Cand

variable {F : Nat} {envC : Env} {pp : BlockShape} {formers : List ConstantVal}
  {memberCtors : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal} {g : ClassGen} {rd : ClassRead}

/-- The major index of a stored recursor is its rule prefix plus its
stored index count. -/
theorem genRec_mI (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) {c : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : (tgtRs out)[c]? = some r) :
    pp.majorIdxAt c = pp.rulePrefixAt c + r.2.2.1 := by
  obtain ⟨R⟩ := h
  obtain ⟨rc, u, hrc, hcu, hE⟩ := R.tyGenAt hr
  obtain ⟨E⟩ := hE
  exact ConLeche.RecTyGen.mI_eq E

/-- The stored domains' length: the rule prefix, the class's
indices, the major. -/
theorem genRds_length
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    {c : Nat} (hc : c < (tgtRs out).length) :
    (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
      = pp.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨-, -, -, -, -, hlen, -⟩ := recStage_tyPis (V := V) mpC h hr ψ
  rw [hlen, genRec_mI h hr]
  congr 2
  have hc' : c < out.length := by simpa [tgtRs] using hc
  simp [tgtRs, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc']

set_option maxHeartbeats 4000000 in
/-- **The candidate of the generated family** — `BlockRecPre.hCand` at the
generated components, from the producer's rows at the old class data. -/
theorem genRecPre_hCand
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (ψ : Name → Nat) (ρ : Nat → V)
    (hDin : ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks)
    (hmN : ∀ c, c < (tgtRs out).length → tgtClsM mc pp out c < (tgtClsD d Dc out c).N)
    (hfitLen : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ((tgtClsD d Dc out c).fields (tgtClsψ cvc out ψ c) (tgtClsM mc pp out c) j).length
        = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
    (hsplit : ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)) ys →
      (prefOf (pp.rulePrefixAt c) ys).length = pp.rulePrefixAt c ∧
      ys = prefOf (pp.rulePrefixAt c) ys
        ++ (idxOf (pp.rulePrefixAt c) ys ++ [majOf ys]) ∧
      tgtClsTup d Dc mc cvc pp out ψ c (idxOf (pp.rulePrefixAt c) ys)
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ
          (prefOf (pp.rulePrefixAt c) ys) c ∧
      majOf ys ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ
          (prefOf (pp.rulePrefixAt c) ys) c)
        (tgtClsTup d Dc mc cvc pp out ψ c
          (idxOf (pp.rulePrefixAt c) ys)))
    (hconcl : ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)) ys →
      blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval envC pp
          (tgtRs out) ψ) (tgtClsU d Dc mc cvc pp out ψ)
          (tgtClsNIdx d pp out) ρ (prefOf (pp.rulePrefixAt c) ys)
          (tagged c (tgtClsTup d Dc mc cvc pp out ψ c
            (idxOf (pp.rulePrefixAt c) ys)) (majOf ys))
        = interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c))
    (hconclTy : ∀ xs : List V, ∀ c, c < (tgtRs out).length →
      ∀ i, i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c) i →
      interp V (consList (xs ++ (isOfW (tgtClsU d Dc mc cvc pp out ψ c)
          (tgtClsNIdx d pp out c) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.elim
          pp.large)) : V))
    (hstep : ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c i j fs → ∀ gv : V,
      (∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ) (tgtRs out).length
          (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
            (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs (c, j, fs)
          (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
            (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
            (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs) →
        app gv v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs v) →
      interp V (consList (genIhvT (tgtRs out).length ρ pp.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp out ψ)
            (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
              (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ) xs c j fs gv)
          (consList (xs ++ fs) ρ)) (genRbAV g rd c j)
        ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs
          (tagged c i (tgtClsInj d Dc mc cvc pp out ψ c j fs)))
    (huniq : ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs) →
      ∀ e e',
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsInj d Dc mc cvc pp out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          xs u e →
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsInj d Dc mc cvc pp out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs u →
        v' ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs u →
        v = v')
    (hind : GenClassInd mpC.base2.acval envC pp out d Dc mc cvc
      (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j) ψ ρ)
    (hrule : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j) (xs ++ fs) →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c))
        (xs ++ ((liftEsK (tgtRs out).length
              ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
                + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)])))
    (hdec : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j) (xs ++ fs) →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c
          (tgtClsTup d Dc mc cvc pp out ψ c
            ((liftEsK (tgtRs out).length
                ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
                  + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))))) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
          = tgtClsInj d Dc mc cvc pp out ψ c j fs)
    (hchain : ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
        xs.length = pp.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c')) (xs ++ (is ++ [x])) →
        r (tagged c' (tgtClsTup d Dc mc cvc pp out ψ c' is) x)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
        SpineFit (chainFrame (tgtRs out).length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
            ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
          (xs ++ fs) →
        (hGr : HasGraph (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
            (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ) (tgtRs out).length
            (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
              (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs (c, j, fs)
            (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
              (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
              (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs)) r) →
        genIhvT (tgtRs out).length ρ pp.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp out ψ)
            (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
              (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ) xs c j fs
            (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
              (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
              (tgtRs out).length
              (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
                (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs
              (c, j, fs)
              (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
                (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
                (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs)) hGr)
          = (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp out mpC.base2.acval envC ψ')
          (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ')
          (fun ψ' => tgtMkAV pp out mpC.base2.acval envC ψ')
          (fun _ => genRbAV g rd) ψ,
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e := by
  obtain ⟨uOf, hruns⟩ := blockRecElimLevel_run h
  have H := graphRecPre_coreR (ℓ := Level.eval ψ (ConLeche.structElimLevel pp.elim
      pp.large)) (K := (tgtRs out).length) (ρ := ρ)
    (nCt := blockRecNCt (tgtRs out)) (rP := pp.rulePrefixAt)
    (rds := blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (concl := blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (RecTy := blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ)
    (es := fun c j => liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
              + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp out mpC.base2.acval envC ψ c j))
    (ihs := genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ)
    (mk := tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ)
    (Rb0 := genRbAV g rd)
    (ihv := genIhvT (tgtRs out).length ρ pp.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp out ψ)
            (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
              (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ))
    (call := genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
                (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j))
    (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (tgtClsInj d Dc mc cvc pp out ψ)
    (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out)
    (tgtClsTup d Dc mc cvc pp out ψ)
    (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (fun c hc =>
      (recStage_tyPis (V := V) mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1)
    (fun c hc => blockRulePdomsAV_length mpC h (List.getElem?_eq_getElem hc) ψ)
    (fun c hc => by rw [genRds_length h ψ hc]; omega)
    (fun c₀ _ m _ => defFun_tgtClsIs_param d Dc mc cvc mpC.base2.acval envC pp out ψ ρ
      (pp.rulePrefixAt c₀) m)
    (fun c₀ _ m hm => defFun_tgtClsCr_param d Dc mc cvc mpC.base2.acval envC pp out ψ ρ (hmN m hm))
    (fun c₀ _ => defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
      (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ) c₀)
    (fun c _ j _ => (tgtClsD d Dc out c).hinj_def (tgtClsψ cvc out ψ c) (tgtClsM mc pp out c) j _)
    (fun _ c _ j _ hc hj hf => by
      have hlen := hf.2.1.length_eq
      rw [tgtFdomsK, liftDomsK_length, ← hfitLen c hc j hj]
      exact hlen)
    (fun n c j hc hj =>
      defRel_tgtClsFit_param d Dc mc cvc mpC.base2.acval envC mpC pp out ψ ρ hDin
        n c j hc (by simpa [tgtFdomsK, liftDomsK_length] using hfitLen c hc j hj))
    (fun n c j _ _ => defRel_genCallT_param (tgtClsTup d Dc mc cvc pp out ψ) ρ
      (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
      (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ n c j)
    (fun n c j _ _ => defFun_blockGraphStep_param (tgtRs out).length ρ pp.rulePrefixAt
      (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ) (tgtClsTup d Dc mc cvc pp out ψ)
      (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
        (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
      (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ) (genRbAV g rd) _ n c j)
    (fun xs c j fs => hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
      (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
      (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs)
    hsplit hconcl hconclTy hstep huniq
    (fun xs P hSepP hstepI => hind xs (fun c j fs =>
      hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
        (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
        (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs) P hSepP hstepI)
    hrule hdec hchain
  obtain ⟨a, ha, hb⟩ := H
  refine ⟨a, ha, fun e he => hb e ?_⟩
  rw [genClsEqs_eq h (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ') (fun _ => genRbAV g rd) ψ]
  exact he

end Cand

/-! ## 3′. The `ih` chain and the step, over ANY classes

`genHchain`/`genHstep` (`ClassRecKit`, `ClassGenStep`) are stated at the
classes read off the generated type (`genIs`/`genCr`).  Here the same two
rows over any classes `Is`/`Cr`/`tup` whose majors are the stored binder
data's fits (`hsplitI`), at the generated calls `genCallT` and the graph's
`ih` values `genIhvT`. -/

section Generic

variable {K : Nat} {ρ : Nat → V} {rP nCt : Nat → Nat} {rds : Nat → List Term}
  {Is Cr : List V → Nat → V} {tup : Nat → List V → V} {pdoms : Nat → List Term}
  {fdoms : Nat → Nat → List Term} {ihd : Nat → Nat → List IhDatum}

/-- The generated calls are the calls `genIhCallAt` names, tagged. -/
theorem genCallT_iff {xs : List V} {c j : Nat} {fs : List V} {v : V} :
    genCallT tup ρ ihd xs c j fs v ↔
      ∃ t is x, genIhCallAt ρ ihd xs c j fs t is x ∧ v = tagged t (tup t is) x := by
  constructor
  · rintro ⟨q, hq, bs, hbs, rfl⟩
    exact ⟨q.1, _, _, ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩, rfl⟩
  · rintro ⟨t, is, x, ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩, rfl⟩
    exact ⟨q, hq, bs, hbs, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`hchain` over any classes**: the graph's `ih` values are the `ih`
terms read at the chain — the `ih` terms read the chain only at their
calls' spines (`hihRead`), each call's spine fits its callee's stored
domains (`hcallTy`), so it is a major of the callee's class
(`hsplitI`) and a predecessor, where the graph is the chain's recursor. -/
theorem genHchainG
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (genCallT tup ρ ihd xs c j fs))
    (hsplitI : ∀ c, c < K → ∀ (xs is : List V) (x : V), xs.length = rP c →
      SpineFit ρ ((rds c)) (xs ++ (is ++ [x])) →
      tup c is ∈ˢ Is xs c ∧ x ∈ˢ app (Cr xs c) (tup c is))
    (hcallTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a : Nat → V),
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        t < K ∧ xs.length = rP t ∧ SpineFit ρ ((rds t)) (xs ++ (is ++ [x])))
    (hihRead : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a a' : Nat → V),
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        (xs ++ (is ++ [x])).foldl SetTheory.app (a t)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a' t)) →
      ((ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = ((ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a' ρ)))) :
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < K → ∀ (is : List V) (x : V),
        xs.length = rP c' →
        SpineFit ρ ((rds c')) (xs ++ (is ++ [x])) →
        r (tagged c' (tup c' is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        (hGr : HasGraph (graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)
          (hSep xs c j fs)) r) →
        genIhvT K ρ rP rds tup htup
            (fun c j => (ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
            xs c j fs (graph r (graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)
              (hSep xs c j fs)) hGr)
          = ((ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ))) := by
  intro a xs r hr c hc j hj fs hxl hsp hGr
  refine (hihRead c hc j hj xs fs a _ hxl hsp fun t is x hcall => ?_).symm
  obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs a hxl hsp t is x hcall
  have hfold := lamTowerA_fold
    (g := fun sp _ => app (graph r (graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)
        (hSep xs c j fs)) hGr)
      (tagged t (tup t (idxOf (rP t) sp)) (majOf sp)))
    (hg := DefFun.app_apply (DefFun.const _)
      (DefFun.tagged_apply t (htup t) (defFun_majOf_revList (rds t).length)))
    hfitT
  rw [idxOf_split hxlT, majOf_split] at hfold
  show _ = (xs ++ (is ++ [x])).foldl SetTheory.app (genFT ρ rP rds tup htup _ t)
  rw [genFT, hfold]
  obtain ⟨hi, hxC⟩ := hsplitI t ht xs is x hxlT hfitT
  have hpred : tagged t (tup t is) x ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)
      (hSep xs c j fs) :=
    mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hi hxC, genCallT_iff.mpr ⟨t, is, x, hcall, rfl⟩⟩
  rw [app_graph hpred]
  exact (hr t ht is x hxlT hfitT).symm

set_option maxHeartbeats 2000000 in
/-- **`hstep` over any classes** (`genHstep`'s argument): the residue is
the minor premise applied to the fields and the graph's `ih` values; the
`ih` values inhabit their binders' types (each call is typed, hence a
predecessor, where the graph lands in the motive, which is the stored
conclusion, the callee's motive variable applied); the minor premise's
typing (`hminor`) lands the residue in `motive_c e⃗ mk`, which is the
kit's motive at the constructed element (`hdecInv`). -/
theorem genHstepG {uX nIdxX : Nat → Nat} {concl : Nat → Term}
    {fit : List V → Nat → V → Nat → List V → Prop} {injX : Nat → Nat → List V → V}
    {es : Nat → Nat → List Term} {mk : Nat → Nat → Term}
    (htup : ∀ t, DefFun (rds t).length fun xs => tup t (idxOf (rP t) (revList xs)))
    (hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (genCallT tup ρ ihd xs c j fs))
    (motPos : Nat → Nat) (minPos : Nat → Nat → Nat)
    (hpdl : ∀ c, c < K → (pdoms c).length = rP c)
    (hlenR : ∀ c, c < K → (rds c).length = rP c + nIdxX c + 1)
    (hmot : ∀ c, c < K → motPos c < rP c)
    (hmin : ∀ c, c < K → ∀ j, j < nCt c → minPos c j < rP c)
    (hIsPre : ∀ xs c i, c < K → i ∈ˢ Is xs c → SpineFit ρ (pdoms c) xs)
    (hsplitI : ∀ c, c < K → ∀ (xs is : List V) (x : V), xs.length = rP c →
      SpineFit ρ ((rds c)) (xs ++ (is ++ [x])) →
      tup c is ∈ˢ Is xs c ∧ x ∈ˢ app (Cr xs c) (tup c is) ∧ isOfW (uX c) (nIdxX c) (tup c is) = is)
    (hdecInv : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs : List V) (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs →
      SpineFit (consList xs ρ) (fdoms c j) fs ∧
      isOfW (uX c) (nIdxX c) i = (es c j).map (interp V (consList (xs ++ fs) ρ)) ∧
      ((es c j).map (interp V (consList (xs ++ fs) ρ))).length = nIdxX c ∧
      interp V (consList (xs ++ fs) ρ) (mk c j) = injX c j fs)
    (hcallTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length → SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∀ q ∈ ihd c j, ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs →
        q.1 < K ∧ xs.length = rP q.1 ∧
        SpineFit ρ ((rds q.1))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])))
    (hbelow : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j,
      IhDatumBelow ((pdoms c).length + (fdoms c j).length) q)
    (hconclMot : ∀ c, c < K → ∀ (xs zs : List V) (x : V), xs.length = rP c →
      zs.length = nIdxX c →
      interp V (consList (xs ++ (zs ++ [x])) ρ) (concl c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (motPos c) pt))
    (hconclTy : ∀ c, c < K → ∀ (xs zs : List V) (x : V),
      SpineFit ρ ((rds c)) (xs ++ (zs ++ [x])) →
      IsTy (interp V (consList (xs ++ (zs ++ [x])) ρ) (concl c)))
    (hminor : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs, SpineFit ρ (pdoms c) xs →
      ∀ fs, SpineFit (consList xs ρ) (fdoms c j) fs →
      ∀ hs : List V, hs.length = (ihd c j).length →
      (∀ (l : Nat) (q : IhDatum) (h : V), (ihd c j)[l]? = some q → hs[l]? = some h →
        h ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((pdoms c).length + (fdoms c j).length) (motPos q.1) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (minPos c j) pt)
        ∈ˢ ((es c j).map (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ) (mk c j)]).foldl SetTheory.app
            (xs.getD (motPos c) pt)) :
    ∀ xs : List V, ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs) (hSep xs c j fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (genIhvT K ρ rP rds tup htup
            (fun c j => (ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
            xs c j fs g)
          (consList (xs ++ fs) ρ))
          (genRb0 (pdoms c).length (minPos c j) (fdoms c j).length (ihd c j).length)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)) := by
  intro xs c hc j hj i fs hi hfit g hg
  have hxs : SpineFit ρ (pdoms c) xs := hIsPre xs c i hc hi
  have hxl : xs.length = (pdoms c).length := hxs.length_eq
  obtain ⟨hfs, hisOf, hesl, hmkE⟩ := hdecInv c hc j hj xs i fs hi hfit
  have hsp : SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs) := SpineFit.append hxs hfs
  have hfl : fs.length = (fdoms c j).length := hfs.length_eq
  generalize hDd : (pdoms c).length + (fdoms c j).length = D at *
  have hDlen : (xs ++ fs).length = D := by simp [hxl, hfl, ← hDd]
  have hagree : ∀ i, i < D →
      consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup htup g) ρ) i = consList (xs ++ fs) ρ i := by
    intro i hi'
    rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]
  -- the graph's `ih` values inhabit their binders' types
  have hih : ∀ q ∈ ihd c j,
      interp V (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup htup g) ρ))
          (genIhAV K (pdoms c).length D q)
        ∈ˢ interp V (consList (xs ++ fs) ρ) (genIhDomAV D (motPos q.1) q) := by
    intro q hq
    obtain ⟨hbT, hbA⟩ := hbelow c hc j hj q hq
    rw [hDd] at hbT hbA
    -- the ih binder's codomain is the callee's conclusion at the call's
    -- spine, a type (`hconclTy`: the recursor type's innermost fibre)
    have hCty : ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs →
        IsTy (interp V (consList bs (consList (xs ++ fs) ρ))
          (Term.mkAppN (.bvar (D + q.2.1.length - 1 - motPos q.1))
            (q.2.2.1 ++ [q.2.2.2]))) := by
      intro bs hbs
      have hbl : bs.length = q.2.1.length := hbs.length_eq
      obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs hxl hsp q hq bs hbs
      have hisl : (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))).length
          = nIdxX q.1 := by
        have := hfitT.length_eq
        simp only [List.length_append, List.length_singleton, List.length_map, hlenR q.1 ht,
          hxlT] at this
        simp only [List.length_map]
        omega
      have hmt := hmot q.1 ht
      have hhd : interp V (consList bs (consList (xs ++ fs) ρ))
          (.bvar (D + q.2.1.length - 1 - motPos q.1)) = xs.getD (motPos q.1) pt := by
        show consList bs (consList (xs ++ fs) ρ) _ = _
        rw [← consList_append, List.append_assoc,
          show D + q.2.1.length - 1 - motPos q.1
            = (fs ++ bs).length + xs.length - 1 - motPos q.1 by simp [hxl, hfl, hbl, ← hDd]; omega]
        exact consList_prefix_getD (by omega)
      rw [interp_mkAppN, ← List.foldl_map, hhd]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← hconclMot q.1 ht xs _ _ hxlT hisl]
      exact hconclTy q.1 ht xs _ _ hfitT
    refine lamTower_mem_piTower q.2.1 hbT hagree (fun bs hbs => ?_) hCty
    have hbl : bs.length = q.2.1.length := hbs.length_eq
    have hargR : ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        interp V (consList bs (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup htup g) ρ))) e
          = interp V (consList bs (consList (xs ++ fs) ρ)) e :=
      fun e he => interp_congr_below V e _ _ _ (hbA e he)
        (fun i hi' => consList_congr_below bs hagree i (by rw [hbl]; exact hi'))
    obtain ⟨is, his_def⟩ : ∃ is, is = q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))) :=
      ⟨_, rfl⟩
    obtain ⟨x, hx_def⟩ : ∃ x, x = interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2 :=
      ⟨_, rfl⟩
    have hbsρ : SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs := hbs
    obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs hxl hsp q hq bs hbsρ
    rw [← his_def, ← hx_def] at hfitT
    have hcall : genIhCallAt ρ ihd xs c j fs q.1 is x := ⟨q, hq, rfl, bs, hbsρ, his_def, hx_def⟩
    -- the body: the chain's recursor at the call's spine, i.e. the graph at the call
    have hbody : interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genFT ρ rP rds tup htup g) ρ)))
        (Term.mkAppN (.bvar (D + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
        = app g (tagged q.1 (tup q.1 is) x) := by
      rw [interp_mkAppN, ← List.foldl_map]
      have hhead : consList bs (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup htup g) ρ))
          (D + q.2.1.length + (K - 1 - q.1)) = genFT ρ rP rds tup htup g q.1 := by
        rw [← consList_append, show D + q.2.1.length + (K - 1 - q.1)
          = (K - 1 - q.1) + (xs ++ fs ++ bs).length by simp [hxl, hfl, hbl, ← hDd]; omega,
          consList_apply_add, chainFrame_apply ht]
      rw [show interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genFT ρ rP rds tup htup g) ρ)))
          (.bvar (D + q.2.1.length + (K - 1 - q.1))) = genFT ρ rP rds tup htup g q.1 from hhead]
      have hpv : (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)).map
          (interp V (consList bs (consList (xs ++ fs)
            (chainFrame K (genFT ρ rP rds tup htup g) ρ)))) = xs := by
        have h := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ bs)
          (ρ := chainFrame K (genFT ρ rP rds tup htup g) ρ) hxl
        rw [← List.append_assoc, consList_append] at h
        simpa [hbl, hfl, ← hDd, Nat.add_sub_cancel_left] using h
      rw [List.map_append, hpv, List.map_congr_left hargR]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← his_def, ← hx_def]
      have hfold := lamTowerA_fold
        (g := fun sp _ => app g (tagged q.1 (tup q.1 (idxOf (rP q.1) sp)) (majOf sp)))
        (hg := DefFun.app_apply (DefFun.const g)
          (DefFun.tagged_apply q.1 (htup q.1) (defFun_majOf_revList (rds q.1).length)))
        hfitT
      rw [idxOf_split hxlT, majOf_split] at hfold
      rw [genFT, hfold]
    -- the graph lands in the motive at the call
    obtain ⟨hiT, hxC, hretT⟩ := hsplitI q.1 ht xs is x hxlT hfitT
    have hpred : tagged q.1 (tup q.1 is) x ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs
        (c, j, fs) (hSep xs c j fs) :=
      mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hiT hxC, genCallT_iff.mpr ⟨_, _, _, hcall, rfl⟩⟩
    have hgv := hg _ hpred
    have hisl : is.length = nIdxX q.1 := by
      have := hfitT.length_eq
      simp only [List.length_append, List.length_singleton, hlenR q.1 ht,
        hxlT] at this
      omega
    rw [blockRecMot_tagged ht, hretT, hconclMot q.1 ht xs is x hxlT hisl] at hgv
    show interp V _ (Term.mkAppN
        (.bvar (D + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
      ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ))
      (Term.mkAppN (.bvar (D + q.2.1.length - 1 - motPos q.1))
        (q.2.2.1 ++ [q.2.2.2]))
    rw [hbody, interp_mkAppN, ← List.foldl_map]
    have hmt := hmot q.1 ht
    have hhd : interp V (consList bs (consList (xs ++ fs) ρ))
        (.bvar (D + q.2.1.length - 1 - motPos q.1)) = xs.getD (motPos q.1) pt := by
      show consList bs (consList (xs ++ fs) ρ) _ = _
      rw [← consList_append, List.append_assoc,
        show D + q.2.1.length - 1 - motPos q.1
          = (fs ++ bs).length + xs.length - 1 - motPos q.1 by simp [hxl, hfl, hbl, ← hDd]; omega]
      exact consList_prefix_getD (by omega)
    rw [hhd]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← his_def, ← hx_def]
    exact hgv
  -- the residue: the minor premise at the fields and the `ih` values
  obtain ⟨hsV, hhsV⟩ : ∃ hsV, hsV = genIhvT K ρ rP rds tup htup
      (fun c j => (ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
      xs c j fs g := ⟨_, rfl⟩
  rw [← hhsV]
  have hsVl : hsV.length = (ihd c j).length := by rw [hhsV]; simp [genIhvT]
  have hmin' := hmin c hc j hj
  have hpl := hpdl c hc
  have key := interp_genRb0 (ρ := ρ) (xs := xs) (fs := fs) (hs := hsV) (minPos := minPos c j)
    (by omega)
  rw [hxl, hfl, hsVl] at key
  rw [key]
  have hres := hminor c hc j hj xs hxs fs hfs hsV hsVl fun l q h hq hh => by
    rw [hhsV] at hh
    simp only [genIhvT, List.map_map, List.getElem?_map, hq, Option.map_some,
      Option.some.injEq] at hh
    subst hh
    rw [← hDd] at hih
    exact hih q (List.mem_of_getElem? hq)
  -- the motive at the constructor
  rw [blockRecMot_tagged hc, hisOf, hconclMot c hc xs _ _ (by rw [hxl, hpl]) hesl, ← hmkE]
  exact hres

end Generic

/-! ## 4. The rows, from the class facts

The producer's rows at the old class data follow from four facts about
the classes and the stored types (stated at one level assignment and
base frame):

* `GenClsSplit` — a fit of recursor `c`'s stored domains is a major
  of class `c` (its index tuple in the index set, its major in the
  carrier, the index spine recovered from the tuple);
* `GenClsBack` — conversely every major of class `c` spells a fit of
  the stored domains;
* `GenClsDec` — a spine fitting the rule's prefix and (declared) field
  domains decodes at class `c`: the fields hole-fit the constructor at
  the tuple of the declared index expressions' readings, which is in the
  index set and recovered from its tuple, and the constructor
  application reads to the injection, in the carrier there;
* the conclusion's typing at every fit of the stored domains (the
  stage record's, `blockRecConcl_univ`). -/

section Rows

variable {F : Nat} {envC : Env} {pp : BlockShape} {formers : List ConstantVal}
  {memberCtors : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

variable (mpC d Dc mc cvc pp out) in
/-- **The class split** at `(ψ, ρ)`: a fit of recursor `c`'s stored binder
data, split at the rule prefix and the class's index count, is a major of
class `c`, its index spine recovered from its tuple. -/
@[expose] def GenClsSplit (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ (xs is : List V) (x : V),
    xs.length = pp.rulePrefixAt c → is.length = (tgtMajor out c).nIdx →
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c))
      (xs ++ (is ++ [x])) →
    tgtClsTup d Dc mc cvc pp out ψ c is
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c ∧
      x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c)
        (tgtClsTup d Dc mc cvc pp out ψ c is) ∧
      isOfW (tgtClsU d Dc mc cvc pp out ψ c) (tgtClsNIdx d pp out c)
        (tgtClsTup d Dc mc cvc pp out ψ c is) = is

variable (mpC d Dc mc cvc pp out) in
/-- **The converse**: every major of class `c` spells a fit of recursor
`c`'s stored domains. -/
@[expose] def GenClsBack (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ (xs : List V) (i x : V),
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
    x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c) i →
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c))
      (xs ++ (isOfW (tgtClsU d Dc mc cvc pp out ψ c)
        (tgtClsNIdx d pp out c) i ++ [x]))

variable (mpC d Dc mc cvc pp out) in
/-- **The decoding at the rule frame**: a spine fitting the rule's prefix
and declared field domains, at a live class, hole-fits constructor `j` of
class `c` at the tuple of the declared index expressions' readings — a
tuple of the index set, its spine recovered — and the constructor
application reads to the injection, which lies in the carrier there. -/
@[expose] def GenClsDec (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
      ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ xs c →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c
        (tgtClsTup d Dc mc cvc pp out ψ c
          ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))) j fs ∧
      tgtClsTup d Dc mc cvc pp out ψ c
          ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c ∧
      isOfW (tgtClsU d Dc mc cvc pp out ψ c) (tgtClsNIdx d pp out c)
          (tgtClsTup d Dc mc cvc pp out ψ c
            ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))))
        = (tgtEsAV pp out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)) ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV pp out mpC.base2.acval envC ψ c j)
        = tgtClsInj d Dc mc cvc pp out ψ c j fs ∧
      tgtClsInj d Dc mc cvc pp out ψ c j fs
        ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c)
          (tgtClsTup d Dc mc cvc pp out ψ c
            ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))))

variable (mpC d Dc mc cvc pp out) in
/-- **The decoding's inverse**: a hole fit of constructor `j` of class `c`
at a tuple of the index set is a fit of the declared field domains, and
the tuple is the declared index expressions' readings'. -/
@[expose] def GenClsDecInv (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ (xs : List V) (i : V) (fs : List V),
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c i j fs →
    SpineFit (consList xs ρ) (tgtFdomsAV pp out mpC.base2.acval envC ψ c j) fs ∧
    i = tgtClsTup d Dc mc cvc pp out ψ c
      ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ)))

/-- A class's index set is guarded by the rule prefix's fit. -/
theorem tgtClsIs_prefix {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {c : Nat} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs := by
  have hg := (tgtClsIs_guard hi).1
  unfold tgtClsG at hg
  by_cases hm : (tgtMajor out c).member.isSome = true
  · rw [ite_eq_left hm] at hg; exact hg.2
  · rw [ite_eq_right hm] at hg; exact hg

/-- An index tuple's spine has the class's index count. -/
theorem isOfW_length (u n : Nat) (t : V) : (isOfW u n t).length = n := by
  unfold isOfW
  split
  · simp
  · exact ConLeche.SetTheory.Tower.projList_length n t

/-- **Row `hsplit`**, from the class split. -/
theorem genRow_hsplit
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)) ys →
      (prefOf (pp.rulePrefixAt c) ys).length = pp.rulePrefixAt c ∧
      ys = prefOf (pp.rulePrefixAt c) ys
        ++ (idxOf (pp.rulePrefixAt c) ys ++ [majOf ys]) ∧
      tgtClsTup d Dc mc cvc pp out ψ c (idxOf (pp.rulePrefixAt c) ys)
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ
          (prefOf (pp.rulePrefixAt c) ys) c ∧
      majOf ys ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ
          (prefOf (pp.rulePrefixAt c) ys) c)
        (tgtClsTup d Dc mc cvc pp out ψ c
          (idxOf (pp.rulePrefixAt c) ys)) := by
  intro c hc ys hfit
  have hlen : ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)).length = pp.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
    rw [genRds_length h ψ hc]
  obtain ⟨xs, is, x, rfl, hxl, hisl, -, -, -⟩ := spineFit_split_three hlen hfit
  obtain ⟨hI, hC, -⟩ := hS c hc xs is x hxl hisl hfit
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split]
  exact ⟨hxl, rfl, hI, hC⟩

/-- **Row `hconcl`**, from the class split. -/
theorem genRow_hconcl
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)) ys →
      blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval envC pp
          (tgtRs out) ψ) (tgtClsU d Dc mc cvc pp out ψ)
          (tgtClsNIdx d pp out) ρ (prefOf (pp.rulePrefixAt c) ys)
          (tagged c (tgtClsTup d Dc mc cvc pp out ψ c
            (idxOf (pp.rulePrefixAt c) ys)) (majOf ys))
        = interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c) := by
  intro c hc ys hfit
  have hlen : ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)).length = pp.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
    rw [genRds_length h ψ hc]
  obtain ⟨xs, is, x, rfl, hxl, hisl, -, -, -⟩ := spineFit_split_three hlen hfit
  obtain ⟨-, -, hret⟩ := hS c hc xs is x hxl hisl hfit
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split, blockRecMot_tagged hc, hret]

/-- **The conclusion's typing at every fit of the stored domains**
(the stage record's inferred sort, `blockRecConcl_univ`, at the pinned
elimination level). -/
theorem genRec_conclTy
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ ys,
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)) ys →
      interp V (consList ys ρ) (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.elim
          pp.large)) : V) := by
  intro c hc ys hfit
  obtain ⟨uOf, hruns⟩ := blockRecElimLevel_run h
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨fvs, conclE, sty, hop, hinf, hens⟩ := hruns c hc
  have hrd : (tgtRs out).getD c default = (tgtRs out)[c] := by
    rw [List.getD_eq_getElem?_getD, hr]; rfl
  rw [hrd] at hop
  have hsat : Sat V (((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c)).reverse) (consList ys ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfit
  have hu := blockRecConcl_univ mpC h hr ψ hop hinf hens _ hsat
  rwa [blockRecElimPin_run h hruns ψ hc] at hu

/-- **Row `hconclTy`**, from the converse split. -/
theorem genRow_hconclTy
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length →
      ∀ i, i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c) i →
      interp V (consList (xs ++ (isOfW (tgtClsU d Dc mc cvc pp out ψ c)
          (tgtClsNIdx d pp out c) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.elim
          pp.large)) : V) :=
  fun xs c hc i hi x hx => genRec_conclTy h ψ ρ c hc _ (hB c hc xs i x hi hx)

/-- A spine fitting the chain-lifted prefix and field domains fits the
base ones, and the lifted index expressions and constructor application
read at the chain frame as the base ones at the base frame. -/
theorem genRec_chainBase
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ a : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length) {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length)
    (hsp : SpineFit (chainFrame (tgtRs out).length a ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
      (xs ++ fs)) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
      ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) ∧
    (liftEsK (tgtRs out).length
        ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
        (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
        (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
      = (tgtEsAV pp out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ)) ∧
    interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
      = interp V (consList (xs ++ fs) ρ) (tgtMkAV pp out mpC.base2.acval envC ψ c j) := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpK : liftDomsK (tgtRs out).length 0
      (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c)
      = blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c :=
    blockRecPdomsK_run (V := V) mpC h hr ψ _
  have hbase := chainFit_base hpK hxl hsp
  have hfl : fs.length = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length := by
    have := hbase.length_eq
    simp only [List.length_append, hxl] at this
    omega
  have hwl : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
        + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length := by
    rw [List.length_append, hxl, hfl]
  refine ⟨hbase, ?_, ?_⟩
  · simp only [liftEsK, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp]
    rw [← hwl, interp_liftN_chainFrame]
  · rw [tgtMkK, ← hwl, interp_liftN_chainFrame]

/-- **Row `hdec`**, from the decoding at the rule frame. -/
theorem genRow_hdec
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hlive : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ xs c) :
    ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j) (xs ++ fs) →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c
          (tgtClsTup d Dc mc cvc pp out ψ c
            ((liftEsK (tgtRs out).length
                ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
                  + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))))) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
          = tgtClsInj d Dc mc cvc pp out ψ c j fs := by
  intro a ha c hc j hj xs fs hxl hsp
  obtain ⟨hbase, hes, hmk⟩ := genRec_chainBase h ψ ρ a hc hxl hsp
  obtain ⟨hfit, -, -, hmkE, -⟩ := hD c hc j hj xs fs hxl hbase
    (hlive a ha c hc j hj xs fs hxl hbase)
  rw [hes, hmk]
  exact ⟨hfit, hmkE⟩

/-- **Row `hrule`**, from the decoding at the rule frame and the converse
split. -/
theorem genRow_hrule
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hlive : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ xs c) :
    ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j) (xs ++ fs) →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c))
        (xs ++ ((liftEsK (tgtRs out).length
              ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
                + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)])) := by
  intro a ha c hc j hj xs fs hxl hsp
  obtain ⟨hbase, hes, hmk⟩ := genRec_chainBase h ψ ρ a hc hxl hsp
  obtain ⟨-, hI, hret, hmkE, hC⟩ := hD c hc j hj xs fs hxl hbase
    (hlive a ha c hc j hj xs fs hxl hbase)
  have hfit := hB c hc xs _ _ hI hC
  rw [hret, ← hmkE] at hfit
  rw [hes, hmk]
  exact hfit

/-- **Row `huniq`**, from the classes' recorded clauses (`genUniq`): the
class fit is the clause's hole fit at the carrier and the injection the
clause's, definitionally; at `ℓ = 0` the conclusion's typing; at a
`Prop`-valued class under a nonzero elimination level, the elimination guard. -/
theorem genRow_huniq
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    (hDin : ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks)
    (hmN : ∀ c, c < (tgtRs out).length → tgtClsM mc pp out c < (tgtClsD d Dc out c).N)
    (hlic : Level.eval ψ (ConLeche.structElimLevel pp.elim pp.large) ≠ 0 →
      ∀ xs, ∀ c, c < (tgtRs out).length →
      (tgtClsD d Dc out c).w (tgtClsψ cvc out ψ c) = 0 →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
      ∀ j fs j' fs',
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c t j fs →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c t j' fs' →
      j = j' ∧ fs = fs') :
    ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs) →
      ∀ e e',
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsInj d Dc mc cvc pp out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          xs u e →
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsInj d Dc mc cvc pp out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs u →
        v' ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs u →
        v = v' := by
  intro xs
  exact genUniq (acval := mpC.base2.acval) (nCt := blockRecNCt (tgtRs out))
    (fun c => tgtClsD d Dc out c) (fun c => tgtClsψ cvc out ψ c)
    (fun c => tgtClsFr d mpC.base2.acval envC pp out ψ ρ xs c)
    (fun c => tgtClsM mc pp out c)
    (fun c hc _ _ => (mpC.lfp_ok _ (hDin c hc)).1) (fun c hc _ _ => hmN c hc)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ hf => hf)
    (genRow_hconclTy h ψ ρ hB xs) (hlic · xs)

section RowsIh

variable {g : ClassGen} {rd : ClassRead}

/-- The generated `ih` terms are the generic ones at the rule frame's
depths: the shared prefix is the rule prefix (`hgpre`), the constructor's
field count the declared fields' (`hnF`). -/
theorem genIhsAV_eq (ψ : Name → Nat) {c j : Nat}
    (hgpre : g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length)
    (hnF : (genCtorAt g rd c j).nF = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
    (K : Nat) (fl : Nat)
    (hfl : fl = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length) :
    genIhsAV mpC.base2.acval envC K g rd ψ c j
      = (genIhdAV mpC.base2.acval envC g rd ψ c j).map
        (genIhAV K (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length + fl)) := by
  rw [genIhsAV, hgpre, hnF, hfl]

set_option maxHeartbeats 2000000 in
/-- **Row `hchain`**, from the `ih` calls' typing at the rule frame
(`hcallTy`), the class split and the `ih` data's bounds. -/
theorem genRow_hchain
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hgpre : ∀ c, c < (tgtRs out).length → g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length)
    (hnF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      (genCtorAt g rd c j).nF = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
    (hcal : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j, q.1 < (tgtRs out).length)
    (hbelow : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
        IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length) q)
    (hcallTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.rulePrefixAt q.1 ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ q.1))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]))) :
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
        xs.length = pp.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ c')) (xs ++ (is ++ [x])) →
        r (tagged c' (tgtClsTup d Dc mc cvc pp out ψ c' is) x)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
        SpineFit (chainFrame (tgtRs out).length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
            ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
          (xs ++ fs) →
        (hGr : HasGraph (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
            (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ) (tgtRs out).length
            (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
              (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs (c, j, fs)
            (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
              (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
              (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs)) r) →
        genIhvT (tgtRs out).length ρ pp.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp out ψ)
            (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
              (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ) xs c j fs
            (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
              (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
              (tgtRs out).length
              (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
                (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs
              (c, j, fs)
              (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
                (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
                (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs)) hGr)
          = (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))) := by
  intro a xs r hr c hc j hj fs hxl hsp hGr
  have hih : ∀ c', c' < (tgtRs out).length → ∀ j', j' < blockRecNCt (tgtRs out) c' →
      genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c' j'
        = (genIhdAV mpC.base2.acval envC g rd ψ c' j').map
          (genIhAV (tgtRs out).length
            (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c').length
            ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c').length
              + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c'
                j').length)) :=
    fun c' hc' j' hj' => genIhsAV_eq ψ (hgpre c' hc') (hnF c' hc' j' hj') _ _
      (by simp [tgtFdomsK, liftDomsK_length])
  -- the chain-frame call typing, from the base one
  have hcallC : ∀ c', c' < (tgtRs out).length → ∀ j', j' < blockRecNCt (tgtRs out) c' →
      ∀ (xs fs : List V) (a : Nat → V),
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c').length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c'
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c' j')
        (xs ++ fs) →
      ∀ t is x, genIhCallAt ρ (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)
          xs c' j' fs t is x →
        t < (tgtRs out).length ∧ xs.length = pp.rulePrefixAt t ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ t)) (xs ++ (is ++ [x])) := by
    intro c' hc' j' hj' xs fs a hxl hsp t is x hcall
    obtain ⟨hbase, -, -⟩ := genRec_chainBase h ψ ρ a hc' hxl hsp
    obtain ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩ := hcall
    exact hcallTy c' hc' j' hj' xs fs hxl hbase q hq bs hbs
  -- `hihRead`, by construction
  have hread := genIhs_hihRead (K := (tgtRs out).length) (ρ := ρ) (nCt := blockRecNCt (tgtRs out))
    (pre := fun c'' => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ
          c'')
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j) hcal
    (fun c' hc' j' hj' q hq => by
      simpa [tgtFdomsK, liftDomsK_length] using hbelow c' hc' j' hj' q hq)
  have H := genHchainG (K := (tgtRs out).length) (ρ := ρ) (rP := pp.rulePrefixAt)
    (nCt := blockRecNCt (tgtRs out))
    (rds := blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (tup := tgtClsTup d Dc mc cvc pp out ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)
    (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
      (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
    (fun xs c' j' fs' => hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
      (fun c'' => ⟨tgtClsU d Dc mc cvc pp out ψ c'', fun _ => rfl⟩)
      (fun c'' j'' => genIhdAV mpC.base2.acval envC g rd ψ c'' j'') _ xs c' j' fs')
    (fun c' hc' xs is x hxl hfit => by
      have hisl : is.length = (tgtMajor out c').nIdx := by
        have := hfit.length_eq
        simp only [List.length_append, List.length_singleton,
          genRds_length h ψ hc', hxl] at this
        omega
      obtain ⟨h1, h2, -⟩ := hS c' hc' xs is x hxl hisl hfit
      exact ⟨h1, h2⟩)
    hcallC
    (fun c' hc' j' hj' xs fs a a' hxl hsp hcall => by
      exact hread c' hc' j' hj' xs fs a a' hxl hsp hcall)
    a xs r hr c hc j hj fs hxl hsp hGr
  rw [genIhvT, hih c hc j hj]
  rw [genIhvT] at H
  exact H

set_option maxHeartbeats 2000000 in
/-- **Row `hstep`**, from the minor premise's typing at the rule frame
(`hminor`), the stored conclusion as the motive applied (`hconclMot`), the
`ih` calls' typing, the class split and the decoding both ways. -/
theorem genRow_hstep
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ) (hDI : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ)
    (hnIdx : ∀ c, c < (tgtRs out).length →
      tgtClsNIdx d pp out c = (tgtMajor out c).nIdx)
    (hgpre : ∀ c, c < (tgtRs out).length → g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length)
    (hnF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      (genCtorAt g rd c j).nF = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
    (hmot : ∀ c, c < (tgtRs out).length →
      classMotPos g (genClsOf rd c) < pp.rulePrefixAt c)
    (hmin : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      g.nP + genMinorSlot g rd c j < pp.rulePrefixAt c)
    (hbelow : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
        IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length) q)
    (hcallTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.rulePrefixAt q.1 ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ q.1))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])))
    (hconclMot : ∀ c, c < (tgtRs out).length → ∀ (xs zs : List V) (x : V),
      xs.length = pp.rulePrefixAt c → zs.length = (tgtMajor out c).nIdx →
      interp V (consList (xs ++ (zs ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (classMotPos g (genClsOf rd c)) pt))
    (hminor : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs →
      ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp out mpC.base2.acval envC ψ c j) fs →
      ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC g rd ψ c j).length →
      (∀ (l : Nat) (q : IhDatum) (hv : V),
        (genIhdAV mpC.base2.acval envC g rd ψ c j)[l]? = some q → hs[l]? = some hv →
        hv ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
              + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
            (classMotPos g (genClsOf rd q.1)) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + genMinorSlot g rd c j) pt)
        ∈ˢ ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ)
              (tgtMkAV pp out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
            (xs.getD (classMotPos g (genClsOf rd c)) pt)) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c i j fs → ∀ gv : V,
      (∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ) (tgtRs out).length
          (genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
            (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)) xs (c, j, fs)
          (hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
            (fun c' => ⟨tgtClsU d Dc mc cvc pp out ψ c', fun _ => rfl⟩)
            (fun c' j' => genIhdAV mpC.base2.acval envC g rd ψ c' j') _ xs c j fs) →
        app gv v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs v) →
      interp V (consList (genIhvT (tgtRs out).length ρ pp.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp out ψ)
            (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
              (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ) xs c j fs gv)
          (consList (xs ++ fs) ρ)) (genRbAV g rd c j)
        ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp out ψ) (tgtClsNIdx d pp out) ρ xs
          (tagged c i (tgtClsInj d Dc mc cvc pp out ψ c j fs)) := by
  intro xs c hc j hj i fs hi hfit gv hg
  have hpdl : ∀ c', c' < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c').length
        = pp.rulePrefixAt c' :=
    fun c' hc' => blockRulePdomsAV_length mpC h (List.getElem?_eq_getElem hc') ψ
  have H := genHstepG (K := (tgtRs out).length) (ρ := ρ) (rP := pp.rulePrefixAt)
    (nCt := blockRecNCt (tgtRs out))
    (rds := blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (tup := tgtClsTup d Dc mc cvc pp out ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (fdoms := fun c j => tgtFdomsAV pp out mpC.base2.acval envC ψ c j)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j)
    (uX := tgtClsU d Dc mc cvc pp out ψ) (nIdxX := tgtClsNIdx d pp out)
    (concl := blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ)
    (injX := tgtClsInj d Dc mc cvc pp out ψ)
    (es := fun c j => tgtEsAV pp out mpC.base2.acval envC ψ c j)
    (mk := fun c j => tgtMkAV pp out mpC.base2.acval envC ψ c j)
    (defFun_tgtClsTup_param d Dc mc cvc pp out ψ pp.rulePrefixAt
      (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ))
    (fun xs c' j' fs' => hasSep_genCallT (tgtClsTup d Dc mc cvc pp out ψ) ρ
      (fun c'' => ⟨tgtClsU d Dc mc cvc pp out ψ c'', fun _ => rfl⟩)
      (fun c'' j'' => genIhdAV mpC.base2.acval envC g rd ψ c'' j'') _ xs c' j' fs')
    (fun r => classMotPos g (genClsOf rd r)) (fun c j => g.nP + genMinorSlot g rd c j)
    hpdl
    (fun c' hc' => by rw [genRds_length h ψ hc', hnIdx c' hc'])
    hmot hmin
    (fun xs c' i _ hi => tgtClsIs_prefix hi)
    (fun c' hc' xs is x hxl hfit => by
      have hisl : is.length = (tgtMajor out c').nIdx := by
        have := hfit.length_eq
        simp only [List.length_append, List.length_singleton,
          genRds_length h ψ hc', hxl] at this
        omega
      exact hS c' hc' xs is x hxl hisl hfit)
    (fun c' hc' j' hj' xs i fs hi hfit => by
      obtain ⟨hfs, rfl⟩ := hDI c' hc' j' hj' xs i fs hi hfit
      have hxs := tgtClsIs_prefix hi
      obtain ⟨-, -, hret, hmkE, -⟩ := hD c' hc' j' hj' xs fs hxs.length_eq (SpineFit.append hxs hfs)
        (tgtClsIs_guard hi).2
      refine ⟨hfs, hret, ?_, hmkE⟩
      rw [← hret, isOfW_length])
    hcallTy hbelow
    (fun c' hc' xs zs x hxl hzl => hconclMot c' hc' xs zs x hxl (by rw [hzl, hnIdx c' hc']))
    (fun c' hc' xs zs x hfit => by
      -- the recursor type's innermost fibre is its conclusion, a type
      obtain ⟨-, -, -, -, heq, hlen, -, -, hwd⟩ :=
        recStage_tyPis mpC h (List.getElem?_eq_getElem hc') ψ
      have hwdρ := hwd ρ
      rw [heq] at hwdρ
      exact isTy_of_wd_mkPisAV (fun h0 => by rw [h0] at hlen; simp at hlen) hwdρ hfit)
    hminor
    xs c hc j hj i fs hi hfit gv hg
  have hih := genIhsAV_eq (mpC := mpC) (envC := envC) (pp := pp) (out := out) (g := g) (rd := rd)
    ψ (hgpre c hc) (hnF c hc j hj) (tgtRs out).length _ rfl
  have hRb : genRbAV g rd c j = genRb0
      (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
      (g.nP + genMinorSlot g rd c j)
      (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length
      (genIhdAV mpC.base2.acval envC g rd ψ c j).length := by
    rw [genRbAV, hgpre c hc, hnF c hc j hj]
    simp [genIhdAV]
  rw [genIhvT, hih, hRb]
  rw [genIhvT] at H
  exact H

end RowsIh

set_option maxHeartbeats 4000000 in
/-- **`hEq`'s grading half at the generated components** (the old
`tgtRecEqs_hEqAny`'s argument): the frame from its grading (`hframe`,
the declared field domains bounded, `hfdB`), the left-hand side an
application chain along the recursor's stored type (the rule's spine
fits it, `genRow_hrule`, its arguments graded, `hargs`), the right-hand
side from the `ih` terms' and the residue's grading at typed tuples
(`hrhs`). -/
theorem genRecEqs_wd
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) {g : ClassGen}
    {rd : ClassRead} (ψ : Name → Nat) (ρ : Nat → V)
    (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ) (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hlive : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ xs c)
    (hfdB : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      DomsBelow (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
        (tgtFdomsAV pp out mpC.base2.acval envC ψ c j))
    (hframe : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenotedTy V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
            ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).getD l default))
    (hargs : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) ys →
      (∀ e ∈ tgtEsAV pp out mpC.base2.acval envC ψ c j,
        WellDenoted V (consList ys ρ) e) ∧
      WellDenoted V (consList ys ρ) (tgtMkAV pp out mpC.base2.acval envC ψ c j))
    (hrhs : ∀ rs : List V, rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c j,
        WellDenoted V (consList ys (consList rs ρ)) v) ∧
      WellDenoted V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV g rd c j)) :
    ∀ (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ)
          (fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ,
        WellDenoted V (consList rs ρ) e := by
  intro tup hlen htyp e he
  rw [← genClsEqs_eq h (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ') (fun _ => genRbAV g rd) ψ] at he
  refine (hEq_iotaEqsAV_of (fun as hl ht c hc j hj => ?_) tup hlen htyp e he).2
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpl := blockRulePdomsAV_length mpC h hr ψ
  have hfdK : tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j
      = tgtFdomsAV pp out mpC.base2.acval envC ψ c j := by
    rw [tgtFdomsK]
    exact liftDomsK_eq_self_of_bounded _ _ (domsBelow_getD (hfdB c hc j hj))
  have hch := consList_eq_chainFrame (V := V) hl ρ
  refine ⟨?_, fun ys hys => ?_⟩
  · rw [hfdK]
    exact fieldsOkB_zero_of_spineGrading _ (fun l hl' ys hys =>
      hframe c hc j hj l hl' (consList as ρ) ys hys)
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_inv hys
  have hxl := hxs.length_eq
  have hsp : SpineFit (chainFrame (tgtRs out).length (fun c => as.getD c pt) ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)
      (xs ++ fs) := by rw [← hch]; exact hys
  obtain ⟨hbase, hesE, hmkE⟩ := genRec_chainBase h ψ ρ (fun c => as.getD c pt) hc hxl hsp
  have hfl : fs.length = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length := by
    have := hbase.length_eq
    simp only [List.length_append, hxl] at this
    omega
  have hwl : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
        + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length := by
    rw [List.length_append, hxl, hfl]
  obtain ⟨hE, hMk⟩ := hargs c hc j hj (xs ++ fs) hbase
  refine ⟨?_, ?_⟩
  · -- the left-hand side: an application chain along the recursor's type
    have hfit := genRow_hrule h ψ ρ hB hD hlive (fun c => as.getD c pt) (fun c hc => ht c hc) c hc j hj xs fs hxl hsp
    have hflK : (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
        = fs.length := by rw [hfdK, hfl]
    have hpv : (prefVarsAV
        (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
            (fun c => as.getD c pt) ρ)))
        = xs := by
      rw [hflK]; exact interp_prefVarsAV hxl
    have hhead : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
          + ((tgtRs out).length - 1 - c))) = as.getD c pt := by
      show consList (xs ++ fs) _ _ = _
      rw [show (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
          + ((tgtRs out).length - 1 - c) = ((tgtRs out).length - 1 - c) + (xs ++ fs).length from by
            rw [List.length_append, hxl, hflK]; omega,
        Nat.sub_zero, consList_apply_add, chainFrame_apply hc]
    obtain ⟨-, -, -, -, hTyE, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) mpC h hr ψ
    have hTF := teleFit_mkPisAV_of_spineFit
      (B := blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c) hfit
    rw [← hTyE] at hTF
    have hvals : (prefVarsAV
            (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
            (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
          ++ liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
              + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp out mpC.base2.acval envC ψ c j)
          ++ [tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j]).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
            (fun c => as.getD c pt) ρ)))
        = xs ++ ((liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
              + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp out ψ c j)]) := by
      rw [List.map_append, List.map_append, hpv, List.map_cons, List.map_nil, List.append_assoc]
    rw [← hvals] at hTF
    have hmem' : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
          + ((tgtRs out).length - 1 - c)))
        ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) := by
      rw [hhead]; exact ht c hc
    rw [← hch] at hTF hmem'
    refine (Rules.wellDenoted_mkAppN_of_fit _
      (f := .bvar ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp out ψ c j).length
          + ((tgtRs out).length - 1 - c))) (hwdTy ρ) trivial (fun x hx => ?_)
      hmem' hTF).1
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        trivial
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        rw [hch, ← hwl, wellDenoted_liftN_chainFrame]
        exact hE e he
    · rw [List.mem_singleton] at hx
      rw [hx, tgtMkK, hch, ← hwl, wellDenoted_liftN_chainFrame]
      exact hMk
  · -- the residue, at the `ih` values
    obtain ⟨hIv, hRv⟩ := hrhs as hl ht c hc j hj (xs ++ fs) hbase
    rw [wd_instsAV (fun v hv => hIv v hv)]
    have key := (wellDenoted_liftN_chainFrame (K := (tgtRs out).length)
      (a := fun c => as.getD c pt) (ρ := ρ)
      ((xs ++ fs) ++ (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ c
        j).map (interp V (consList (xs ++ fs) (consList as ρ))))
      (genRbAV g rd c j)).mpr (by simpa only [consList_append] using hRv)
    rw [← hch] at key
    simp only [consList_append, List.length_append, List.length_map] at key ⊢
    rw [← hxl, ← hfs.length_eq]
    exact key

end Rows

/-! ## 5. The family premise, assembled -/

section Assembly

variable {F : Nat} {envC : Env} {pp : BlockShape}
  {memberCtors : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal} {g : ClassGen} {rd : ClassRead}

variable (pp out mpC d Dc mc cvc g rd) in
/-- **What the candidate still asks**, at one level assignment and base
frame: the class facts (split both ways, decoding both ways), the
classes' liveness at a typed tuple's rule frames, the classes' recorded clauses, the elimination guard, the generated `ih`s'
data (callees, bounds, calls' typing), the stored conclusion as the
motive applied, the minor premise's typing at the rule frame, the
prefix positions, and the class induction (lane B2's interface). -/
structure GenPreHyps (ψ : Name → Nat) (ρ : Nat → V) : Prop where
  split : GenClsSplit pp out mpC d Dc mc cvc ψ ρ
  back : GenClsBack pp out mpC d Dc mc cvc ψ ρ
  dec : GenClsDec pp out mpC d Dc mc cvc ψ ρ
  decInv : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ
  live : ∀ a : Nat → V, (∀ c, c < (tgtRs out).length →
      a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
      ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ xs c
  nIdx : ∀ c, c < (tgtRs out).length →
    tgtClsNIdx d pp out c = (tgtMajor out c).nIdx
  din : ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks
  mN : ∀ c, c < (tgtRs out).length → tgtClsM mc pp out c < (tgtClsD d Dc out c).N
  fitLen : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ((tgtClsD d Dc out c).fields (tgtClsψ cvc out ψ c) (tgtClsM mc pp out c) j).length
      = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length
  lic : Level.eval ψ (ConLeche.structElimLevel pp.elim pp.large) ≠ 0 →
    ∀ xs, ∀ c, c < (tgtRs out).length →
    (tgtClsD d Dc out c).w (tgtClsψ cvc out ψ c) = 0 →
    ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c →
    ∀ j fs j' fs',
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c t j fs →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp out ψ ρ xs c t j' fs' →
    j = j' ∧ fs = fs'
  gpre : ∀ c, c < (tgtRs out).length → g.pre.length
    = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
  nF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    (genCtorAt g rd c j).nF = (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length
  mot : ∀ c, c < (tgtRs out).length →
    classMotPos g (genClsOf rd c) < pp.rulePrefixAt c
  min : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    g.nP + genMinorSlot g rd c j < pp.rulePrefixAt c
  cal : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j, q.1 < (tgtRs out).length
  below : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
      IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
        + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length) q
  callTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
      ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd ψ c j,
    ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs →
      q.1 < (tgtRs out).length ∧ xs.length = pp.rulePrefixAt q.1 ∧
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ q.1))
        (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]))
  conclMot : ∀ c, c < (tgtRs out).length → ∀ (xs zs : List V) (x : V),
    xs.length = pp.rulePrefixAt c → zs.length = (tgtMajor out c).nIdx →
    interp V (consList (xs ++ (zs ++ [x])) ρ)
        (blockRecConclAV mpC.base2.acval envC pp (tgtRs out) ψ c)
      = (zs ++ [x]).foldl SetTheory.app (xs.getD (classMotPos g (genClsOf rd c)) pt)
  minor : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs →
    ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp out mpC.base2.acval envC ψ c j) fs →
    ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC g rd ψ c j).length →
    (∀ (l : Nat) (q : IhDatum) (hv : V),
      (genIhdAV mpC.base2.acval envC g rd ψ c j)[l]? = some q → hs[l]? = some hv →
      hv ∈ˢ interp V (consList (xs ++ fs) ρ)
        (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length
            + (tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length)
          (classMotPos g (genClsOf rd q.1)) q)) →
    (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + genMinorSlot g rd c j) pt)
      ∈ˢ ((tgtEsAV pp out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ))
          ++ [interp V (consList (xs ++ fs) ρ)
            (tgtMkAV pp out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
          (xs.getD (classMotPos g (genClsOf rd c)) pt)
  ind : GenClassInd mpC.base2.acval envC pp out d Dc mc cvc
    (fun c j => genIhdAV mpC.base2.acval envC g rd ψ c j) ψ ρ

set_option maxHeartbeats 4000000 in
/-- **The candidate, from `GenPreHyps`.** -/
theorem genRecPre_hCandH
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (ψ : Name → Nat) (ρ : Nat → V) (H : GenPreHyps pp out mpC d Dc mc cvc g rd ψ ρ) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp out mpC.base2.acval envC ψ')
          (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ')
          (fun ψ' => tgtMkAV pp out mpC.base2.acval envC ψ')
          (fun _ => genRbAV g rd) ψ,
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e :=
  genRecPre_hCand h ψ ρ H.din H.mN H.fitLen
    (genRow_hsplit h ψ ρ H.split) (genRow_hconcl h ψ ρ H.split)
    (genRow_hconclTy h ψ ρ H.back)
    (genRow_hstep h ψ ρ H.split H.dec H.decInv H.nIdx H.gpre H.nF H.mot H.min H.below
      H.callTy H.conclMot H.minor)
    (genRow_huniq h ψ ρ H.back H.din H.mN H.lic) H.ind
    (genRow_hrule h ψ ρ H.back H.dec H.live) (genRow_hdec h ψ ρ H.dec H.live)
    (genRow_hchain h ψ ρ H.split H.gpre H.nF H.cal H.below H.callTy)

set_option maxHeartbeats 4000000 in
/-- **THE FAMILY PREMISE AT THE GENERATED STAGE** — the skeleton's `hpre`
goal, from the family's level (`hTy`, `blockRecLevel_run`), the equations'
grading at typed tuples (`hEqWd`), and `GenPreHyps` at every level
assignment and base frame. -/
theorem genRecPre
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    {s : (Name → Nat) → Nat}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (tgtRs out).length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) ∈ˢ univ (s ψ) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c))
    (hEqWd : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ)
          (fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ,
        WellDenoted V (consList rs ρ) e)
    (H : ∀ (ψ : Name → Nat) (ρ : Nat → V), GenPreHyps pp out mpC d Dc mc cvc g rd ψ ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V (s ψ) (tgtRs out).length (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd ψ)
          (fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ)
        ρ := by
  intro ψ ρ
  refine ⟨fun c hc => hTy ψ ρ c hc, fun rs hl ht e he =>
    ⟨blockRecEqs_univZero _ _ _ _ _ _ _ _ ψ _ e he, hEqWd ψ ρ rs hl ht e he⟩, ?_⟩
  exact genRecPre_hCandH h ψ ρ (H ψ ρ)

end Assembly

end ConLeche.Model
