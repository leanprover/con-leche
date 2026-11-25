module

import ConLeche.SetModel.NestRecCls
public import ConLeche.Model.Inductives.TargetNestKit
public import ConLeche.Model.Inductives.TargetClassRows

public section

/-!
# The class induction from a NODE PRESENTATION

The class induction (`TgtClassIndG`) is the node kit's induction over
node majors (`NestNodeInd.ind_recNodesOn`) along a class→node relation
at which the recursor classes' data are the nodes' and the recursor's
calls land at related nodes.  The kit's classes are the positivity
derivation's NODES — one instantiation may be visited at several nodes,
and the visits' nesting orders the induction.  This module builds it
from a PRESENTATION of
the nodes as recorded lfp clauses (`TgtNodePres`), whose fields are the
facts about the nodes one by one — the recursor-side plumbing (the
predecessor set, the kit, the transport of the class data) is done here,
once:

* the nodes: `nC` recorded clauses `Db b` at level assignments `ψb b`,
  TRUE frames `frb b`, depths `dp b`, admissible frames `Adm`
  (`lfpNestKit`'s data and its `hcl`/`hAdm`/`trans`/`top`: `trans` is
  positivity at the instantiation, `KeyPos` at a derived node, the
  clause's `fitsMono` at the block's own);
* the class tie, SEMANTIC: at a related pair `Rel c b` the class's
  clause, level assignment, frame and component are the node's
  (`tgtClsD`/`tgtClsψ`/`tgtClsFr`/`tgtClsM`), and the class's guard holds;
* the calls, at a related pair and a TRUE decoding, one callee node per
  call target (`hcall`): a node `b'` related to the callee's class at
  which the target lands, at EVERY admissible visit of the caller —
  its own group (`b' = b`, the target in the visit's hole tuple), an
  enclosing node (`G`), or a deeper node at an admissible frame
  (`NodeLands`, the kit's `calls` disjunction).

The predecessors of a node decoding are then DEFINED as the related
classes' call targets, each at its chosen callee node (`TgtNodePres.pred`),
and the kit is `lfpNestKit`.

`tgtClassInd_of_pres` — `TgtClassIndG` from presentations whose relation covers every GUARDED class (an
unguarded class has no major: its index set is empty).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

theorem addOwn_padTuple_eq {G : V} {b N : Nat} {Is : Nat → V} (Y : Nat → V) :
    addOwn G b N Is (padTuple fun i : Fin N => Y i.val) = addOwn G b N Is Y := by
  apply ext
  intro u
  simp only [mem_addOwn]
  constructor
  · rintro (hu | ⟨c, t, y, hc, ht, hy, rfl⟩)
    · exact Or.inl hu
    · exact Or.inr ⟨c, t, y, hc, ht, by rwa [padTuple_lt _ hc] at hy, rfl⟩
  · rintro (hu | ⟨c, t, y, hc, ht, hy, rfl⟩)
    · exact Or.inl hu
    · exact Or.inr ⟨c, t, y, hc, ht, by rwa [padTuple_lt _ hc], rfl⟩

theorem frame_congr_members (D : LfpDatum V) (ψ : Name → Nat) {ρp X X' : Nat → V}
    (h : ∀ m, m < D.k → X m = X' m) :
    D.frame ψ ρp X = D.frame ψ ρp X' := by
  unfold LfpDatum.frame
  congr 1
  refine List.map_congr_left fun m hm => ?_
  have hmk : m < D.k := List.mem_range.mp hm
  unfold LfpDatum.holeVal
  congr 1
  funext vs; rw [h m hmk]

theorem hfits_congr_members {D : LfpDatum V} {ψ : Name → Nat} {ρp X X' : Nat → V}
    (h : ∀ m, m < D.k → X m = X' m) (t : V) (c j : Nat) (fs : List V) :
    D.HFits ψ ρp X t c j fs ↔ D.HFits ψ ρp X' t c j fs := by
  simp only [LfpDatum.HFits, frame_congr_members D ψ h]

private theorem defHoleFn_cons_list_np {r n : Nat} {g : List V → V} (hg : DefHoleFn (r + n) g) :
    ∀ (as : List V), as.length = r → DefHoleFn n fun vs => g (as ++ vs) := by
  induction r generalizing g with
  | zero =>
    intro as hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    rw [Nat.zero_add] at hg
    simpa only [List.nil_append] using hg
  | succ r ih =>
    intro as hlen
    cases as with
    | nil => simp at hlen
    | cons a as =>
      rw [Nat.succ_add] at hg
      exact ih (hg.cons a) as (by simpa using hlen)

private theorem defFun_mkTower_ofFn_np {k : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => Tower.mkTower (List.ofFn fun i => As i env)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [Tower.mkTower]
  | r + 1, As, hAs => by
    have hrest := defFun_mkTower_ofFn_np (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact (DefFun.spair_apply (hAs 0) hrest).congr fun env => by
      simp [List.ofFn_succ, Tower.mkTower]

private theorem defFun_tupW_ofFn_np (u : Nat) {k r : Nat}
    (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefFun k fun env => tupW u (List.ofFn fun i => As i env) := by
  by_cases hu : u = 0
  · subst hu
    exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn_np As hAs).congr fun _ => (tupW_pos hu _).symm

private theorem holeFam_congr_eq_np {Fs : List Term} {ρ ρ' : Nat → V} {g g' : List V → V}
    {hg : DefHoleFn Fs.length g} {hg' : DefHoleFn Fs.length g'}
    (hρ : ρ = ρ') (hg_eq : g = g') :
    holeFam ρ Fs g hg = holeFam ρ' Fs g' hg' := by
  subst hρ hg_eq
  rfl

private theorem defFun_holeFam_app_ofFn_np (u : Nat) (tail : Nat → V) :
    ∀ (Fs : List Term) {k m r : Nat}
      (Xs : Fin m → (Fin k → V) → V) (_ : ∀ i, DefFun k (Xs i))
      (Y : (Fin k → V) → V) (_ : DefFun k Y)
      (As : Fin r → (Fin k → V) → V) (_ : ∀ i, DefFun k (As i)),
      DefFun k fun env =>
        holeFam (Semantics.prepend (fun i => Xs i env) tail) Fs
          (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs)))
          (defHoleFn_cons_list_np (DefHoleFn.of_app_tupW (Y env) u (r + Fs.length))
            (List.ofFn fun i => As i env) List.length_ofFn)
  | [], k, m, r, Xs, hXs, Y, hY, As, hAs =>
    (DefFun.app_apply hY (defFun_tupW_ofFn_np u As hAs)).congr fun env => by
      rw [holeFam_nil, List.append_nil]
  | F :: Fs, k, m, r, Xs, hXs, Y, hY, As, hAs => by
    have hF : DefFun k fun env => interp V (Semantics.prepend (fun i => Xs i env) tail) F :=
      (interp_defFun_prepend tail m F).comp hXs
    let Xs' : Fin (m + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (k + 1) (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    let Y' : (Fin (k + 1) → V) → V := fun w => Y (ftail w)
    have hY' : DefFun (k + 1) Y' := hY.weaken
    let As' : Fin (r + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if hi : i.val < r then As ⟨i.val, hi⟩ (ftail w) else w 0
    have hAs' : ∀ i, DefFun (k + 1) (As' i) := fun ⟨i, hi⟩ => by
      dsimp only [As']
      split
      · exact (hAs _).weaken
      · exact DefFun.proj 0
    have hrec := defFun_holeFam_app_ofFn_np u tail Fs Xs' hXs' Y' hY' As' hAs'
    let hg_all : ∀ env, DefHoleFn (F :: Fs).length
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs))) := fun env =>
      defHoleFn_cons_list_np (DefHoleFn.of_app_tupW (Y env) u (r + (F :: Fs).length))
        (List.ofFn fun i => As i env) List.length_ofFn
    let F_lam : V → (Fin k → V) → V := fun x env =>
      holeFam (cons x (Semantics.prepend (fun i => Xs i env) tail)) Fs
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ x :: vs)))
        ((hg_all env).cons x)
    have hrec' : DefFun (k + 1) fun w => F_lam (w 0) (ftail w) := by
      refine hrec.congr fun w => ?_
      have hρ : Semantics.prepend (fun i => Xs' i w) tail =
          cons (w 0) (Semantics.prepend (fun i => Xs i (ftail w)) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs']
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      have hA_eq : List.ofFn (fun i => As' i w) =
          List.ofFn (fun i => As i (ftail w)) ++ [w 0] := by
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, As']
        by_cases hj : j < r
        · simp [hj, List.getElem_append_left]
        · have hjr : j = r := by omega
          subst hjr
          simp [List.getElem_append_right]
      have h_fn : (fun vs => app (Y' w) (tupW u (List.ofFn (fun i => As' i w) ++ vs))) =
          (fun vs => app (Y (ftail w)) (tupW u (List.ofFn (fun i => As i (ftail w)) ++ w 0 :: vs))) := by
        funext vs
        change app (Y (ftail w)) (tupW u (List.ofFn (fun i => As' i w) ++ vs)) = _
        rw [hA_eq, List.append_assoc, List.singleton_append]
      exact holeFam_congr_eq_np hρ h_fn
    have hGraph : ∀ env, HasGraph (interp V (Semantics.prepend (fun i => Xs i env) tail) F)
        (fun x => F_lam x env) := fun env =>
      holeFam_hasGraph (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)
    refine (DefFun.lamV_apply_curry (F := F_lam) (h := hGraph) hrec' hF).congr fun env => ?_
    exact (holeFam_cons (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)).symm

private theorem defFun_holeVal_np (D : LfpDatum V) (ψ : Name → Nat) (tail : Nat → V)
    {k len : Nat} (Xs : Fin len → (Fin k → V) → V) (hXs : ∀ i, DefFun k (Xs i))
    (Ym : (Fin k → V) → V) (hYm : DefFun k Ym) (m : Nat) :
    DefFun k fun env =>
      holeFam (Semantics.prepend (fun i => Xs i env) tail) (D.ids m ψ)
        (fun vs => app (Ym env) (tupW (D.u m ψ) vs))
        (DefHoleFn.of_app_tupW (Ym env) (D.u m ψ) (D.ids m ψ).length) := by
  have h0 := defFun_holeFam_app_ofFn_np (D.u m ψ) tail (D.ids m ψ) Xs hXs Ym hYm
    (Fin.elim0 : Fin 0 → (Fin k → V) → V) (fun i => Fin.elim0 i)
  refine h0.congr fun env => ?_
  refine holeFam_congr_eq_np rfl ?_
  funext vs
  rw [List.ofFn_zero, List.nil_append]

private theorem consList_map_prepend (as : List V) {len : Nat}
    (bs : Fin len → V) (tail : Nat → V) :
    consList as (Semantics.prepend bs tail) =
      Semantics.prepend (fun i : Fin (as.length + len) =>
        if hi : i.val < as.length then as[as.length - 1 - i.val]'(by omega)
        else bs ⟨i.val - as.length, by omega⟩) tail := by
  funext j
  by_cases hj : j < as.length
  · rw [consList_getD_of_lt _ _ _ hj]
    simp only [Semantics.prepend, dite_eq_left (by omega : j < as.length + len),
      dite_eq_left hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : as.length - 1 - j < as.length), Option.getD_some]
  · have hge : as.length ≤ j := Nat.le_of_not_lt hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + as.length := ⟨j - as.length, by omega⟩
    rw [consList_apply_add]
    by_cases hm : m < len
    · have hm' : m + as.length < as.length + len := by omega
      simp only [Semantics.prepend, dite_eq_left hm, dite_eq_left hm',
        dite_eq_right (by omega : ¬ m + as.length < as.length)]
      congr 1; apply Fin.ext; dsimp; omega
    · have hm' : ¬ (m + as.length < as.length + len) := by omega
      simp only [Semantics.prepend, dite_eq_right hm, dite_eq_right hm']
      congr 1; omega

private theorem defRel_spineFit_prepend_np {k : Nat} (tail : Nat → V) :
    ∀ (Fs : List Term) (fs : List V) {d : Nat} (Zs : Fin d → (Fin k → V) → V),
      (∀ i, DefFun k (Zs i)) →
      DefRel k fun env => SpineFit (Semantics.prepend (fun i => Zs i env) tail) Fs fs
  | [], [], _, _, _ => DefRel.true
  | [], _ :: _, _, _, _ => DefRel.false
  | _ :: _, [], _, _, _ => DefRel.false
  | F :: Fs, a :: fs, d, Zs, hZs => by
    let Zs' : Fin (d + 1) → (Fin k → V) → V := fun i env =>
      if h0 : i.val = 0 then a else Zs ⟨i.val - 1, by omega⟩ env
    have hZs' : ∀ i, DefFun k (Zs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Zs']; split
      · exact DefFun.const a
      · exact hZs _
    have hrest := defRel_spineFit_prepend_np tail Fs fs Zs' hZs'
    refine (DefRel.and
      (DefRel.mem_apply (DefFun.const a) ((interp_defFun_prepend tail d F).comp hZs))
      hrest).congr fun env => ?_
    refine and_congr_right fun _ => ?_
    have hp : Semantics.prepend (fun i => Zs' i env) tail =
        cons a (Semantics.prepend (fun i => Zs i env) tail) := by
      funext j
      cases j with
      | zero => simp [Semantics.prepend, Zs', cons]
      | succ j =>
        by_cases hj : j < d
        · simp [Semantics.prepend, Zs', hj, show j + 1 < d + 1 by omega, cons]
        · have hj1 : ¬ (j + 1 < d + 1) := by omega
          simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
          congr 1; omega
    rw [hp]

private theorem defRel_HFits_np (D : LfpDatum V) (ψ : Name → Nat) (tail : Nat → V)
    {k len : Nat} (hkN : D.k ≤ D.N)
    (Xs : Fin len → (Fin k → V) → V) (hXs : ∀ i, DefFun k (Xs i))
    (Ys : Fin D.N → (Fin k → V) → V) (hYs : ∀ m, DefFun k (Ys m))
    (t : V) (c j : Nat) (fs : List V) :
    DefRel k fun env =>
      D.HFits ψ (Semantics.prepend (fun i => Xs i env) tail)
        (padTuple fun m => Ys m env) t c j fs := by
  let HV : Fin D.k → (Fin k → V) → V := fun m env =>
    D.holeVal ψ (Semantics.prepend (fun i => Xs i env) tail) (padTuple fun q => Ys q env) m.val
  have hHV : ∀ m : Fin D.k, DefFun k (HV m) := fun ⟨m, hm⟩ => by
    have hmN : m < D.N := Nat.lt_of_lt_of_le hm hkN
    refine (defFun_holeVal_np D ψ tail Xs hXs (Ys ⟨m, hmN⟩) (hYs ⟨m, hmN⟩) m).congr fun env => ?_
    dsimp only [HV, LfpDatum.holeVal]
    refine holeFam_congr_eq_np rfl ?_
    funext vs
    rw [padTuple_lt _ hmN]
  let Zs : Fin (D.k + len) → (Fin k → V) → V := fun i env =>
    if hi : i.val < D.k then HV ⟨D.k - 1 - i.val, by omega⟩ env
    else Xs ⟨i.val - D.k, by omega⟩ env
  have hZs : ∀ i, DefFun k (Zs i) := fun ⟨i, hi⟩ => by
    dsimp only [Zs]; split
    · exact hHV _
    · exact hXs _
  have hfr_eq : ∀ env,
      D.frame ψ (Semantics.prepend (fun i => Xs i env) tail) (padTuple fun q => Ys q env) =
        Semantics.prepend (fun i => Zs i env) tail := fun env => by
    unfold LfpDatum.frame
    funext idx
    have hl : (List.map (D.holeVal ψ (Semantics.prepend (fun i => Xs i env) tail)
        (padTuple fun q => Ys q env)) (List.range D.k)).length = D.k := by simp
    by_cases hid : idx < D.k
    · rw [consList_getD_of_lt _ _ _ (by omega)]
      simp only [List.getD_eq_getElem?_getD, hl]
      rw [List.getElem?_eq_getElem (by rw [hl]; omega), Option.getD_some,
        List.getElem_map, List.getElem_range]
      simp only [Semantics.prepend, dite_eq_left (by omega : idx < D.k + len),
        Zs, dite_eq_left hid, HV]
    · obtain ⟨m, rfl⟩ : ∃ m, idx = m + D.k := ⟨idx - D.k, by omega⟩
      have hlhs : consList (List.map (D.holeVal ψ (Semantics.prepend (fun i => Xs i env) tail)
          (padTuple fun q => Ys q env)) (List.range D.k))
          (Semantics.prepend (fun i => Xs i env) tail) (m + D.k) =
          Semantics.prepend (fun i => Xs i env) tail m := by
        have h1 := consList_apply_add
          (List.map (D.holeVal ψ (Semantics.prepend (fun i => Xs i env) tail)
            (padTuple fun q => Ys q env)) (List.range D.k))
          (Semantics.prepend (fun i => Xs i env) tail) m
        rwa [hl] at h1
      rw [hlhs]
      by_cases hm : m < len
      · simp only [Semantics.prepend, dite_eq_left hm,
          dite_eq_left (by omega : m + D.k < D.k + len),
          Zs, dite_eq_right (by omega : ¬ m + D.k < D.k)]
        congr 1; apply Fin.ext; dsimp; omega
      · simp only [Semantics.prepend, dite_eq_right hm,
          dite_eq_right (by omega : ¬ m + D.k < D.k + len)]
        congr 1; omega
  let Ws : Fin (fs.length + (D.k + len)) → (Fin k → V) → V := fun i env =>
    if hi : i.val < fs.length then fs[fs.length - 1 - i.val]'(by omega)
    else Zs ⟨i.val - fs.length, by omega⟩ env
  have hWs : ∀ i, DefFun k (Ws i) := fun ⟨i, hi⟩ => by
    dsimp only [Ws]; split
    · exact DefFun.const _
    · exact hZs _
  have hcons_eq : ∀ env,
      consList fs (D.frame ψ (Semantics.prepend (fun i => Xs i env) tail)
          (padTuple fun q => Ys q env)) =
        Semantics.prepend (fun i => Ws i env) tail := fun env => by
    rw [hfr_eq env, consList_map_prepend]
  have hsp := defRel_spineFit_prepend_np tail (D.fields ψ c j) fs Zs hZs
  have hres : DefRel k fun env => ∀ l, l < (D.ids c ψ).length → ∃ e,
      (D.resIdx ψ c j)[l]? = some e ∧
        interp V (Semantics.prepend (fun i => Ws i env) tail) e = Tower.projS l t := by
    refine DefRel.finForall_lt fun l _ => ?_
    cases hopt : (D.resIdx ψ c j)[l]? with
    | none => exact DefRel.false.congr fun _ => ⟨False.elim, fun ⟨_, he, _⟩ => by cases he⟩
    | some e =>
      refine (DefRel.eq_apply ((interp_defFun_prepend tail _ e).comp hWs)
        (DefFun.const (Tower.projS l t))).congr fun env => ?_
      exact ⟨fun heq => ⟨e, rfl, heq⟩, fun ⟨_, he, heq⟩ => by cases he; exact heq⟩
  refine (DefRel.and (DefRel.constProp (j < D.nctors c)) (DefRel.and hsp hres)).congr fun env => ?_
  simp only [LfpDatum.HFits]
  rw [hcons_eq env, hfr_eq env]

/-- **A call target lands at node `b'`** from node `b`'s decoding
`(m, t, j, fs)`: at every admissible visit `(G, ρ)` of `b` and every hole
tuple `Y` the fields fit at, the target `y` (component `m'`, index `t'`)
is in `Y` (`b' = b`, the own group), satisfies `nenc b' m' t' y ∈ˢ G`
(an enclosing node), or lies in a deeper node's class at an admissible
frame of it, the caller's tuple added to `G` via `addOwn`. -/
@[expose] def NodeLands (nC : Nat) (Db : Nat → LfpDatum V) (ψb : Nat → Name → Nat)
    (frLen : Nat → Nat) (tailb : Nat → Nat → V) (frb : (b : Nat) → Fin (frLen b) → V)
    (dp : Nat → Nat)
    (Adm : (b : Nat) → V → (Fin (frLen b) → V) → Prop)
    (b m : Nat) (t : V) (j : Nat) (fs : List V) (b' m' : Nat) (t' y : V) : Prop :=
  ∀ (G : V) (ρ : Fin (frLen b) → V), Adm b G ρ → ∀ Y : Fin (Db b).N → V,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N
      ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) (padTuple Y) →
    (Db b).HFits (ψb b) (prepend ρ (tailb b)) (padTuple Y) t m j fs →
    (b' = b ∧ y ∈ˢ app (padTuple Y m') t') ∨ nenc b' m' t' y ∈ˢ G ∨
      (dp b < dp b' ∧ b' < nC ∧ ∃ ρ' : Fin (frLen b') → V,
        Adm b' (addOwn G b (Db b).N
          ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) (padTuple Y)) ρ' ∧
        y ∈ˢ app ((lfpSClause (Db b') (ψb b')
          ((Db b').idx (ψb b') (prepend (frb b') (tailb b')))
          (frLen b') (tailb b')).carrier ρ' m') t')

private theorem defFun_lfpSClause_carrier_np (D : LfpDatum V) (ψ : Name → Nat) (Is : Nat → V)
    (len : Nat) (tail : Nat → V) {m : Nat} (hm : m < D.N) :
    DefFun len fun ρ : Fin len → V => (lfpSClause D ψ Is len tail).carrier ρ m := by
  unfold SClause.carrier lfpSClause
  exact DefFun.lfpTuple_apply
    (fun c _ => DefFun.const (Is c))
    (fun ps => D.hΦ ψ (prepend ps tail))
    (fun m' hm' => D.hΦ_def ψ tail len m' hm')
    hm

private theorem defRel_nodeLands_np {nC : Nat} {Db : Nat → LfpDatum V} {ψb : Nat → Name → Nat}
    {frLen : Nat → Nat} {tailb : Nat → Nat → V} {frb : (b : Nat) → Fin (frLen b) → V}
    {dp : Nat → Nat} {Adm : (b : Nat) → V → (Fin (frLen b) → V) → Prop}
    (b m : Nat) (t : V) (j : Nat) (fs : List V) (b' m' : Nat)
    (hm' : m' < (Db b').N) (hk : (Db b).k ≤ (Db b).N)
    (hAdm_b : DefRel (frLen b + 1) fun v => Adm b (v 0) (ftail v))
    (hAdm_b' : DefRel (frLen b' + 1) fun v => Adm b' (v 0) (ftail v)) :
    DefRel 2 fun w =>
      NodeLands nC Db ψb frLen tailb frb dp Adm b m t j fs b' m' (w 0) (w 1) := by
  let Isb : Nat → V := (Db b).idx (ψb b) (prepend (frb b) (tailb b))
  let Isb' : Nat → V := (Db b').idx (ψb b') (prepend (frb b') (tailb b'))
  let M := (Db b).N + (frLen b + (1 + 2))
  have hG_p : DefFun (V := V) M fun v => v ⟨(Db b).N + frLen b, by omega⟩ :=
    DefFun.proj ⟨(Db b).N + frLen b, by omega⟩
  have ht'_p : DefFun (V := V) M fun v => v ⟨(Db b).N + frLen b + 1, by omega⟩ :=
    DefFun.proj ⟨(Db b).N + frLen b + 1, by omega⟩
  have hy_p : DefFun (V := V) M fun v => v ⟨(Db b).N + frLen b + 2, by omega⟩ :=
    DefFun.proj ⟨(Db b).N + frLen b + 2, by omega⟩
  let ρ_p : Fin (frLen b) → (Fin M → V) → V := fun i v => v ⟨(Db b).N + i.val, by omega⟩
  have hρ_p : ∀ i, DefFun (V := V) M (ρ_p i) := fun i => DefFun.proj ⟨(Db b).N + i.val, by omega⟩
  let Y_p : Fin (Db b).N → (Fin M → V) → V := fun q v => v ⟨q.val, by omega⟩
  have hY_p : ∀ q, DefFun (V := V) M (Y_p q) := fun q => DefFun.proj ⟨q.val, by omega⟩
  have hAdmB : DefRel M fun v => Adm b (v ⟨(Db b).N + frLen b, by omega⟩) (fun i => ρ_p i v) := by
    let Gs : Fin (frLen b + 1) → (Fin M → V) → V := fun j v =>
      if hj : j.val = 0 then v ⟨(Db b).N + frLen b, by omega⟩
      else ρ_p ⟨j.val - 1, by omega⟩ v
    have hGs : ∀ j, DefFun M (Gs j) := fun ⟨j, hj⟩ => by
      dsimp only [Gs]; split
      · exact hG_p
      · exact hρ_p _
    refine (hAdm_b.comp hGs).congr fun v => ?_
    have heq : (fun i : Fin (frLen b) => ftail (fun j => Gs j v) i) = fun i => ρ_p i v := by
      funext i; dsimp only [ftail, Gs]
      split
      · next h0 => exact absurd h0 (Nat.succ_ne_zero _)
      · rfl
    simp only [Gs, heq]; rfl
  have hInSp : DefRel M fun v => InTupleSpace ((Db b).w (ψb b)) (Db b).N Isb
      (padTuple fun q => Y_p q v) :=
    DefRel.finForall_lt fun q hq =>
      DefRel.mem_apply ((hY_p ⟨q, hq⟩).congr fun v => (padTuple_lt (fun q => Y_p q v) hq).symm)
        (DefFun.const (famSpace ((Db b).w (ψb b)) (Isb q)))
  have hHF : DefRel M fun v =>
      (Db b).HFits (ψb b) (prepend (fun i => ρ_p i v) (tailb b))
        (padTuple fun q => Y_p q v) t m j fs :=
    defRel_HFits_np (Db b) (ψb b) (tailb b) hk ρ_p hρ_p Y_p hY_p t m j fs
  have hOwn : DefRel M fun v => b' = b ∧
      v ⟨(Db b).N + frLen b + 2, by omega⟩ ∈ˢ app (padTuple (fun q => Y_p q v) m')
        (v ⟨(Db b).N + frLen b + 1, by omega⟩) := by
    by_cases hbb : b' = b
    · subst hbb
      have hm'_lt : m' < (Db b').N := hm'
      refine (DefRel.and (DefRel.constProp (b' = b'))
        (DefRel.mem_apply hy_p (DefFun.app_apply
          ((hY_p ⟨m', hm'_lt⟩).congr fun v => (padTuple_lt (fun q => Y_p q v) hm'_lt).symm)
          ht'_p))).congr fun _ => Iff.rfl
    · exact DefRel.false.congr fun _ => ⟨False.elim, fun h => hbb h.1⟩
  have hEnc : DefRel M fun v => nenc b' m' (v ⟨(Db b).N + frLen b + 1, by omega⟩)
      (v ⟨(Db b).N + frLen b + 2, by omega⟩) ∈ˢ v ⟨(Db b).N + frLen b, by omega⟩ :=
    DefRel.mem_apply (DefFun.nenc_apply b' m' ht'_p hy_p) hG_p
  let M' := frLen b' + M
  have hG_p' : DefFun M' fun u => fdrop u ⟨(Db b).N + frLen b, by omega⟩ := hG_p.fdrop_apply
  have hY_p' : ∀ q : Fin (Db b).N, DefFun M' fun u => Y_p q (fdrop u) :=
    fun q => (hY_p q).fdrop_apply
  have hAddOwn : DefFun M' fun u =>
      addOwn (fdrop u ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
        (padTuple fun q => Y_p q (fdrop u)) := by
    refine (DefFun.addOwn_apply b (Db b).N hG_p'
      (fun c _ => DefFun.const (Isb c))
      (fun c hc => (hY_p' ⟨c, hc⟩).congr fun u =>
        (padTuple_lt (fun q => Y_p q (fdrop u)) hc).symm)).congr fun u => ?_
    rfl
  have hAdmB' : DefRel M' fun u =>
      Adm b' (addOwn (fdrop u ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
        (padTuple fun q => Y_p q (fdrop u))) (ftake u) := by
    let Gs' : Fin (frLen b' + 1) → (Fin M' → V) → V := fun k u =>
      if hk0 : k.val = 0 then addOwn (fdrop u ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
        (padTuple fun q => Y_p q (fdrop u))
      else ftake u ⟨k.val - 1, by omega⟩
    have hGs' : ∀ k, DefFun M' (Gs' k) := fun ⟨k, hk0⟩ => by
      dsimp only [Gs']; split
      · exact hAddOwn
      · exact DefFun.ftake_proj _
    refine (hAdm_b'.comp hGs').congr fun u => ?_
    have heq : (fun i : Fin (frLen b') => ftail (fun k => Gs' k u) i) = ftake u := by
      funext i; dsimp only [ftail, Gs']
      split
      · next h0 => exact absurd h0 (Nat.succ_ne_zero _)
      · congr 1
    simp only [Gs', heq]; rfl
  have hCar : DefFun M' fun u =>
      (lfpSClause (Db b') (ψb b') Isb' (frLen b') (tailb b')).carrier (ftake u) m' :=
    (defFun_lfpSClause_carrier_np (Db b') (ψb b') Isb' (frLen b') (tailb b') hm').comp
      fun i => DefFun.ftake_proj i
  have hDeepBody : DefRel M' fun u =>
      Adm b' (addOwn (fdrop u ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
        (padTuple fun q => Y_p q (fdrop u))) (ftake u) ∧
      fdrop u ⟨(Db b).N + frLen b + 2, by omega⟩ ∈ˢ
        app ((lfpSClause (Db b') (ψb b') Isb' (frLen b') (tailb b')).carrier (ftake u) m')
          (fdrop u ⟨(Db b).N + frLen b + 1, by omega⟩) :=
    DefRel.and hAdmB' (DefRel.mem_apply hy_p.fdrop_apply (DefFun.app_apply hCar ht'_p.fdrop_apply))
  have hDeep : DefRel M fun v =>
      dp b < dp b' ∧ b' < nC ∧ ∃ ρ' : Fin (frLen b') → V,
        Adm b' (addOwn (v ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
          (padTuple fun q => Y_p q v)) ρ' ∧
        v ⟨(Db b).N + frLen b + 2, by omega⟩ ∈ˢ
          app ((lfpSClause (Db b') (ψb b') Isb' (frLen b') (tailb b')).carrier ρ' m')
            (v ⟨(Db b).N + frLen b + 1, by omega⟩) :=
    DefRel.and (DefRel.constProp (dp b < dp b'))
      (DefRel.and (DefRel.constProp (b' < nC))
        ((DefRel.exists_fin hDeepBody).congr fun v =>
          exists_congr fun ρ' => by
            have heq1 : ftake (fappend ρ' v) = ρ' := by
              funext i; exact fappend_lt ρ' v i.isLt
            have heq2 : fdrop (fappend ρ' v) = v := by
              funext i; dsimp only [fdrop]; rw [fappend_ge ρ' v (Nat.le_add_right _ _)]
              congr 1; apply Fin.ext; dsimp; omega
            rw [heq1, heq2]))
  have hCore : DefRel M fun v =>
      Adm b (v ⟨(Db b).N + frLen b, by omega⟩) (fun i => ρ_p i v) →
      InTupleSpace ((Db b).w (ψb b)) (Db b).N Isb (padTuple fun q => Y_p q v) →
      (Db b).HFits (ψb b) (prepend (fun i => ρ_p i v) (tailb b))
        (padTuple fun q => Y_p q v) t m j fs →
      (b' = b ∧ v ⟨(Db b).N + frLen b + 2, by omega⟩ ∈ˢ
        app (padTuple (fun q => Y_p q v) m') (v ⟨(Db b).N + frLen b + 1, by omega⟩)) ∨
      nenc b' m' (v ⟨(Db b).N + frLen b + 1, by omega⟩)
        (v ⟨(Db b).N + frLen b + 2, by omega⟩) ∈ˢ v ⟨(Db b).N + frLen b, by omega⟩ ∨
      (dp b < dp b' ∧ b' < nC ∧ ∃ ρ' : Fin (frLen b') → V,
        Adm b' (addOwn (v ⟨(Db b).N + frLen b, by omega⟩) b (Db b).N Isb
          (padTuple fun q => Y_p q v)) ρ' ∧
        v ⟨(Db b).N + frLen b + 2, by omega⟩ ∈ˢ
          app ((lfpSClause (Db b') (ψb b') Isb' (frLen b') (tailb b')).carrier ρ' m')
            (v ⟨(Db b).N + frLen b + 1, by omega⟩)) :=
    hAdmB.imp (hInSp.imp (hHF.imp (hOwn.or (hEnc.or hDeep))))
  have hForAll := DefRel.forall_ (DefRel.forall_fin (DefRel.forall_fin hCore))
  refine hForAll.congr fun w => ?_
  have hcoord : ∀ (G : V) (ρ : Fin (frLen b) → V) (Y : Fin (Db b).N → V),
      (∀ q : Fin (Db b).N, Y_p q (fappend Y (fappend ρ (fcons G w))) = Y q) ∧
      ((fun i : Fin (frLen b) => ρ_p i (fappend Y (fappend ρ (fcons G w)))) = ρ) ∧
      ((fappend Y (fappend ρ (fcons G w))) ⟨(Db b).N + frLen b, by omega⟩ = G) ∧
      ((fappend Y (fappend ρ (fcons G w))) ⟨(Db b).N + frLen b + 1, by omega⟩ = w 0) ∧
      ((fappend Y (fappend ρ (fcons G w))) ⟨(Db b).N + frLen b + 2, by omega⟩ = w 1) := by
    intro G ρ Y
    refine ⟨fun q => fappend_lt Y (fappend ρ (fcons G w)) q.isLt, ?_, ?_, ?_, ?_⟩
    · funext i; dsimp only [ρ_p]
      rw [fappend_ge Y (fappend ρ (fcons G w)) (by dsimp; omega)]
      rw [fappend_lt ρ (fcons G w) (by dsimp; omega)]
      congr 1; apply Fin.ext; dsimp; omega
    · rw [fappend_ge Y (fappend ρ (fcons G w)) (by dsimp; omega)]
      rw [fappend_ge ρ (fcons G w) (by dsimp; omega)]
      rw [show (⟨↑(⟨(Db b).N + frLen b - (Db b).N, by omega⟩ : Fin (frLen b + 3)) - frLen b,
          by omega⟩ : Fin 3) = 0 from Fin.ext (by dsimp; omega)]
      rfl
    · rw [fappend_ge Y (fappend ρ (fcons G w)) (by dsimp; omega)]
      rw [fappend_ge ρ (fcons G w) (by dsimp; omega)]
      rw [show (⟨↑(⟨(Db b).N + frLen b + 1 - (Db b).N, by omega⟩ : Fin (frLen b + 3)) - frLen b,
          by omega⟩ : Fin 3) = 1 from Fin.ext (by dsimp; omega)]
      rfl
    · rw [fappend_ge Y (fappend ρ (fcons G w)) (by dsimp; omega)]
      rw [fappend_ge ρ (fcons G w) (by dsimp; omega)]
      rw [show (⟨↑(⟨(Db b).N + frLen b + 2 - (Db b).N, by omega⟩ : Fin (frLen b + 3)) - frLen b,
          by omega⟩ : Fin 3) = 2 from Fin.ext (by dsimp; omega)]
      rfl
  constructor
  · intro h G ρ hA Y hIn hFit
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hcoord G ρ Y
    have hY0 := h G ρ Y
    simp only [hp1, hp2, hp3, hp4, hp5] at hY0
    exact hY0 hA hIn hFit
  · intro h G ρ Y hA hIn hFit
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hcoord G ρ Y
    simp only [hp1, hp2, hp3, hp4, hp5] at hA hIn hFit ⊢
    exact h G ρ hA Y hIn hFit

section Pres

variable (envC : Env)
  (acval : Name → (Name → Nat) → Term) (p : BlockShape)
  (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
  (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
  (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
  (call : List V → Nat → Nat → List V → V → Prop)

/-- **A presentation of the recursor classes' nodes** at the prefix spine
`xs` (see the module docstring). -/
structure TgtNodePres where
  nC : Nat
  Db : Nat → LfpDatum V
  ψb : Nat → Name → Nat
  frLen : Nat → Nat
  tailb : Nat → Nat → V
  frb : (b : Nat) → Fin (frLen b) → V
  /-- the live nodes: their index sets are their clause's at the true frame
  (`pinIdx`), the others' empty -/
  live : Nat → Prop
  dp : Nat → Nat
  Dd : Nat
  hD : ∀ b, b < nC → dp b < Dd
  Adm : (b : Nat) → V → (Fin (frLen b) → V) → Prop
  hAdm_def : ∀ b, b < nC → DefRel (frLen b + 1) fun v => Adm b (v 0) (ftail v)
  hcl : ∀ b, b < nC → LfpClause acval (Db b)
  hAdm : ∀ b, b < nC → ∀ (G : V) (ρ : Fin (frLen b) → V), Adm b G ρ → live b ∧
    Sat V ((Db b).params (ψb b)).reverse (prepend ρ (tailb b)) ∧
      ∀ c, c < (Db b).N → (Db b).idx (ψb b) (prepend ρ (tailb b)) c =
        (Db b).idx (ψb b) (prepend (frb b) (tailb b)) c
  top : ∀ b, b < nC → live b → ∀ G : V,
    (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
      live b' → t ∈ˢ (Db b').idx (ψb b') (prepend (frb b') (tailb b')) c →
      y ∈ˢ app ((Db b').carrier (ψb b') (prepend (frb b') (tailb b')) c) t →
      nenc b' c t y ∈ˢ G) →
    Adm b G (frb b)
  /-- **the tie to the true frame** (positivity at the instantiation):
  at an admissible frame whose hypotheses hold of true elements, a spine
  fitting at holes below the true carrier fits at the true frame -/
  trans : ∀ b, b < nC → ∀ G : V,
    (∀ b' c t y, nenc b' c t y ∈ˢ G →
      y ∈ˢ app ((lfpSClause (Db b') (ψb b')
        (pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b'))
        (frLen b') (tailb b')).carrier (frb b') c) t) →
    ∀ ρ : Fin (frLen b) → V, Adm b G ρ → ∀ Y,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y →
    TupleLe (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y
      ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) →
    ∀ t c j fs, c < (Db b).N → (Db b).HFits (ψb b) (prepend ρ (tailb b)) Y t c j fs →
      (Db b).HFits (ψb b) (prepend (frb b) (tailb b))
        ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) t c j fs
  /-- the class → node relation -/
  Rel : Nat → Nat → Prop
  mOf : Nat → Nat → Nat
  hb : ∀ c b, c < (tgtRs out).length → Rel c b → b < nC
  hm : ∀ c b, c < (tgtRs out).length → Rel c b → mOf c b < (Db b).N
  /-- the class tie: at a related pair the class's data are the node's -/
  hDb : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsD d Dc out c = Db b
  hψb : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsψ cvc out ψ c = ψb b
  hfr : ∀ c b, c < (tgtRs out).length → Rel c b →
    tgtClsFr d acval envC p out ψ ρ xs c = prepend (frb b) (tailb b)
  hmc : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsM mc p out c = mOf c b
  hG : ∀ c b, c < (tgtRs out).length → Rel c b →
    tgtClsG d acval envC p out ψ ρ xs c ∧ tgtClsLive d Dc cvc acval envC p out ψ ρ xs c
  hlive : ∀ c b, c < (tgtRs out).length → Rel c b → live b
  hnCt : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    (Db b).HFits (ψb b) (prepend (frb b) (tailb b))
      ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) t (mOf c b) j fs →
      j < blockRecNCt (tgtRs out) c
  /-- **the calls**: at a related pair and a true decoding, every call
  target that is a major lands at a node related to its class -/
  hcall : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    t ∈ˢ (Db b).idx (ψb b) (prepend (frb b) (tailb b)) (mOf c b) →
    (Db b).HFits (ψb b) (prepend (frb b) (tailb b))
      ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) t (mOf c b) j fs →
    ∀ c' t' y, c' < (tgtRs out).length →
      t' ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c' →
      y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c') t' →
      call xs c j fs (tagged c' t' y) →
      ∃ b', Rel c' b' ∧
        NodeLands nC Db ψb frLen tailb frb dp Adm b (mOf c b) t j fs b' (mOf c' b') t' y

end Pres

section Build

variable {envC : Env}
  {acval : Name → (Name → Nat) → Term} {p : BlockShape}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
  {call : List V → Nat → Nat → List V → V → Prop}

namespace TgtNodePres

variable (P : TgtNodePres envC acval p out d Dc mc cvc ψ ρ xs call)

/-- The presentation's clause at node `b`. -/
@[expose] noncomputable def cl (b : Nat) : SClause V (P.frLen b) :=
  lfpSClause (P.Db b) (P.ψb b)
    (pinIdx (P.Db b) (P.ψb b) (prepend (P.frb b) (P.tailb b)) (P.live b))
    (P.frLen b) (P.tailb b)

theorem cl_carrier {b : Nat} (hl : P.live b) :
    (P.cl b).carrier (P.frb b) =
      (P.Db b).carrier (P.ψb b) (prepend (P.frb b) (P.tailb b)) := by
  unfold cl; rw [pinIdx_of hl]; exact lfpSClause_carrier rfl

/-- The class tie, read at the class data. -/
theorem cls_eq {c b : Nat} (hc : c < (tgtRs out).length) (hR : P.Rel c b) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c
        = (P.Db b).idx (P.ψb b) (prepend (P.frb b) (P.tailb b)) (P.mOf c b) ∧
      tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c
        = (P.Db b).carrier (P.ψb b) (prepend (P.frb b) (P.tailb b)) (P.mOf c b) ∧
      tgtClsInj d Dc mc cvc p out ψ c = (P.Db b).inj (P.ψb b) (P.mOf c b) ∧
      (∀ t j fs, tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs c t j fs ↔
        (P.Db b).HFits (P.ψb b) (prepend (P.frb b) (P.tailb b))
          ((P.Db b).carrier (P.ψb b) (prepend (P.frb b) (P.tailb b))) t
          (P.mOf c b) j fs) := by
  classical
  have hD := P.hDb c b hc hR
  have hψ := P.hψb c b hc hR
  have hf := P.hfr c b hc hR
  have hm := P.hmc c b hc hR
  have hg := P.hG c b hc hR
  refine ⟨?_, ?_, ?_, fun t j fs => ?_⟩
  · rw [tgtClsIs_of hg.1 hg.2, hD, hψ, hf, hm]
  · simp only [tgtClsCr, hD, hψ, hf, hm]
  · simp only [tgtClsInj, hD, hψ, hm]
  · simp only [tgtClsFit, hD, hψ, hf, hm]

/-- A preliminary kit (no predecessors): its majors `U` depend only on
the nodes. -/
@[expose] noncomputable def kit0 : NestKit V :=
  lfpNestKit (acval := acval) P.nC P.Db P.ψb P.frLen P.tailb P.frb P.live P.dp P.Dd P.hD P.Adm
    (fun _ => empty) P.hcl P.hAdm P.trans
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ u hu => absurd hu (not_mem_empty u)) P.top

theorem hasSep_pred
    (hSep : ∀ c j fs, HasSep (unionSet (tgtRs out).length
      (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs)) (call xs c j fs))
    (e : NDec V) :
    HasSep P.kit0.U fun u => ∃ c, c < (tgtRs out).length ∧ P.Rel c e.cls ∧ P.mOf c e.cls = e.c ∧
      e.t ∈ˢ (P.Db e.cls).idx (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)) e.c ∧
      (P.Db e.cls).HFits (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls))
        ((P.Db e.cls).carrier (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)))
        e.t e.c e.j e.fs ∧
      ∃ c' t' y b', c' < (tgtRs out).length ∧ P.Rel c' b' ∧
        t' ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c' ∧
        y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c') t' ∧
        call xs c e.j e.fs (tagged c' t' y) ∧
        NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
          e.cls e.c e.t e.j e.fs b' (P.mOf c' b') t' y ∧
        u = nenc b' (P.mOf c' b') t' y := by
  classical
  by_cases he : e.cls < P.nC
  · let IsX := tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs
    let CrX := tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs
    let Ucls := unionSet (tgtRs out).length IsX CrX
    let Side (c c' b' : Nat) : Prop :=
      P.Rel c e.cls ∧ P.mOf c e.cls = e.c ∧
      e.t ∈ˢ (P.Db e.cls).idx (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)) e.c ∧
      (P.Db e.cls).HFits (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls))
        ((P.Db e.cls).carrier (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)))
        e.t e.c e.j e.fs ∧
      P.Rel c' b'
    let Q' : V → Prop := fun u => ∃ c, c < (tgtRs out).length ∧
      ∃ c', c' < (tgtRs out).length ∧ ∃ b', b' < P.nC ∧
        Side c c' b' ∧
        ∃ t', t' ∈ˢ IsX c' ∧
          ∃ y, y ∈ˢ app (CrX c') t' ∧
            call xs c e.j e.fs (tagged c' t' y) ∧
            NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
              e.cls e.c e.t e.j e.fs b' (P.mOf c' b') t' y ∧
            u = nenc b' (P.mOf c' b') t' y
    have hQ'def : DefPred Q' := by
      refine DefRel.finExists_lt fun c _ => DefRel.finExists_lt fun c' hc' =>
        DefRel.finExists_lt fun b' hb' => ?_
      by_cases hs : Side c c' b'
      · let Cset : V := sep Ucls (call xs c e.j e.fs) (hSep c e.j e.fs)
        have hm' : P.mOf c' b' < (P.Db b').N := P.hm c' b' hc' hs.2.2.2.2
        have hNL : DefRel 2 fun w =>
            NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
              e.cls e.c e.t e.j e.fs b' (P.mOf c' b') (w 0) (w 1) :=
          defRel_nodeLands_np e.cls e.c e.t e.j e.fs b' (P.mOf c' b')
            hm' (P.hcl e.cls he).kN (P.hAdm_def e.cls he) (P.hAdm_def b' hb')
        have hNL3 : DefRel 3 fun w =>
            NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
              e.cls e.c e.t e.j e.fs b' (P.mOf c' b') (w 1) (w 0) :=
          hNL.reIndex fun i => if i.val = 0 then 1 else 0
        have hBody : DefRel 3 fun w =>
            tagged c' (w 1) (w 0) ∈ˢ Cset ∧
            NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
              e.cls e.c e.t e.j e.fs b' (P.mOf c' b') (w 1) (w 0) ∧
            w 2 = nenc b' (P.mOf c' b') (w 1) (w 0) :=
          DefRel.and
            (DefRel.mem_apply (DefFun.tagged_apply c' (DefFun.proj 1) (DefFun.proj 0))
              (DefFun.const Cset))
            (DefRel.and hNL3
              (DefRel.eq_apply (DefFun.proj 2)
                (DefFun.nenc_apply b' (P.mOf c' b') (DefFun.proj 1) (DefFun.proj 0))))
        have hExY : DefRel 2 fun v =>
            ∃ y, y ∈ˢ app (CrX c') (v 0) ∧
              tagged c' (v 0) y ∈ˢ Cset ∧
              NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
                e.cls e.c e.t e.j e.fs b' (P.mOf c' b') (v 0) y ∧
              v 1 = nenc b' (P.mOf c' b') (v 0) y :=
          DefRel.bExists_curry
            (DefFun.app_apply (DefFun.const (CrX c')) (DefFun.proj 0)) hBody
        have hExT : DefRel 1 fun v =>
            ∃ t', t' ∈ˢ IsX c' ∧
              ∃ y, y ∈ˢ app (CrX c') t' ∧
                tagged c' t' y ∈ˢ Cset ∧
                NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
                  e.cls e.c e.t e.j e.fs b' (P.mOf c' b') t' y ∧
                v 0 = nenc b' (P.mOf c' b') t' y :=
          DefRel.bExists_curry (DefFun.const (IsX c')) hExY
        refine (DefRel.and (DefRel.constProp (Side c c' b')) hExT).congr fun v => ?_
        refine and_congr_right fun _ => exists_congr fun t' => and_congr_right fun ht' =>
          exists_congr fun y => and_congr_right fun hy => and_congr_left fun _ => ?_
        have hmemU : tagged c' t' y ∈ˢ Ucls := tagged_mem_unionSet hc' ht' hy
        dsimp only [Cset]
        rw [mem_sep]
        exact ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨hmemU, hc⟩⟩
      · exact DefRel.false.congr fun _ => ⟨False.elim, fun ⟨hs', _⟩ => hs hs'⟩
    refine (hasSep_of_defPred hQ'def).congr fun u _ => ?_
    constructor
    · rintro ⟨c, hc, c', hc', b', -, hs, t', ht', y, hy, hcl, hL, rfl⟩
      exact ⟨c, hc, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, c', t', y, b', hc', hs.2.2.2.2,
        ht', hy, hcl, hL, rfl⟩
    · rintro ⟨c, hc, hR, hm, ht, hHF, c', t', y, b', hc', hR', ht', hy, hcl, hL, rfl⟩
      exact ⟨c, hc, c', hc', b', P.hb c' b' hc' hR', ⟨hR, hm, ht, hHF, hR'⟩,
        t', ht', y, hy, hcl, hL, rfl⟩
  · refine (hasSep_of_defPred (p := fun _ => False) (DefRel.false (V := V))).congr fun u _ => ?_
    exact ⟨False.elim, fun ⟨c, hc, hR, _⟩ => he (P.hb c e.cls hc hR)⟩

/-- **The predecessors of a node decoding**: the call targets of the
related classes' true decodings, each at its callee node. -/
@[expose] noncomputable def pred
    (hSep : ∀ c j fs, HasSep (unionSet (tgtRs out).length
      (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs)) (call xs c j fs))
    (e : NDec V) : V :=
  sep P.kit0.U (fun u => ∃ c, c < (tgtRs out).length ∧ P.Rel c e.cls ∧ P.mOf c e.cls = e.c ∧
    e.t ∈ˢ (P.Db e.cls).idx (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)) e.c ∧
    (P.Db e.cls).HFits (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls))
      ((P.Db e.cls).carrier (P.ψb e.cls) (prepend (P.frb e.cls) (P.tailb e.cls)))
      e.t e.c e.j e.fs ∧
    ∃ c' t' y b', c' < (tgtRs out).length ∧ P.Rel c' b' ∧
      t' ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c' ∧
      y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c') t' ∧
      call xs c e.j e.fs (tagged c' t' y) ∧
      NodeLands P.nC P.Db P.ψb P.frLen P.tailb P.frb P.dp P.Adm
        e.cls e.c e.t e.j e.fs b' (P.mOf c' b') t' y ∧
      u = nenc b' (P.mOf c' b') t' y)
    (P.hasSep_pred hSep e)

/-- **The node kit**, its predecessors `pred`. -/
@[expose] noncomputable def kit
    (hSep : ∀ c j fs, HasSep (unionSet (tgtRs out).length
      (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs)) (call xs c j fs)) :
    NestKit V :=
  lfpNestKit (acval := acval) P.nC P.Db P.ψb P.frLen P.tailb P.frb P.live P.dp P.Dd P.hD P.Adm
    (P.pred hSep) P.hcl P.hAdm
    P.trans (fun b hb G ρ' hρ Y hY c t j fs _ _ hf u hu => by
      obtain ⟨-, c0, -, -, hm0, -, -, c', t', y, b', hc', hR', ht', hy', -, hL, rfl⟩ :=
        mem_sep.mp hu
      have hb' := P.hb c' b' hc' hR'
      have hm' := P.hm c' b' hc' hR'
      obtain ⟨hIs', -⟩ := P.cls_eq hc' hR'
      refine ⟨b', P.mOf c' b', t', y, hb', hm', P.hlive c' b' hc' hR',
        by rw [← hIs']; exact ht', rfl, ?_⟩
      let Y' : Fin (P.Db b).N → V := fun i => Y i.val
      have hkN := (P.hcl b hb).kN
      have hY' : InTupleSpace ((P.Db b).w (P.ψb b)) (P.Db b).N
          ((P.Db b).idx (P.ψb b) (prepend (P.frb b) (P.tailb b))) (padTuple Y') :=
        fun q hq => by rw [padTuple_lt Y' hq]; exact hY q hq
      have hf' : (P.Db b).HFits (P.ψb b) (prepend ρ' (P.tailb b)) (padTuple Y') t c j fs :=
        (hfits_congr_members (fun m hm => padTuple_lt Y' (Nat.lt_of_lt_of_le hm hkN)) t c j fs).mpr
          hf
      rcases hL G ρ' hρ Y' hY' hf' with ⟨rfl, hyY⟩ | hG | ⟨hlt, -, ρ'', hρ'', hyc⟩
      · exact Or.inl ⟨rfl, by rwa [padTuple_lt Y' hm'] at hyY⟩
      · exact Or.inr (Or.inl hG)
      · refine Or.inr (Or.inr ⟨hlt, ρ'', ?_, hyc⟩)
        rwa [← addOwn_padTuple_eq Y])
    P.top

end TgtNodePres

/-- **The empty presentation**: no node, no related class (for a prefix
spine at which no class is guarded). -/
@[expose] def TgtNodePres.empty :
    TgtNodePres envC acval p out d Dc mc cvc ψ ρ xs call where
  nC := 0
  Db := Dc
  ψb := fun _ => ψ
  frLen := fun _ => 0
  tailb := fun _ => ρ
  frb := fun _ => Fin.elim0
  live := fun _ => False
  dp := fun _ => 0
  Dd := 0
  hD := fun _ h => absurd h (Nat.not_lt_zero _)
  Adm := fun _ _ _ => False
  hAdm_def := fun _ h => absurd h (Nat.not_lt_zero _)
  hcl := fun _ h => absurd h (Nat.not_lt_zero _)
  hAdm := fun _ h => absurd h (Nat.not_lt_zero _)
  top := fun _ h => absurd h (Nat.not_lt_zero _)
  trans := fun _ h => absurd h (Nat.not_lt_zero _)
  Rel := fun _ _ => False
  mOf := fun _ _ => 0
  hb := fun _ _ _ h => h.elim
  hm := fun _ _ _ h => h.elim
  hDb := fun _ _ _ h => h.elim
  hψb := fun _ _ _ h => h.elim
  hfr := fun _ _ _ h => h.elim
  hmc := fun _ _ _ h => h.elim
  hG := fun _ _ _ h => h.elim
  hlive := fun _ _ _ h => h.elim
  hnCt := fun _ _ _ h => h.elim
  hcall := fun _ _ _ h => h.elim

/-- **An unguarded or dead class has no major.** -/
theorem tgtClsIs_unguarded {c : Nat}
    (hg : ¬ (tgtClsG d acval envC p out ψ ρ xs c ∧ tgtClsLive d Dc cvc acval envC p out ψ ρ xs c)) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c = empty := by
  classical
  simp only [tgtClsIs, ite_eq_right hg]

/-- **`TgtClassInd` from node presentations** whose relation covers every
GUARDED class at its prefix spine. -/
theorem tgtClassInd_of_pres {call : List V → Nat → Nat → List V → V → Prop}
    (hP : ∀ xs : List V, ∃ P : TgtNodePres envC acval p out d Dc mc cvc ψ ρ xs call,
      ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c →
        tgtClsLive d Dc cvc acval envC p out ψ ρ xs c → ∃ b, P.Rel c b) :
    TgtClassIndG envC acval p out d Dc mc cvc ψ ρ call := by
  classical
  intro xs hSep Q hSepQ hstep u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  by_cases hg : tgtClsG d acval envC p out ψ ρ xs c ∧ tgtClsLive d Dc cvc acval envC p out ψ ρ xs c
  · obtain ⟨P, hex⟩ := hP xs
    exact (P.kit hSep).toNodeInd.ind_recNodesOn (tgtRs out).length
      (fun c => tgtClsG d acval envC p out ψ ρ xs c ∧ tgtClsLive d Dc cvc acval envC p out ψ ρ xs c)
      P.Rel P.mOf
      (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
      (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
      (fun e => graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length call xs e
        (hSep e.1 e.2.1 e.2.2))
      (fun c hc hg => hex c hc hg.1 hg.2) P.hb P.hm
      (fun c b hc hR => by
        rw [(P.cls_eq hc hR).1]
        show _ = pinIdx (P.Db b) (P.ψb b) (prepend (P.frb b) (P.tailb b)) (P.live b) (P.mOf c b)
        rw [pinIdx_of (P.hlive c b hc hR)])
      (fun c b hc hR => by
        rw [(P.cls_eq hc hR).2.1]
        exact (P.cl_carrier (P.hlive c b hc hR)).symm ▸ rfl)
      (fun c b hc hR j fs => by rw [(P.cls_eq hc hR).2.2.1]; rfl)
      (fun c b hc hR t j fs hf => P.hnCt c b hc hR t j fs (by
        have := hf
        change (P.Db b).HFits (P.ψb b) (prepend (P.frb b) (P.tailb b))
          ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs at this
        rwa [P.cl_carrier (P.hlive c b hc hR)] at this))
      (fun c b hc hR t j fs hf => ((P.cls_eq hc hR).2.2.2 t j fs).mpr (by
        have := hf
        change (P.Db b).HFits (P.ψb b) (prepend (P.frb b) (P.tailb b))
          ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs at this
        rwa [P.cl_carrier (P.hlive c b hc hR)] at this))
      (fun c b hc hR t j fs ht hf v hv => by
        obtain ⟨hvU, hcall⟩ := mem_graphPredG.mp hv
        obtain ⟨c', hc', t', ht', y, hy, rfl⟩ := mem_unionSet.mp hvU
        have hf' : (P.Db b).HFits (P.ψb b) (prepend (P.frb b) (P.tailb b))
            ((P.Db b).carrier (P.ψb b) (prepend (P.frb b) (P.tailb b))) t (P.mOf c b) j fs := by
          have := hf
          change (P.Db b).HFits (P.ψb b) (prepend (P.frb b) (P.tailb b))
            ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs at this
          rwa [P.cl_carrier (P.hlive c b hc hR)] at this
        have ht0 : t ∈ˢ (P.Db b).idx (P.ψb b) (prepend (P.frb b) (P.tailb b)) (P.mOf c b) := by
          have := ht
          change t ∈ˢ pinIdx (P.Db b) (P.ψb b) (prepend (P.frb b) (P.tailb b))
            (P.live b) (P.mOf c b) at this
          rwa [pinIdx_of (P.hlive c b hc hR)] at this
        obtain ⟨b', hR', hL⟩ := P.hcall c b hc hR t j fs ht0 hf' c' t' y hc' ht' hy hcall
        refine ⟨c', t', y, hc', rfl, b', hR', mem_sep.mpr ⟨?_, c, hc, hR, rfl, ht0, hf',
          c', t', y, b', hc', hR', ht', hy, hcall, hL, rfl⟩⟩
        obtain ⟨hIs', hCr', -⟩ := P.cls_eq hc' hR'
        refine P.kit0.nenc_mem_U (P.hb c' b' hc' hR') (P.hm c' b' hc' hR') ?_ ?_
        · show t' ∈ˢ pinIdx (P.Db b') (P.ψb b') (prepend (P.frb b') (P.tailb b'))
            (P.live b') (P.mOf c' b')
          rw [pinIdx_of (P.hlive c' b' hc' hR'), ← hIs']; exact ht'
        · show y ∈ˢ app ((P.cl b').carrier (P.frb b') (P.mOf c' b')) t'
          rw [P.cl_carrier (P.hlive c' b' hc' hR'), ← hCr']; exact hy)
      Q hSepQ hstep c hc hg t ht x hx
  · rw [tgtClsIs_unguarded hg] at ht
    exact absurd ht (not_mem_empty t)

end Build

/-! ## The tie -/

/-- **THE TIE** (`hex`): every GUARDED recursor class at the
prefix spine `xs` — outside majors included — is related to a node of
the presentation. -/
@[expose] def TgtNodeHex {envC : Env}
    {acval : Name → (Name → Nat) → Term} {p : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    {call : List V → Nat → Nat → List V → V → Prop}
    (P : TgtNodePres envC acval p out d Dc mc cvc ψ ρ xs call) : Prop :=
  ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c →
    tgtClsLive d Dc cvc acval envC p out ψ ρ xs c → ∃ b, P.Rel c b

end ConLeche.Model
