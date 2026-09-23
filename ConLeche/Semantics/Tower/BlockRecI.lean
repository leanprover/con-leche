module

public import ConLeche.Semantics.Tower.SigChainI
import ConLeche.Semantics.Tower.FixFamI
import ConLeche.Semantics.Tower.TowerMk
import ConLeche.Semantics.Kit
@[expose] public section

/-!
# The recursor family of a k-member block: the leaf and its ι laws (task #315)

The uniform route's recursor stage CHECKS the stream's recursors
(`ConLeche/Kernel/Inductives/BlockRec.lean`) instead of
generating them.  What the model owes in exchange is a VALUE for each
of the `K` recursors of the block that satisfies exactly the equations
the check certified — one chosen tuple, pinned by its ι equations
(DESIGN "DESIGN DOCUMENT 2, v2" §3.2, the leaf):

    blockRecAV c  :=  projAV c (fst (choice.{s} (Σ' rs : ⟨RecTy_0, …, RecTy_{K-1}⟩, IotaAll rs) prf))

with `RecTy_c` the READING of the stream's recursor type of class `c`
(a `mkPisAV` over its binder data: the parameters, the arbitrary
`nP…rP-1` stretch, the indices and the major, then the conclusion) and

    IotaAll rs  =  ⋀_{c,j} ∀ x⃗ f⃗, eqE (app^ (projAV c rs) [x⃗, e⃗_j, C_j p⃗ f⃗]) (Rb_{c,j}[rec ↦ rs])

the conjunction over every class `c` and constructor `j` of the rule's
equation at the rule's own prefix `x⃗` (`rP` binders, read off the
recursor's record) and the constructor's fields `f⃗`.

**Where the recursor occurrences went.**  The stored right-hand side's
recursor occurrences are the GUARDED SPINES `rec_{c'} x⃗ e⃗(a⃗) (f_i a⃗)`
the check abstracted to `ih` openers (`abstractIh`,
`ConLeche/Verify/Inductives/BlockRecInv.lean`), so the substitution
`[rec ↦ rs]` is performed AT THE SPINE LEVEL, once per ih opener:
`Rb = Rb''[ih_i ↦ ihFun_i]` with `Rb''` the RESIDUE — recursor-free by
construction, which is why the residue may be typed at the
CONSTRUCTORS' environment (G1).  `instsAV` below is that substitution,
and `interp_instsAV` is the substitution lemma: reading the
substituted body at a frame is reading the residue at the frame
extended by the ih VALUES.  Nothing here has to descend through the
right-hand side's syntax — the check already did.

**What is input and what is generated.**  Everything the equation
mentions is INPUT data, read at the CHAIN frame (under the `K` Σ'
binders, where class `c`'s component is `bvar (K-1-c)`): the rule's
prefix domains `pdoms`, the constructor's field domains `fdoms`, its
index expressions `es`, the constructed major `mk`, the ih terms `ihs`
and the residue `Rb`.  The Model tier supplies them as the readings of
the stored forms, lifted by `K`; the ih terms' canonical shape (the
curried λ-tower over the field's telescope of the guarded call) is
`ihFunAV`.

The chain kit itself — `sigChainAV`/`selChainAV`/`projChainAV`,
`andChainAV`, `ChainOk`, `blockRecAVI_facts` — is
`ConLeche/Semantics/Tower/SigChainI.lean`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Frame kit -/

theorem consList_getD_of_lt : ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
    consList as σ k = as.getD (as.length - 1 - k) pt
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with hlt | hge
    · rw [consList_getD_of_lt as (cons a σ) k hlt, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega, List.getD_cons_succ]
    · have hk' : k = as.length := by simp at hk; omega
      subst hk'
      rw [← Nat.zero_add as.length, consList_apply_add, cons_zero, List.length_cons,
        show as.length + 1 - 1 - (0 + as.length) = 0 from by omega, List.getD_cons_zero]

/-! ## Substituting a block of innermost binders

`instsAV d vs e` replaces the `vs.length` innermost binders of `e` by
`vs` — `vs[0]` the OUTERMOST of the replaced block, every `v` written
at the frame BELOW the block (so `vs[t]` is lifted past the `t`
binders still standing when its turn comes).  This is the ih
substitution `[ih_i ↦ ihFun_i]` of the design. -/

def instsAV : Nat → List AnnotTerm → AnnotTerm → AnnotTerm
  | _, [], e => e
  | d, v :: vs, e => (instsAV (d + 1) vs e).inst (v.liftN d 0)

omit [SetTheory V] in
@[simp] theorem instsAV_nil (d : Nat) (e : AnnotTerm) : instsAV d [] e = e := rfl

theorem interp_instsAV_go : ∀ (vs : List AnnotTerm) (pre : List V) (e : AnnotTerm) (ρ : Nat → V),
    interp V (consList pre ρ) (instsAV pre.length vs e)
      = interp V (consList (pre ++ vs.map (interp V ρ)) ρ) e
  | [], pre, e, ρ => by simp
  | v :: vs, pre, e, ρ => by
    show interp V (consList pre ρ)
      ((instsAV (pre.length + 1) vs e).inst ((v.liftN pre.length 0))) = _
    rw [interp_inst0, interp_liftN_consList, consList_snoc']
    have h := interp_instsAV_go vs (pre ++ [interp V ρ v]) e ρ
    rw [List.length_append, List.length_singleton] at h
    rw [h]
    simp

/-- **THE SUBSTITUTION LEMMA** (spine-structural): the
body with the ih openers substituted, read at a frame, is the RESIDUE
read at that frame extended by the ih VALUES.  The recursion through
the right-hand side's syntax is the check's (`abstractIh`), not the
model's. -/
theorem interp_instsAV (vs : List AnnotTerm) (e : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (instsAV 0 vs e) = interp V (consList (vs.map (interp V ρ)) ρ) e := by
  have h := interp_instsAV_go (V := V) vs [] e ρ
  simpa using h

theorem wd_instsAV_go : ∀ (vs : List AnnotTerm) (pre : List V) (e : AnnotTerm) (ρ : Nat → V),
    (∀ v ∈ vs, WellDenoted V ρ v) →
    (WellDenoted V (consList pre ρ) (instsAV pre.length vs e)
      ↔ WellDenoted V (consList (pre ++ vs.map (interp V ρ)) ρ) e)
  | [], pre, e, ρ, _ => by simp
  | v :: vs, pre, e, ρ, hv => by
    show WellDenoted V (consList pre ρ)
      ((instsAV (pre.length + 1) vs e).inst ((v.liftN pre.length 0))) ↔ _
    rw [WellDenoted_inst0 V ((wd_liftN_consList v pre ρ).mpr (hv v (.head _))),
      interp_liftN_consList, consList_snoc']
    have h := wd_instsAV_go vs (pre ++ [interp V ρ v]) e ρ fun v' hv' => hv v' (.tail _ hv')
    rw [List.length_append, List.length_singleton] at h
    rw [h]
    simp

theorem wd_instsAV {vs : List AnnotTerm} {e : AnnotTerm} {ρ : Nat → V}
    (hv : ∀ v ∈ vs, WellDenoted V ρ v) :
    WellDenoted V ρ (instsAV 0 vs e) ↔ WellDenoted V (consList (vs.map (interp V ρ)) ρ) e := by
  have h := wd_instsAV_go (V := V) vs [] e ρ hv
  simpa using h

theorem foldl_app_map (f : AnnotTerm → V) (b : V) :
    ∀ as : List AnnotTerm,
      as.foldl (fun r a => SetTheory.app r (f a)) b = (as.map f).foldl SetTheory.app b
  | [] => rfl
  | a :: as => by
    show (as.foldl (fun r a => SetTheory.app r (f a)) (SetTheory.app b (f a))) = _
    rw [foldl_app_map f _ as]
    rfl

/-! ## The rule's own prefix variables

A rule binds `rP + nF` λs: the recursor's own prefix (the parameters
and the arbitrary stretch), then the constructor's fields.  A guarded
call's prefix arguments are the rule's OWN prefix variables (the kernel
requires `rP_{c'} = rP`), and so is the ι equation's left-hand side's prefix. -/

/-- The `rP` prefix variables as bvars, at the frame
`prefix ++ (nF further binders)`. -/
def prefVarsAV (rP nF : Nat) : List AnnotTerm :=
  (List.range rP).map fun l => .bvar (nF + rP - 1 - l)

/-- **The prefix variables read back the prefix spine.** -/
theorem interp_prefVarsAV {rP : Nat} {xs bs : List V} {ρ : Nat → V} (hx : xs.length = rP) :
    (prefVarsAV rP bs.length).map (interp V (consList (xs ++ bs) ρ)) = xs := by
  have hlen : (xs ++ bs).length = bs.length + rP := by
    rw [List.length_append, hx]; omega
  have hval : ∀ l, l < rP →
      interp V (consList (xs ++ bs) ρ) (.bvar (bs.length + rP - 1 - l)) = xs.getD l pt := by
    intro l hl
    show consList (xs ++ bs) ρ (bs.length + rP - 1 - l) = _
    rw [consList_getD_of_lt _ _ _ (by omega), hlen,
      show bs.length + rP - 1 - (bs.length + rP - 1 - l) = l from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
  calc (prefVarsAV rP bs.length).map (interp V (consList (xs ++ bs) ρ))
      = (List.range rP).map (fun l => xs.getD l pt) := by
        rw [prefVarsAV, List.map_map]
        exact List.map_congr_left fun l hl => hval l (List.mem_range.mp hl)
    _ = xs := range_map_getD hx

/-! ## The ι equation of one rule -/

/-- The binder data of a `Prop`-valued Π-tower over the given domains
(both numerals `0`: the tower is a proposition and so is its body). -/
def propBinders (doms : List AnnotTerm) : List (Nat × Nat × AnnotTerm) :=
  doms.map fun D => (0, 0, D)

omit [SetTheory V] in
@[simp] theorem propBinders_doms (doms : List AnnotTerm) :
    (propBinders doms).map (·.2.2) = doms := by
  simp [propBinders, Function.comp_def]

omit [SetTheory V] in
theorem propBinders_cod {doms : List AnnotTerm} : ∀ d ∈ propBinders doms, d.2.1 = 0 := by
  intro d hd
  obtain ⟨D, -, rfl⟩ := List.mem_map.mp hd
  rfl

/-- A `Prop`-valued Π-tower over an equation is a truth value. -/
theorem mkPisAV_eqE_univZero {l r : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ ds, d.2.1 = 0) → interp V σ (mkPisAV ds (.eqE l r)) ∈ˢ (univZero : V)
  | [], _, _ => eqv_mem_univZero _ _
  | d :: ds, σ, hz => by
    show piR d.2.1 _ _ ∈ˢ _
    rw [hz d (.head _)]
    exact piR_zero_mem_univZero

/-- **One rule's ι equation**, at the CHAIN frame (under the `K` Σ'
binders, class `c`'s component `bvar (K-1-c)`).  Quantified over the
rule's prefix `x⃗` (domains `pdoms`) and the constructor's fields `f⃗`
(domains `fdoms`); the left-hand side is the class's component applied
along `(x⃗, e⃗_j, mk_j)`, the right-hand side the residue `Rb` with its
ih openers substituted by `ihs`. -/
def iotaEqAV (K c : Nat) (pdoms fdoms es : List AnnotTerm) (mk : AnnotTerm)
    (ihs : List AnnotTerm) (Rb : AnnotTerm) : AnnotTerm :=
  mkPisAV (propBinders (pdoms ++ fdoms))
    (.eqE
      (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
        (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]))
      (instsAV 0 ihs Rb))

/-- The ι equation is a truth value. -/
theorem iotaEqAV_univZero {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} :
    interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) ∈ˢ (univZero : V) :=
  mkPisAV_eqE_univZero propBinders_cod

/-- **The ι equation is graded** when the domains are graded along the
telescope and both sides are graded at every fitting spine. -/
theorem wd_iotaEqAV {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V}
    (hdoms : FieldsOkB 0 σ (pdoms ++ fdoms))
    (hbody : ∀ ys, SpineFit σ (pdoms ++ fdoms) ys →
      WellDenoted V (consList ys σ)
          (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
            (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk])) ∧
        WellDenoted V (consList ys σ) (instsAV 0 ihs Rb)) :
    WellDenoted V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) := by
  refine WellDenoted_mkPisAV_of (by simpa using hdoms) fun ys hsp => ?_
  rw [propBinders_doms] at hsp
  rw [WellDenoted_eqE]
  exact hbody ys hsp

/-- **The two sides of one rule's ι equation**, read at a fitting
spine `xs ++ fs` of the rule's prefix and the constructor's fields:
the left is the class's component folded along `(x⃗, e⃗_j, mk_j)`, the
right is the RESIDUE at the ih values. -/
theorem iotaEqAV_sides {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R) {xs fs : List V}
    (hxl : xs.length = pdoms.length) (hfl : fs.length = fdoms.length) :
    interp V (consList (xs ++ fs) σ)
        (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
          (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]))
        = (xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R ∧
      interp V (consList (xs ++ fs) σ) (instsAV 0 ihs Rb)
        = interp V (consList (ihs.map (interp V (consList (xs ++ fs) σ)))
            (consList (xs ++ fs) σ)) Rb := by
  refine ⟨?_, interp_instsAV _ _ _⟩
  have hhead : interp V (consList (xs ++ fs) σ)
      (.bvar (pdoms.length + fdoms.length + (K - 1 - c))) = R := by
    show consList (xs ++ fs) σ (pdoms.length + fdoms.length + (K - 1 - c)) = R
    rw [show pdoms.length + fdoms.length + (K - 1 - c)
          = (K - 1 - c) + (xs ++ fs).length from by
        rw [List.length_append, hxl, hfl]; omega,
      consList_apply_add, hR]
  have hpre : (prefVarsAV pdoms.length fdoms.length).map (interp V (consList (xs ++ fs) σ))
      = xs := by
    have h := interp_prefVarsAV (V := V) (rP := pdoms.length) (xs := xs) (bs := fs) (ρ := σ) hxl
    rw [hfl] at h
    exact h
  have hargs : (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]).map
      (interp V (consList (xs ++ fs) σ))
      = xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ)) := by
    simp only [List.map_append, hpre, List.append_assoc]
  rw [interp_mkAppN, foldl_app_map, hhead, hargs]

/-- The length of a fit of the rule's binder data. -/
theorem iotaEqAV_fs_length {pdoms fdoms : List AnnotTerm} {σ : Nat → V} {xs fs : List V}
    (hxl : xs.length = pdoms.length) (hsp : SpineFit σ (pdoms ++ fdoms) (xs ++ fs)) :
    fs.length = fdoms.length := by
  have h := hsp.length_eq
  rw [List.length_append, List.length_append, hxl] at h
  omega

/-- **THE ι LAW, extracted**: at a fitting spine `xs ++ fs` of the
rule's prefix and the constructor's fields, the class's component
applied along the rule's left-hand side equals the residue read at the
frame extended by the ih values.  `hR` names the component: the
consumer instantiates `σ` with the chain frame `consList rs ρ`, where
`σ (K-1-c) = rs.getD c pt` is the class's leaf. -/
theorem iotaEqAV_law {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R)
    (h : (pt : V) ∈ˢ interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb))
    {xs fs : List V} (hxl : xs.length = pdoms.length)
    (hsp : SpineFit σ (pdoms ++ fdoms) (xs ++ fs)) :
    ((xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R)
      = interp V (consList ((ihs.map (interp V (consList (xs ++ fs) σ)))) (consList (xs ++ fs) σ))
          Rb := by
  have heq := (pt_mem_mkPisAV_eqE_iff (V := V) (propBinders_cod (doms := pdoms ++ fdoms))).mp h
    (xs ++ fs) (by rw [propBinders_doms]; exact hsp)
  obtain ⟨hl, hr⟩ := iotaEqAV_sides hR hxl (iotaEqAV_fs_length hxl hsp)
  rw [hl, hr] at heq
  exact heq

/-- **The ι equation is INHABITED** by the laws at every fitting spine —
the direction the three regimes' candidates are fed through. -/
theorem pt_mem_iotaEqAV_of {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R)
    (h : ∀ xs fs : List V, xs.length = pdoms.length →
      SpineFit σ (pdoms ++ fdoms) (xs ++ fs) →
      ((xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R)
        = interp V (consList ((ihs.map (interp V (consList (xs ++ fs) σ))))
            (consList (xs ++ fs) σ)) Rb) :
    (pt : V) ∈ˢ interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) := by
  refine (pt_mem_mkPisAV_eqE_iff (V := V) (propBinders_cod (doms := pdoms ++ fdoms))).mpr
    fun ys hsp => ?_
  rw [propBinders_doms] at hsp
  have hlen : ys.length = pdoms.length + fdoms.length := by
    rw [hsp.length_eq, List.length_append]
  have hys : ys = ys.take pdoms.length ++ ys.drop pdoms.length := (List.take_append_drop _ _).symm
  have hxl : (ys.take pdoms.length).length = pdoms.length := by
    rw [List.length_take]; omega
  rw [hys] at hsp ⊢
  obtain ⟨hl, hr⟩ := iotaEqAV_sides hR hxl (iotaEqAV_fs_length hxl hsp)
  rw [hl, hr]
  exact h _ _ hxl hsp

/-! ## The λ-tower whose body sees the spine

The candidate the three regimes supply is a λ-tower over the
recursor's whole binder data whose body needs the PREFIX values (the
parameters and the arbitrary stretch: the kit is built per prefix
frame), the INDEX values and the MAJOR — i.e. the accumulated spine,
not just the leaf frame.  `lamTowerA` is `lamTower` with that
accumulator; its two laws are the same two. -/

/-- The semantic λ-tower over binder data, with the body a function of
the ACCUMULATED spine and the leaf frame. -/
noncomputable def lamTowerA (m : Nat) :
    (Nat → V) → List V → List (Nat × Nat × AnnotTerm) → (List V → (Nat → V) → V) → V
  | ρ, acc, [], g => g acc ρ
  | ρ, acc, d :: ds, g => lamR m (interp V ρ d.2.2) fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g

/-- `lamTowerA`'s walk premise: at every leaf frame reached the body is
in the conclusion's reading (a truth value at a zero bit). -/
def TowerWalkA (m : Nat) (C : AnnotTerm) (g : List V → (Nat → V) → V) :
    (Nat → V) → List V → List (Nat × Nat × AnnotTerm) → Prop
  | ρ, acc, [] => g acc ρ ∈ˢ interp V ρ C ∧ (m = 0 → interp V ρ C ∈ˢ (univZero : V))
  | ρ, acc, d :: ds => ∀ a, a ∈ˢ interp V ρ d.2.2 → TowerWalkA m C g (cons a ρ) (acc ++ [a]) ds

/-- **The tower inhabits the Π-tower's reading** — `mem_type` of the
candidate. -/
theorem lamTowerA_mem {m : Nat} {C : AnnotTerm} {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → TowerWalkA m C g ρ acc ds →
      lamTowerA m ρ acc ds g ∈ˢ interp V ρ (mkPisAV ds C)
  | [], _, _, _, h => h.1
  | d :: ds, ρ, acc, hz, h => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g)
      ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun a => interp V (cons a ρ) (mkPisAV ds C)
    exact lamR_mem_zero_agree (hz d (.head _))
      fun a ha => lamTowerA_mem (fun d' hd' => hz d' (.tail _ hd')) (h a ha)

/-- **The tower's fold along a fitting spine** (nonzero bit) — the ι
law's left-hand side. -/
theorem lamTowerA_fold {m : Nat} (hm : m ≠ 0) {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc bs : List V},
      SpineFit ρ (ds.map (·.2.2)) bs →
      bs.foldl SetTheory.app (lamTowerA m ρ acc ds g) = g (acc ++ bs) (consList bs ρ)
  | [], _, acc, [], _ => by simp [lamTowerA]
  | [], _, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, [], hsp => hsp.elim
  | d :: ds, ρ, acc, b :: bs, hsp => by
    show bs.foldl SetTheory.app (SetTheory.app (lamR m (interp V ρ d.2.2)
      fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g) b) = _
    rw [app_lamR_pos hm hsp.1, consList_cons, lamTowerA_fold hm hsp.2]
    simp

/-! ## The family: its ι equations, its leaf, and its facts -/

/-- The family's ι equations: one per class `c < K` and constructor
`j < nCt c`, in class-major order.  `IotaAll` of the design. -/
def iotaEqsAV (K : Nat) (nCt : Nat → Nat) (pdoms : Nat → List AnnotTerm)
    (fdoms es : Nat → Nat → List AnnotTerm) (mk : Nat → Nat → AnnotTerm)
    (ihs : Nat → Nat → List AnnotTerm) (Rb : Nat → Nat → AnnotTerm) : List AnnotTerm :=
  (List.range K).flatMap fun c =>
    (List.range (nCt c)).map fun j =>
      iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j)

omit [SetTheory V] in
theorem mem_iotaEqsAV {K : Nat} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {c j : Nat}
    (hc : c < K) (hj : j < nCt c) :
    iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j)
      ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb :=
  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc,
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

omit [SetTheory V] in
/-- Every member of the family's equation list IS one rule's equation —
the form every per-equation premise is discharged in. -/
theorem forall_iotaEqsAV {K : Nat} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {P : AnnotTerm → Prop}
    (h : ∀ c, c < K → ∀ j, j < nCt c →
      P (iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j))) :
    ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb, P e := by
  intro e he
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  exact h c (List.mem_range.mp hc) j (List.mem_range.mp hj)

/-- **THE LEAF**: the recursor of class `c` is the `c`-th projection of
the ONE chosen tuple of the `K` recursor types pinned by every rule's ι
equation. -/
def blockRecAV (s K : Nat) (RecTy : Nat → AnnotTerm) (eqs : List AnnotTerm) (c : Nat) :
    AnnotTerm :=
  blockRecAVI s K RecTy eqs c

/-- The chain frame of a tuple: the base frame under the `K` Σ'
binders, class `c`'s component at `bvar (K-1-c)`. -/
noncomputable def chainFrame (K : Nat) (a ρ : Nat → V) : Nat → V :=
  consList ((List.range K).map a) ρ

theorem chainFrame_apply {K c : Nat} (hc : c < K) (a ρ : Nat → V) :
    chainFrame K a ρ (K - 1 - c) = a c := by
  have hlen : ((List.range K).map a).length = K := by simp
  rw [chainFrame, consList_getD_of_lt _ _ _ (by omega), hlen,
    show K - 1 - (K - 1 - c) = c from by omega, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hc]
  rfl

/-- **The premise of the recursor family's leaf** at a base frame `ρ`:
the `K` recursor types are formed at level `s`, the ι equations are
truth values and graded at every fitting tuple, and a CANDIDATE tuple
satisfies them.  The candidate is what the three proof regimes supply
(DESIGN v2 §3.2 WF, §3.3 IND, §3.4 SQ); everything else is read off the
check's certificates. -/
structure BlockRecPre (V : Type uv) [SetTheory V] (s K : Nat) (RecTy : Nat → AnnotTerm)
    (eqs : List AnnotTerm) (ρ : Nat → V) : Prop where
  /-- The recursor types are sets of the chain's level, and graded. -/
  hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c)
  /-- The ι equations are truth values and graded at every tuple typed
  at the recursor types. -/
  hEq : ∀ rs : List V, rs.length = K →
    (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
    ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e
  /-- **The recursion theorem**: a tuple typed at the recursor types
  satisfying every ι equation. -/
  hCand : ∃ cand : Nat → V, (∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c)) ∧
    ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (chainFrame K cand ρ) e

/-- **The leaf's facts**: there is ONE tuple `a` whose components are
the classes' leaves — typed at the recursor types (`mem_type`) and
graded — and which satisfies every ι equation. -/
theorem blockRecAV_facts {s K : Nat} {RecTy : Nat → AnnotTerm} {eqs : List AnnotTerm}
    {ρ : Nat → V} (h : BlockRecPre V s K RecTy eqs ρ) :
    ∃ a : Nat → V,
      (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c) ∧
        interp V ρ (blockRecAV s K RecTy eqs c) = a c ∧
        WellDenoted V ρ (blockRecAV s K RecTy eqs c)) ∧
      ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  obtain ⟨cand, hcand, hcandEq⟩ := h.hCand
  exact blockRecAVI_facts s K RecTy eqs ρ h.hTy h.hEq cand hcand hcandEq

/-- **THE ι LAWS OF THE FAMILY**, extracted at the leaf: one tuple `a`,
its components the classes' leaves, and for every class `c` and
constructor `j` the equation
`rec_c x⃗ e⃗_j (C_j p⃗ f⃗) = Rb_{c,j}` at the ih values — the
`RecRuleLaw`-shaped statement the Model tier converts. -/
theorem blockRecAV_iota {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat}
    {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
    {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
    {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}
    (h : BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ) :
    ∃ a : Nat → V,
      (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c) ∧
        interp V ρ (blockRecAV s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) c) = a c ∧
        WellDenoted V ρ
          (blockRecAV s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) c)) ∧
      ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        (xs ++ (es c j ++ [mk c j]).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))).foldl SetTheory.app (a c)
          = interp V
              (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))
                (consList (xs ++ fs) (chainFrame K a ρ))) (Rb c j) := by
  obtain ⟨a, ha, haEq⟩ := blockRecAV_facts h
  refine ⟨a, ha, fun c hc j hj xs fs hxl hsp => ?_⟩
  exact iotaEqAV_law (chainFrame_apply hc a ρ) (haEq _ (mem_iotaEqsAV hc hj)) hxl hsp

/-! ## The guarded call's ih term: the curried λ-tower

A rule's `ih` opener for a recursive/reflexive/nested field `f_i` is
valued, in the design, at the CURRIED λ-tower over the field's
TELESCOPE (the ih's domain is the telescope, not the predecessor set)
of the guarded call `rec_{c'} x⃗ e⃗(a⃗) (f_i a⃗)` — the
very spine the check abstracted.  At the chain frame that call's head
is class `c'`'s component, so the tower is spellable here, and its
FOLD along a fitting telescope spine is the call's value. -/

/-- The ih term of a guarded field: the curried λ-tower (bit `ℓ`) over
the field's telescope `tl` of `rec_{c'} x⃗ e⃗(a⃗) (f_i a⃗)`, at the frame
`prefix ++ fields` under the `K` chain binders.  `eis` are the field's
index expressions and `fap` the applied field, both at the frame
`prefix ++ fields ++ telescope`. -/
def ihFunAV (ℓ K c' rP nF : Nat) (tl : List (Nat × Nat × AnnotTerm)) (eis : List AnnotTerm)
    (fap : AnnotTerm) : AnnotTerm :=
  mkLamsC ℓ tl
    (AnnotTerm.mkAppN (.bvar (tl.length + nF + rP + (K - 1 - c')))
      (prefVarsAV rP (nF + tl.length) ++ eis ++ [fap]))

theorem interp_mkLamsC_A (m : Nat) (b : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) (acc : List V),
      interp V ρ (mkLamsC m ds b) = lamTowerA m ρ acc ds (fun _ σ => interp V σ b)
  | [], _, _ => rfl
  | d :: ds, ρ, acc => by
    show lamR m (interp V ρ d.2.2) (fun a => interp V (cons a ρ) (mkLamsC m ds b)) = _
    exact lamR_congr fun a _ => interp_mkLamsC_A m b ds (cons a ρ) (acc ++ [a])

/-- **The ih term's fold**: the curried tower applied along a fitting
spine `a⃗` of the field's telescope is the GUARDED CALL's value — class
`c'`'s component folded along `(x⃗, e⃗(a⃗), f_i a⃗)`.  This is what makes
the ih openers' values the recursor's own values at the predecessors
(regime WF: `app g (tagged c' ⟨e⃗(a⃗)⟩ (f_i a⃗))` through `rec_eq`). -/
theorem ihFunAV_fold {ℓ K c' rP nF : Nat} {tl : List (Nat × Nat × AnnotTerm)}
    {eis : List AnnotTerm} {fap : AnnotTerm} (hℓ : ℓ ≠ 0) {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c') = R) {xs fs as : List V}
    (hxl : xs.length = rP) (hfl : fs.length = nF) (hal : as.length = tl.length)
    (hsp : SpineFit (consList (xs ++ fs) σ) (tl.map (·.2.2)) as) :
    as.foldl SetTheory.app
        (interp V (consList (xs ++ fs) σ) (ihFunAV ℓ K c' rP nF tl eis fap))
      = (xs ++ (eis ++ [fap]).map (interp V (consList (xs ++ fs ++ as) σ))).foldl
          SetTheory.app R := by
  have hfr : consList as (consList (xs ++ fs) σ) = consList (xs ++ (fs ++ as)) σ := by
    rw [consList_append, consList_append, consList_append]
  rw [ihFunAV, interp_mkLamsC_A (acc := ([] : List V)), lamTowerA_fold hℓ hsp, hfr,
    interp_mkAppN, foldl_app_map]
  have hlen : (xs ++ (fs ++ as)).length = nF + tl.length + rP := by
    rw [List.length_append, List.length_append, hxl, hfl, hal]; omega
  have hhead : interp V (consList (xs ++ (fs ++ as)) σ)
      (.bvar (tl.length + nF + rP + (K - 1 - c'))) = R := by
    show consList (xs ++ (fs ++ as)) σ (tl.length + nF + rP + (K - 1 - c')) = R
    rw [show tl.length + nF + rP + (K - 1 - c')
          = (K - 1 - c') + (xs ++ (fs ++ as)).length from by rw [hlen]; omega,
      consList_apply_add, hR]
  have hpre : (prefVarsAV rP (nF + tl.length)).map (interp V (consList (xs ++ (fs ++ as)) σ))
      = xs := by
    have h := interp_prefVarsAV (V := V) (rP := rP) (xs := xs) (bs := fs ++ as) (ρ := σ) hxl
    rw [List.length_append, hfl, hal] at h
    exact h
  rw [hhead]
  have hxsfs : xs ++ fs ++ as = xs ++ (fs ++ as) := by rw [List.append_assoc]
  rw [hxsfs]
  simp only [List.map_append, hpre, List.append_assoc]

/-! ## Two named obligations: one elimination level (D-d) and the residue (G1) -/

/-- **D-d, stated** (DESIGN v2 §3.2): the family eliminates at ONE
level.  The leaf is a Σ'-chain at a single `s` and the candidate is a
λ-tower at a single bit, so every class's binder data must carry the
SAME zeroness — which is what a common elimination level gives (the
kernel's elimination-level pin, `checkBlockRecElimPin`). -/
def OneElimLevel (ℓ K : Nat) (rds : Nat → List (Nat × Nat × AnnotTerm)) : Prop :=
  ∀ c, c < K → ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)

/-- **G1's shape, stated**: what the Model tier owes about ONE rule's
RESIDUE at ONE frame — it is graded, and its value lands in the
target, at the frame `(x⃗, f⃗)` extended by the ih openers' VALUES.
The residue is recursor-free by construction, which is why
this is a statement about the CONSTRUCTORS' environment and not about
one holding the recursors.

Both regimes consume exactly this: in WF the target is the kit's
motive `B (tagged c ⟨ı⃗⟩ (C_j p⃗ f⃗))` and the fact IS `WfRecKit.hst`; in
IND the target is a truth value and the fact is `indCand_hCand`'s
`hres`.  The grading half is `hEq_iotaEqsAV_of`'s right conjunct. -/
def ResidueOk (V : Type uv) [SetTheory V] (Rb : AnnotTerm) (ihvals : List V) (ρ' : Nat → V)
    (B : V) : Prop :=
  WellDenoted V (consList ihvals ρ') Rb ∧ interp V (consList ihvals ρ') Rb ∈ˢ B

/-! ## The premise's two halves, in the form their owners prove them -/

section Assemble

variable {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **The ι equations are graded** when every rule's binder data is
graded along the telescope and both its sides are graded at every
fitting spine — the Model tier's half (G1's `WellDenotedV` under
`CtxOk`, and the leaf's own grading for the left-hand side). -/
theorem hEq_iotaEqsAV_of
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j))) :
    ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e := by
  intro rs hlen hmem
  refine forall_iotaEqsAV fun c hc j hj => ⟨iotaEqAV_univZero, ?_⟩
  obtain ⟨hd, hb⟩ := hwd rs hlen hmem c hc j hj
  exact wd_iotaEqAV hd hb

/-- **The candidate's obligations, in the form the three regimes prove
them** (DESIGN v2 §3.2 WF, §3.3 IND, §3.4 SQ): a tuple typed at the
recursor types whose components satisfy every rule's ι law at every
fitting spine of the rule's prefix and the constructor's fields. -/
theorem hCand_iotaEqsAV_of (cand : Nat → V)
    (hty : ∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c))
    (hiota : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K cand ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (xs ++ (es c j ++ [mk c j]).map
          (interp V (consList (xs ++ fs) (chainFrame K cand ρ)))).foldl SetTheory.app (cand c)
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K cand ρ))))
              (consList (xs ++ fs) (chainFrame K cand ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e :=
  ⟨cand, hty, forall_iotaEqsAV fun c hc j hj =>
    pt_mem_iotaEqAV_of (chainFrame_apply hc cand ρ) (hiota c hc j hj)⟩

end Assemble

/-- `TowerWalkA` from the facts at every fitting spine. -/
theorem towerWalkA_of_spines_body {m : Nat} {C : AnnotTerm} {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ ys, SpineFit ρ (ds.map (·.2.2)) ys →
        g (acc ++ ys) (consList ys ρ) ∈ˢ interp V (consList ys ρ) C ∧
          (m = 0 → interp V (consList ys ρ) C ∈ˢ (univZero : V))) →
      TowerWalkA m C g ρ acc ds
  | [], ρ, acc, h => by
    have h0 := h [] trivial
    rw [List.append_nil, consList_nil] at h0
    exact h0
  | d :: ds, ρ, acc, h => by
    intro a ha
    refine towerWalkA_of_spines_body fun ys hsp => ?_
    have := h (a :: ys) ⟨ha, hsp⟩
    rw [consList_cons] at this
    simpa using this

end ConLeche.Semantics
