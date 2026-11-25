module

public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Tower.FixTower
public import ConLeche.SetModel.Access
public section

/-!
# The LFP CLAUSE of an inductive block

**A member's denotation `⟦I⟧ p⃗` is the least fixed point of its
block's right-hand-side operator, with holes for the recursive
fields.**  The recursor model's graph route asks nothing else of an
inductive: the recursor's uniqueness is ONE induction over the majors,
a corollary of this clause (`Model/Inductives/BlockRecGraph.lean`).

**Why a separate datum.**  The clause is recorded in `EnvModelM`
(`Model/Env/EnvModelM.lean`), which sits BELOW the block
representation (`BlockData`/`BlockModelAt`,
`Model/Inductives/BlockRep.lean`) in the import order.  So the clause
is stated over `LfpDatum`, the part of a block's representation the
clause reads — its member names, widths, parameter and index
telescopes, the operator `Φ`, and the constructors' fit relation and
injections — and a uniform block's datum is `BlockData.toLfp d`
(`BlockRep.lean`), its fields literally `d`'s.  The OPERATOR is
therefore exactly the one `BlockModelAt` uses: `d.Φ`, which at the
block's data is the hole operator `holeOp` (`BlockData.withPhi`,
`BlockDatum.lean`); the clause's `fibre` says what that operator IS, fibre by fibre
(injections of the spines fitting a constructor, a recursive field
read at the tuple's component) — the NARROW clause: a container's
instance is read ordinarily, it is not a component.

**The clause** (`LfpClause`), at every level assignment `ψ` and every
parameter frame `ρp` satisfying the parameter telescope (exactly the
quantification `BlockModelAt` has, which is what the install proves):

* `maps` — `Φ` maps the tuple space into itself;
* `fitAcc` — the hole fit is ACCESSIBLE (`LfpDatum.FitAcc`), with a
  bound of the level at a `Type`-valued block;
* `fibre` — component `c`'s fibre at `(X, t)` is the set of injections
  of the spines fitting one of `c`'s constructors at `(X, t)`;
* `leaf` — a member's former, at fitting parameters and its own
  indices, is the least pre-fixed tuple's component at the index
  tuple.

**Derived, not recorded** (tasks #326, #327), at every level: the
operator's accessibility (`LfpClause.acc`, through `fibre`), hence (W)
(`LfpClause.closed`, `AccW.closed`) and monotonicity (`LfpClause.mono`);
the fit's growth (`LfpClause.fitsMono`, `FitAcc.mono`).

**Universe instantiation.**  `leaf` holds at EVERY level assignment
`ψ`.  A use `.const I us` under `φ` reads the leaf at
`Level.substFn φ lps us` (`EnvModelM.constType`'s crossing), which is
one such `ψ`.  The installer establishes the clause at every `ψ` because it checks
the block's parameters once, polymorphically, and the model reads the
member's leaf as a function of the assignment.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.SetModel (lamV lamV_congr lamV_ext app_lamV lamV_eq_pt lamV_ne_pt_of lamV_eq_graph)
open ConLeche.SetTheory.Tower (mkTower projS)


open ConLeche (Name Level)

universe w

section HoleFam

variable {V : Type w} [SetTheory V]

/-- Definability of a hole leaf function `g : List V → V` at arity `n`. -/
@[expose] def DefHoleFn (n : Nat) (g : List V → V) : Prop :=
  DefFun n fun xs : Fin n → V => g (List.ofFn xs)

theorem DefHoleFn.cons (a : V) {n : Nat} {g : List V → V}
    (hg : DefHoleFn (n + 1) g) : DefHoleFn n fun as => g (a :: as) := by
  unfold DefHoleFn at hg ⊢
  let Gs : Fin (n + 1) → (Fin n → V) → V
    | ⟨0, _⟩ => fun _ => a
    | ⟨i + 1, hi⟩ => fun xs => xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  have hGs : ∀ j : Fin (n + 1), DefFun n (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact DefFun.const a
    | succ j => exact DefFun.proj ⟨j, Nat.lt_of_succ_lt_succ hj⟩
  refine (DefFun.comp hg hGs).congr fun xs => ?_
  congr 1
  rw [List.ofFn_succ]
  rfl

theorem DefHoleFn.append (ps : List V) {n : Nat} {g : List V → V}
    (hg : DefHoleFn (ps.length + n) g) : DefHoleFn n fun bs => g (ps ++ bs) := by
  induction ps generalizing n g with
  | nil => simpa using hg
  | cons p ps ih =>
    have hg' : DefHoleFn (ps.length + n) (fun vs => g (p :: vs)) :=
      DefHoleFn.cons p (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg)
    simpa [List.cons_append] using ih hg'

theorem DefFun.mkTower_ofFn :
    ∀ (n : Nat), DefFun (V := V) n fun xs : Fin n → V => mkTower (List.ofFn xs)
  | 0 => DefFun.empty.congr fun xs => by
    rw [@List.ofFn_zero _ xs]
    rfl
  | n + 1 => by
    have ih := (DefFun.mkTower_ofFn n).reIndex Fin.succ
    refine (DefFun.spair_apply (DefFun.proj 0) ih).congr fun xs => ?_
    rw [List.ofFn_succ]
    rfl

theorem DefHoleFn.of_app_tupW (X : V) (u n : Nat) :
    DefHoleFn n fun vs => app X (tupW u vs) := by
  unfold DefHoleFn
  by_cases hu : u = 0
  · subst hu
    exact (DefFun.const (app X pt)).congr fun xs => by dsimp only; rw [tupW_zero]
  · exact (DefFun.app_apply (DefFun.const X) (DefFun.mkTower_ofFn n)).congr fun xs => by
      dsimp only; rw [tupW_pos hu]

theorem DefHoleFn.of_interp (ρ : Nat → V) (n : Nat) (b : Term) :
    DefHoleFn n fun vs => interp V (consList vs ρ) b := by
  unfold DefHoleFn
  have hre : DefFun n fun xs : Fin n → V =>
      interp V (prepend (fun i : Fin n => xs ⟨n - 1 - i.val, by omega⟩) ρ) b :=
    (interp_defFun_prepend ρ n b).reIndex fun i => ⟨n - 1 - i.val, by omega⟩
  refine hre.congr fun xs => ?_
  congr 1
  have hcons : ∀ (m : Nat) (ys : Fin m → V) (σ : Nat → V),
      consList (List.ofFn ys) σ =
        prepend (fun i : Fin m => ys ⟨m - 1 - i.val, by omega⟩) σ := by
    intro m
    induction m with
    | zero =>
      intro ys σ
      rw [@List.ofFn_zero _ ys, consList_nil]
      funext i
      simp [prepend]
    | succ m ih =>
      intro ys σ
      rw [List.ofFn_succ, consList_cons, ih (fun j => ys j.succ) (ConLeche.Semantics.cons (ys 0) σ)]
      funext i
      by_cases hi : i < m
      · have hi' : i < m + 1 := Nat.lt_succ_of_lt hi
        simp only [prepend, hi, hi', ↓reduceDIte]
        congr 1
        apply Fin.ext
        dsimp
        omega
      · by_cases heq : i = m
        · subst heq
          simp only [prepend, Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceDIte, Nat.sub_self,
            ConLeche.Semantics.cons]
          congr 1
          apply Fin.ext
          dsimp
          omega
        · have hge : m + 1 ≤ i := by omega
          have hge' : m ≤ i := by omega
          simp only [prepend, Nat.not_lt_of_le hge, Nat.not_lt_of_le hge', ↓reduceDIte]
          have hsub : i - m = (i - (m + 1)) + 1 := by omega
          rw [hsub]
          rfl
  exact (hcons n xs ρ).symm

theorem defFun1_fcons_hole {d : Nat} {F : (Fin (d + 1) → V) → V}
    (hF : DefFun (d + 1) F) (xs : Fin d → V) :
    DefFun 1 fun v => F (fcons (v 0) xs) := by
  let Gs : Fin (d + 1) → (Fin 1 → V) → V
    | ⟨0, _⟩ => fun v => v 0
    | ⟨i + 1, h⟩ => fun _ => xs ⟨i, Nat.lt_of_succ_lt_succ h⟩
  have hGs : ∀ j : Fin (d + 1), DefFun 1 (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact DefFun.proj 0
    | succ j => exact DefFun.const (xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
  refine (DefFun.comp hF hGs).congr fun v => ?_
  congr 1
  funext ⟨j, hj⟩
  cases j with
  | zero => rfl
  | succ j => rfl

theorem defFun_prepend_tail {d n : Nat} (xs : Fin d → V)
    {G : (Fin (d + n) → V) → V} (hG : DefFun (d + n) G) :
    DefFun (0 + n) fun bs : Fin (0 + n) → V =>
      G fun i => if h : i.val < d then xs ⟨i.val, h⟩
        else bs ⟨i.val - d, by omega⟩ := by
  let Gs : Fin (d + n) → (Fin (0 + n) → V) → V := fun i =>
    if h : i.val < d then fun _ => xs ⟨i.val, h⟩
    else fun bs => bs ⟨i.val - d, by omega⟩
  have hGs : ∀ i : Fin (d + n), DefFun (0 + n) (Gs i) := fun i => by
    dsimp only [Gs]
    split
    · exact DefFun.const _
    · exact DefFun.proj _
  refine (DefFun.comp hG hGs).congr fun bs => ?_
  congr 1
  funext i
  dsimp only [Gs]
  split <;> rfl

/-- Proof-carrying worker for `holeFam`. -/
noncomputable def holeFamDef (d : Nat) (ρ : Nat → V) :
    (Fs : List Term) → (G : (Fin (d + Fs.length) → V) → V) → DefFun (d + Fs.length) G →
    { f : (Fin d → V) → V // DefFun d f }
  | [], G, hG => ⟨G, hG⟩
  | F :: Fs, G, hG =>
    let re : Fin (d + (Fs.length + 1)) → Fin ((d + 1) + Fs.length) := fun i =>
      if h : i.val < d then ⟨i.val + 1, by omega⟩
      else if h' : i.val = d then ⟨0, by omega⟩
      else ⟨i.val, by omega⟩
    let G' : (Fin ((d + 1) + Fs.length) → V) → V := fun w => G (fun i => w (re i))
    have hG' : DefFun ((d + 1) + Fs.length) G' := hG.reIndex re
    let F' := interpDef V ρ d F
    let tail' := holeFamDef (d + 1) ρ Fs G' hG'
    ⟨fun xs => lamV (F'.val xs) (fun a => tail'.val (fcons a xs))
        (hasGraph_of_defFun1 (defFun1_fcons_hole tail'.property xs)),
      ConLeche.SetModel.DefFun.lamV_apply tail'.property F'.property⟩

theorem holeFamDef_congr (d : Nat) (ρ : Nat → V) :
    ∀ (Fs : List Term) {G G' : (Fin (d + Fs.length) → V) → V}
      (hG : DefFun (d + Fs.length) G) (hG' : DefFun (d + Fs.length) G'),
      (∀ w, G w = G' w) →
      ∀ xs, (holeFamDef d ρ Fs G hG).val xs = (holeFamDef d ρ Fs G' hG').val xs
  | [], _, _, _, _, heq, xs => heq xs
  | F :: Fs, G, G', hG, hG', heq, xs => by
    simp only [holeFamDef]
    refine lamV_congr _ _ fun a _ => ?_
    exact holeFamDef_congr (d + 1) ρ Fs _ _ (fun w => heq _) (fcons a xs)

theorem holeFamDef_prepend :
    ∀ (Fs : List Term) (d : Nat) (xs : Fin d → V) (ρ : Nat → V)
      (G : (Fin (d + Fs.length) → V) → V) (hG : DefFun (d + Fs.length) G),
      (holeFamDef d ρ Fs G hG).val xs =
        (holeFamDef 0 (prepend xs ρ) Fs
          (fun bs => G fun i => if h : i.val < d then xs ⟨i.val, h⟩ else bs ⟨i.val - d, by omega⟩)
          (defFun_prepend_tail xs hG)).val Fin.elim0
  | [], d, xs, ρ, G, hG => by
    simp only [holeFamDef]
    congr 1
    funext ⟨i, hi⟩
    simp [hi]
  | F :: Fs, d, xs, ρ, G, hG => by
    simp only [holeFamDef]
    have hF : (interpDef V ρ d F).val xs = (interpDef V (prepend xs ρ) 0 F).val Fin.elim0 :=
      interpDef_prepend V F d xs ρ
    refine lamV_ext hF _ _ fun a _ => ?_
    rw [holeFamDef_prepend Fs (d + 1) (fcons a xs) ρ]
    rw [holeFamDef_prepend Fs 1 (fcons a Fin.elim0) (prepend xs ρ)]
    simp only [prepend_fcons, prepend_zero]
    refine holeFamDef_congr 0 (cons a (prepend xs ρ)) Fs _ _ (fun bs => ?_) Fin.elim0
    congr 1
    funext ⟨i, hi⟩
    by_cases h1 : i < d
    · have h2 : i < d + 1 := Nat.lt_succ_of_lt h1
      simp [h1, fcons]
    · by_cases h2 : i = d
      · subst h2
        simp [h1]
      · have h3 : ¬ i < d + 1 := by omega
        have h4 : i - d ≠ 0 := by omega
        have h5 : ¬ i - d < 1 := by omega
        simp only [h1, h2, h3, Nat.not_lt_zero, h4, h5, ↓reduceDIte]
        congr 1

/-- **The λ-tower over a telescope** `Fs`, read progressively from `ρ`,
of `g` at the bound values — proof-carrying value-read (`lamV`), the
reading of the spelled hole term (the hole values): a level all of whose
continuations are empty is the point. -/
@[expose] noncomputable def holeFam (ρ : Nat → V) :
    (Fs : List Term) → (g : List V → V) → DefHoleFn Fs.length g → V
  | Fs, g, hg =>
    (holeFamDef 0 ρ Fs
      (fun xs => g (List.ofFn fun i : Fin Fs.length =>
        xs ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add Fs.length).symm⟩))
      (hg.reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add Fs.length).symm⟩)).val
      Fin.elim0

theorem holeFam_nil (ρ : Nat → V) (g : List V → V) (hg : DefHoleFn ([] : List Term).length g) :
    holeFam ρ [] g hg = g [] := by
  simp only [holeFam, holeFamDef]
  rw [@List.ofFn_zero _ _]

theorem holeFam_hasGraph (ρ : Nat → V) (F : Term) (Fs : List Term) (g : List V → V)
    (hg : DefHoleFn (F :: Fs).length g) :
    HasGraph (interp V ρ F) fun a =>
      holeFam (cons a ρ) Fs (fun as => g (a :: as)) (hg.cons a) := by
  let re : Fin (0 + (Fs.length + 1)) → Fin (1 + Fs.length) := fun i =>
    if h : i.val < 0 then ⟨i.val + 1, by omega⟩
    else if h' : i.val = 0 then ⟨0, by omega⟩
    else ⟨i.val, by omega⟩
  let G0 : (Fin (0 + (Fs.length + 1)) → V) → V := fun xs =>
    g (List.ofFn fun i : Fin (Fs.length + 1) =>
      xs ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add (Fs.length + 1)).symm⟩)
  have hG0 : DefFun (0 + (Fs.length + 1)) G0 :=
    hg.reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add (Fs.length + 1)).symm⟩
  let tail' := holeFamDef 1 ρ Fs (fun w => G0 fun i => w (re i)) (hG0.reIndex re)
  refine (hasGraph_of_defFun1 (F := fun a => tail'.val (fcons a Fin.elim0))
    (defFun1_fcons_hole tail'.property Fin.elim0)).congr fun a _ => ?_
  dsimp only [tail']
  rw [holeFamDef_prepend Fs 1 (fcons a Fin.elim0) ρ]
  rw [prepend_fcons, prepend_zero]
  unfold holeFam
  refine holeFamDef_congr 0 (cons a ρ) Fs _ _ (fun bs => ?_) Fin.elim0
  dsimp only [G0]
  congr 1
  rw [List.ofFn_succ]
  congr 1

theorem holeFam_cons (ρ : Nat → V) (F : Term) (Fs : List Term) (g : List V → V)
    (hg : DefHoleFn (F :: Fs).length g) :
    holeFam ρ (F :: Fs) g hg =
      lamV (interp V ρ F) (fun a => holeFam (cons a ρ) Fs (fun as => g (a :: as)) (hg.cons a))
        (holeFam_hasGraph ρ F Fs g hg) := by
  simp only [holeFam, holeFamDef]
  refine lamV_ext rfl _ _ fun a _ => ?_
  rw [holeFamDef_prepend Fs 1 (fcons a Fin.elim0) ρ, prepend_fcons, prepend_zero]
  refine holeFamDef_congr 0 (cons a ρ) Fs _ _ (fun bs => ?_) Fin.elim0
  congr 1
  rw [List.ofFn_succ]
  congr 1

theorem holeFam_defFun_prepend (d : Nat) (ρ : Nat → V) (Fs : List Term) (g : List V → V)
    (hg : DefHoleFn Fs.length g) :
    DefFun d fun xs => holeFam (prepend xs ρ) Fs g hg := by
  let G : (Fin (d + Fs.length) → V) → V := fun w =>
    g (List.ofFn fun i : Fin Fs.length => w ⟨d + i.val, by omega⟩)
  have hG : DefFun (d + Fs.length) G :=
    hg.reIndex fun i => ⟨d + i.val, by omega⟩
  refine (holeFamDef d ρ Fs G hG).property.congr fun xs => ?_
  rw [holeFamDef_prepend Fs d xs ρ G hG]
  unfold holeFam
  refine holeFamDef_congr 0 (prepend xs ρ) Fs _ _ (fun bs => ?_) Fin.elim0
  dsimp only [G]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_ofFn] at h1
  simp only [List.getElem_ofFn]
  have hnot : ¬ d + i < d := by omega
  simp [hnot]

omit [SetTheory V] in
theorem shiftE_one_succ (n : Nat) (ρ : Nat → V) :
    shiftE n 0 (fun j => ρ (j + 1)) = shiftE (n + 1) 0 ρ := by
  funext i; simp only [shiftE, Nat.not_lt_zero, ite_false]; rw [Nat.add_assoc]

omit [SetTheory V] in
theorem frameIdx_concat (n : Nat) (ρ : Nat → V) :
    frameIdx (n + 1) ρ = frameIdx n (fun j => ρ (j + 1)) ++ [ρ 0] := by
  unfold frameIdx
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro l hl
    have := List.mem_range.mp hl
    show ρ (n + 1 - 1 - l) = ρ (n - 1 - l + 1)
    congr 1; omega
  · simp

/-- `spineFit_frameIdx_of_sat`, by induction on the length. -/
theorem spineFit_frameIdx_of_sat_len :
    ∀ (n : Nat) {Ds : List Term} {ρ : Nat → V}, Ds.length = n → Sat V Ds.reverse ρ →
      SpineFit (shiftE Ds.length 0 ρ) Ds (frameIdx Ds.length ρ)
  | 0, Ds, _, hn, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn; trivial
  | n + 1, Ds, ρ, hn, h => by
    rcases List.eq_nil_or_concat Ds with rfl | ⟨Ds', D, rfl⟩
    · exact absurd hn (by simp)
    rw [List.concat_eq_append] at hn h ⊢
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at h
    have h0 : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) D := by
      have := h 0 D rfl; simpa using this
    have htl : Sat V Ds'.reverse (fun j => ρ (j + 1)) := Sat_tail h
    have hlen : Ds'.length = n := by simpa using hn
    have hih := spineFit_frameIdx_of_sat_len n hlen htl
    rw [List.length_append, List.length_singleton, frameIdx_concat, ← shiftE_one_succ]
    refine hih.append ⟨?_, trivial⟩
    rw [consList_frameIdx]
    exact h0

/-- **A satisfied reversed context is a fitting spine of its own frame
index over its shift.** -/
theorem spineFit_frameIdx_of_sat {Ds : List Term} {σ : Nat → V}
    (h : Sat V Ds.reverse σ) :
    SpineFit (shiftE Ds.length 0 σ) Ds (frameIdx Ds.length σ) :=
  spineFit_frameIdx_of_sat_len _ rfl h

end HoleFam

/-- **The part of a block's representation the lfp clause reads** (see
the module docstring).  A uniform block's is `BlockData.toLfp`. -/
structure LfpDatum (V : Type w) [SetTheory V] where
  /-- the members' names, by position -/
  names : List Name
  /-- the number of MEMBERS -/
  k : Nat
  /-- the operator's WIDTH (members, then instance components) -/
  N : Nat
  /-- the result sort's value, per level assignment -/
  w : (Name → Nat) → Nat
  /-- the parameter telescope -/
  params : (Name → Nat) → List Term
  /-- member `m`'s OWN parameter telescope (its former's binders): a
  hole's λ-tower is over it, as the member's former value is.  At a
  checked block it is `Sat`-equivalent to `params`. -/
  pars : Nat → (Name → Nat) → List Term
  /-- per component: its own index telescope -/
  ids : Nat → (Name → Nat) → List Term
  /-- per component: its index-tuple sort -/
  u : Nat → (Name → Nat) → Nat
  /-- **the tuple operator**, at a level assignment and a parameter frame -/
  Φ : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- first-order tuple definability of `Φ ψ ρp` -/
  hΦ : ∀ (ψ : Name → Nat) (ρp : Nat → V), DefTupleOp N (Φ ψ ρp)
  /-- parametric first-order definability of `Φ ψ` across a `d`-element
  parameter prefix and the `N`-tuple -/
  hΦ_def : ∀ (ψ : Name → Nat) (tail : Nat → V) (d m : Nat), m < N →
    DefFun (N + d) fun v =>
      Φ ψ (Semantics.prepend (fdrop v) tail) (padTuple (ftake v)) m
  /-- the constructor injections -/
  inj : (Name → Nat) → Nat → Nat → List V → V
  /-- first-order definability of constructor injections at every arity -/
  hinj_def : ∀ (ψ : Name → Nat) (c j n : Nat),
    DefFun n fun xs => inj ψ c j (List.ofFn xs)
  /-- **the hole reading** (charter item 2): component `c`'s
  constructor count -/
  nctors : Nat → Nat
  /-- component `c`'s constructor `j`'s name -/
  ctorName : Nat → Nat → Name
  /-- component `c`'s constructor `j`'s FIELD READINGS WITH HOLES: the
  member-abstracted constructor domains, read at the parameters, then
  one hole per member (member `m` at the variable `nP + m`), then the
  earlier fields -/
  fields : (Name → Nat) → Nat → Nat → List Term
  /-- component `c`'s constructor `j`'s result index readings, below the
  fields -/
  resIdx : (Name → Nat) → Nat → Nat → List Term

namespace LfpDatum

variable {V : Type w} [SetTheory V] (D : LfpDatum V)

/-- Member `mm`'s name. -/
@[expose] def member (mm : Nat) : Name := D.names.getD mm .anonymous

/-- The tuple of index-tuple sets at a parameter frame. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun c => idxSet (D.u c ψ) ρp (D.ids c ψ)

/-- **A parameter frame fits the block**: it satisfies the parameter
telescope, and some member's index telescope has a fit there (a full fit
of that member's telescope; where a frame has none, the block's tower
determines nothing there, task #443). -/
@[expose] def FrFit (ψ : Name → Nat) (ρp : Nat → V) : Prop :=
  Sat V (D.params ψ).reverse ρp ∧ ∃ mm, mm < D.k ∧ ∃ is, SpineFit ρp (D.ids mm ψ) is

/-- **The carrier**: the least pre-fixed tuple of the operator. -/
@[expose] noncomputable def carrier (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  lfpTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) (D.hΦ ψ ρp)

/-- First-order definability of component `c`'s index-tuple set across a `d`-element
parameter prefix. -/
theorem defFun_idx (ψ : Name → Nat) (tail : Nat → V) (d c : Nat) :
    DefFun d fun ps => D.idx ψ (Semantics.prepend ps tail) c :=
  DefFun.towerSet_apply (D.u c ψ) (defTeleS_teleOfFields tail (D.ids c ψ) d)

/-- First-order definability of component `m` of `D.carrier` across a `d`-element
parameter prefix. -/
theorem defFun_carrier (ψ : Name → Nat) (tail : Nat → V) (d m : Nat) (hm : m < D.N) :
    DefFun d fun ps => D.carrier ψ (Semantics.prepend ps tail) m :=
  DefFun.lfpTuple_apply
    (fun c _ => D.defFun_idx ψ tail d c)
    (fun ps => D.hΦ ψ (Semantics.prepend ps tail))
    (fun m' hm' => D.hΦ_def ψ tail d m' hm')
    hm

/-- Composition of `D.hΦ_def` with definable parameter slots `ρs` and tuple slots `Xs`. -/
theorem hΦ_comp (ψ : Name → Nat) (tail : Nat → V) {r n : Nat}
    {ρs : Fin r → (Fin n → V) → V} (hρs : ∀ i, DefFun n (ρs i))
    {Xs : (Fin n → V) → Nat → V} (hXs : ∀ m, m < D.N → DefFun n fun v => Xs v m)
    {m : Nat} (hm : m < D.N) :
    DefFun n fun v => D.Φ ψ (Semantics.prepend (fun i => ρs i v) tail) (Xs v) m := by
  let Gs : Fin (D.N + r) → (Fin n → V) → V := fun j v =>
    if hj : j.val < D.N then Xs v j.val
    else ρs ⟨j.val - D.N, by omega⟩ v
  have hGs : ∀ j : Fin (D.N + r), DefFun n (Gs j) := fun j => by
    dsimp only [Gs]
    split
    · next hj => exact hXs j.val hj
    · exact hρs ⟨j.val - D.N, by omega⟩
  refine ((D.hΦ_def ψ tail r m hm).comp hGs).congr fun v => ?_
  have hfdrop : fdrop (fun j : Fin (D.N + r) => Gs j v) = fun i => ρs i v := by
    funext ⟨i, hi⟩
    have hge : ¬ (D.N + i < D.N) := by omega
    simp only [fdrop, Gs, hge, ↓reduceDIte]
    congr 1
    apply Fin.ext
    dsimp
    omega
  rw [hfdrop]
  refine (D.hΦ ψ (Semantics.prepend (fun i => ρs i v) tail)).1 _ _ (fun m' hm' => ?_) m hm
  simp only [padTuple_lt _ hm', ftake, Gs, hm', ↓reduceDIte]

/-- Parametric first-order definability of `D.Φ` on `mixT G (D.carrier ...) (padTuple (ftake v))`
across a `d`-element parameter frame mapped by `ρs`. -/
theorem hΦ_param (ψ : Name → Nat) (tail : Nat → V) {G : Nat → Prop} {r d : Nat}
    {ρs : Fin r → (Fin d → V) → V} (hρs : ∀ i, DefFun d (ρs i))
    {m : Nat} (hm : m < D.N) :
    DefFun (D.N + d) fun v =>
      D.Φ ψ (Semantics.prepend (fun i => ρs i (fdrop v)) tail)
        (mixT G (D.carrier ψ (Semantics.prepend (fun i => ρs i (fdrop v)) tail))
          (padTuple (ftake v))) m := by
  refine D.hΦ_comp ψ tail (fun i => (hρs i).fdrop_apply) (fun m' hm' => ?_) hm
  by_cases hG : G m'
  · exact (DefFun.ftake_proj ⟨m', hm'⟩).congr fun v => by
      simp only [mixT, hG, ↓reduceIte, padTuple_lt _ hm']
  · exact ((D.defFun_carrier ψ tail r m' hm').comp fun i => (hρs i).fdrop_apply).congr fun v => by
      simp only [mixT, hG, ↓reduceIte]

/-- **Member `m`'s hole value** at the tuple `X`: the
λ-tower over `m`'s indices (read at the parameter frame) of `X m` at the
index tuple — the family of `X`, curried (a hole stands for the member's
WHOLE application to the block's parameters, `nestCrest`). -/
@[expose] noncomputable def holeVal (ψ : Name → Nat) (ρp X : Nat → V) (m : Nat) : V :=
  holeFam ρp (D.ids m ψ) (fun vs => app (X m) (tupW (D.u m ψ) vs))
    (DefHoleFn.of_app_tupW (X m) (D.u m ψ) (D.ids m ψ).length)

/-- **The hole frame** at `(ρp, X)`: the parameter frame with member
`m`'s hole value at the variable `nP + m` (so the last member is
innermost). -/
@[expose] noncomputable def frame (ψ : Name → Nat) (ρp X : Nat → V) : Nat → V :=
  consList ((List.range D.k).map (D.holeVal ψ ρp X)) ρp

/-- **The hole types**: member `m`'s hole type is its index telescope over the block's sort,
read at the variable `nP + m` (over the parameters and the earlier holes). -/
@[expose] def holeTys (ψ : Name → Nat) : List Term :=
  (List.range D.k).map fun m => (mkPisAV (D.ids m ψ) (.sort (D.w ψ))).liftN m 0

theorem holeTys_length (ψ : Name → Nat) : (D.holeTys ψ).length = D.k := by
  simp [holeTys]

/-- **The hole fit**: `fs` fits component `c`'s constructor `j` at the
hole frame of `(ρp, X)` — each field in its reading with holes at the
earlier ones — and its result index readings are the components of the
index tuple `t`. -/
@[expose] def HFits (ψ : Name → Nat) (ρp X : Nat → V) (t : V) (c j : Nat) (fs : List V) :
    Prop :=
  j < D.nctors c ∧ SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs ∧
    ∀ l, l < (D.ids c ψ).length → ∃ e, (D.resIdx ψ c j)[l]? = some e ∧
      interp V (consList fs (D.frame ψ ρp X)) e = projS l t

/-- **The hole fit is accessible with the bound `A`** (task #327): a
spine fitting a constructor at the hole frame of a tuple of the space has
a SUPPORT — set-encoded occurrences of the tuple via a graph `g` over
`B ⊆ˢ A` — and fits at the hole frame of every tuple of the space holding it. -/
@[expose] def FitAcc (ψ : Name → Nat) (ρp : Nat → V) (A : V) : Prop :=
  ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N → ∀ (t : V) (j : Nat) (fs : List V),
    D.HFits ψ ρp X t c j fs → ∃ (B g : V), B ⊆ˢ A ∧
      g ∈ˢ piSet B (fun _ => occSpace D.N (D.idx ψ ρp) X) (hasSigmaPairs_const _ _) ∧
      ∀ X', InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X' →
        (∀ a, a ∈ˢ B → app g a ∈ˢ occSpace D.N (D.idx ψ ρp) X') →
        D.HFits ψ ρp X' t c j fs

variable {D}

/-- **An accessible fit grows with the tuple**: its support is held by
every larger tuple. -/
theorem FitAcc.mono {ψ : Name → Nat} {ρp : Nat → V} {A : V} (h : D.FitAcc ψ ρp A)
    {X Y : Nat → V} (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X)
    (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y) (hXY : TupleLe D.N (D.idx ψ ρp) X Y)
    {c : Nat} (hc : c < D.N) {t : V} {j : Nat} {fs : List V} (hf : D.HFits ψ ρp X t c j fs) :
    D.HFits ψ ρp Y t c j fs := by
  obtain ⟨B, g, -, hg, hs⟩ := h X hX c hc t j fs hf
  exact hs Y hY fun a ha => occSpace_mono hXY _ (app_mem_of_mem_piSet hg ha)

/-- **An operator whose fibres are the injections of an accessible fit is
accessible**, with the fit's bound. -/
theorem FitAcc.accTuple {ψ : Name → Nat} {ρp : Nat → V} {A : V} (h : D.FitAcc ψ ρp A)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs) :
    AccTuple (D.w ψ) D.N (D.idx ψ ρp) D.N (D.idx ψ ρp) (D.Φ ψ ρp) A := by
  intro X hX c hc t ht x hx
  obtain ⟨j, fs, hf, rfl⟩ := (hfib X hX c hc t ht x).mp hx
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX c hc t j fs hf
  exact ⟨B, g, hB, hg, fun X' hX' h' => (hfib X' hX' c hc t ht _).mpr ⟨j, fs, hs X' hX' h', rfl⟩⟩

/-- **The fit's accessibility is congruent** in the readings the fit
reads. -/
theorem FitAcc.congr {D' : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} {A : V}
    (hw : D.w ψ = D'.w ψ) (hN : D.N = D'.N) (hk : D.k = D'.k)
    (hu : ∀ m, D.u m ψ = D'.u m ψ) (hi : ∀ c, D.ids c ψ = D'.ids c ψ)
    (hn : ∀ c, D.nctors c = D'.nctors c)
    (hf : ∀ c j, j < D.nctors c → D.fields ψ c j = D'.fields ψ c j)
    (he : ∀ c j, j < D.nctors c → D.resIdx ψ c j = D'.resIdx ψ c j)
    (h : D.FitAcc ψ ρp A) : D'.FitAcc ψ ρp A := by
  have hfr : ∀ X, D.frame ψ ρp X = D'.frame ψ ρp X := by
    intro X
    unfold frame holeVal
    simp only [hk]
    congr 1
    apply List.map_congr_left
    intro m _
    simp only [hu, hi]
  have hH : ∀ X t c j fs, D.HFits ψ ρp X t c j fs ↔ D'.HFits ψ ρp X t c j fs := by
    intro X t c j fs
    unfold HFits
    constructor
    · rintro ⟨hj, hsp, hr⟩
      rw [hf c j hj, hfr X] at hsp
      rw [he c j hj, hfr X, hi c] at hr
      exact ⟨hn c ▸ hj, hsp, hr⟩
    · rintro ⟨hj, hsp, hr⟩
      have hj0 : j < D.nctors c := (hn c) ▸ hj
      rw [← hf c j hj0, ← hfr X] at hsp
      rw [← he c j hj0, ← hfr X, ← hi c] at hr
      exact ⟨hj0, hsp, hr⟩
  have hidx : D.idx ψ ρp = D'.idx ψ ρp := by
    unfold idx
    funext c
    simp only [hu, hi]
  have hocc : ∀ X, occSpace D.N (D.idx ψ ρp) X = occSpace D'.N (D'.idx ψ ρp) X := by
    intro X
    apply SetTheory.ext fun u => ?_
    rw [mem_occSpace, mem_occSpace, hN, hidx]
  unfold FitAcc at h ⊢
  intro X hX c hc t j fs hfit
  have hX0 : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X := by
    rw [hw, hN, hidx]; exact hX
  have hc0 : c < D.N := hN ▸ hc
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX0 c hc0 t j fs ((hH X t c j fs).mpr hfit)
  have hg' : g ∈ˢ piSet B (fun _ => occSpace D'.N (D'.idx ψ ρp) X) (hasSigmaPairs_const _ _) := by
    rwa [← hocc X]
  refine ⟨B, g, hB, hg', fun X' hX' h' => (hH X' t c j fs).mp ?_⟩
  have hX'0 : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X' := by
    rw [hw, hN, hidx]; exact hX'
  exact hs X' hX'0 fun a ha => (hocc X') ▸ h' a ha

end LfpDatum

/-! ## The hole values -/

section HoleVals

variable {V : Type w} [SetTheory V]

/-- A λ-tower applied to a spine fitting its telescope computes. -/
theorem holeFam_app :
    ∀ {ρ : Nat → V} {Fs : List Term} {as : List V} (g : List V → V)
      {hg : DefHoleFn Fs.length g},
      SpineFit ρ Fs as → as.foldl app (holeFam ρ Fs g hg) = g as
  | _, [], [], g, hg, _ => by rw [holeFam_nil]; rfl
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim
  | ρ, F :: Fs, a :: as, g, hg, h => by
    rw [List.foldl_cons, holeFam_cons, app_lamV h.1]
    exact holeFam_app (fun bs => g (a :: bs)) h.2

/-- **Where the tower is the point**: with leaves that are never the
point at a fitting spine, a level is the point exactly when no spine
fits its telescope — the same for any two such leaf families. -/
theorem holeFam_eq_pt_iff :
    ∀ {ρ : Nat → V} {Fs : List Term} {g g' : List V → V}
      {hg_def : DefHoleFn Fs.length g} {hg'_def : DefHoleFn Fs.length g'},
      (∀ vs, SpineFit ρ Fs vs → g vs ≠ pt) → (∀ vs, SpineFit ρ Fs vs → g' vs ≠ pt) →
      (holeFam ρ Fs g hg_def = pt ↔ holeFam ρ Fs g' hg'_def = pt)
  | _, [], _, _, _, _, hg, hg' => by
    rw [holeFam_nil, holeFam_nil]
    exact ⟨fun h => absurd h (hg [] trivial), fun h => absurd h (hg' [] trivial)⟩
  | ρ, F :: Fs, g, g', hg_def, hg'_def, hg, hg' => by
    rw [holeFam_cons, holeFam_cons]
    have key : ∀ x, x ∈ˢ interp V ρ F →
        (holeFam (cons x ρ) Fs (fun as => g (x :: as)) (hg_def.cons x) = pt ↔
          holeFam (cons x ρ) Fs (fun as => g' (x :: as)) (hg'_def.cons x) = pt) := fun x hx =>
      holeFam_eq_pt_iff (fun vs hvs => hg (x :: vs) ⟨hx, hvs⟩)
        (fun vs hvs => hg' (x :: vs) ⟨hx, hvs⟩)
    constructor
    · intro h
      refine lamV_eq_pt fun x hx => (key x hx).mp ?_
      exact Classical.byContradiction fun hne => lamV_ne_pt_of hx hne h
    · intro h
      refine lamV_eq_pt fun x hx => (key x hx).mpr ?_
      exact Classical.byContradiction fun hne => lamV_ne_pt_of hx hne h

/-- **Off a fitting spine the tower's value does not depend on its
leaves** (as long as they are never the point at a fitting spine): it is
the point where a level is, `∅` where a graph is applied off its domain. -/
theorem holeFam_foldl_nofit :
    ∀ {ρ : Nat → V} {Fs : List Term} {vs : List V} {g g' : List V → V}
      {hg_def : DefHoleFn Fs.length g} {hg'_def : DefHoleFn Fs.length g'},
      (∀ vs, SpineFit ρ Fs vs → g vs ≠ pt) → (∀ vs, SpineFit ρ Fs vs → g' vs ≠ pt) →
      vs.length = Fs.length → ¬ SpineFit ρ Fs vs →
      vs.foldl app (holeFam ρ Fs g hg_def) = vs.foldl app (holeFam ρ Fs g' hg'_def)
  | _, [], [], _, _, _, _, _, _, _, hn => absurd trivial hn
  | _, [], _ :: _, _, _, _, _, _, _, h, _ => by simp at h
  | _, _ :: _, [], _, _, _, _, _, _, h, _ => by simp at h
  | ρ, F :: Fs, a :: vs, g, g', hg_def, hg'_def, hg, hg', hlen, hn => by
    rw [List.foldl_cons, List.foldl_cons, holeFam_cons, holeFam_cons]
    by_cases ha : a ∈ˢ interp V ρ F
    · rw [app_lamV ha, app_lamV ha]
      exact holeFam_foldl_nofit (fun ws hws => hg (a :: ws) ⟨ha, hws⟩)
        (fun ws hws => hg' (a :: ws) ⟨ha, hws⟩) (by simpa using hlen) fun h => hn ⟨ha, h⟩
    · have hpt := holeFam_eq_pt_iff (ρ := ρ) (Fs := F :: Fs)
        (hg_def := hg_def) (hg'_def := hg'_def) hg hg'
      rw [holeFam_cons, holeFam_cons] at hpt
      by_cases hp : lamV (interp V ρ F)
          (fun x => holeFam (cons x ρ) Fs (fun as => g (x :: as)) (hg_def.cons x))
          (holeFam_hasGraph ρ F Fs g hg_def) = pt
      · rw [hp, hpt.mp hp, app_pt]
      · have hp' := fun h => hp (hpt.mpr h)
        rw [lamV_eq_graph hp, lamV_eq_graph hp', app_graph_of_not_mem ha,
          app_graph_of_not_mem ha]

namespace LfpDatum

variable {D : LfpDatum V}

/-- **A hole applied to fitting indices is the tuple's component** at the
index tuple. -/
theorem holeVal_app {ψ : Name → Nat} {ρp X : Nat → V} {m : Nat} {is : List V}
    (his : SpineFit ρp (D.ids m ψ) is) :
    is.foldl app (D.holeVal ψ ρp X m) = app (X m) (tupW (D.u m ψ) is) := by
  unfold holeVal
  exact holeFam_app _ his

end LfpDatum

end HoleVals

variable {V : Type w} [SetTheory V]

/-- **The constructors' result indices fit the index telescope** at
the carrier: a spine hole-fitting constructor `(c, j)` at the carrier
of a satisfying parameter frame has result index readings fitting
component `c`'s index telescope there.  The recursor's rule data at an
OUTSIDE class need it (the fired major's index tuple lies in the index
set: `instCtor_decode`); recorded as `LfpClause.resIdxFit`. -/
@[expose] def LfpResIdxFit (D : LfpDatum V) : Prop :=
  ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ fs : List V,
      SpineFit (D.frame ψ ρp (D.carrier ψ ρp)) (D.fields ψ c j) fs →
      SpineFit ρp (D.ids c ψ)
        ((D.resIdx ψ c j).map (interp V (consList fs (D.frame ψ ρp (D.carrier ψ ρp)))))

/-- **The lfp clause** of the block `D`, over the leaf valuation
`acval` (see the module docstring). -/
structure LfpClause (acval : Name → (Name → Nat) → Term) (D : LfpDatum V) : Prop where
  /-- the members come first among the components -/
  kN : D.k ≤ D.N
  /-- **every component's index telescope is graded** at every
  satisfying parameter frame: what inverting
  an index tuple back to its spine (`isOfW_tupW`) needs at a container -/
  idxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ c, c < D.N → IdxOk (D.u c ψ) ρp (D.ids c ψ)
  /-- **`Φ` maps the tuple space into itself** -/
  maps : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    MapsTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)
  /-- **the hole fit is accessible**, with a bound of the level at a
  `Type`-valued block (task #327): the operator's accessibility, (W) and
  monotonicity, and the fit's growth follow at every level -/
  fitAcc : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∃ A, (D.w ψ ≠ 0 → A ∈ˢ (tg (D.w ψ) : V)) ∧ D.FitAcc ψ ρp A
  /-- **what `Φ` is**: component `c`'s fibre at `(X, t)` is the set of
  injections of the spines fitting one of `c`'s constructors -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
    ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
      x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs
  /-- **the leaf**: a member's former at fitting parameters and its own
  indices is the carrier's component at the index tuple -/
  leaf : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (D.params ψ) as → SpineFit (consList as ρ) (D.ids mm ψ) is →
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      = app (D.carrier ψ (consList as ρ) mm) (tupW (D.u mm ψ) is)
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, D.w ψ = 0 → ∀ c j fs, D.inj ψ c j fs = pt
  /-- at a `Type`-valued block a component's injections are injective
  across its constructors, at spines of the constructors' lengths -/
  mkInj : ∀ ψ : Name → Nat, D.w ψ ≠ 0 → ∀ c, c < D.N → ∀ j fs j' fs',
    j < D.nctors c → j' < D.nctors c →
    fs.length = (D.fields ψ c j).length → fs'.length = (D.fields ψ c j').length →
    D.inj ψ c j fs = D.inj ψ c j' fs' → j = j' ∧ fs = fs'
  /-- **the constructors**: component `c`'s constructor `j`, at fitting
  parameters and fields fitting its hole reading at the carrier, is its
  injection -/
  ctor : ∀ c, c < D.N → ∀ j (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V) (t : V),
    SpineFit ρ (D.params ψ) as → t ∈ˢ D.idx ψ (consList as ρ) c →
    D.HFits ψ (consList as ρ) (D.carrier ψ (consList as ρ)) t c j fs →
    (as ++ fs).foldl app (interp V ρ (acval (D.ctorName c j) ψ)) = D.inj ψ c j fs
  /-- **each member's own parameter telescope is the block's** (R23's M1):
  as long, and satisfied where the block's is — what `holeVal_app` needs
  to read a hole applied to the block's parameters -/
  parsLen : ∀ mm, mm < D.k → ∀ ψ : Name → Nat, (D.pars mm ψ).length = (D.params ψ).length
  parsSat : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (D.params ψ).reverse ρ → Sat V (D.pars mm ψ).reverse ρ
  /-- **… and satisfied only where the block's is** (M1′):
  a container instance's parameters are typed by the container's own
  former telescope, the leaf reads them at the block's -/
  parsSatInv : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (D.pars mm ψ).reverse ρ → Sat V (D.params ψ).reverse ρ
  /-- **the constructors' result indices fit the index telescope** at the
  carrier -/
  resIdxFit : LfpResIdxFit D
  /-- **at a `Type`-valued block no injection is the point** (the
  container case of the accessibility route — the TYPE REGIME of a
  container instance, whose truth-valued fibre is then empty).  A
  uniform block's injections are tagged pairs, `Nat`'s are von Neumann
  numerals, and a positive-level unit is `∅` (task #342 B), so no
  parameter guard is needed. -/
  injNePt : ∀ ψ : Name → Nat, D.w ψ ≠ 0 → ∀ c j fs, D.inj ψ c j fs ≠ pt
  /-- **above `Prop` the injections read no level** (task #342 S5c): two
  `Type`-valued level valuations inject the same fields alike — what
  the ι step's case 2 needs, where the constructor's own levels are not
  compared with the recursor's -/
  injFrame : ∀ ψ ψ' : Name → Nat, D.w ψ ≠ 0 → D.w ψ' ≠ 0 →
    ∀ c j fs, D.inj ψ c j fs = D.inj ψ' c j fs
  /-- **the constructors' fields are small** at a `Type`-valued block, at
  every hole frame of the tuple space (the frame walk of a container reads its constructors' fields along the
  accessibility relation, which supports small elements only — the
  install's own `FieldsOkB`, recorded) -/
  fieldsOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp → D.w ψ ≠ 0 →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N → ∀ j, j < D.nctors c →
      FieldsOkB (D.w ψ) (D.frame ψ ρp X) (D.fields ψ c j)

namespace LfpClause

variable {acval : Name → (Name → Nat) → Term} {D : LfpDatum V}

/-- **Transport**: the clause reads the leaf valuation only at the
members' and the constructors' names. -/
theorem congr (h : LfpClause acval D) {acval' : Name → (Name → Nat) → Term}
    (hag : ∀ mm, mm < D.k → acval' (D.member mm) = acval (D.member mm))
    (hagC : ∀ c, c < D.N → ∀ j, j < D.nctors c → acval' (D.ctorName c j) = acval (D.ctorName c j)) :
    LfpClause acval' D where
  kN := h.kN
  idxOk := h.idxOk
  maps := h.maps
  fitAcc := h.fitAcc
  fibre := h.fibre
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    rw [hag mm hmm]; exact h.leaf mm hmm ψ ρ as is hsa hsi
  mkZero := h.mkZero
  mkInj := h.mkInj
  ctor := fun c hc j ψ ρ as fs t hsa ht hf => by
    rw [hagC c hc j hf.1]; exact h.ctor c hc j ψ ρ as fs t hsa ht hf
  parsLen := h.parsLen
  parsSat := h.parsSat
  parsSatInv := h.parsSatInv
  resIdxFit := h.resIdxFit
  injNePt := h.injNePt
  injFrame := h.injFrame
  fieldsOk := h.fieldsOk


/-- **The operator is accessible** (`AccW`), its fibres the injections of
the accessible fit. -/
theorem acc (h : LfpClause acval D) (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (D.params ψ).reverse ρp) : AccW (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) :=
  (h.fitAcc ψ ρp hsat).elim fun A hA => ⟨A, hA.1, hA.2.accTuple (h.fibre ψ ρp hsat)⟩

/-- **The hole fit grows with the tuple**: a spine fitting a constructor
at the hole frame of a tuple fits it at the hole frame of every larger
tuple (`FitAcc.mono`). -/
theorem fitsMono (h : LfpClause acval D) (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (D.params ψ).reverse ρp) (X Y : Nat → V)
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y)
    (hXY : TupleLe D.N (D.idx ψ ρp) X Y) (c : Nat) (hc : c < D.N) (t : V) (j : Nat)
    (fs : List V) (hf : D.HFits ψ ρp X t c j fs) : D.HFits ψ ρp Y t c j fs :=
  (h.fitAcc ψ ρp hsat).elim fun _ hA => hA.2.mono hX hY hXY hc hf

/-- **(W)**: the operator has a closed tuple, from its accessibility
(`AccW.closed`). -/
theorem closed (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) :
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) L :=
  (h.acc ψ ρp hsat).closed (hΦ := D.hΦ ψ ρp) (h.maps ψ ρp hsat)

/-- **The operator is monotone**, from its accessibility (`AccW.mono`). -/
theorem mono (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) :
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) :=
  (h.acc ψ ρp hsat).mono

/-- **The carrier is a fixed point**, componentwise. -/
theorem carrier_eq (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) :
    D.Φ ψ ρp (D.carrier ψ ρp) c = D.carrier ψ ρp c :=
  lfpTuple_eq (h.closed hsat) (h.mono hsat) (h.maps ψ ρp hsat) hc

/-- **The carrier's case analysis**: an element of component `c`'s
carrier is the injection of a spine fitting one of `c`'s constructors
at the carrier. -/
theorem carrier_case (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) {t : V}
    (ht : t ∈ˢ D.idx ψ ρp c) {x : V} (hx : x ∈ˢ app (D.carrier ψ ρp c) t) :
    ∃ j fs, D.HFits ψ ρp (D.carrier ψ ρp) t c j fs ∧ x = D.inj ψ c j fs := by
  rw [← h.carrier_eq hsat hc] at hx
  exact (h.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _ _) c hc t ht x).mp hx


/-- **The fibre in hole form**: component `c`'s fibre at `(X, t)` is the
set of injections of the spines fitting one of `c`'s constructors'
readings with holes at the hole frame of `X`. -/
theorem fibre_holes (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {c : Nat} (hc : c < D.N) {t : V}
    (ht : t ∈ˢ D.idx ψ ρp c) (x : V) :
    x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs :=
  h.fibre ψ ρp hsat X hX c hc t ht x

end LfpClause

end ConLeche.Model
