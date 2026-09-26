module

public import ConLeche.Semantics.Tower.FixTower
public import ConLeche.Semantics.SubstAV
import ConLeche.Semantics.Univ
import ConLeche.SetTheory.Derive.LfpTuple

@[expose] public section

/-!
# The leaves of a block of `k` recursive families

The non-dependent tuple value; the type-former leaf of a block; the
block functor's laws; the block operator's hole chains.
-/

/-!
## The non-dependent tuple VALUE

`ndTowerAV` (`Semantics/BasisType.lean`) spells the non-dependent pair
tower's TYPE; the block carrier's leaf also has to spell an inhabitant
of one — the operator tuple `⟨λ t. Σ_j …⟩_m` that `lfpTuple k` takes as
its second argument.  `ndMkTowerAV` is that inhabitant's spelling, the
`.psigmaMk [r, r]` tower over the same component types, and this module
carries its two laws (its value is the uniform tupler `mkTower` of the
components' values; it is graded) plus the set-level membership
`ndMkTowerSet_mem` that puts it in `ndTowerSet`.

The type arguments of `.psigmaMk` are NOT junk: the pinned pair's value
computes only at a member of the component's type and a member of the
tail tower's, which is exactly what the tuple's own typing gives.  The
fibre argument is a `λ` whose body is the TAIL's type tower, so that
tower starts at depth `1` — the reason `ndTowerAV` lifts its components
to their own depth itself.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower (mkTower projS)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The value -/

/-- The non-dependent tuple value at level `r`: `⟨G s, …, G (s+n-1)⟩`,
with the component TYPES `Gty` at the base frame (the tail tower lifts
its own components past the fibre binder). -/
def ndMkTowerAV (r : Nat) (Gty G : Nat → AnnotTerm) : Nat → Nat → AnnotTerm
  | _, 0 => .const .punitUnit [r]
  | s, n + 1 =>
    AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]

/-- The tuple value's set: the uniform tupler over the components. -/
noncomputable def ndMkTowerSet (g : Nat → V) : Nat → Nat → V
  | _, 0 => pt
  | s, n + 1 => spair (g s) (ndMkTowerSet g (s + 1) n)

theorem ndMkTowerSet_eq_mkTower (g : Nat → V) :
    ∀ (n s : Nat), ndMkTowerSet g s n = mkTower ((List.range n).map fun i => g (s + i))
  | 0, _ => rfl
  | n + 1, s => by
    show spair (g s) (ndMkTowerSet g (s + 1) n) = _
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show _ = mkTower (g (s + 0) :: _)
    rw [Nat.add_zero, ndMkTowerSet_eq_mkTower g n (s + 1)]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    show g (s + 1 + i) = g (s + (i + 1))
    rw [show s + 1 + i = s + (i + 1) from by omega]

/-- **Intro**: a tuple whose components sit in the tower's is a member
of the tower's carrier. -/
theorem ndMkTowerSet_mem {r : Nat} (hr : r ≠ 0) {F g : Nat → V} :
    ∀ (n s : Nat), (∀ m, m < s + n → g m ∈ˢ F m) →
      ndMkTowerSet g s n ∈ˢ ndTowerSet V r F s n
  | 0, _, _ => pt_mem_unitSet
  | n + 1, s, hg => by
    show spair (g s) (ndMkTowerSet g (s + 1) n)
      ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n
    exact spair_mem hr (hg s (by omega))
      (ndMkTowerSet_mem hr n (s + 1) fun m hm => hg m (by omega))

theorem ndMkTowerSet_zero (g : Nat → V) (n : Nat) :
    ndMkTowerSet g 0 n = mkTower ((List.range n).map g) := by
  rw [ndMkTowerSet_eq_mkTower]
  congr 1
  exact List.map_congr_left fun i _ => by rw [Nat.zero_add]

theorem projS_ndMkTowerSet {g : Nat → V} :
    ∀ (n s i : Nat), i < n → projS i (ndMkTowerSet g s n) = g (s + i)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by
    show sfst (spair (g s) (ndMkTowerSet g (s + 1) n)) = g (s + 0)
    rw [sfst_spair, Nat.add_zero]
  | n + 1, s, i + 1, hi => by
    show projS i (ssnd (spair (g s) (ndMkTowerSet g (s + 1) n))) = g (s + (i + 1))
    rw [ssnd_spair, projS_ndMkTowerSet n (s + 1) i (Nat.lt_of_succ_lt_succ hi),
      show s + 1 + i = s + (i + 1) from by omega]

/-! ## The pinned pair constructor's four-step product -/

/-- The four-step product `psigmaMk.{r,r}` inhabits, at the joint level
`max r r = r`. -/
theorem psigmaMkV_rr_mem {r : Nat} (hr : r ≠ 0) :
    psigmaMkV V r r ∈ˢ piR r (univ r : V) fun A =>
      piR r (psigmaFibreSpace V r A) fun B =>
        piR r A fun a => piR r (SetTheory.app B a) fun _ =>
          sigmaSet r A fun x => SetTheory.app B x := by
  have hmax : Nat.max r r = r := Nat.max_self r
  rw [psigmaMkV, hmax]
  exact lamR_mem fun A _ => lamR_mem fun B _ => lamR_mem fun a ha =>
    lamR_mem fun b hb => spair_mem hr ha hb

/-! ## The tuple value's two laws -/

/-- **The tuple value reads back as the uniform tupler of its
components, and is graded.**  Both halves at once: the grading's app
slots need the value's own memberships. -/
theorem ndMkTowerAV_facts {r : Nat} (hr : r ≠ 0) {Gty G : Nat → AnnotTerm} {F g : Nat → V}
    {ρ : Nat → V} :
    ∀ (n s : Nat),
      (∀ m, m < s + n → interp V ρ (Gty m) = F m) →
      (∀ m, m < s + n → WellDenoted V ρ (Gty m)) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      (∀ m, m < s + n → interp V ρ (G m) = g m) →
      (∀ m, m < s + n → WellDenoted V ρ (G m)) →
      (∀ m, m < s + n → g m ∈ˢ F m) →
      interp V ρ (ndMkTowerAV r Gty G s n) = ndMkTowerSet g s n ∧
        WellDenoted V ρ (ndMkTowerAV r Gty G s n)
  | 0, _, _, _, _, _, _, _ => ⟨rfl, trivial⟩
  | n + 1, s, hGty, hGtyok, hF, hG, hGok, hg => by
    have hvac : ¬ r + 1 = 0 := Nat.succ_ne_zero r
    have hA : interp V ρ (Gty s) = F s := hGty s (by omega)
    have hAu : interp V ρ (Gty s) ∈ˢ (univ r : V) := hA ▸ hF s (by omega)
    have htail : ∀ x : V, interp V (cons x ρ) (ndTowerAV r Gty (s + 1) 1 n)
        = ndTowerSet V r F (s + 1) n := fun x =>
      ndTowerAV_interp V n (s + 1) 1 (cons x ρ)
        (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun m hm => hGty m (by omega))
        (fun m hm => hF m (by omega))
    have hBv : interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n))
        = lamR (r + 1) (interp V ρ (Gty s))
            fun _ => ndTowerSet V r F (s + 1) n := by
      rw [interp_lam]
      exact lamR_congr fun x _ => htail x
    have hBmem : interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n))
        ∈ˢ psigmaFibreSpace V r (interp V ρ (Gty s)) := by
      rw [hBv]
      show lamR (r + 1) (interp V ρ (Gty s)) (fun _ => ndTowerSet V r F (s + 1) n)
        ∈ˢ piR (r + 1) (interp V ρ (Gty s)) (fun _ => (univ r : V))
      exact lamR_mem fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hBok : WellDenoted V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)) := by
      rw [WellDenoted_lam]
      refine ⟨hGtyok s (by omega), fun x _ => ?_, fun _ => (univ r : V),
        fun x _ => ?_, fun h0 => absurd h0 hvac⟩
      · exact ndTowerAV_wellDenoted V n (s + 1) 1 (cons x ρ)
          (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun m hm => hGty m (by omega))
          (fun m hm => hGtyok m (by omega)) (fun m hm => hF m (by omega))
      · rw [htail x]
        exact ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hav : interp V ρ (G s) = g s := hG s (by omega)
    have hamem : interp V ρ (G s) ∈ˢ interp V ρ (Gty s) := by rw [hav, hA]; exact hg s (by omega)
    obtain ⟨hbv, hbok⟩ := ndMkTowerAV_facts hr n (s + 1) (fun m hm => hGty m (by omega))
      (fun m hm => hGtyok m (by omega)) (fun m hm => hF m (by omega))
      (fun m hm => hG m (by omega)) (fun m hm => hGok m (by omega))
      (fun m hm => hg m (by omega))
    have hBapp : SetTheory.app (interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)))
        (interp V ρ (G s)) = ndTowerSet V r F (s + 1) n := by
      rw [hBv, app_lamR_pos hvac hamem]
    have hbmem : interp V ρ (ndMkTowerAV r Gty G (s + 1) n)
        ∈ˢ SetTheory.app (interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)))
            (interp V ρ (G s)) := by
      rw [hBapp, hbv]
      exact ndMkTowerSet_mem hr n (s + 1) fun m hm => hg m (by omega)
    -- the four-step application chain
    have hmk : interp V ρ (.const .psigmaMk [r, r]) = psigmaMkV V r r := rfl
    have hchain : AppChainOk (interp V ρ (.const .psigmaMk [r, r]))
        (([Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
           G s, ndMkTowerAV r Gty G (s + 1) n] : List AnnotTerm).map (interp V ρ)) := by
      rw [hmk]
      have hstep := psigmaMkV_rr_mem (V := V) hr
      have h1 := app_mem_piR_pos hr hstep hAu
      have h2 := app_mem_piR_pos hr h1 hBmem
      have h3 := app_mem_piR_pos hr h2 hamem
      intro l hl
      match l, hl with
      | 0, _ => exact ⟨r, univ r, _, hstep, hAu, fun h0 => absurd h0 hr⟩
      | 1, _ =>
        exact ⟨r, psigmaFibreSpace V r (interp V ρ (Gty s)), _, h1, hBmem,
          fun h0 => absurd h0 hr⟩
      | 2, _ => exact ⟨r, interp V ρ (Gty s), _, h2, hamem, fun h0 => absurd h0 hr⟩
      | 3, _ => exact ⟨r, _, _, h3, hbmem, fun h0 => absurd h0 hr⟩
    have hcl := mkAppN_wellDenoted_of_chain (f := (.const .psigmaMk [r, r] : AnnotTerm))
      (args := [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
        G s, ndMkTowerAV r Gty G (s + 1) n]) (σ := ρ) trivial
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hGtyok s (by omega)
        · exact hBok
        · exact hGok s (by omega)
        · exact hbok)
      hchain
    refine ⟨?_, hcl.1⟩
    show interp V ρ (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]) = _
    rw [hcl.2, hmk]
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V r r)
      (interp V ρ (Gty s))) _) _) _ = _
    rw [psigmaMkV_app V hAu hBmem hamem hbmem, if_neg (by rw [show Nat.max r r = r from Nat.max_self r]; exact hr)]
    show spair (interp V ρ (G s)) (interp V ρ (ndMkTowerAV r Gty G (s + 1) n)) = _
    rw [hav, hbv]
    rfl


/-!
## The type-former leaf of a BLOCK of `k` recursive families

A block of `k` mutually recursive families is the least pre-fixed
TUPLE of ONE functor on tuples of families (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`), member `m`'s component
living over its OWN index-tuple set `I_m` at its own index universe
`u_m` — no member tag enters any index set, and a member whose indices
are all propositions keeps `u_m = 0` and the point tuple:

    T_m := λ p⃗ ı⃗_m. proj_m (lfpTuple.{u⃗, w} ⟨I_0, …, I_{k-1}⟩ F) ⟨ı⃗_m⟩
    F   := λ (Xs : ⟨I_0 → Sort w, …⟩). ⟨λ t. Σ_j tower_{m,j}(Xs, t)⟩_m

A recursive field of constructor `j` of member `m` targeting member `c`
reads `proj_c Xs ⟨e⃗⟩` — the target's component of the family tuple at
the target's own index tuple.  Constructor tags stay MEMBER-LOCAL:
member `m`'s sum runs over member `m`'s own constructors,
`sumMkAV w j` with `j` the member-local position.

This module: the spelled pieces, their readings and gradings, the
block's semantic operator, and the leaf's three laws
(`blockTyG_mem/_wellDenoted/_fold`) under one hereditary premise
(`ParamsOkG`); the functor's laws and the hole chains follow below.
-/


open SetTheory SetTheory.Tower
open ConLeche.Term (lv tupleIdxSort tupleFamSort)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The block's level list -/

/-- The block's level instantiation of `lfpTuple k`: one index
universe per member, then the block's own sort. -/
def blockUs (k w : Nat) (uf : Nat → Nat) : List Nat := (List.range k).map uf ++ [w]

theorem blockUs_lt {k w : Nat} {uf : Nat → Nat} {m : Nat} (hm : m < k) :
    lv (blockUs k w uf) m = uf m := by
  unfold blockUs ConLeche.Term.lv
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hm),
    List.getElem?_map, List.getElem?_range hm]
  rfl

theorem blockUs_top (k w : Nat) (uf : Nat → Nat) : lv (blockUs k w uf) k = w := by
  unfold blockUs ConLeche.Term.lv
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The block's family-tuple sort, the numeral every binder of
`lfpTuple k`'s type carries. -/
abbrev blockR (k w : Nat) (uf : Nat → Nat) : Nat := tupleFamSort k (blockUs k w uf)

/-- The block's index-tuple sort. -/
abbrev blockS (k w : Nat) (uf : Nat → Nat) : Nat := tupleIdxSort (blockUs k w uf)

theorem blockR_ne_zero (k w : Nat) (uf : Nat → Nat) : blockR k w uf ≠ 0 :=
  tupleFamSort_ne_zero k _

theorem blockS_ne_zero (k w : Nat) (uf : Nat → Nat) : blockS k w uf ≠ 0 :=
  tupleIdxSort_ne_zero _


/-! ## The operator, the carrier tuple, and the leaf -/

/-- Member `m`'s arm of the block operator, under the family-tuple
binder: `λ (t : I_m). Σ_j tower_{m,j}(Xs, t)`. -/
def blockArmG (w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : AnnotTerm :=
  .lam (w + 1) ((idxTyAV (uf m) (Idss m)).liftN 1 0)
    (sumBodyAV w (Chs m))

/-- The family tuple's type, spelled at the block's own index sets
(`Fams` at the concrete `⟨I_0, …⟩` rather than at a bound tuple). -/
def famsTyBAV (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) : AnnotTerm :=
  ndTowerAV (blockR k w uf) (fun m => famTyAV (uf m) w (Idss m)) 0 0 k

/-- The index-set tuple `⟨I_0, …, I_{k-1}⟩`. -/
def idxTupAV (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) : AnnotTerm :=
  ndMkTowerAV (blockS k w uf) (fun m => .sort (uf m)) (fun m => idxTyAV (uf m) (Idss m)) 0 k

/-- **The block's operator**: ONE λ over the family tuple, the tuple of
the members' arms. -/
def blockFunG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm)) :
    AnnotTerm :=
  .lam (blockR k w uf) (famsTyBAV k w uf Idss)
    (ndMkTowerAV (blockR k w uf) (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
      (fun m => blockArmG w uf Idss Chs m) 0 k)

/-- The block's carrier tuple: `lfpTuple k` at the index-set tuple and
the operator. -/
def blockBodyG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm)) :
    AnnotTerm :=
  AnnotTerm.mkAppN (.const (.lfpTuple k) (blockUs k w uf))
    [idxTupAV k w uf Idss, blockFunG k w uf Idss Chs]

/-- **Member `m`'s type-former leaf**: the λ-tower over the parameter
and index domains, the carrier tuple's `m`-th component at the tuple of
the index variables. -/
def blockTyG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (pps : List (Nat × Nat × AnnotTerm)) (m : Nat) : AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2))
    (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
        (Idss m).length 0))
      (mkTowerGo (uf m) (Idss m)))

/-! ## The block's semantic operator -/

/-- The members' index-tuple sets at a parameter frame. -/
noncomputable def blockIdx (uf : Nat → Nat) (ρp : Nat → V) (Idss : Nat → List AnnotTerm) :
    Nat → V := fun m => idxSet (uf m) ρp (Idss m)

/-- The operator's fibre at `(Y, t)` for member `m`, with `Y` the
family tuple AS A VALUE (the frame's family slot, which the chains read
through `projS`). -/
noncomputable def blockStepG (w : Nat) (ρp : Nat → V) (Chs : Nat → List (List AnnotTerm))
    (m : Nat) (Y t : V) : V :=
  sumSet w (sumFibre w (cons t (cons Y ρp)) (Chs m))

/-- **The block's tuple operator**: componentwise the member's own
graph over its own index-tuple set, the argument tuple passed to the
chains as the uniform tupler of its components. -/
noncomputable def blockPhiG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    (Nat → V) → Nat → V :=
  fun Xs m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
    (blockStepG w ρp Chs m (ndMkTowerSet Xs 0 k))

/-- **The block's carrier**: the least pre-fixed tuple of its
operator. -/
noncomputable def blockFamG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    Nat → V :=
  lfpTuple w k (blockIdx uf ρp Idss)
    (blockPhiG k w ρp uf Idss Chs)

/-! ## The premises and the level bookkeeping -/

/-- The members' index telescopes are graded, below `k`. -/
def BlockIdxOk (k : Nat) (uf : Nat → Nat) (ρp : Nat → V) (Idss : Nat → List AnnotTerm) : Prop :=
  ∀ m, m < k → IdxOk (uf m) ρp (Idss m)

/-- The family tuple's carrier at the block's own index sets. -/
noncomputable def famsSpaceB (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) : V :=
  ndTowerSet V (blockR k w uf) (fun m => lfpFamSpace V w (idxSet (uf m) ρp (Idss m))) 0 k

/-- **The X-chains are graded** at every family tuple of the tuple
space and every index tuple of the member. -/
def BlockChainsOkG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    Prop :=
  ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ m, m < k → ∀ t, t ∈ˢ idxSet (uf m) ρp (Idss m) →
    SumFieldsOkB w (cons t (cons Y ρp))
      (Chs m)

section Levels

variable {k w : Nat} {uf : Nat → Nat}

theorem uf_le_levMax {m : Nat} (hm : m < k) :
    uf m ≤ ConLeche.Term.levMax (blockUs k w uf) := by
  have h : lv (blockUs k w uf) m = uf m := blockUs_lt hm
  rw [← h]
  exact ConLeche.Term.lv_le_levMax _ m

theorem univ_uf_mem_blockS {m : Nat} (hm : m < k) :
    (univ (uf m) : V) ∈ˢ (univ (blockS k w uf) : V) :=
  univ_mono (Nat.succ_le_succ (uf_le_levMax hm)) _ (univ_mem_univ _)

theorem famSpace_mem_blockR {m : Nat} (hm : m < k) {I : V} (hI : I ∈ˢ (univ (uf m) : V)) :
    lfpFamSpace V w I ∈ˢ (univ (blockR k w uf) : V) := by
  have h := piR_mem_univ (u := uf m) (v := w + 1) hI (fun _ _ => univ_mem_univ w)
  rw [if_neg (Nat.succ_ne_zero _)] at h
  refine univ_mono ?_ _ h
  refine Nat.max_le_of_le_of_le (Nat.le_trans (uf_le_levMax hm) (Nat.le_max_left _ _)) ?_
  have : w + 1 = lv (blockUs k w uf) k + 1 := by rw [blockUs_top]
  rw [this]
  exact Nat.le_max_right _ _

end Levels

/-! ## The two spelled tuples -/

section Facts

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- **The index-set tuple**: its value, its grading. -/
theorem idxTupAV_facts (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    interp V ρp (idxTupAV k w uf Idss) = ndMkTowerSet (blockIdx uf ρp Idss) 0 k ∧
      WellDenoted V ρp (idxTupAV k w uf Idss) :=
  ndMkTowerAV_facts (blockS_ne_zero k w uf) k 0
    (fun _ _ => rfl) (fun _ _ => trivial)
    (fun m hm => univ_uf_mem_blockS (by omega))
    (fun m hm => (idxTyAV_facts (hI m (by omega))).1)
    (fun m hm => (idxTyAV_facts (hI m (by omega))).2.2)
    (fun m hm => (idxTyAV_facts (hI m (by omega))).2.1)

/-- **The family tuple's type**: its value, its grading. -/
theorem famsTyBAV_facts (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    interp V ρp (famsTyBAV k w uf Idss) = famsSpaceB k w ρp uf Idss ∧
      WellDenoted V ρp (famsTyBAV k w uf Idss) :=
  ⟨ndTowerAV_interp V k 0 0 ρp (shiftE_zero_zero ρp)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).1)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1),
   ndTowerAV_wellDenoted V k 0 0 ρp (shiftE_zero_zero ρp)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).1)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).2.2)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1)⟩

/-- The index-set tuple's components are the members' index sets. -/
theorem projS_idxTup {m : Nat} (hm : m < k) :
    projS m (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) = idxSet (uf m) ρp (Idss m) := by
  rw [projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  rfl

end Facts

/-! ## The operator's reading -/

/-- The block operator's value: one λ over the family tuple, the tuple
of the members' graphs. -/
noncomputable def blockFunVG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    V :=
  lamR (blockR k w uf) (famsSpaceB k w ρp uf Idss) fun Y =>
    ndMkTowerSet (fun m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
      (blockStepG w ρp Chs m Y)) 0 k

section Operator

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

theorem blockStepG_univ (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    blockStepG w ρp Chs m Y t ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB (hok Y hY m hm t ht)

/-- Member `m`'s graph lives in its own family space. -/
theorem blockArmG_mem (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) :
    lamR (w + 1) (idxSet (uf m) ρp (Idss m))
        (blockStepG w ρp Chs m Y)
      ∈ˢ lfpFamSpace V w (idxSet (uf m) ρp (Idss m)) :=
  lamR_mem fun _ ht => blockStepG_univ hok hY hm ht

/-- The frame under the operator's family-tuple binder. -/
theorem idxTyAV_lift1B (h : IdxOk (uf m) ρp (Idss m)) (Y : V) :
    interp V (cons Y ρp) ((idxTyAV (uf m) (Idss m)).liftN 1 0) = idxSet (uf m) ρp (Idss m) ∧
      WellDenoted V (cons Y ρp) ((idxTyAV (uf m) (Idss m)).liftN 1 0) := by
  rw [interp_liftN, WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]
  exact ⟨(idxTyAV_facts h).1, (idxTyAV_facts h).2.2⟩

/-- **A member's arm**: its value and its grading, under the operator's
binder. -/
theorem blockArmG_facts (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) :
    interp V (cons Y ρp) (blockArmG w uf Idss Chs m)
        = lamR (w + 1) (idxSet (uf m) ρp (Idss m))
            (blockStepG w ρp Chs m Y) ∧
      WellDenoted V (cons Y ρp) (blockArmG w uf Idss Chs m) := by
  obtain ⟨hiv, hiok⟩ := idxTyAV_lift1B (m := m) (hI m hm) Y
  constructor
  · unfold blockArmG
    rw [interp_lam, hiv]
    refine lamR_congr fun t ht => ?_
    exact sumBodyAV_interp (hok Y hY m hm t ht)
  · unfold blockArmG
    rw [WellDenoted_lam]
    refine ⟨hiok, fun t ht => ?_, fun _ => (univ w : V), fun t ht => ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hiv] at ht
      exact sumBodyAV_wellDenoted (hok Y hY m hm t ht)
    · rw [hiv] at ht
      rw [sumBodyAV_interp (hok Y hY m hm t ht)]
      exact blockStepG_univ hok hY hm ht

/-- **The block's operator**: its value and its grading. -/
theorem blockFunG_facts (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    interp V ρp (blockFunG k w uf Idss Chs)
        = blockFunVG k w ρp uf Idss Chs ∧
      WellDenoted V ρp (blockFunG k w uf Idss Chs) := by
  obtain ⟨hfv, hfok⟩ := famsTyBAV_facts (w := w) hI
  have hbody : ∀ Y : V, Y ∈ˢ famsSpaceB k w ρp uf Idss →
      interp V (cons Y ρp) (ndMkTowerAV (blockR k w uf)
          (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
          (fun m => blockArmG w uf Idss Chs m) 0 k)
        = ndMkTowerSet (fun m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
            (blockStepG w ρp Chs m Y)) 0 k ∧
      WellDenoted V (cons Y ρp) (ndMkTowerAV (blockR k w uf)
          (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
          (fun m => blockArmG w uf Idss Chs m) 0 k) := by
    intro Y hY
    have hty : ∀ m, m < k →
        interp V (cons Y ρp) ((famTyAV (uf m) w (Idss m)).liftN 1 0)
          = lfpFamSpace V w (idxSet (uf m) ρp (Idss m)) := fun m hm => by
      rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
      exact (famTyAV_facts (hI m hm)).1
    refine ndMkTowerAV_facts (blockR_ne_zero k w uf) k 0
      (fun m hm => hty m (by omega)) (fun m hm => ?_)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1)
      (fun m hm => (blockArmG_facts hI hok hY (by omega)).1)
      (fun m hm => (blockArmG_facts hI hok hY (by omega)).2)
      (fun m hm => blockArmG_mem hok hY (by omega))
    rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]
    exact (famTyAV_facts (w := w) (hI m (by omega))).2.2
  refine ⟨?_, ?_⟩
  · unfold blockFunG blockFunVG
    rw [interp_lam, hfv]
    exact lamR_congr fun Y hY => (hbody Y hY).1
  · unfold blockFunG
    rw [WellDenoted_lam]
    refine ⟨hfok, fun Y hY => ?_, fun _ => famsSpaceB k w ρp uf Idss, fun Y hY => ?_,
      fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
    · rw [hfv] at hY; exact (hbody Y hY).2
    · rw [hfv] at hY
      rw [(hbody Y hY).1]
      exact ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0
        fun m hm => blockArmG_mem hok hY (by omega)

end Operator

/-! ## The carrier tuple's reading -/

section Body

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

theorem lfpFamSpace_eq' (w : Nat) (I : V) : lfpFamSpace V w I = famSpace w I :=
  piR_pos (Nat.succ_ne_zero w)

/-- The spelled index tuple inhabits the constant's first domain. -/
theorem idxTup_mem (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    ndMkTowerSet (blockIdx uf ρp Idss) 0 k
      ∈ˢ tupleSortsSpace V k (blockUs k w uf) :=
  ndMkTowerSet_mem (blockS_ne_zero k w uf) k 0 fun m hm => by
    have hmk : m < k := by omega
    rw [blockUs_lt (w := w) hmk]
    exact (idxTyAV_facts (hI m hmk)).2.1

/-- At the spelled index tuple the constant's family-tuple space IS the
block's own. -/
theorem tupleFamsSpace_eq (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) :
    tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k)
      = famsSpaceB k w ρp uf Idss := by
  unfold tupleFamsSpace famsSpaceB
  refine ndTowerSet_congr V k 0 fun m hm => ?_
  have hmk : m < k := by omega
  rw [projS_idxTup hmk, blockUs_top]

/-- The block's operator inhabits the constant's second domain. -/
theorem blockFunVG_mem (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (blockR k w uf) (famsSpaceB k w ρp uf Idss)
        fun _ => famsSpaceB k w ρp uf Idss :=
  lamR_mem fun Y hY =>
    ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun m hm => blockArmG_mem hok hY (by omega)

/-- **The induced tuple operator IS the block's**, on the tuple space
and below `k` — the congruence `lfpTuple_congr` consumes. -/
theorem tupleOpV_blockFunVG {Xs : Nat → V} (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) {m : Nat} (hm : m < k) :
    tupleOpV V k (blockFunVG k w ρp uf Idss Chs) Xs m
      = blockPhiG k w ρp uf Idss Chs Xs m := by
  have hmem : ndMkTowerSet Xs 0 k ∈ˢ famsSpaceB k w ρp uf Idss :=
    ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun c hc => by
      rw [lfpFamSpace_eq']
      exact hXs c (by omega)
  show projS m (SetTheory.app _ (mkTower ((List.range k).map Xs))) = _
  rw [← ndMkTowerSet_zero]
  unfold blockFunVG
  rw [app_lamR_pos (blockR_ne_zero k w uf) hmem, projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  rfl

/-- The constant's application at the block's two spelled arguments. -/
theorem blockBodyG_app (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    SetTheory.app (SetTheory.app (lfpTupleV V k (blockUs k w uf))
        (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        (blockFunVG k w ρp uf Idss Chs)
      = ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k := by
  have hIs := idxTup_mem (w := w) hI
  have hF : blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [tupleFamsSpace_eq k w ρp uf Idss]; exact blockFunVG_mem hok
  rw [lfpTupleV_app V hIs hF,
    ndMkTowerSet_zero (blockFamG k w ρp uf Idss Chs) k]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  have hmk : m < k := List.mem_range.mp hm
  rw [blockUs_top]
  refine lfpTuple_congr (fun c hc => projS_idxTup hc) (fun X hX c hc => ?_) hmk
  have hX' : InTupleSpace w k (blockIdx uf ρp Idss) X := fun c hc => by
    have h : X c ∈ˢ famSpace w (projS c (ndMkTowerSet (blockIdx uf ρp Idss) 0 k)) := hX c hc
    rwa [projS_idxTup hc] at h
  exact tupleOpV_blockFunVG hX' hc

/-- **The carrier tuple reads to the tuple of the members' carriers.** -/
theorem blockBodyG_interp (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    interp V ρp (blockBodyG k w uf Idss Chs)
      = ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k := by
  have hiv := (idxTupAV_facts (w := w) hI).1
  have hfv := (blockFunG_facts hI hok).1
  show SetTheory.app (SetTheory.app (interp V ρp (.const (.lfpTuple k) (blockUs k w uf)))
    (interp V ρp (idxTupAV k w uf Idss)))
    (interp V ρp (blockFunG k w uf Idss Chs)) = _
  rw [show interp V ρp (.const (.lfpTuple k) (blockUs k w uf))
      = lfpTupleV V k (blockUs k w uf) from rfl, hiv, hfv]
  exact blockBodyG_app hI hok

/-- **The carrier tuple is in the block's family-tuple space**, with
no premise at all: the least pre-fixed tuple is total. -/
theorem blockFamG_tuple_mem (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k
      ∈ˢ famsSpaceB k w ρp uf Idss :=
  ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun m hm => by
    rw [lfpFamSpace_eq']
    exact lfpTuple_mem w k (blockIdx uf ρp Idss) _ m (by omega)

/-- **The carrier tuple is graded.** -/
theorem blockBodyG_wellDenoted (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    WellDenoted V ρp (blockBodyG k w uf Idss Chs) := by
  obtain ⟨hiv, hiok⟩ := idxTupAV_facts (w := w) hI
  obtain ⟨hfv, hfok⟩ := blockFunG_facts hI hok
  have hIs := idxTup_mem (w := w) hI
  have hc : interp V ρp (.const (.lfpTuple k) (blockUs k w uf))
      = lfpTupleV V k (blockUs k w uf) := rfl
  have hF : blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [tupleFamsSpace_eq k w ρp uf Idss]; exact blockFunVG_mem hok
  have hhead : SetTheory.app (interp V ρp (.const (.lfpTuple k) (blockUs k w uf)))
      (interp V ρp (idxTupAV k w uf Idss))
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (piR (tupleFamSort k (blockUs k w uf))
          (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
          fun _ => tupleFamsSpace V k (blockUs k w uf)
            (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [hc, hiv]
    exact app_mem_piR_pos (blockR_ne_zero k w uf) (lfpTupleV_mem V k (blockUs k w uf)) hIs
  show WellDenoted V ρp (.app (.app (.const (.lfpTuple k) (blockUs k w uf)) _) _)
  rw [WellDenoted_app]
  refine ⟨?_, hfok, tupleFamSort k (blockUs k w uf), _, _, hhead, ?_,
    fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, hiok, tupleFamSort k (blockUs k w uf),
      tupleSortsSpace V k (blockUs k w uf), _,
      hc ▸ lfpTupleV_mem V k (blockUs k w uf), hiv ▸ hIs,
      fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
  · rw [hfv]; exact hF

end Body

/-! ## The leaf's three laws -/

/-- The base of member `m`'s leaf premise, at the frame below the
parameters AND the member's index binders: the block's index
telescopes graded there, its X-chains graded there, and the frame's
index tuple fitting the member's telescope. -/
def BlockBaseG (k w : Nat) (ρ : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : Prop :=
  BlockIdxOk k uf (shiftE (Idss m).length 0 ρ) Idss ∧
  BlockChainsOkG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs ∧
  SpineFit (shiftE (Idss m).length 0 ρ) (Idss m) (frameIdx (Idss m).length ρ)

/-- `ParamsOkG`: member `m`'s leaf's one hereditary premise — the
parameter and index telescope graded, `BlockBaseG` at the base. -/
def ParamsOkG (k w : Nat) (ρ : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : List (Nat × Nat × AnnotTerm) → Prop
  | [] => BlockBaseG k w ρ uf Idss Chs m
  | d :: pps => d.2.1 ≠ 0 ∧ WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 →
        ParamsOkG k w (cons a ρ) uf Idss Chs m pps

section Leaf

variable {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- The leaf's body at the base frame: member `m`'s carrier at the
frame's index tuple. -/
theorem blockLeafBodyG_facts {ρ : Nat → V} {m : Nat} (hm : m < k)
    (h : BlockBaseG k w ρ uf Idss Chs m) :
    interp V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m)))
        = SetTheory.app
            (blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m)
            (tupW (uf m) (frameIdx (Idss m).length ρ)) ∧
      interp V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m))) ∈ˢ (univ w : V) ∧
      WellDenoted V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m))) := by
  obtain ⟨hI, hok, hsp⟩ := h
  have hρ : consList (frameIdx (Idss m).length ρ) (shiftE (Idss m).length 0 ρ) = ρ :=
    consList_frameIdx (Idss m).length ρ
  have hbv : interp V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0)
      = ndMkTowerSet (blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs) 0 k := by
    rw [interp_liftN]
    exact blockBodyG_interp hI hok
  have hbok : WellDenoted V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0) := by
    rw [WellDenoted_liftN]
    exact blockBodyG_wellDenoted hI hok
  have hbmem : interp V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0)
      ∈ˢ famsSpaceB k w (shiftE (Idss m).length 0 ρ) uf Idss := by
    rw [hbv]; exact blockFamG_tuple_mem k w _ uf Idss Chs
  have hpv : interp V ρ (projAV m ((blockBodyG k w uf Idss Chs).liftN (Idss m).length 0))
      = blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m := by
    rw [projAV_interp, hbv, projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  have hpok : WellDenoted V ρ (projAV m ((blockBodyG k w uf Idss Chs).liftN (Idss m).length 0)) :=
    projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) m k 0 _ ρ hm
      (fun c hc => famSpace_mem_blockR (by omega)
        (idxTyAV_facts (hI c (by omega))).2.1) hbok hbmem
  have htv : interp V ρ (mkTowerGo (uf m) (Idss m)) = tupW (uf m) (frameIdx (Idss m).length ρ) := by
    have h1 := mkTowerGo_interp (ρp := shiftE (Idss m).length 0 ρ)
      (bs := frameIdx (Idss m).length ρ) (fun _ => (hI m hm).2) hsp
    rw [hρ] at h1
    rw [h1]
    rfl
  have htok : WellDenoted V ρ (mkTowerGo (uf m) (Idss m)) := by
    have h1 := mkTowerGo_wellDenoted (ρp := shiftE (Idss m).length 0 ρ)
      (bs := frameIdx (Idss m).length ρ) (hI m hm).1 hsp
    rwa [hρ] at h1
  have htmem : tupW (uf m) (frameIdx (Idss m).length ρ)
      ∈ˢ idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m) := tupW_mem hsp
  have hfam : blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m
      ∈ˢ famSpace w (idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m)) :=
    lfpTuple_mem w k _ _ m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_app, hpv, htv]
  · rw [interp_app, hpv, htv]
    exact famSpace_app hfam htmem
  · rw [WellDenoted_app]
    refine ⟨hpok, htok, w + 1, idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m),
      fun _ => (univ w : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hpv]
      have := hfam
      rwa [← lfpFamSpace_eq' (V := V) w
        (idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m))] at this
    · rw [htv]; exact htmem

/-- **The leaf inhabits its type's reading.** -/
theorem blockTyG_mem {m : Nat} (hm : m < k) :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkG k w ρ uf Idss Chs m pps →
      interp V ρ (blockTyG k w uf Idss Chs pps m)
        ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], _, h => (blockLeafBodyG_facts hm h).2.1
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => blockTyG_mem hm (h.2.2 a ha))

/-- **The leaf is graded.** -/
theorem blockTyG_wellDenoted {m : Nat} (hm : m < k) :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkG k w ρ uf Idss Chs m pps →
      WellDenoted V ρ (blockTyG k w uf Idss Chs pps m)
  | [], _, h => (blockLeafBodyG_facts hm h).2.2
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam (w + 1) d.2.2 (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
    rw [WellDenoted_lam]
    exact ⟨h.2.1, fun a ha => blockTyG_wellDenoted hm (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => blockTyG_mem hm (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter-and-index
spine the leaf computes member `m`'s carrier at the spine's tuple. -/
theorem blockTyG_fold {m : Nat} (hm : m < k)
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hbase : BlockBaseG k w (consList as ρ) uf Idss Chs m) :
    as.foldl SetTheory.app
        (interp V ρ (blockTyG k w uf Idss Chs pps m))
      = SetTheory.app
          (blockFamG k w (shiftE (Idss m).length 0 (consList as ρ)) uf Idss Chs m)
          (tupW (uf m) (frameIdx (Idss m).length (consList as ρ))) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [blockTyG,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp']
  exact (blockLeafBodyG_facts hm hbase).1

end Leaf

/-!
## The block functor's laws

What the least pre-fixed TUPLE needs of the block's operator: the
family space's components, and that the operator preserves the tuple
space.  The operator is generic in the members' constructor chains
`Chs`; its instance is the hole chains below, and the member's fibre as
the tagged union of its STORED constructors is read at them by the
override law (`Model/Inductives/BlockHoleFold.lean`).
-/


/-! ## The recursive slot at a family tuple -/

section Slot

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The target's component of a tuple of the family space** is a
family over the target's index tuples. -/
theorem projS_mem_famsSpaceB {c : Nat} (hc : c < k) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) :
    projS c Y ∈ˢ lfpFamSpace V w (idxSet (uf c) ρp (Idss c)) := by
  have := projS_mem_ndTowerSet V (blockR_ne_zero k w uf) k 0 hY c hc
  rwa [Nat.zero_add] at this

end Slot

/-! ## The operator preserves the tuple space -/

section Functor

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- A tuple of the tuple space, tupled up, is in the family space. -/
theorem ndMkTowerSet_mem_famsSpaceB {Xs : Nat → V}
    (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) :
    ndMkTowerSet Xs 0 k ∈ˢ famsSpaceB k w ρp uf Idss :=
  ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun c hc => by
    rw [lfpFamSpace_eq']
    exact hXs c (by omega)

theorem projS_ndMkTowerSet_zero {Xs : Nat → V} {c : Nat} (hc : c < k) :
    projS c (ndMkTowerSet Xs 0 k) = Xs c := by
  rw [projS_ndMkTowerSet k 0 c hc, Nat.zero_add]

theorem app_blockPhi {Chs : Nat → List (List AnnotTerm)} {Xs : Nat → V} {m : Nat} {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    SetTheory.app (blockPhiG k w ρp uf Idss Chs Xs m) t
      = blockStepG w ρp Chs m (ndMkTowerSet Xs 0 k) t :=
  app_lamR_pos (Nat.succ_ne_zero w) ht

/-- **The block's operator preserves the tuple space.** -/
theorem blockPhi_maps_of {Chs : Nat → List (List AnnotTerm)}
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    MapsTuple w k (blockIdx uf ρp Idss) (blockPhiG k w ρp uf Idss Chs) := by
  intro X hX m hm
  show lamR (w + 1) (idxSet (uf m) ρp (Idss m)) _ ∈ˢ famSpace w (blockIdx uf ρp Idss m)
  rw [← lfpFamSpace_eq']
  exact lamR_mem fun t ht =>
    blockStepG_univ hok (ndMkTowerSet_mem_famsSpaceB hX) hm ht

end Functor

/-!
## The block operator's HOLE chains

Charter item 2: a block's operator is the interpretation of its
constructor types with HOLES at the members.  A constructor's fields
with holes (`LfpDatum.fields`, `Model/Annot/BlockLfp.lean`) are read at
the parameters, then one variable per member (the holes), then the
earlier fields.  The block's operator term (`blockPhiG`/`blockTyG`,
above) is generic in its chains; this section builds the
chains from the fields with holes, with NO field classification: every
field, whatever it mentions, is the same substitution.

**The hole terms.**  Under the operator's binders (the index tuple `t`
innermost, then the family tuple `Y`, then the parameter frame), member
`m`'s hole is replaced by `holeTmAV`: the λ-tower over the member's own
parameter telescope (read below the parameter frame) and then its index
telescope READ AT THE ACTUAL PARAMETERS, of `Y`'s component `m` at the
tuple of the index variables.  It is graded at every family tuple of the
tuple space (`holeTmAV_wellDenoted`).  It is not the model's hole value
(`LfpDatum.holeVal`, whose index domains follow its own λ-bound
parameters), but the two agree APPLIED TO THE ACTUAL PARAMETERS, which is
the only way a hole occurs (`HoleApp`); the model
tier relates them by `interp_congr_holeApp`.

**The chains.**  Field `i` (below `i` earlier fields) is substituted in
parallel (`AnnotTerm.substAV`) at the cut `i`: hole
variables by the hole terms, the parameter frame's variables moved past
`t` and `Y` (`holeTau`).  The result index readings likewise, below all
fields, as the chain's index equations (`holeEqsAV`).  At a family tuple
`Y` the chain's entries read as the fields at the frame whose holes hold
the hole terms' values (`spineFit_holeEntsAV`, `eqAll_holeEqsAV`), and
the operator's fibre is the injections of the spines fitting them
(`blockStepG_termChs_mem_iff`, generic in terminated chains).
-/


/-! ## Grading crosses a parallel substitution -/

/-- **A substituted term is graded** exactly when the subject is graded
at the substituted valuation, provided the substituted terms are graded
where they are read. -/
theorem WellDenoted_substAV (τ : Nat → AnnotTerm) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V), (∀ j, WellDenoted V (shiftE k 0 ρ) (τ j)) →
      (WellDenoted V ρ (AnnotTerm.substAV τ e k) ↔ WellDenoted V (substE V τ k ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ hτ
    by_cases hi : i < k
    · rw [AnnotTerm.substAV_bvar_lt τ hi]; simp
    · rw [AnnotTerm.substAV_bvar_ge τ (by omega), WellDenoted_liftN]
      simp only [WellDenoted_bvar, iff_true]
      exact hτ _
  | sort u => intro k ρ _; simp [AnnotTerm.substAV]
  | const c us => intro k ρ _; simp [AnnotTerm.substAV]
  | prf => intro k ρ _; simp [AnnotTerm.substAV]
  | app f a ihf iha =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_app, WellDenoted_app, WellDenoted_app, ihf k ρ hτ, iha k ρ hτ,
      interp_substAV, interp_substAV]
  | lam u A b ihA ihb =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_lam, WellDenoted_lam, WellDenoted_lam, ihA k ρ hτ, interp_substAV]
    simp only [ihb (k + 1) _ (hτ' _), interp_substAV, cons_substE]
  | pi u v A B ihA ihB =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_pi, WellDenoted_pi, WellDenoted_pi, ihA k ρ hτ, interp_substAV]
    simp only [ihB (k + 1) _ (hτ' _), cons_substE]
  | eqE a b iha ihb =>
    intro k ρ hτ
    show WellDenoted V ρ (.eqE _ _) ↔ WellDenoted V _ (.eqE _ _)
    rw [WellDenoted_eqE, WellDenoted_eqE, iha k ρ hτ, ihb k ρ hτ]
  | fst e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_fst, WellDenoted_fst, WellDenoted_fst, ih k ρ hτ, interp_substAV]
  | snd e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_snd, WellDenoted_snd, WellDenoted_snd, ih k ρ hτ, interp_substAV]

/-! ## The hole terms -/

/-- **Member `m`'s hole term** under the operator's binders `t`, `Y`
(then the parameter frame): the λ-tower over the member's own parameter
telescope `Ps` (read below the parameter frame) and its index telescope
`Is` read at the ACTUAL parameters, of `Y`'s component `m` at the tuple
of the index variables. -/
def holeTmAV (u m : Nat) (Ps Is : List AnnotTerm) : AnnotTerm :=
  mkLamsAV ((liftFields (Ps.length + 2) 0 Ps ++ liftFields (Ps.length + 2) 0 Is).map (1, ·))
    (.app (projAV m (.bvar (Ps.length + Is.length + 1)))
      (mkTowerGo u (liftFields (Ps.length + 2) 0 Is)))

/-- **The hole substitution**: variable `j < k` (member `k - 1 - j`'s
hole: the last member is innermost) by that member's hole term, a
parameter-frame variable `k + j` moved past `t` and `Y`. -/
def holeTau (k : Nat) (H : Nat → AnnotTerm) : Nat → AnnotTerm :=
  fun j => if j < k then H (k - 1 - j) else .bvar (j - k + 2)

/-- A constructor's fields with holes as chain entries: field `i`
substituted at the cut `i`. -/
def holeEntsAV (k : Nat) (H : Nat → AnnotTerm) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | i, F :: Fs => AnnotTerm.substAV (holeTau k H) F i :: holeEntsAV k H (i + 1) Fs

/-- A constructor's result index readings with holes as the chain's
index equations (below its `nF` fields). -/
def holeEqsAV (k : Nat) (H : Nat → AnnotTerm) (nIdx nF : Nat) (Es : List AnnotTerm) :
    List (AnnotTerm × AnnotTerm) :=
  (List.range nIdx).map fun l =>
    (AnnotTerm.substAV (holeTau k H) (Es.getD l default) nF, projAV l (.bvar nF))

/-- **Terminated chains**: per member, per constructor, the entries and
then the index equations. -/
def termChs (Ents : Nat → List (List AnnotTerm))
    (Eqs : Nat → List (List (AnnotTerm × AnnotTerm))) : Nat → List (List AnnotTerm) :=
  fun m => (List.range (Ents m).length).map fun j =>
    (Ents m).getD j [] ++ [idxEqAV ((Eqs m).getD j [])]

/-- **The block's hole chains**: member `m`'s constructors' fields with
holes `Fsss m` and result index readings `Esss m`, member `m` having
`nIdxs m` indices, the holes the terms `H`. -/
def holeChs (k : Nat) (H : Nat → AnnotTerm) (nIdxs : Nat → Nat)
    (Fsss Esss : Nat → List (List AnnotTerm)) : Nat → List (List AnnotTerm) :=
  termChs (fun m => (Fsss m).map (holeEntsAV k H 0))
    (fun m => (List.range (Fsss m).length).map fun j =>
      holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []))

omit [SetTheory V] in
theorem holeEntsAV_length (k : Nat) (H : Nat → AnnotTerm) :
    ∀ (i : Nat) (Fs : List AnnotTerm), (holeEntsAV k H i Fs).length = Fs.length
  | _, [] => rfl
  | i, _ :: Fs => by simp [holeEntsAV, holeEntsAV_length k H (i + 1) Fs]


/-! ## Reading the hole chains -/

/-- **The substituted valuation IS the hole frame**: at the operator's
frame, position `j < k` holds member `k - 1 - j`'s hole term's value,
the rest is the parameter frame. -/
theorem substE_holeTau {k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {t Y : V}
    {hv : Nat → V} (hH : ∀ m, m < k → interp V (cons t (cons Y ρp)) (H m) = hv m) :
    substE V (holeTau k H) 0 (cons t (cons Y ρp)) = consList ((List.range k).map hv) ρp := by
  funext j
  have hlen : ((List.range k).map hv).length = k := by simp
  unfold substE
  rw [if_neg (Nat.not_lt_zero _), shiftE_zero_zero, Nat.sub_zero]
  unfold holeTau
  by_cases hj : j < k
  · rw [if_pos hj, hH _ (by omega), consList_getD_of_lt _ _ _ (by rw [hlen]; exact hj), hlen,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rw [if_neg hj, interp_bvar]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + k := ⟨j - k, by omega⟩
    rw [show i + k - k + 2 = i + 2 by omega]
    have := consList_apply_add ((List.range k).map hv) ρp i
    rw [hlen] at this
    rw [this]
    rfl

/-- **The entries fit where the fields with holes fit** at the frame the
substitution produces, below any common prefix. -/
theorem spineFit_holeEntsAV (k : Nat) (H : Nat → AnnotTerm) :
    ∀ (Fs : List AnnotTerm) (as : List V) (σ : Nat → V) (fs : List V),
      SpineFit (consList as σ) (holeEntsAV k H as.length Fs) fs ↔
        SpineFit (consList as (substE V (holeTau k H) 0 σ)) Fs fs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | F :: Fs, as, σ, f :: fs => by
    show (f ∈ˢ interp V (consList as σ) (AnnotTerm.substAV (holeTau k H) F as.length) ∧ _) ↔
      (f ∈ˢ interp V _ F ∧ _)
    have hs : substE V (holeTau k H) as.length (consList as σ)
        = consList as (substE V (holeTau k H) 0 σ) := by
      have := substE_consList V (holeTau k H) as 0 σ
      rwa [Nat.add_zero] at this
    rw [interp_substAV, hs]
    refine and_congr Iff.rfl ?_
    have := spineFit_holeEntsAV k H Fs (as ++ [f]) σ fs
    rw [List.length_append, List.length_singleton] at this
    rw [consList_append, consList_append] at this
    exact this

/-- **The index equations hold** exactly when the result index readings
with holes, at the hole frame and the fields, are the index tuple's
components. -/
theorem eqAll_holeEqsAV {k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {t Y : V}
    {n nF : Nat} {Es : List AnnotTerm} {fs : List V} (hlen : fs.length = nF) :
    EqAll (consList fs (cons t (cons Y ρp))) (holeEqsAV k H n nF Es) ↔
      ∀ l, l < n → interp V (consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))))
        (Es.getD l default) = projS l t := by
  have hs : substE V (holeTau k H) nF (consList fs (cons t (cons Y ρp)))
      = consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))) := by
    subst hlen
    have := substE_consList V (holeTau k H) fs 0 (cons t (cons Y ρp))
    rwa [Nat.add_zero] at this
  have hproj : ∀ l, interp V (consList fs (cons t (cons Y ρp))) (projAV l (.bvar nF))
      = projS l t := by
    intro l
    subst hlen
    rw [projAV_interp, interp_bvar, Xframe_t]
  unfold EqAll holeEqsAV
  constructor
  · intro h l hl
    have := h _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
    rw [interp_substAV, hs, hproj] at this
    exact this
  · intro h e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    show interp V _ (AnnotTerm.substAV _ _ _) = interp V _ (projAV _ _)
    rw [interp_substAV, hs, hproj]
    exact h l (List.mem_range.mp hl)

/-! ## The operator's fibre at terminated chains -/

/-- **The tagged union of terminated chains, at any frame**: an element
is the injection of a spine fitting one of the entries whose index
equations hold — the tag the chain's position, the point at a
`Prop`-valued sort.  No premise: the chains' grading is not needed to
read the union. -/
theorem sumSet_termChs_mem_iff {w : Nat} {σ : Nat → V}
    {Ents : List (List AnnotTerm)} {Eqs : List (List (AnnotTerm × AnnotTerm))} {x : V} :
    x ∈ˢ sumSet w (sumFibre w σ ((List.range Ents.length).map fun j =>
        Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])) ↔
      ∃ j fs, j < Ents.length ∧ SpineFit σ (Ents.getD j []) fs ∧
        EqAll (consList fs σ) (Eqs.getD j []) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  have hget : ∀ j, ((List.range Ents.length).map fun j =>
      Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])[j]? = if j < Ents.length then
        some (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])]) else none := by
    intro j
    rw [List.getElem?_map]
    split
    · next h => rw [List.getElem?_range h]; rfl
    · next h => rw [List.getElem?_eq_none (by simpa using h)]; rfl
  constructor
  · intro hx
    by_cases hw : w = 0
    · subst hw
      obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
      unfold sumFibre at ha
      rw [hget] at ha
      by_cases hj : j < Ents.length
      · rw [if_pos hj] at ha
        obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
        obtain ⟨fs, -, hsp, hall⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfit)
        exact ⟨j, fs, hj, hsp, hall, by rw [if_pos rfl]⟩
      · rw [if_neg hj] at ha
        exact absurd ha (not_mem_empty _)
    · obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
      unfold sumFibre at ha
      rw [hget] at ha
      by_cases hj : j < Ents.length
      · rw [if_pos hj] at ha
        obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
        obtain ⟨fs, hfs, hsp, hall⟩ := spineFit_append_idxEq.mp hfit
        refine ⟨j, fs, hj, hsp, hall, ?_⟩
        rw [if_neg hw, heta, hfs]
      · rw [if_neg hj] at ha
        exact absurd ha (not_mem_empty _)
  · rintro ⟨j, fs, hj, hsp, hall, rfl⟩
    have hspE : SpineFit σ (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])
        (fs ++ [pt]) := spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩
    have hfib : sumFibre w σ ((List.range Ents.length).map fun j =>
          Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])]) j
        = towerSet w (teleOfFields σ (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])) :=
      sumFibre_of_getElem? (by rw [hget, if_pos hj])
    by_cases hw : w = 0
    · subst hw
      rw [if_pos rfl]
      refine pt_mem_sumSet_zero (i := j) (a := pt) ?_
      rw [hfib]
      exact pt_mem_tower_teleOfFields hspE
    · rw [if_neg hw]
      refine inj_mem hw ?_
      rw [hfib]
      exact mkTower_mem_teleOfFields hw hspE

/-- **The fibre of the operator at terminated chains**: an element is
the injection of a spine fitting one of the member's constructors'
entries whose index equations hold — the tag member-local, the point at
a `Prop`-valued block (`sumSet_termChs_mem_iff` at the operator's
frame). -/
theorem blockStepG_termChs_mem_iff {w : Nat} {ρp : Nat → V}
    {Ents : Nat → List (List AnnotTerm)} {Eqs : Nat → List (List (AnnotTerm × AnnotTerm))}
    {m : Nat} {Y t x : V} :
    x ∈ˢ blockStepG w ρp (termChs Ents Eqs) m Y t ↔
      ∃ j fs, j < (Ents m).length ∧ SpineFit (cons t (cons Y ρp)) ((Ents m).getD j []) fs ∧
        EqAll (consList fs (cons t (cons Y ρp))) ((Eqs m).getD j []) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  unfold blockStepG termChs
  exact sumSet_termChs_mem_iff

/-- **The fibre of the operator at the hole chains**: the injections of
the spines fitting a constructor's fields with holes at the hole frame,
whose result index readings there are the index tuple's components. -/
theorem blockStepG_holeChs_mem_iff {w k : Nat} {ρp : Nat → V} {H : Nat → AnnotTerm}
    {nIdxs : Nat → Nat} {Fsss Esss : Nat → List (List AnnotTerm)}
    {m : Nat} {Y t x : V} :
    x ∈ˢ blockStepG w ρp (holeChs k H nIdxs Fsss Esss) m Y t ↔
      ∃ j fs, j < (Fsss m).length ∧
        SpineFit (substE V (holeTau k H) 0 (cons t (cons Y ρp))) ((Fsss m).getD j []) fs ∧
        (∀ l, l < nIdxs m → interp V (consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))))
          (((Esss m).getD j []).getD l default) = projS l t) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  unfold holeChs
  rw [blockStepG_termChs_mem_iff]
  simp only [List.length_map]
  refine exists_congr fun j => exists_congr fun fs => ?_
  constructor
  · rintro ⟨hj, hsp, hall, rfl⟩
    have hent : ((Fsss m).map (holeEntsAV k H 0)).getD j [] = holeEntsAV k H 0 ((Fsss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]; rfl
    rw [hent] at hsp
    have hsp' := (spineFit_holeEntsAV k H ((Fsss m).getD j []) [] _ fs).mp hsp
    have hlen : fs.length = ((Fsss m).getD j []).length := by
      have := hsp'.length_eq; exact this
    have heq : ((List.range (Fsss m).length).map fun j =>
        holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j [])).getD j []
        = holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
    rw [heq] at hall
    exact ⟨hj, hsp', (eqAll_holeEqsAV hlen).mp hall, rfl⟩
  · rintro ⟨hj, hsp, hall, rfl⟩
    have hent : ((Fsss m).map (holeEntsAV k H 0)).getD j [] = holeEntsAV k H 0 ((Fsss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]; rfl
    have hlen : fs.length = ((Fsss m).getD j []).length := hsp.length_eq
    have heq : ((List.range (Fsss m).length).map fun j =>
        holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j [])).getD j []
        = holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
    refine ⟨hj, ?_, ?_, rfl⟩
    · rw [hent]; exact (spineFit_holeEntsAV k H ((Fsss m).getD j []) [] _ fs).mpr hsp
    · rw [heq]; exact (eqAll_holeEqsAV hlen).mpr hall

/-! ## Grading -/

/-- The hole substitution's terms are graded at the operator's frame when
the hole terms are. -/
theorem holeTau_wellDenoted {k : Nat} {H : Nat → AnnotTerm} {σ : Nat → V}
    (hH : ∀ m, m < k → WellDenoted V σ (H m)) (as : List V) (j : Nat) :
    WellDenoted V (shiftE as.length 0 (consList as σ)) (holeTau k H j) := by
  rw [shiftE_consList]
  unfold holeTau
  split
  · exact hH _ (by omega)
  · simp

/-- **The entries are graded** exactly when the fields with holes are,
at the frame the substitution produces. -/
theorem FieldsOkB_holeEntsAV {w k : Nat} {H : Nat → AnnotTerm} {σ : Nat → V}
    (hH : ∀ m, m < k → WellDenoted V σ (H m)) :
    ∀ (Fs : List AnnotTerm) (as : List V),
      FieldsOkB w (consList as σ) (holeEntsAV k H as.length Fs) ↔
        FieldsOkB w (consList as (substE V (holeTau k H) 0 σ)) Fs
  | [], _ => Iff.rfl
  | F :: Fs, as => by
    have hs : substE V (holeTau k H) as.length (consList as σ)
        = consList as (substE V (holeTau k H) 0 σ) := by
      have := substE_consList V (holeTau k H) as 0 σ
      rwa [Nat.add_zero] at this
    show (WellDenoted V _ (AnnotTerm.substAV _ F _) ∧ _ ∧ _) ↔ (WellDenoted V _ F ∧ _ ∧ _)
    rw [WellDenoted_substAV (holeTau k H) F as.length _ (holeTau_wellDenoted hH as),
      interp_substAV, hs]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_))
    have := FieldsOkB_holeEntsAV (w := w) hH Fs (as ++ [a])
    rw [List.length_append, List.length_singleton, consList_append, consList_append] at this
    exact this

/-- **The index equations are graded** at the operator's frame, at a
fitting field spine. -/
theorem holeEqsAV_ok {u k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {Ids : List AnnotTerm}
    (hI : IdxOk u ρp Ids) {Y t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hH : ∀ m, m < k → WellDenoted V (cons t (cons Y ρp)) (H m)) {bs : List V} {nF : Nat}
    (hlen : bs.length = nF) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList bs (substE V (holeTau k H) 0 (cons t (cons Y ρp)))) E)
    (hEs : Es.length = Ids.length) :
    EqsOk (consList bs (cons t (cons Y ρp))) (holeEqsAV k H Ids.length nF Es) := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < Ids.length := List.mem_range.mp hl
  subst hlen
  have hs : substE V (holeTau k H) bs.length (consList bs (cons t (cons Y ρp)))
      = consList bs (substE V (holeTau k H) 0 (cons t (cons Y ρp))) := by
    have := substE_consList V (holeTau k H) bs 0 (cons t (cons Y ρp))
    rwa [Nat.add_zero] at this
  refine ⟨?_, ?_⟩
  · show WellDenoted V _ (AnnotTerm.substAV _ _ _)
    rw [WellDenoted_substAV (holeTau k H) _ bs.length _ (holeTau_wellDenoted hH bs), hs]
    exact hEok _ (getD_mem_of_lt (by omega))
  · show WellDenoted V _ (projAV l (.bvar bs.length))
    refine projAV_wellDenoted_tower (w := u) (Fs := Ids) (ρ := ρp) (by simp) ?_ hI.2 hl'
    rw [interp_bvar, Xframe_t]
    exact ht

/-- A λ-tower of graph-regime binders over a graded telescope with a
body graded at every fitting spine is graded. -/
theorem mkLamsAV_one_wellDenoted {b : AnnotTerm} :
    ∀ {Ts : List AnnotTerm} {ρ : Nat → V}, FieldsOkB 0 ρ Ts →
      (∀ vs, SpineFit ρ Ts vs → WellDenoted V (consList vs ρ) b) →
      WellDenoted V ρ (mkLamsAV (Ts.map (1, ·)) b)
  | [], _, _, hb => hb [] trivial
  | T :: Ts, ρ, hT, hb => by
    show WellDenoted V ρ (.lam 1 T (mkLamsAV (Ts.map (1, ·)) b))
    rw [WellDenoted_lam]
    refine ⟨hT.1, fun x hx => mkLamsAV_one_wellDenoted (hT.2.2 x hx)
      (fun vs hvs => hb (x :: vs) ⟨hx, hvs⟩),
      fun x => ConLeche.SetTheory.sing (interp V (cons x ρ) (mkLamsAV (Ts.map (1, ·)) b)),
      fun x _ => ConLeche.SetTheory.mem_sing.mpr rfl, fun h => absurd h (by decide)⟩

theorem FieldsOkB_zero_of {w : Nat} :
    ∀ {Ts : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Ts → FieldsOkB 0 ρ Ts
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, fun h0 => absurd rfl h0, fun a ha => FieldsOkB_zero_of (h.2.2 a ha)⟩

theorem FieldsOkB_append_iff {w : Nat} :
    ∀ {A B : List AnnotTerm} {ρ : Nat → V},
      FieldsOkB w ρ A → (∀ vs, SpineFit ρ A vs → FieldsOkB w (consList vs ρ) B) →
      FieldsOkB w ρ (A ++ B)
  | [], _, _, _, hB => hB [] trivial
  | _ :: _, _, _, hA, hB => ⟨hA.1, hA.2.1, fun a ha =>
      FieldsOkB_append_iff (hA.2.2 a ha) fun vs hvs => hB (a :: vs) ⟨ha, hvs⟩⟩

theorem fieldsBound_liftFields {w n : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V},
      FieldsBound w σ (liftFields n k Fs) ↔ FieldsBound w (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsBound, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_)
    rw [cons_shiftE]
    exact fieldsBound_liftFields

section Hole

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The hole term is graded** at the operator's frame at every family
tuple of the tuple space: its parameter binders by the member's own
parameter telescope's grading (below the parameter frame), its index
binders by the member's index telescope's (at the actual parameters),
the application by the tuple space. -/
theorem holeTmAV_wellDenoted (hIall : BlockIdxOk (V := V) k uf ρp Idss) {m : Nat} (hm : m < k)
    {Ps : List AnnotTerm} (hP : FieldsOkB 0 (shiftE Ps.length 0 ρp) Ps)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) (t : V) :
    WellDenoted V (cons t (cons Y ρp)) (holeTmAV (uf m) m Ps (Idss m)) := by
  have hsh : shiftE (Ps.length + 2) 0 (cons t (cons Y ρp)) = shiftE Ps.length 0 ρp := by
    rw [show Ps.length + 2 = Ps.length + 1 + 1 by omega, shiftE_succ_cons, shiftE_succ_cons]
  have hshI : ∀ ps : List V, ps.length = Ps.length →
      shiftE (Ps.length + 2) 0 (consList ps (cons t (cons Y ρp))) = ρp := by
    intro ps hps
    have := shiftE_consList_add ps 2 (cons t (cons Y ρp))
    rw [hps] at this
    rw [this, show (2 : Nat) = 1 + 1 by rfl, shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
  unfold holeTmAV
  refine mkLamsAV_one_wellDenoted ?_ ?_
  · refine FieldsOkB_append_iff ?_ fun ps hps => ?_
    · rw [FieldsOkB_liftFields, hsh]; exact hP
    · have hlen : ps.length = Ps.length := by
        have := hps.length_eq; rwa [liftFields_length] at this
      rw [FieldsOkB_liftFields, hshI ps hlen]
      exact FieldsOkB_zero_of (hIall m hm).1
  · intro vs hvs
    obtain ⟨ps, is, rfl, hps, his⟩ := spineFit_append_split hvs
    have hlen : ps.length = Ps.length := by
      have := hps.length_eq; rwa [liftFields_length] at this
    have hlenI : is.length = (Idss m).length := by
      have := his.length_eq; rwa [liftFields_length] at this
    have hisR : SpineFit ρp (Idss m) is := by
      rw [spineFit_liftFields, hshI ps hlen] at his; exact his
    have hbd : uf m ≠ 0 → FieldsBound (uf m) (consList ps (cons t (cons Y ρp)))
        (liftFields (Ps.length + 2) 0 (Idss m)) := fun _ => by
      rw [fieldsBound_liftFields, hshI ps hlen]; exact (hIall m hm).2
    have hok : FieldsOkB (uf m) (consList ps (cons t (cons Y ρp)))
        (liftFields (Ps.length + 2) 0 (Idss m)) := by
      rw [FieldsOkB_liftFields, hshI ps hlen]; exact (hIall m hm).1
    have hY' : consList (ps ++ is) (cons t (cons Y ρp)) (Ps.length + (Idss m).length + 1) = Y := by
      have := Xframe_X ρp (ps ++ is) t Y
      rwa [List.length_append, hlen, hlenI] at this
    have htv := mkTowerGo_interp hbd his
    rw [← consList_append] at htv
    have hXm : projS m Y ∈ˢ piR (w + 1) (idxSet (uf m) ρp (Idss m)) fun _ => (univ w : V) :=
      projS_mem_famsSpaceB hm hY
    rw [WellDenoted_app]
    refine ⟨?_, ?_, w + 1, idxSet (uf m) ρp (Idss m), fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h (Nat.succ_ne_zero w)⟩
    · have hFu : ∀ c, c < 0 + k → lfpFamSpace V w (idxSet (uf c) ρp (Idss c))
          ∈ˢ (univ (blockR k w uf) : V) := fun c hc =>
        famSpace_mem_blockR (by omega) (idxTyAV_facts (hIall c (by omega))).2.1
      exact projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) m k 0 _ _ hm hFu trivial
        (by rw [interp_bvar, hY']; exact hY)
    · have := mkTowerGo_wellDenoted hok his
      rwa [← consList_append] at this
    · rw [projAV_interp, interp_bvar, hY']; exact hXm
    · rw [htv]
      exact tupW_mem (u := uf m) hisR

end Hole

end ConLeche.Semantics
