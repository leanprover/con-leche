module

public import ConLeche.Model.Inductives.ClassRecKit

public section

/-!
# The step's typing at the generated family (`hstep`, G1-syn)

The graph route's producer at the generated family (`graphRecPre_gen`,
`ClassRecKit.lean`) asks for the STEP's typing, `hstep`: the rule's
residue, read at the fields and at the `ih` values the graph gives,
lands in the motive at the constructor.  At the generated rule the
residue is the MINOR PREMISE applied to the fields and the `ih`s
(`genRb0`), so its typing is the minor premise's own type: a minor of
type `Π f⃗ (ih⃗ : Π a⃗, motive_t e⃗ (f a⃗)), motive_c es mk` applied to
fitting fields and to `ih` values of their binders' types lands in
`motive_c es mk`.  What is left is that the graph's `ih` values ARE of
their binders' types: a generated `ih` is `λ a⃗, rec_t x⃗ e⃗ (f a⃗)`
(`genIhAV`), read at the chain valuation of the graph (`genF`) it is
`λ a⃗, g (tagged t e⃗ (f a⃗))` (the tower's fold), and the graph lands
in the motive at every predecessor — which the call is.

This file proves `hstep` over the minor premise's typing stated
semantically (`hminor`), the class side's call typing (`hihTy`, as in
`genIhs_hcallTy`), the conclusion's reading (`hconcl`: the motive's
variable applied to the index and major variables), and the class
side's `hmk` and index fit.  The `ih` binders' types are
`genIhDomAV` — the generated `ih`'s own telescope over the motive's
variable applied to its arguments, BY CONSTRUCTION the `ih` term's
type.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The residue and the `ih` binders -/

/-- **The generated residue**: at the rule's frame extended by the `ih`
values (depth `nPre + nF + nIh`), the minor premise of prefix position
`minPos` applied to the fields and the `ih` values. -/
@[expose] def genRb0 (nPre minPos nF nIh : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nIh + nF + (nPre - 1 - minPos)))
    (prefVarsAV nF nIh ++ prefVarsAV nIh 0)

/-- **A generated `ih` binder's type**, at the rule's depth `D`: the
`ih`'s telescope over the callee's motive (prefix position `mt`) applied
to the `ih`'s index and major arguments. -/
@[expose] def genIhDomAV (D mt : Nat) (q : IhDatum) : AnnotTerm :=
  mkPisAV (q.2.1.map fun p => (0, p.1, p.2))
    (AnnotTerm.mkAppN (.bvar (D + q.2.1.length - 1 - mt)) (q.2.2.1 ++ [q.2.2.2]))

/-- A prefix variable at a frame extended by `n` values. -/
theorem consList_prefix_getD {xs bs : List V} {ρ : Nat → V} {k : Nat} (hk : k < xs.length) :
    consList (xs ++ bs) ρ (bs.length + xs.length - 1 - k) = xs.getD k pt := by
  have hlen : (xs ++ bs).length = bs.length + xs.length := by simp; omega
  rw [consList_getD_of_lt _ _ _ (by omega), hlen,
    show bs.length + xs.length - 1 - (bs.length + xs.length - 1 - k) = k by omega,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]

theorem interp_genRb0 {ρ : Nat → V} {xs fs hs : List V} {minPos : Nat}
    (hmin : minPos < xs.length) :
    interp V (consList hs (consList (xs ++ fs) ρ))
        (genRb0 xs.length minPos fs.length hs.length)
      = (fs ++ hs).foldl SetTheory.app (xs.getD minPos pt) := by
  rw [genRb0, interp_mkAppN, ← List.foldl_map]
  have h1 : (prefVarsAV fs.length hs.length).map (interp V (consList hs (consList (xs ++ fs) ρ)))
      = fs := by
    have := interp_prefVarsAV (V := V) (xs := fs) (bs := hs) (ρ := consList xs ρ) rfl
    rw [consList_append] at this
    rw [consList_append]
    exact this
  have h2 : (prefVarsAV hs.length 0).map (interp V (consList hs (consList (xs ++ fs) ρ))) = hs := by
    have := interp_prefVarsAV (V := V) (xs := hs) (bs := []) (ρ := consList (xs ++ fs) ρ) rfl
    simpa using this
  rw [List.map_append, h1, h2]
  congr 1
  show consList hs (consList (xs ++ fs) ρ) (hs.length + fs.length + (xs.length - 1 - minPos)) = _
  rw [← consList_append, List.append_assoc,
    show hs.length + fs.length + (xs.length - 1 - minPos)
      = (fs ++ hs).length + xs.length - 1 - minPos by simp; omega]
  exact consList_prefix_getD hmin

/-- **A λ-tower inhabits the Π-tower of the same binder data**, as soon
as its body inhabits the codomain at every fitting spine — at two frames
that agree below the telescope's bound. -/
theorem lamTower_mem_piTower :
    ∀ (tl : List (Nat × AnnotTerm)) {D : Nat} {σ σ' : Nat → V} {b C : AnnotTerm},
      FieldsBelow D (tl.map (·.2)) → (∀ i, i < D → σ i = σ' i) →
      (∀ bs, SpineFit σ' (tl.map (·.2)) bs →
        interp V (consList bs σ) b ∈ˢ interp V (consList bs σ') C) →
      interp V σ (mkLamsAV tl b) ∈ˢ interp V σ' (mkPisAV (tl.map fun p => (0, p.1, p.2)) C)
  | [], D, σ, σ', b, C, _, _, h => by simpa [mkLamsAV, mkPisAV] using h [] trivial
  | (v, A) :: tl, D, σ, σ', b, C, hb, hag, h => by
    show lamR v (interp V σ A) (fun x => interp V (cons x σ) (mkLamsAV tl b))
      ∈ˢ piR v (interp V σ' A) (fun x => interp V (cons x σ') (mkPisAV _ C))
    have hA : interp V σ A = interp V σ' A := interp_congr_below V A D σ σ' hb.1 hag
    rw [hA]
    refine lamR_mem fun x hx => ?_
    refine lamTower_mem_piTower tl (D := D + 1) hb.2 (fun i hi => ?_) (fun bs hbs => ?_)
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have := h (x :: bs) ⟨hx, hbs⟩
      simpa [consList_cons] using this

/-! ## `hstep` -/

section Step

variable {K : Nat} {ρ : Nat → V} {rP nCt : Nat → Nat}
  {pre idxB : Nat → List (Nat × Nat × AnnotTerm)} {majB : Nat → Nat × Nat × AnnotTerm}
  {uX : Nat → Nat} {concl : Nat → AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {injX : Nat → Nat → List V → V} {ihd : Nat → Nat → List IhDatum}

omit [SetTheory V] in
/-- Frames agreeing below `D` still agree below `D + |bs|` once extended
by the same spine. -/
theorem consList_congr_below : ∀ (bs : List V) {σ σ' : Nat → V} {D : Nat},
    (∀ i, i < D → σ i = σ' i) → ∀ i, i < D + bs.length → consList bs σ i = consList bs σ' i
  | [], _, _, _, h, i, hi => h i (by simpa using hi)
  | b :: bs, σ, σ', D, h, i, hi => by
    rw [consList_cons, consList_cons]
    refine consList_congr_below bs (D := D + 1) (fun k hk => ?_) i (by simp at hi; omega)
    cases k with
    | zero => rfl
    | succ k => exact h k (by omega)

set_option maxHeartbeats 1600000 in
/-- **`hstep` at the generated family.**  The residue is the minor
premise applied to the fields and the graph's `ih` values; the `ih`
values inhabit their binders' types (the graph lands in the motive at
the calls, which are predecessors); the minor premise's typing
(`hminor`) then lands the residue in `motive_c es mk`, which is the
kit's motive at the constructor (`hconcl`, the index fit and `hmk`). -/
theorem genHstep (P : List (Nat × Nat × AnnotTerm))
    (hpre : ∀ c, c < K → pre c = P) (hpl : ∀ c, c < K → rP c = P.length)
    (motPos : Nat → Nat) (minPos : Nat → Nat → Nat)
    (hmot : ∀ c, c < K → motPos c < P.length)
    (hmin : ∀ c, c < K → ∀ j, j < nCt c → minPos c j < P.length)
    (hIdx : ∀ c, c < K → ∀ xs, SpineFit ρ (genPdoms pre c) xs →
      IdxOk (uX c) (consList xs ρ) (genIdxDoms idxB c))
    (hcal : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j, q.1 < K)
    (hbelow : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j,
      IhDatumBelow (P.length + (fdoms c j).length) q)
    (hihTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (genPdoms pre c).length →
      SpineFit ρ (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      ∀ q ∈ ihd c j, ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
        SpineFit (consList xs ρ) (genIdxDoms idxB q.1)
            (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))) ∧
          interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2
            ∈ˢ interp V (consList (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))))
                (consList xs ρ)) (majB q.1).2.2)
    (hconcl : ∀ c, c < K → ∀ (xs zs : List V) (x : V), xs.length = P.length →
      zs.length = (idxB c).length →
      interp V (consList (xs ++ (zs ++ [x])) ρ) (concl c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (motPos c) pt))
    (hminor : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs, SpineFit ρ (P.map (·.2.2)) xs →
      ∀ fs, SpineFit (consList xs ρ) (fdoms c j) fs →
      ∀ hs : List V, hs.length = (ihd c j).length →
      (∀ (l : Nat) (q : IhDatum) (h : V), (ihd c j)[l]? = some q → hs[l]? = some h →
        h ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV (P.length + (fdoms c j).length) (motPos q.1) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (minPos c j) pt)
        ∈ˢ ((es c j).map (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ) (mk c j)]).foldl SetTheory.app
            (xs.getD (motPos c) pt))
    (hesFit : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (genPdoms pre c).length →
      SpineFit ρ (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      SpineFit (consList xs ρ) (genIdxDoms idxB c)
        ((es c j).map (interp V (consList (xs ++ fs) ρ))))
    (hmk : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (genPdoms pre c).length →
      SpineFit ρ (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      interp V (consList (xs ++ fs) ρ) (mk c j) = injX c j fs) :
    ∀ xs : List V, ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ genIs ρ pre idxB uX xs c → genFit ρ uX fdoms es xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG (genIs ρ pre idxB uX) (genCr ρ pre idxB majB uX) K
          (genCall uX (genIhCallAt ρ ihd)) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl uX (fun c => (idxB c).length) ρ xs v) →
      interp V (consList (genIhv K ρ rP pre idxB majB uX
            (fun c j => (ihd c j).map (genIhAV K P.length (P.length + (fdoms c j).length)))
            xs c j fs g)
          (consList (xs ++ fs) ρ))
          (genRb0 P.length (minPos c j) (fdoms c j).length (ihd c j).length)
        ∈ˢ blockRecMot K concl uX (fun c => (idxB c).length) ρ xs (tagged c i (injX c j fs)) := by
  intro xs c hc j hj i fs hi hfit g hg
  have hxs : SpineFit ρ (genPdoms pre c) xs := genIs_fits hi
  have hxsP : SpineFit ρ (P.map (·.2.2)) xs := by rw [genPdoms, hpre c hc] at hxs; exact hxs
  have hxl : xs.length = P.length := by rw [hxsP.length_eq, List.length_map]
  have hxl' : xs.length = (genPdoms pre c).length := by
    rw [hxl, genPdoms, hpre c hc, List.length_map]
  obtain ⟨hfs, rfl⟩ := hfit
  have hsp : SpineFit ρ (genPdoms pre c ++ fdoms c j) (xs ++ fs) := SpineFit.append hxs hfs
  have hfl : fs.length = (fdoms c j).length := hfs.length_eq
  have hDlen : (xs ++ fs).length = P.length + (fdoms c j).length := by simp [hxl, hfl]
  have hagree : ∀ i, i < P.length + (fdoms c j).length →
      consList (xs ++ fs) (chainFrame K (genF ρ rP pre idxB majB uX g) ρ) i
        = consList (xs ++ fs) ρ i := by
    intro i hi'
    rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]
  -- the graph's `ih` values inhabit their binders' types
  have hih : ∀ q ∈ ihd c j,
      interp V (consList (xs ++ fs) (chainFrame K (genF ρ rP pre idxB majB uX g) ρ))
          (genIhAV K P.length (P.length + (fdoms c j).length) q)
        ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV (P.length + (fdoms c j).length) (motPos q.1) q) := by
    intro q hq
    obtain ⟨hbT, hbA⟩ := hbelow c hc j hj q hq
    have ht := hcal c hc j hj q hq
    refine lamTower_mem_piTower q.2.1 hbT hagree fun bs hbs => ?_
    have hbl : bs.length = q.2.1.length := by rw [hbs.length_eq, List.length_map]
    -- the arguments, read at the base frame
    have hargR : ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        interp V (consList bs (consList (xs ++ fs) (chainFrame K (genF ρ rP pre idxB majB uX g) ρ)))
            e = interp V (consList bs (consList (xs ++ fs) ρ)) e :=
      fun e he => interp_congr_below V e _ _ _ (hbA e he)
        (fun i hi' => consList_congr_below bs hagree i (by rw [hbl]; exact hi'))
    obtain ⟨is, his_def⟩ : ∃ is, is = q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))) :=
      ⟨_, rfl⟩
    obtain ⟨x, hx_def⟩ : ∃ x, x = interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2 :=
      ⟨_, rfl⟩
    -- the call, and its typing
    have hbsρ : SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs := hbs
    have hcall : genIhCallAt ρ ihd xs c j fs q.1 is x := ⟨q, hq, rfl, bs, hbsρ, his_def, hx_def⟩
    obtain ⟨hisF, hxF⟩ := hihTy c hc j hj xs fs hxl' hsp q hq bs hbsρ
    rw [← his_def, ← hx_def] at hxF
    rw [← his_def] at hisF
    have hxsT : SpineFit ρ (genPdoms pre q.1) xs := by
      rw [genPdoms, hpre q.1 ht]; exact hxsP
    have hfitT := genRds_fit (pre := pre) (idxB := idxB) (majB := majB) hxsT hisF hxF
    have hxlT : xs.length = rP q.1 := by rw [hxl, hpl q.1 ht]
    -- the body: the chain's recursor at the call's spine, i.e. the graph at the call
    have hbody : interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genF ρ rP pre idxB majB uX g) ρ)))
        (AnnotTerm.mkAppN (.bvar (P.length + (fdoms c j).length + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV P.length (P.length + (fdoms c j).length - P.length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
        = app g (tagged q.1 (tupW (uX q.1) is) x) := by
      rw [interp_mkAppN, ← List.foldl_map]
      have hhead : consList bs (consList (xs ++ fs) (chainFrame K (genF ρ rP pre idxB majB uX g) ρ))
          (P.length + (fdoms c j).length + q.2.1.length + (K - 1 - q.1))
            = genF ρ rP pre idxB majB uX g q.1 := by
        rw [← consList_append, show P.length + (fdoms c j).length + q.2.1.length + (K - 1 - q.1)
          = (K - 1 - q.1) + (xs ++ fs ++ bs).length by simp [hxl, hfl, hbl]; omega,
          consList_apply_add, chainFrame_apply ht]
      rw [show interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genF ρ rP pre idxB majB uX g) ρ)))
          (.bvar (P.length + (fdoms c j).length + q.2.1.length + (K - 1 - q.1)))
          = genF ρ rP pre idxB majB uX g q.1 from hhead]
      have hpv : (prefVarsAV P.length (P.length + (fdoms c j).length - P.length + q.2.1.length)).map
          (interp V (consList bs (consList (xs ++ fs)
            (chainFrame K (genF ρ rP pre idxB majB uX g) ρ)))) = xs := by
        have h := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ bs)
          (ρ := chainFrame K (genF ρ rP pre idxB majB uX g) ρ) hxl
        rw [← List.append_assoc, consList_append] at h
        simpa [hbl, hfl, Nat.add_sub_cancel_left] using h
      rw [List.map_append, hpv, List.map_congr_left hargR]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← his_def, ← hx_def]
      have hfold := lamTowerA_fold (m := 1) Nat.one_ne_zero
        (g := fun sp _ => app g (tagged q.1 (tupW (uX q.1) (idxOf (rP q.1) sp)) (majOf sp)))
        (acc := []) hfitT
      rw [List.nil_append, idxOf_split hxlT, majOf_split] at hfold
      rw [genF, hfold]
    -- the graph lands in the motive at the call
    have hpred : tagged q.1 (tupW (uX q.1) is) x ∈ˢ graphPredG (genIs ρ pre idxB uX)
        (genCr ρ pre idxB majB uX) K (genCall uX (genIhCallAt ρ ihd)) xs (c, j, fs) := by
      obtain ⟨hiT, hxC⟩ := genMajor_mem (hIdx q.1 ht) hxsT hisF hxF
      exact mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hiT hxC, ⟨q.1, is, x, hcall, rfl⟩⟩
    have hgv := hg _ hpred
    rw [blockRecMot_tagged ht] at hgv
    have hisl : (genIdxDoms idxB q.1).length = (idxB q.1).length := by simp [genIdxDoms]
    rw [← hisl, isOfW_tupW (hIdx q.1 ht xs hxsT) hisF, hconcl q.1 ht xs is x hxl
      (by rw [hisF.length_eq, hisl])] at hgv
    -- the codomain reads the same motive at the same arguments
    show interp V _ (AnnotTerm.mkAppN
        (.bvar (P.length + (fdoms c j).length + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV P.length (P.length + (fdoms c j).length - P.length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
      ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ))
      (AnnotTerm.mkAppN (.bvar (P.length + (fdoms c j).length + q.2.1.length - 1 - motPos q.1))
        (q.2.2.1 ++ [q.2.2.2]))
    rw [hbody, interp_mkAppN, ← List.foldl_map]
    have hmt := hmot q.1 ht
    have hhd : interp V (consList bs (consList (xs ++ fs) ρ))
        (.bvar (P.length + (fdoms c j).length + q.2.1.length - 1 - motPos q.1))
        = xs.getD (motPos q.1) pt := by
      show consList bs (consList (xs ++ fs) ρ) _ = _
      rw [← consList_append, List.append_assoc,
        show P.length + (fdoms c j).length + q.2.1.length - 1 - motPos q.1
          = (fs ++ bs).length + xs.length - 1 - motPos q.1 by simp [hxl, hfl, hbl]; omega]
      exact consList_prefix_getD (by omega)
    rw [hhd]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← his_def, ← hx_def]
    exact hgv
  -- the residue: the minor premise at the fields and the `ih` values
  obtain ⟨hsV, hhsV⟩ : ∃ hsV, hsV = genIhv K ρ rP pre idxB majB uX
      (fun c j => (ihd c j).map (genIhAV K P.length (P.length + (fdoms c j).length)))
      xs c j fs g := ⟨_, rfl⟩
  rw [← hhsV]
  have hsVl : hsV.length = (ihd c j).length := by rw [hhsV]; simp [genIhv]
  have hmin' := hmin c hc j hj
  have key := interp_genRb0 (ρ := ρ) (xs := xs) (fs := fs) (hs := hsV) (minPos := minPos c j)
    (by omega)
  rw [hxl, hfl, hsVl] at key
  rw [key]
  have hres := hminor c hc j hj xs hxsP fs hfs hsV hsVl fun l q h hq hh => by
    rw [hhsV] at hh
    simp only [genIhv, List.map_map, List.getElem?_map, hq, Option.map_some,
      Option.some.injEq] at hh
    subst hh
    exact hih q (List.mem_of_getElem? hq)
  -- the motive at the constructor
  have hesF := hesFit c hc j hj xs fs hxl' hsp
  rw [blockRecMot_tagged hc]
  have hisl : (genIdxDoms idxB c).length = (idxB c).length := by simp [genIdxDoms]
  rw [← hisl, isOfW_tupW (hIdx c hc xs hxs) hesF, hconcl c hc xs _ _ hxl
    (by rw [hesF.length_eq, hisl]), ← hmk c hc j hj xs fs hxl' hsp]
  exact hres

end Step

end ConLeche.Model
