module

public import ConLeche.Model.Inductives.MutualRuleRead
public import ConLeche.Model.Inductives.FixRuleOk
public import ConLeche.Model.Inductives.MutualRecLeaf
public section

/-!
# The mutual block's rule core, at the readings (task #278, M2.2c)

`ConLeche/Model/Inductives/FixRecLaw.lean`'s `interp_fixRuleCoreAV`
with `k` motives: rule `J`'s core `mutualRuleCoreAV` — minor `J` at the
fields and at the inductive hypotheses, hypothesis `i` firing the
recursor leaf of the member its field targets — reads, at the rule's
frame `(p⃗, M⃗, S⃗, f⃗)`, to the minor's fold over the fields and the
hypotheses' λ-towers.

The pieces are the fixpoint route's at a `k`-motive frame: the
prefix's reading (`map_recPrefixBvarsMK_interp`), the ih application's
arguments (`ihAppAVK_args_interp`) and the ih application itself
(`interp_ihAppAVK`) — `lamTower_ihTeleAtGo` and `interp_ihIdxAtMK` do
the telescope work unchanged.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

/-! `frameIdx` is spelled `Semantics.frameIdx` throughout: the plain
name resolves to `FixRecRead`'s frame lemma. -/

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The `k`-motive prefix, read -/

/-- **The `k`-motive recursor's leading spine reads to the block**:
the parameters, the `k` motives in member order and the `n` minors. -/
theorem map_recPrefixBvarsMK_interp {nP k n nF : Nat} {as₁ Ms ms fs : List V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = k) (hlenM : ms.length = n)
    (hlenF : fs.length = nF) (bs : List V) :
    (recPrefixBvarsMK nP k n nF bs.length).map
        (interp V (consList bs (consList fs (consList ms (consList Ms (consList as₁ ρ))))))
      = as₁ ++ Ms ++ ms := by
  unfold recPrefixBvarsMK paramBvarsAt
  rw [List.map_append, List.map_append]
  congr 1
  congr 1
  · -- the parameters
    apply List.ext_getElem
    · simp [hlenP]
    · intro t h1 h2
      have ht : t < nP := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [show nP + nF + n + k + bs.length - 1 - t
          = ((((nP - 1 - t) + Ms.length) + ms.length) + fs.length) + bs.length from by omega,
        consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add,
        consList_getD_lt as₁ ρ (nP - 1 - t) (by omega),
        show as₁.length - 1 - (nP - 1 - t) = t from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  · -- the motives
    apply List.ext_getElem
    · simp [hlenK]
    · intro t h1 h2
      have ht : t < k := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [show nF + n + k - 1 - t + bs.length
          = (((k - 1 - t) + ms.length) + fs.length) + bs.length from by omega,
        consList_apply_add, consList_apply_add, consList_apply_add,
        consList_getD_lt Ms _ (k - 1 - t) (by omega),
        show Ms.length - 1 - (k - 1 - t) = t from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  · -- the minors
    apply List.ext_getElem
    · simp [hlenM]
    · intro l h1 h2
      have hl : l < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [show nF + n - 1 - l + bs.length = ((n - 1 - l) + fs.length) + bs.length from by omega,
        consList_apply_add, consList_apply_add,
        consList_getD_lt ms _ (n - 1 - l) (by omega),
        show ms.length - 1 - (n - 1 - l) = l from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The ih application at a `k`-motive frame -/

/-- The ih application's arguments read, under telescope values, to
the block, the field's index values and the field applied to the
values (`ihAppAVb_args_interp` with `k` motives). -/
theorem ihAppAVK_args_interp {nP k n nF i : Nat} {as₁ Ms ms fs bs : List V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = k) (hk : 0 < k) (hlenM : ms.length = n)
    (hlenF : fs.length = nF) (hi : i < nF) (Eis : List AnnotTerm) :
    (recPrefixBvarsMK nP k n nF bs.length ++ Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]).map
      (interp V (consList bs (consList fs (consList ms (consList Ms (consList as₁ ρ))))))
      = as₁ ++ Ms ++ ms ++
        Eis.map (interp V (consList bs (consList (fs.take i) (consList as₁ ρ)))) ++
        [(Semantics.frameIdx bs.length (consList bs (consList (fs.take i) (consList as₁ ρ)))).foldl
          SetTheory.app (fs.getD i pt)] := by
  rw [List.map_append, List.map_append, List.map_map]
  have hpre := map_recPrefixBvarsMK_interp (ρ := ρ) hlenP hlenK hlenM hlenF bs
  have hEis : Eis.map
      (interp V (consList bs (consList fs (consList ms (consList Ms (consList as₁ ρ)))))
        ∘ ihIdxAtM nF (n + k) i 0 bs.length)
      = Eis.map (interp V (consList bs (consList (fs.take i) (consList as₁ ρ)))) := by
    apply List.map_congr_left
    intro E _
    simp only [Function.comp_def]
    have := interp_ihIdxAtMK (ρp := consList as₁ ρ) (Ms := Ms) (ms := ms) (l := 0)
      (nF := nF) (o := n + k) (i := i)
      (by omega) (by omega) hlenF (ihs := []) rfl (Nat.le_of_lt hi) bs E
    exact this
  have hfld : interp V (consList bs (consList fs (consList ms (consList Ms (consList as₁ ρ)))))
      (AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length))
      = (Semantics.frameIdx bs.length (consList bs (consList (fs.take i) (consList as₁ ρ)))).foldl
          SetTheory.app (fs.getD i pt) := by
    rw [interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app),
      map_teleVarsAV_interp, Semantics.frameIdx_consList', interp_bvar,
      show nF - 1 - i + bs.length = (nF - 1 - i) + bs.length from rfl, consList_apply_add,
      consList_getD_lt fs _ _ (by omega), show fs.length - 1 - (nF - 1 - i) = i from by omega]
  rw [hpre, hEis, List.map_cons, List.map_nil, hfld]

/-- **The ih application reads to the λ-tower** over the field's
telescope at the field's own frame of the target member's leaf at the
block, the field's index values and the field applied to the
telescope's values (`interp_ihAppAVb` with `k` motives). -/
theorem interp_ihAppAVK {b nP k n nF i : Nat} {as₁ Ms ms fs : List V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = k) (hk : 0 < k) (hlenM : ms.length = n)
    (hlenF : fs.length = nF) (hi : i < nF) {R : AnnotTerm} {rV : V}
    (hR : ∀ bs : List V,
      interp V (consList bs (consList fs (consList ms (consList Ms (consList as₁ ρ))))) R = rV)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    interp V (consList fs (consList ms (consList Ms (consList as₁ ρ))))
        (ihAppAVK R nP k n nF i (rebit b tl) Eis)
      = lamTower b (consList (fs.take i) (consList as₁ ρ)) tl fun σ' =>
          (as₁ ++ Ms ++ ms ++ Eis.map (interp V σ') ++
            [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app rV := by
  obtain ⟨M0, Mrest, rfl⟩ : ∃ M0 Mrest, Ms = M0 :: Mrest := by
    cases Ms with
    | nil => rw [List.length_nil] at hlenK; omega
    | cons M0 Mrest => exact ⟨M0, Mrest, rfl⟩
  have hunf : ihAppAVK R nP k n nF i (rebit b tl) Eis
      = mkLamsC b (ihTeleAtR nF (n + k) i 0 tl)
          (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF tl.length ++
            Eis.map (ihIdxAtM nF (n + k) i 0 tl.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + tl.length)) (teleVarsAV tl.length)])) := by
    unfold ihAppAVK mkLamsC ihTeleAtR
    rw [ihTeleAtGo_rebit, rebit_map_lam, rebit_length]
  rw [hunf, interp_mkLamsC]
  have hms : (Mrest ++ ms).length + 1 = n + k := by
    rw [List.length_append, hlenM]
    rw [List.length_cons] at hlenK
    omega
  have hfr : consList fs (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))
      = consList [] (consList fs (consList (Mrest ++ ms) (cons M0 (consList as₁ ρ)))) := by
    rw [consList_nil, consList_motives_cons]
  rw [hfr]
  unfold ihTeleAtR
  refine lamTower_ihTeleAtGo hms hlenF (Nat.le_of_lt hi) tl [] fun bs hbs => ?_
  simp only [consList_nil]
  rw [← consList_motives_cons (M0 := M0) (Mrest := Mrest) (ms := ms) (ρp := consList as₁ ρ),
    ← hbs, interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app),
    ihAppAVK_args_interp hlenP hlenK hk hlenM hlenF hi, hR bs]

/-! ## The rule's core -/

/-- **The mutual rule's core reads to the minor's fold** at the fields
and the inductive-hypothesis values — the λ-towers over the recursive
fields' telescopes of the TARGET member's leaf at the block, the
calls' index values and the field along the telescope. -/
theorem interp_mutualRuleCoreAV {ℓ b nP k n nF j : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {as₁ Ms ms as₂ : List V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = k) (hk : 0 < k) (hlenM : ms.length = n)
    (hlenF : as₂.length = nF) (hjn : j < n)
    {Rof : Nat → AnnotTerm} (hRcl : ∀ t, Term.bvarsBelow 0 (Rof t).erase) {tgts : Nat → Nat}
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
        (mutualRuleCoreAV b Rof tgts nP k n nF j (recIdx rs nF) tls Eis)
      = (as₂ ++ (recIdx rs nF).map fun i =>
          lamTower ℓ (consList (as₂.take i) (consList as₁ ρ)) (tls.getD i [])
            fun σ' =>
              (as₁ ++ Ms ++ ms ++ ((Eis.getD i []).map (interp V σ')) ++
                [(Semantics.frameIdx ((tls.getD i []).length) σ').foldl
                  SetTheory.app (as₂.getD i pt)]).foldl
                SetTheory.app (interp V ρ (Rof (tgts i)))).foldl
          SetTheory.app (ms.getD j pt) := by
  unfold mutualRuleCoreAV
  rw [interp_mkAppN,
    ← List.foldl_map
      (f := interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ)))))
      (g := SetTheory.app),
    List.map_append, List.map_map, interp_bvar,
    show fieldBvars nF = (List.range nF).map (fun q => AnnotTerm.bvar (nF - 1 - q)) from rfl,
    map_fieldBvars_interp hlenF,
    show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega, consList_apply_add,
    consList_getD_lt ms _ (n - 1 - j) (by omega),
    show ms.length - 1 - (n - 1 - j) = j from by omega]
  congr 2
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  simp only [Function.comp_def]
  have h := interp_ihAppAVK (b := b) (ρ := ρ) hlenP hlenK hk hlenM hlenF hik
    (R := Rof (tgts i)) (rV := interp V ρ (Rof (tgts i)))
    (fun bs => interp_closed (V := V) (hRcl (tgts i)) _ ρ) (tls.getD i []) (Eis.getD i [])
  rw [h, lamTower_bit_agree hbz.symm]

omit [SetTheory V] in
/-- The block frame sits `k + n + nIdx + 1` binders below the
parameter frame. -/
theorem shiftE_blockFrame {n nIdx k : Nat} {as₁ Ms ms is : List V} {t : V} {ρ : Nat → V}
    (hlenK : Ms.length = k) (hlenM : ms.length = n) (hlenI : is.length = nIdx) :
    shiftE (k + n + nIdx + 1) 0 (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ) = consList as₁ ρ := by
  have hσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
      = consList (Ms ++ ms ++ is ++ [t]) (consList as₁ ρ) := by
    simp only [List.append_assoc]
    rw [consList_append]
  have hlen : (Ms ++ ms ++ is ++ [t]).length = k + n + nIdx + 1 := by
    simp only [List.length_append, List.length_singleton, hlenK, hlenM, hlenI]
  rw [hσ, ← hlen]
  exact shiftE_consList _ _

/-! ## The member recursor's leaf, folded -/

set_option maxHeartbeats 1600000 in
/-- **Member `mm`'s recursor leaf, folded** along a spine fitting its
STORED type's binder data — the parameters `as₁`, the `k` motives `Ms`,
the `n` minors `ms`, member `mm`'s index values `is` and the major `t`:
its value is the AUXILIARY recursor (the fixpoint route's leaf at the
auxiliary data) applied to the parameters, the motive dispatch, the
minors, the tagged tuple `⟨inj mm ı⃗⟩` and the major. -/
theorem interp_mutualRecAVI_fold {m : EnvModel V env} {ψ : Name → Nat}
    {ℓ W w nP s b : Nat} {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {FssR Fss₀ Ess' : List (List AnnotTerm)} {mems : Nat → Nat} {tgts : Nat → Nat → Nat}
    {cds : List CtorDatumR} {mm : Nat}
    {ρ : Nat → V} {as₁ Ms ms is : List V} {t : V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = Ls.length)
    (hlenM : ms.length = cds.length) (hlenI : is.length = nIdxs.getD mm 0)
    (hok : WellDenoted V ρ (mutualRecAVI m ψ ℓ W w nP s b elimL Ls nIdxs pps ipss Idss rss tlss
      Eiss' FssR Fss₀ Ess' mems tgts cds mm))
    (hsp : SpineFit ρ
      ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map (·.2.2))
      (as₁ ++ Ms ++ ms ++ is ++ [t]))
    (hT : TagOk W (consList as₁ ρ) Idss)
    {Ids : List AnnotTerm} (hIdss : Idss[mm]? = some Ids)
    (hidxFit : SpineFit (consList as₁ ρ) Ids is)
    (hclA : Term.bvarsBelow 0
      (auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds).erase) :
    (as₁ ++ Ms ++ ms ++ is ++ [t]).foldl SetTheory.app
        (interp V ρ (mutualRecAVI m ψ ℓ W w nP s b elimL Ls nIdxs pps ipss Idss rss tlss Eiss'
          FssR Fss₀ Ess' mems tgts cds mm))
      = (as₁ ++ [interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)
              (motDispAV ℓ W w (Ls.length + cds.length + nIdxs.getD mm 0 + 1)
                (cds.length + nIdxs.getD mm 0 + 1) Ls.length Idss rss tlss Eiss' Fss₀ Ess')] ++
          ms ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]).foldl SetTheory.app
        (interp V ρ
          (auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts
            cds)) := by
  have hlenX : (Ms ++ ms ++ is ++ [t]).length
      = Ls.length + cds.length + nIdxs.getD mm 0 + 1 := by
    simp only [List.length_append, List.length_singleton, hlenK, hlenM, hlenI]
  have hfrσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
      = consList (Ms ++ ms ++ is ++ [t]) (consList as₁ ρ) := by
    simp only [List.append_assoc]
    rw [consList_append]
  -- the λ-tower folds along the spine
  have hlds : ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map
      fun d : Nat × Nat × AnnotTerm => (b, d.2.2)).map (·.2)
      = (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map (·.2.2) := by
    rw [List.map_map]
    rfl
  unfold mutualRecAVI mkLamsC
  rw [mkLamsAV_fold_graded hok (by rw [hlds]; exact hsp)]
  -- the body, at the frame
  unfold mutualRecBodyAV
  rw [interp_mkAppN,
    ← List.foldl_map (f := interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ))
      (g := SetTheory.app)]
  -- the head: the auxiliary leaf is closed
  have hhead : interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)
      ((auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts
        cds).liftN (Ls.length + cds.length + nIdxs.getD mm 0 + 1) 0)
      = interp V ρ
        (auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds) := by
    rw [interp_liftN]
    exact interp_closed (V := V) hclA _ _
  -- the parameters
  have hpar : (paramBvarsAt nP (nP + (Ls.length + cds.length + nIdxs.getD mm 0 + 1))).map
      (interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)) = as₁ := by
    rw [map_paramBvarsAt_interp (ρp := consList as₁ ρ) (fun j => by
        rw [hfrσ, ← hlenX, consList_apply_add]), ← hlenP, range_reverse_map_consList]
  -- the minors
  have hmin : (((List.range cds.length).map fun J =>
        AnnotTerm.bvar (nIdxs.getD mm 0 + 1 + cds.length - 1 - J))).map
      (interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)) = ms := by
    have hσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
        = consList (is ++ [t]) (consList ms (consList Ms (consList as₁ ρ))) := by
      simp only [List.append_assoc]
      rw [consList_append, consList_append, consList_append]
    rw [hσ, List.map_map]
    apply List.ext_getElem
    · simp [hlenM]
    · intro J h1 h2
      have hJ : J < cds.length := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, Function.comp_def, interp_bvar]
      rw [show nIdxs.getD mm 0 + 1 + cds.length - 1 - J
          = (cds.length - 1 - J) + (is ++ [t]).length from by
        simp only [List.length_append, List.length_singleton, hlenI]; omega,
        consList_apply_add, consList_getD_lt ms _ (cds.length - 1 - J) (by omega),
        show ms.length - 1 - (cds.length - 1 - J) = J from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  -- the tagged index tuple
  have hfrD : shiftE (Ls.length + cds.length + nIdxs.getD mm 0 + 1) 0
      (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ) = consList as₁ ρ := by
    rw [hfrσ, ← hlenX]
    exact shiftE_consList _ _
  have hidxV : (idxVarsAV (nIdxs.getD mm 0) 1).map
      (interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)) = is := by
    have hσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
        = cons t (consList is (consList ms (consList Ms (consList as₁ ρ)))) := by
      simp only [consList_append, consList_cons, consList_nil]
    rw [hσ, map_idxVarsAV_interp
      (ρ₀ := consList is (consList ms (consList Ms (consList as₁ ρ))))
      (show RecFrameS 1 _ _ from by
        show shiftE 1 0 (cons t (consList is (consList ms (consList Ms (consList as₁ ρ))))) = _
        rw [shiftE_succ_cons, shiftE_zero_zero]),
      frameIdx_consList hlenI]
  have htag := tagTupleAV_facts (W := W) hT hIdss hfrD
    (Es := idxVarsAV (nIdxs.getD mm 0) 1)
    (fun E hE => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp hE; trivial)
    (by rw [hidxV]; exact hidxFit)
  rw [hidxV] at htag
  -- the major
  have hmaj : interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ) (AnnotTerm.bvar 0) = t := by
    have hσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
        = cons t (consList is (consList ms (consList Ms (consList as₁ ρ)))) := by
      simp only [consList_append, consList_cons, consList_nil]
    rw [interp_bvar, hσ, cons_zero]
  rw [List.map_append, List.map_append, List.map_append, List.map_append, hpar, hmin, hhead,
    List.map_cons, List.map_nil, List.map_cons, List.map_nil, List.map_cons, List.map_nil,
    htag.1, hmaj]

/-! ## The dispatch's value, frame by frame -/

/-- **The motive dispatch's value** at any frame `D` binders below the
parameter frame: the tag recursor at the parameter frame applied to
the tag motive and the frame's motive slots.  Two frames over the SAME
parameter frame whose motive slots carry the same values therefore
give the same dispatch — which is what the rule's inductive
hypotheses need, their frames sitting at a different depth from the
recursor's own. -/
theorem interp_motDispAV_eq {ℓ W w D mOff k : Nat} {ρp σ : Nat → V}
    (hfr : shiftE D 0 σ = ρp) {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss Ess' : List (List AnnotTerm)} :
    interp V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess')
      = (interp V ρp (tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess') :: motVals σ mOff k).foldl
          SetTheory.app (interp V ρp (dispTowerAV ℓ W w k Idss)) := by
  unfold motDispAV
  rw [interp_mkAppN, ← List.foldl_map (f := interp V σ) (g := SetTheory.app), List.map_cons,
    interp_liftN, interp_liftN, hfr]
  congr 2
  unfold motVals
  rw [List.map_map]
  apply List.map_congr_left
  intro m' _
  simp only [Function.comp_def, interp_bvar]

/-- Two frames over one parameter frame with equal motive slots give
equal dispatches. -/
theorem interp_motDispAV_congr {ℓ W w D D' mOff mOff' k : Nat} {ρp σ σ' : Nat → V}
    (hfr : shiftE D 0 σ = ρp) (hfr' : shiftE D' 0 σ' = ρp)
    (hmot : motVals σ mOff k = motVals σ' mOff' k) {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)} :
    interp V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess')
      = interp V σ' (motDispAV ℓ W w D' mOff' k Idss rss tlss Eiss' Fss Ess') := by
  rw [interp_motDispAV_eq hfr, interp_motDispAV_eq hfr', hmot]

/-- **The block frame's motive slots are the motives**: at
`(p⃗, M⃗, S⃗, ı⃗, t)` — the frame of member `mm`'s recursor body, with
`nIdx` index values — the dispatch's slots `mOff + k - 1 - m'` at
`mOff = n + nIdx + 1` carry `M⃗` in member order, whatever `nIdx` is. -/
theorem motVals_blockFrame {n nIdx k : Nat} {as₁ Ms ms is : List V} {t : V} {ρ : Nat → V}
    (hlenK : Ms.length = k) (hlenM : ms.length = n) (hlenI : is.length = nIdx) :
    motVals (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ) (n + nIdx + 1) k = Ms := by
  have hσ : consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ
      = consList (ms ++ is ++ [t]) (consList Ms (consList as₁ ρ)) := by
    simp only [List.append_assoc]
    rw [consList_append, consList_append]
  have hlenT : (ms ++ is ++ [t]).length = n + nIdx + 1 := by
    simp only [List.length_append, List.length_singleton, hlenM, hlenI]
  unfold motVals
  rw [hσ]
  apply List.ext_getElem
  · simp [hlenK]
  · intro m' h1 h2
    have hm' : m' < k := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [show n + nIdx + 1 + k - 1 - m' = (k - 1 - m') + (ms ++ is ++ [t]).length from by
        rw [hlenT]; omega,
      consList_apply_add, consList_getD_lt Ms _ (k - 1 - m') (by omega),
      show Ms.length - 1 - (k - 1 - m') = m' from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The member recursor's rule law -/

set_option maxHeartbeats 12800000 in
/-- **The member recursor's iota at the readings** (the mutual twin of
`fixRecLawCore`'s graph-regime step).  At a spine fitting member
`mm`'s STORED binder data whose major is constructor `j`'s value, the
member's recursor is the rule's core — minor `j` at the fields and at
the inductive hypotheses, each firing the recursor leaf of the member
its field targets.

The proof is the fixpoint route's, once: the member leaf FOLDS to the
auxiliary recursor at the parameters, the motive dispatch, the minors,
the tagged tuple and the major (`interp_mutualRecAVI_fold`), whose iota
is `nativeRecAVI_iota`; the mutual core's hypotheses fold the same way
(`interp_mutualRuleCoreAV` then `interp_mutualRecAVI_fold` again), and
the dispatch inside a hypothesis is the recursor's own
(`interp_motDispAV_congr` at `motVals_blockFrame`).

Every spine-fit premise is the member leaf's TYPING
(`Model/Inductives/MutualRecTyping.lean`); the law takes them. -/
theorem mutualRecIotaCore {m : EnvModel V env} {ψ : Name → Nat} {ℓ W w nP s b : Nat}
    {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' EissRaw : List (List (List AnnotTerm))} {FssR Fss₀ Ess' : List (List AnnotTerm)}
    {mems : Nat → Nat} {tgts : Nat → Nat → Nat} {cds : List CtorDatumR} {Rof : Nat → AnnotTerm}
    {j nF mm : Nat} {ρ : Nat → V} {as₁ Ms ms is as₂ : List V} {t dispV : V}
    (hbz : ℓ = 0 ↔ b = 0) (hℓ : ℓ ≠ 0) (hw : w ≠ 0)
    (hmm : mm < Ls.length) (hj : j < cds.length) (hlenFss : FssR.length = cds.length)
    (hlenP : as₁.length = nP) (hlenK : Ms.length = Ls.length)
    (hlenM : ms.length = cds.length) (hlenI : is.length = nIdxs.getD mm 0)
    (hlenF : as₂.length = nF) (hFsj : (FssR.getD j []).length = nF)
    (hRof : ∀ q, q < Ls.length → Rof q
      = mutualRecAVI m ψ ℓ W w nP s b elimL Ls nIdxs pps ipss Idss rss tlss Eiss' FssR Fss₀ Ess'
          mems tgts cds q)
    (hokR : ∀ q, q < Ls.length → ∀ σ : Nat → V, WellDenoted V σ (Rof q))
    (hclR : ∀ q, Term.bvarsBelow 0 (Rof q).erase)
    (hclA : Term.bvarsBelow 0
      (auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds).erase)
    (hT : TagOk W (consList as₁ ρ) Idss)
    {Ids : List AnnotTerm} (hIdss : Idss[mm]? = some Ids)
    (hidxFit : SpineFit (consList as₁ ρ) Ids is)
    (hspPub : SpineFit ρ
      ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map (·.2.2))
      (as₁ ++ Ms ++ ms ++ is ++ [t]))
    (hdisp : interp V (consList (as₁ ++ Ms ++ ms ++ is ++ [t]) ρ)
        (motDispAV ℓ W w (Ls.length + cds.length + nIdxs.getD mm 0 + 1)
          (cds.length + nIdxs.getD mm 0 + 1) Ls.length Idss rss tlss Eiss' Fss₀ Ess') = dispV)
    (hpre : FixPre V ℓ w W nP FssR Ess' Fss₀ (auxIds W Idss) rss tlss Eiss'
      (auxRecDataAV m ψ W w nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds) s)
    (hspAux : SpineFit ρ
      ((auxRecDataAV m ψ W w nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds).map (·.2.2))
      (as₁ ++ [dispV] ++ ms ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]))
    (hmajV : t = inj j (mkTower (as₂ ++ [pt])))
    (hEtag : ∀ i ∈ recIdx (rss.getD j []) nF,
      (Eiss'.getD j []).getD i []
        = [tagTupleAV W (tgts j i) (i + ((tlss.getD j []).getD i []).length) Idss
            ((EissRaw.getD j []).getD i [])])
    (htgt : ∀ i ∈ recIdx (rss.getD j []) nF, tgts j i < Ls.length)
    (hih : ∀ i ∈ recIdx (rss.getD j []) nF, ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList as₁ ρ))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      (∃ Ids' : List AnnotTerm, Idss[tgts j i]? = some Ids' ∧
        SpineFit (consList as₁ ρ) Ids'
          (((EissRaw.getD j []).getD i []).map
            (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))))) ∧
      (∀ E ∈ (EissRaw.getD j []).getD i [],
        WellDenoted V (consList bs (consList (as₂.take i) (consList as₁ ρ))) E) ∧
      (((EissRaw.getD j []).getD i []).length = nIdxs.getD (tgts j i) 0) ∧
      SpineFit ρ
        ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts (tgts j i)).map (·.2.2))
        (as₁ ++ Ms ++ ms ++
          (((EissRaw.getD j []).getD i []).map
            (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))) ++
          [(Semantics.frameIdx ((tlss.getD j []).getD i []).length
              (consList bs (consList (as₂.take i) (consList as₁ ρ)))).foldl
            SetTheory.app (as₂.getD i pt)])) :
    (as₁ ++ Ms ++ ms ++ is ++ [t]).foldl SetTheory.app (interp V ρ (Rof mm))
      = interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
          (mutualRuleCoreAV b Rof (tgts j) nP Ls.length cds.length nF j
            (recIdx (rss.getD j []) nF) (tlss.getD j []) (EissRaw.getD j [])) := by
  have hk : 0 < Ls.length := by omega
  have hlenmsF : ms.length = FssR.length := by rw [hlenM, hlenFss]
  -- the left-hand side: the member leaf folds to the auxiliary recursor
  rw [hRof mm hmm, interp_mutualRecAVI_fold hlenP hlenK hlenM hlenI
      (by rw [← hRof mm hmm]; exact hokR mm hmm ρ) hspPub hT hIdss hidxFit hclA, hdisp]
  -- the auxiliary recursor's iota
  unfold auxRecAV
  rw [nativeRecAVI_iota hpre hw hℓ ρ hspAux (by rw [hlenFss]; exact hj)
    (show as₂.length = (FssR.getD j []).length from by rw [hlenF, hFsj]) hmajV]
  -- the K-frame's accessors
  have hfrK : consList (as₁ ++ [dispV] ++ ms ++ [inj mm (mkTower (is ++ [pt]))]) ρ
      = consList [inj mm (mkTower (is ++ [pt]))] (consList ms (cons dispV (consList as₁ ρ))) :=
    consList_kframe as₁ dispV ms [inj mm (mkTower (is ++ [pt]))] ρ
  have hIdsLen : (auxIds W Idss).length = 1 := rfl
  rw [hfrK, hIdsLen,
    kframe_frP (his := show [inj mm (mkTower (is ++ [pt]))].length = 1 from rfl) hlenmsF,
    kframe_frMs (his := show [inj mm (mkTower (is ++ [pt]))].length = 1 from rfl) hlenmsF
      (by rw [hlenFss]; exact hj),
    ← hfrK,
    frKSpine_of nP FssR.length 1
      (show (as₁ ++ [dispV] ++ ms).length = nP + 1 + FssR.length from by
        simp only [List.length_append, List.length_singleton, hlenP, hlenmsF])
      (show [inj mm (mkTower (is ++ [pt]))].length = 1 from rfl) ρ,
    hFsj]
  -- the right-hand side: the rule's core
  rw [interp_mutualRuleCoreAV (ℓ := ℓ) hbz hlenP hlenK hk hlenM hlenF hj hclR]
  -- the minors agree; match the inductive hypotheses
  congr 2
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  refine lamTower_congr_leaves fun bs hbs => ?_
  obtain ⟨⟨Ids', hIds', hfit'⟩, hEok', hEn', hsp'⟩ := hih i hi bs hbs
  have hrawlen : (((EissRaw.getD j []).getD i []).map
      (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).length
      = nIdxs.getD (tgts j i) 0 := by rw [List.length_map]; exact hEn'
  -- the mutual hypothesis folds to the auxiliary recursor as well
  rw [hRof (tgts j i) (htgt i hi),
    interp_mutualRecAVI_fold hlenP hlenK hlenM hrawlen
      (by rw [← hRof (tgts j i) (htgt i hi)]; exact hokR (tgts j i) (htgt i hi) ρ) hsp' hT hIds'
      hfit' hclA]
  -- the dispatch inside the hypothesis is the recursor's own
  rw [interp_motDispAV_congr (ρp := consList as₁ ρ)
      (shiftE_blockFrame (as₁ := as₁) (Ms := Ms) (ms := ms)
        (is := ((EissRaw.getD j []).getD i []).map
          (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))))
        (t := (Semantics.frameIdx ((tlss.getD j []).getD i []).length
          (consList bs (consList (as₂.take i) (consList as₁ ρ)))).foldl
          SetTheory.app (as₂.getD i pt)) (ρ := ρ) hlenK hlenM hrawlen)
      (shiftE_blockFrame (as₁ := as₁) (Ms := Ms) (ms := ms) (is := is) (t := t) (ρ := ρ)
        hlenK hlenM hlenI)
      (by
        rw [motVals_blockFrame (as₁ := as₁) (Ms := Ms) (ms := ms)
            (is := ((EissRaw.getD j []).getD i []).map
              (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))))
            (t := (Semantics.frameIdx ((tlss.getD j []).getD i []).length
              (consList bs (consList (as₂.take i) (consList as₁ ρ)))).foldl
              SetTheory.app (as₂.getD i pt)) (ρ := ρ) hlenK hlenM hrawlen,
          motVals_blockFrame (as₁ := as₁) (Ms := Ms) (ms := ms) (is := is) (t := t) (ρ := ρ)
            hlenK hlenM hlenI]),
    hdisp, hEtag i hi]
  -- the tagged index expression's value
  have htagi := tagTupleAV_facts (W := W) (ρp := consList as₁ ρ) hT hIds'
    (d := i + ((tlss.getD j []).getD i []).length)
    (τ := consList bs (consList (as₂.take i) (consList as₁ ρ)))
    (by
      have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
        rw [hbs.length_eq, List.length_map]
      have hlentk : (as₂.take i).length = i := by rw [List.length_take]; omega
      rw [← consList_append,
        show i + ((tlss.getD j []).getD i []).length = (as₂.take i ++ bs).length from by
          rw [List.length_append, hlentk, hlenbs]]
      exact shiftE_consList _ _)
    hEok' hfit'
  rw [List.map_cons, List.map_nil, htagi.1]
  rfl

end ConLeche.Model
