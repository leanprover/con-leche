module

public import ConLeche.Model.Inductives.MutualRuleRead
public import ConLeche.Model.Inductives.FixRuleOk
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

end ConLeche.Model
