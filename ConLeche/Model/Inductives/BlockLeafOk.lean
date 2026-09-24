module

public import ConLeche.Model.Inductives.FixLeafOk
public import ConLeche.Semantics.Tower.BlockFamI
public section

/-!
# The block leaf's P currency (task #315 M3)

`FixLeafOk.lean` at `k` members.  The validity machinery of that file
is REUSED, not restated — `ChainValidFacts` never mentions the family
slot (its clauses are about a field's telescope and index expressions
at the SHADOW frame, which is target-blind), and so are
`AnnotValid_congr_noBVar`, `AnnotValid_mkPisAV_of/_inv`,
`fieldsValid_liftTele2`, `fieldsValid_congr_exclP`, `tuplerAV_validV`
and `underTowerValid_of_fields`.  What is ported is the WALK, whose
recursive branch now reads the TARGET member's component of the family
tuple (`recSlotB_facts`, `Semantics/Tower/BlockFamI.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The validity walk at k -/

/-! ## Closedness -/

section Below

omit [SetTheory V] in
/-- The non-dependent tower is closed at its components' bound plus
its own depth. -/
theorem ndTowerAV_below {r b : Nat} {G : Nat → AnnotTerm} :
    ∀ (n s d : Nat), (∀ i, i < s + n → Term.bvarsBelow b (G i).erase) →
      Term.bvarsBelow (b + d) (ndTowerAV r G s d n).erase
  | 0, _, _, _ => by simp [ndTowerAV, Term.bvarsBelow]
  | n + 1, s, d, hG => by
    show Term.bvarsBelow (b + d) (AnnotTerm.erase
      (.app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
        (.lam (r + 1) ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))))
    have hC : Term.bvarsBelow (b + d) ((G s).liftN d 0).erase := by
      rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN d (G s).erase b 0 (hG s (by omega))
    have htail : Term.bvarsBelow (b + d + 1) (ndTowerAV r G (s + 1) (d + 1) n).erase := by
      have := ndTowerAV_below (r := r) (G := G) (b := b) n (s + 1) (d + 1)
        (fun i hi => hG i (by omega))
      rwa [show b + (d + 1) = b + d + 1 from by omega] at this
    simp only [AnnotTerm.erase_app, AnnotTerm.erase_lam, Term.bvarsBelow]
    exact ⟨⟨trivial, hC⟩, hC, htail⟩

omit [SetTheory V] in
/-- The non-dependent tuple VALUE is closed at its components' bound. -/
theorem ndMkTowerAV_below {r b : Nat} {Gty G : Nat → AnnotTerm} :
    ∀ (n s : Nat), (∀ i, i < s + n → Term.bvarsBelow b (Gty i).erase) →
      (∀ i, i < s + n → Term.bvarsBelow b (G i).erase) →
      Term.bvarsBelow b (ndMkTowerAV r Gty G s n).erase
  | 0, _, _, _ => by simp [ndMkTowerAV, Term.bvarsBelow]
  | n + 1, s, hGty, hG => by
    show Term.bvarsBelow b (AnnotTerm.erase (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]))
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
    intro a ha
    simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | h
    · exact hGty s (by omega)
    · simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
      refine ⟨hGty s (by omega), ?_⟩
      have := ndTowerAV_below (r := r) (G := Gty) (b := b) n (s + 1) 1
        (fun i hi => hGty i (by omega))
      rwa [show b + 1 = b + 1 from rfl] at this
    · exact hG s (by omega)
    · exact ndMkTowerAV_below (r := r) (Gty := Gty) (G := G) n (s + 1)
        (fun i hi => hGty i (by omega)) (fun i hi => hG i (by omega))
    · exact nomatch h

/-! ### The chains and the leaf -/

/-! ### The operator tower -/

section LeafBelow

variable {k w nP nIdx : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

omit [SetTheory V] in
theorem famTyAV_below {u w : Nat} {Ids : List AnnotTerm} (h : FieldsBelow nP Ids) :
    Term.bvarsBelow nP (famTyAV u w Ids).erase := by
  unfold famTyAV
  simp only [AnnotTerm.erase_pi, AnnotTerm.erase_sort, Term.bvarsBelow]
  exact ⟨towerBodyAV_below h, trivial⟩

omit [SetTheory V] in
/-- Member `m`'s arm of the operator, below the operator's λ. -/
theorem blockArmAV_below {m : Nat} (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow (nP + 1)
      (blockArmG w uf Idss Chs m).erase := by
  unfold blockArmG
  simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN 1 (idxTyAV (uf m) (Idss m)).erase nP 0
      (towerBodyAV_below (hIds m))
  · exact sumBodyAV_below hchains

omit [SetTheory V] in
/-- The block's operator, below the parameter frame. -/
theorem blockFunAV_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockFunG k w uf Idss Chs).erase := by
  unfold blockFunG
  simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · unfold famsTyBAV
    have := ndTowerAV_below (r := blockR k w uf)
      (G := fun m => famTyAV (uf m) w (Idss m)) (b := nP) k 0 0
      (fun i _ => famTyAV_below (hIds i))
    rwa [Nat.add_zero] at this
  · exact ndMkTowerAV_below (r := blockR k w uf) (b := nP + 1) k 0
      (fun i _ => by
        rw [AnnotTerm.erase_liftN]
        exact VExprAux.bvarsBelow_liftN 1 (famTyAV (uf i) w (Idss i)).erase nP 0
          (famTyAV_below (hIds i)))
      (fun i hi => blockArmAV_below hIds (hchains i (by omega)))

omit [SetTheory V] in
/-- The index-set tuple, below the parameter frame. -/
theorem idxTupAV_below (hIds : ∀ c, FieldsBelow nP (Idss c)) :
    Term.bvarsBelow nP (idxTupAV k w uf Idss).erase := by
  unfold idxTupAV
  exact ndMkTowerAV_below (r := blockS k w uf) (b := nP) k 0
    (fun _ _ => by simp only [AnnotTerm.erase_sort]; trivial)
    (fun i _ => towerBodyAV_below (hIds i))

omit [SetTheory V] in
/-- The block's carrier tuple, below the parameter frame. -/
theorem blockBodyAV_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockBodyG k w uf Idss Chs).erase := by
  unfold blockBodyG
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact idxTupAV_below hIds
  · exact blockFunAV_below hIds hchains
  · exact nomatch h

omit [SetTheory V] in
/-- **A member's former leaf is closed.** -/
theorem blockTyAV_below {m : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIdsLen : (Idss m).length = nIdx)
    (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow 0
      (blockTyG k w uf Idss Chs pps m).erase := by
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add, ← hIdsLen]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · refine projAV_below ?_
    rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN (Idss m).length
      (blockBodyG k w uf Idss Chs).erase nP 0
      (blockBodyAV_below hIds hchains)
  · exact mkTowerGo_below (w := uf m) (hIds m)

end LeafBelow

end Below

/-! ## The leaf's currency -/

section Currency

variable {k w nP : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- The non-dependent tuple VALUE is bit-valid, hereditarily from its
components'. -/
theorem ndMkTowerAV_validV {r : Nat} {Gty G : Nat → AnnotTerm} {ρ : Nat → V} :
    ∀ (n s : Nat), (∀ i, i < s + n → AnnotValid V ρ (Gty i)) →
      (∀ i, i < s + n → AnnotValid V ρ (G i)) →
      AnnotValid V ρ (ndMkTowerAV r Gty G s n)
  | 0, _, _, _ => by simp [ndMkTowerAV]
  | n + 1, s, hGty, hG => by
    show AnnotValid V ρ (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n])
    refine mkAppN_validV (by simp) ?_
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | h
    · exact hGty s (by omega)
    · rw [AnnotValid_lam]
      exact ⟨hGty s (by omega), fun x _ =>
        ndTowerAV_annotValid V n (s + 1) 1 (cons x ρ)
          (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun i hi => hGty i (by omega))⟩
    · exact hG s (by omega)
    · exact ndMkTowerAV_validV n (s + 1) (fun i hi => hGty i (by omega))
        (fun i hi => hG i (by omega))
    · exact nomatch h

/-- **The block's carrier tuple is bit-valid** at the parameter
frame. -/
theorem blockBodyAV_validV {ρp : Nat → V} (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c))
    (hchains : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp))
        (Chs c)) :
    AnnotValid V ρp (blockBodyG k w uf Idss Chs) := by
  unfold blockBodyG
  refine mkAppN_validV (by simp) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · -- the index-set tuple
    unfold idxTupAV
    exact ndMkTowerAV_validV k 0 (fun _ _ => trivial)
      (fun i hi => towerBodyAV_validV (hIV i (by omega)))
  · -- the operator
    unfold blockFunG
    rw [AnnotValid_lam]
    have hfam : ∀ i, i < k → AnnotValid V ρp (famTyAV (uf i) w (Idss i)) := by
      intro i hi
      unfold famTyAV
      rw [AnnotValid_pi]
      exact ⟨towerBodyAV_validV (hIV i hi), fun _ _ => trivial,
        fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    refine ⟨?_, fun Y hY => ?_⟩
    · unfold famsTyBAV
      exact ndTowerAV_annotValid V k 0 0 ρp (shiftE_zero_zero ρp)
        (fun i hi => hfam i (by omega))
    · rw [(famsTyBAV_facts (w := w) hI).1] at hY
      have hsh1 : shiftE 1 0 (cons Y ρp) = ρp := by
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      refine ndMkTowerAV_validV k 0 (fun i hi => ?_) (fun i hi => ?_)
      · rw [AnnotValid_liftN, hsh1]; exact hfam i (by omega)
      · unfold blockArmG
        rw [AnnotValid_lam]
        refine ⟨by rw [AnnotValid_liftN, hsh1]; exact towerBodyAV_validV (hIV i (by omega)),
          fun t ht => ?_⟩
        rw [interp_liftN, hsh1, (idxTyAV_facts (hI i (by omega))).1] at ht
        exact sumBodyAV_validV (hchains Y hY i (by omega) t ht)
  · exact nomatch h

/-- The leaf's body is bit-valid at the frame below the parameters and
the member's index variables. -/
theorem blockLeafBody_validV {ρp : Nat → V} (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c))
    (hchains : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp))
        (Chs c))
    {m : Nat} (hm : m < k) {is : List V} (hsp : SpineFit ρp (Idss m) is) :
    AnnotValid V (consList is ρp)
      (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0))
        (mkTowerGo (uf m) (Idss m))) := by
  have hsh : shiftE (Idss m).length 0 (consList is ρp) = ρp := by
    rw [← hsp.length_eq]; exact shiftE_consList is ρp
  rw [AnnotValid_app]
  refine ⟨?_, mkTowerGo_validV (hIV m hm) (fun _ => (hI m hm).2) hsp⟩
  refine projAV_validV ?_
  rw [AnnotValid_liftN, hsh]
  exact blockBodyAV_validV hI hIV hchains

/-- **The block former leaf's P currency**: graded at the hereditary
premise, valid under the tower. -/
theorem blockTyAV_wellDenotedV {m : Nat} (hm : m < k)
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkG k w ρ uf Idss Chs m pps)
    (hval : UnderTowerValid ρ
      (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0))
        (mkTowerGo (uf m) (Idss m))) pps) :
    WellDenotedV V ρ (blockTyG k w uf Idss Chs pps m) :=
  ⟨blockTyG_wellDenoted hm hok, mkLamsC_validV (m := w + 1) hval⟩

end Currency

end ConLeche.Model
