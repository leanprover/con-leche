module

public import ConLeche.Model.Inductives.BlockRecWD
import ConLeche.Model.Inductives.BlockRecLeaf
import ConLeche.Semantics.Tower.FixWire
public section

/-!
# The tuple variable and the recursor leaf read alike (task #315, U-9)

The specification's rules are written with the tuple's variables
(`tupleVarAV`) at the recursive occurrences, so an equation mentions no
leaf at all; the block's rules, once the recursors are stored, are
written with the members' leaves (`mutualRuleCoreAV`'s `Rof`).  This
module is the bridge between the two spellings, in the model's three
currencies:

* **congruence of the readings** — a minor premise, the minor entries
  and the recursor's/rule's binder data depend on the model only
  through the constructors' leaves (`minorAVAtRM_congr`,
  `fixMinorsDataM_congr`, `mutualRecDataAV_congr`,
  `mutualRuleDataAV_congr`), so the readings computed at one model are
  the readings computed at any model that values the constructors
  alike;
* **the head bridge** — an inductive hypothesis' λ-tower
  (`ihAppAVK`) and a rule's right-hand side (`specRuleCoreAV` versus
  `mutualRuleCoreAV`) read the same, are graded the same and are
  bit-valid the same when the tuple's variable and the leaf at its
  place read the same under the tower's binders
  (`interp_ihAppAVK_head_congr` and its `WellDenoted`/`AnnotValid`
  twins, `interp_specRuleCoreAV_leaf` and its twins);
* **closedness of the leaf-headed core** (`mutualRuleCoreAV_below`) —
  `specRuleCoreAV_below` with the tuple variable's bound replaced by
  the leaves' own closedness.

Two further facts the stage consumes: a λ-tower's grading premise from
its walk (`underTowerOk_of_fieldsOkB`, the `WellDenoted` twin of
`underTowerValid_of_fieldsValid`), and the small frame facts the
bridge's callers need — a spine recovered from a satisfying frame
(`spineFit_of_sat_len`), a frame's agreement below its spine
(`consList_agree_below`) and the converse of `BlockModel.mem_specEqs`
(`BlockModel.mem_specEqs_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Congruence of the readings in the model

The readings the recursor stage builds mention the model only at the
constructors' leaves (`minorAVAtRM`'s motive application), so two
models that value the block's constructors alike build the same
readings. -/

section Congr

variable {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂} {ψ : Name → Nat}
  {nP : Nat}

/-- A minor premise's reading mentions the model only at the
constructor's leaf. -/
theorem minorAVAtRM_congr {mot : Nat} {moti : Nat → Nat} {C : Name} {nF b o : Nat}
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm} {recIdx : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hC : m₁.acval C ψ = m₂.acval C ψ) :
    minorAVAtRM mot moti m₁ C ψ nP nF b o ds Es recIdx tls Eiss
      = minorAVAtRM mot moti m₂ C ψ nP nF b o ds Es recIdx tls Eiss := by
  unfold minorAVAtRM
  rw [hC]

/-- The minor entries mention the model only at the constructors'
leaves. -/
theorem fixMinorsDataM_congr {b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (o : Nat),
      (∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) →
      fixMinorsDataM mots tgts m₁ ψ nP b cds o = fixMinorsDataM mots tgts m₂ ψ nP b cds o
  | _, _, [], _, _ => rfl
  | mots, tgts, (_, _, _, _, _, _, _) :: cs, o, h => by
    simp only [fixMinorsDataM]
    rw [minorAVAtRM_congr (h _ List.mem_cons_self),
      fixMinorsDataM_congr (fun J => mots (J + 1)) (fun J => tgts (J + 1)) cs (o + 1)
        fun cd hcd => h cd (List.mem_cons_of_mem _ hcd)]

/-- The recursor type's binder data mentions the model only at the
constructors' leaves. -/
theorem mutualRecDataAV_congr {Ls : List AnnotTerm} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {mm : Nat}
    (hC : ∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    mutualRecDataAV m₁ ψ Ls nP nIdxs ℓ pps ipss cds mots tgts mm
      = mutualRecDataAV m₂ ψ Ls nP nIdxs ℓ pps ipss cds mots tgts mm := by
  unfold mutualRecDataAV
  rw [fixMinorsDataM_congr mots tgts cds Ls.length hC]

/-- A rule's binder data mentions the model only at the constructors'
leaves. -/
theorem mutualRuleDataAV_congr {Ls : List AnnotTerm} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {ds : List (Nat × Nat × AnnotTerm)}
    (hC : ∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    mutualRuleDataAV m₁ ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds
      = mutualRuleDataAV m₂ ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds := by
  unfold mutualRuleDataAV
  rw [fixMinorsDataM_congr mots tgts cds Ls.length hC]

end Congr

/-! ## Kit: the three currencies through a λ-tower and an application chain -/

/-- A λ-tower's reading depends on its body only at the frames of its
own fitting spines. -/
theorem interp_mkLamsAV_congr {b₁ b₂ : AnnotTerm} :
    ∀ {ds : List (Nat × AnnotTerm)} {σ : Nat → V},
      (∀ bs : List V, bs.length = ds.length → SpineFit σ (ds.map (·.2)) bs →
        interp V (consList bs σ) b₁ = interp V (consList bs σ) b₂) →
      interp V σ (mkLamsAV ds b₁) = interp V σ (mkLamsAV ds b₂)
  | [], σ, h => by
    have := h [] rfl trivial
    rwa [consList_nil] at this
  | d :: ds, σ, h => by
    simp only [mkLamsAV, interp_lam]
    refine lamR_congr fun x hx => ?_
    refine interp_mkLamsAV_congr (ds := ds) fun bs hlen hfit => ?_
    have := h (x :: bs) (by simp [hlen]) ⟨hx, hfit⟩
    rwa [consList_cons] at this

/-- A λ-tower's grading transfers to a body that reads the same and is
graded at every fitting spine. -/
theorem WellDenoted_mkLamsAV_congr {b₁ b₂ : AnnotTerm} :
    ∀ {ds : List (Nat × AnnotTerm)} {σ : Nat → V},
      (∀ bs : List V, bs.length = ds.length → SpineFit σ (ds.map (·.2)) bs →
        interp V (consList bs σ) b₁ = interp V (consList bs σ) b₂) →
      (∀ bs : List V, bs.length = ds.length → SpineFit σ (ds.map (·.2)) bs →
        WellDenoted V (consList bs σ) b₁ → WellDenoted V (consList bs σ) b₂) →
      WellDenoted V σ (mkLamsAV ds b₁) → WellDenoted V σ (mkLamsAV ds b₂)
  | [], σ, _, hw, h => by
    have hw' := hw [] rfl trivial
    rw [consList_nil] at hw'
    exact hw' h
  | d :: ds, σ, hi, hw, h => by
    simp only [mkLamsAV, WellDenoted_lam] at h ⊢
    obtain ⟨hA, hb, B, hB, hBz⟩ := h
    refine ⟨hA, fun x hx => ?_, B, fun x hx => ?_, hBz⟩
    · refine WellDenoted_mkLamsAV_congr (ds := ds) (fun bs hlen hfit => ?_)
        (fun bs hlen hfit => ?_) (hb x hx)
      · have := hi (x :: bs) (by simp [hlen]) ⟨hx, hfit⟩
        rwa [consList_cons] at this
      · have := hw (x :: bs) (by simp [hlen]) ⟨hx, hfit⟩
        rwa [consList_cons] at this
    · have heq : interp V (cons x σ) (mkLamsAV ds b₂) = interp V (cons x σ) (mkLamsAV ds b₁) := by
        refine interp_mkLamsAV_congr (ds := ds) fun bs hlen hfit => ?_
        have := hi (x :: bs) (by simp [hlen]) ⟨hx, hfit⟩
        rw [consList_cons] at this
        exact this.symm
      rw [heq]
      exact hB x hx

/-- A λ-tower's bit validity transfers to a body valid at every
fitting spine. -/
theorem AnnotValid_mkLamsAV_congr {b₁ b₂ : AnnotTerm} :
    ∀ {ds : List (Nat × AnnotTerm)} {σ : Nat → V},
      (∀ bs : List V, bs.length = ds.length → SpineFit σ (ds.map (·.2)) bs →
        AnnotValid V (consList bs σ) b₁ → AnnotValid V (consList bs σ) b₂) →
      AnnotValid V σ (mkLamsAV ds b₁) → AnnotValid V σ (mkLamsAV ds b₂)
  | [], σ, hv, h => by
    have hv' := hv [] rfl trivial
    rw [consList_nil] at hv'
    exact hv' h
  | d :: ds, σ, hv, h => by
    simp only [mkLamsAV, AnnotValid_lam] at h ⊢
    refine ⟨h.1, fun x hx => ?_⟩
    refine AnnotValid_mkLamsAV_congr (ds := ds) (fun bs hlen hfit => ?_) (h.2 x hx)
    have := hv (x :: bs) (by simp [hlen]) ⟨hx, hfit⟩
    rwa [consList_cons] at this

/-- Same head, pointwise-equal arguments (`interp_mkAppN_congr`). -/
theorem interp_mkAppN_args_congr {σ : Nat → V} {f : AnnotTerm} {args₁ args₂ : List AnnotTerm}
    (hm : args₁.map (interp V σ) = args₂.map (interp V σ)) :
    interp V σ (AnnotTerm.mkAppN f args₁) = interp V σ (AnnotTerm.mkAppN f args₂) :=
  interp_mkAppN_congr args₁ args₂ rfl hm

/-- Same arguments, equally-reading heads. -/
theorem interp_mkAppN_head_congr {σ : Nat → V} {f₁ f₂ : AnnotTerm} {args : List AnnotTerm}
    (hf : interp V σ f₁ = interp V σ f₂) :
    interp V σ (AnnotTerm.mkAppN f₁ args) = interp V σ (AnnotTerm.mkAppN f₂ args) :=
  interp_mkAppN_congr args args hf rfl

/-- An application chain's grading transfers along equally-reading
heads and arguments: the `app` clause's semantic package mentions the
parts only through their readings. -/
theorem WellDenoted_mkAppN_congr {σ : Nat → V} :
    ∀ {args₁ args₂ : List AnnotTerm} {f₁ f₂ : AnnotTerm},
      interp V σ f₁ = interp V σ f₂ →
      args₁.map (interp V σ) = args₂.map (interp V σ) →
      WellDenoted V σ f₂ → (∀ a ∈ args₂, WellDenoted V σ a) →
      WellDenoted V σ (AnnotTerm.mkAppN f₁ args₁) → WellDenoted V σ (AnnotTerm.mkAppN f₂ args₂) := by
  intro args₁
  induction args₁ with
  | nil =>
    intro args₂ f₁ f₂ _ hm hf₂ _ _
    cases args₂ with
    | nil => exact hf₂
    | cons a as => simp at hm
  | cons a₁ as₁ ih =>
    intro args₂ f₁ f₂ hf hm hf₂ hall hwd
    cases args₂ with
    | nil => simp at hm
    | cons a₂ as₂ =>
      simp only [List.map_cons, List.cons.injEq] at hm
      rw [AnnotTerm.mkAppN_cons] at hwd
      rw [AnnotTerm.mkAppN_cons]
      have hhead : WellDenoted V σ (.app f₁ a₁) := (WellDenoted.mkAppN_inv hwd).1
      rw [WellDenoted_app] at hhead
      obtain ⟨-, -, v, A, B, hpi, hmemA, hz⟩ := hhead
      refine ih (by simp only [interp_app, hf, hm.1]) hm.2 ?_
        (fun a ha => hall a (List.mem_cons_of_mem _ ha)) hwd
      rw [WellDenoted_app]
      refine ⟨hf₂, hall a₂ List.mem_cons_self, v, A, B, ?_, ?_, hz⟩
      · rw [← hf]; exact hpi
      · rw [← hm.1]; exact hmemA

/-- Same head, pointwise-equal arguments (themselves graded). -/
theorem WellDenoted_mkAppN_args_congr {σ : Nat → V} {f : AnnotTerm} {args₁ args₂ : List AnnotTerm}
    (hm : args₁.map (interp V σ) = args₂.map (interp V σ))
    (hall : ∀ a ∈ args₂, WellDenoted V σ a)
    (hwd : WellDenoted V σ (AnnotTerm.mkAppN f args₁)) :
    WellDenoted V σ (AnnotTerm.mkAppN f args₂) :=
  WellDenoted_mkAppN_congr rfl hm (WellDenoted.mkAppN_inv hwd).1 hall hwd

/-- Same arguments, equally-reading heads. -/
theorem WellDenoted_mkAppN_head_congr {σ : Nat → V} {f₁ f₂ : AnnotTerm} {args : List AnnotTerm}
    (hf : interp V σ f₁ = interp V σ f₂) (hf₂ : WellDenoted V σ f₂)
    (hwd : WellDenoted V σ (AnnotTerm.mkAppN f₁ args)) :
    WellDenoted V σ (AnnotTerm.mkAppN f₂ args) :=
  WellDenoted_mkAppN_congr hf rfl hf₂ (WellDenoted.mkAppN_inv hwd).2 hwd

/-- Same head, replaced arguments: bit validity is structural. -/
theorem AnnotValid_mkAppN_args_congr {σ : Nat → V} {f : AnnotTerm} {args₁ args₂ : List AnnotTerm}
    (hall : ∀ a ∈ args₂, AnnotValid V σ a)
    (hv : AnnotValid V σ (AnnotTerm.mkAppN f args₁)) :
    AnnotValid V σ (AnnotTerm.mkAppN f args₂) :=
  mkAppN_validV (AnnotValid.mkAppN_inv hv).1 hall

/-- Same arguments, replaced head. -/
theorem AnnotValid_mkAppN_head_congr {σ : Nat → V} {f₁ f₂ : AnnotTerm} {args : List AnnotTerm}
    (hf₂ : AnnotValid V σ f₂) (hv : AnnotValid V σ (AnnotTerm.mkAppN f₁ args)) :
    AnnotValid V σ (AnnotTerm.mkAppN f₂ args) :=
  mkAppN_validV hf₂ (AnnotValid.mkAppN_inv hv).2

/-! ## The head bridge at an inductive hypothesis -/

omit [SetTheory V] in
/-- The ih tower's binder data has the field telescope's length. -/
theorem ihAppAVK_doms_length (k n nF i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    (((ihTeleAtR nF (n + k) i 0 tl).map fun d => (d.2.1, d.2.2)) : List (Nat × AnnotTerm)).length
      = tl.length := by
  rw [List.length_map, ihTeleAtR_length]

/-- **The head bridge, read**: an ih tower reads the same with two
heads that read alike under the tower's binders. -/
theorem interp_ihAppAVK_head_congr {R₁ R₂ : AnnotTerm} {nP k n nF i : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} {σ : Nat → V}
    (h : ∀ bs : List V, bs.length = tl.length →
      interp V (consList bs σ) R₁ = interp V (consList bs σ) R₂) :
    interp V σ (ihAppAVK R₁ nP k n nF i tl Eis)
      = interp V σ (ihAppAVK R₂ nP k n nF i tl Eis) := by
  unfold ihAppAVK
  refine interp_mkLamsAV_congr fun bs hlen _ => ?_
  rw [ihAppAVK_doms_length] at hlen
  exact interp_mkAppN_head_congr (h bs hlen)

/-- **The head bridge, graded**. -/
theorem WellDenoted_ihAppAVK_head_congr {R₁ R₂ : AnnotTerm} {nP k n nF i : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} {σ : Nat → V}
    (h : ∀ bs : List V, bs.length = tl.length →
      interp V (consList bs σ) R₁ = interp V (consList bs σ) R₂)
    (hR₂ : ∀ bs : List V, bs.length = tl.length → WellDenoted V (consList bs σ) R₂)
    (hwd : WellDenoted V σ (ihAppAVK R₁ nP k n nF i tl Eis)) :
    WellDenoted V σ (ihAppAVK R₂ nP k n nF i tl Eis) := by
  unfold ihAppAVK at hwd ⊢
  refine WellDenoted_mkLamsAV_congr (fun bs hlen _ => ?_) (fun bs hlen _ => ?_) hwd
  · rw [ihAppAVK_doms_length] at hlen
    exact interp_mkAppN_head_congr (h bs hlen)
  · rw [ihAppAVK_doms_length] at hlen
    exact WellDenoted_mkAppN_head_congr (h bs hlen) (hR₂ bs hlen)

/-- **The head bridge, bit-valid**. -/
theorem AnnotValid_ihAppAVK_head_congr {R₁ R₂ : AnnotTerm} {nP k n nF i : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} {σ : Nat → V}
    (hR₂ : ∀ bs : List V, bs.length = tl.length → AnnotValid V (consList bs σ) R₂)
    (hv : AnnotValid V σ (ihAppAVK R₁ nP k n nF i tl Eis)) :
    AnnotValid V σ (ihAppAVK R₂ nP k n nF i tl Eis) := by
  unfold ihAppAVK at hv ⊢
  refine AnnotValid_mkLamsAV_congr (fun bs hlen _ => ?_) hv
  rw [ihAppAVK_doms_length] at hlen
  exact AnnotValid_mkAppN_head_congr (hR₂ bs hlen)

/-! ## The head bridge at a rule's core

The specification's right-hand side (`specRuleCoreAV`) and the block's
(`mutualRuleCoreAV`) differ exactly at the ih towers' heads: the
tuple's variable for the member the field targets, against that
member's recursor leaf. -/

section RuleCore

variable {b k : Nat} {Rof : Nat → AnnotTerm} {tgtsJ : Nat → Nat} {nP n nF J : Nat}
  {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eiss : List (List AnnotTerm)} {σ : Nat → V}

omit [SetTheory V] in
/-- The two cores share their head and their field arguments; only the
ih towers differ. -/
theorem specRuleCoreAV_eq_mkAppN :
    specRuleCoreAV b k tgtsJ nP n nF J recIdx tls Eiss
      = AnnotTerm.mkAppN (.bvar (nF + n - 1 - J))
        (fieldBvars nF ++ recIdx.map fun i =>
          ihAppAVK (tupleVarAV k (nP + k + n + nF + (tls.getD i []).length) (tgtsJ i))
            nP k n nF i (rebit b (tls.getD i [])) (Eiss.getD i [])) := rfl

omit [SetTheory V] in
theorem mutualRuleCoreAV_eq_mkAppN :
    mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss
      = AnnotTerm.mkAppN (.bvar (nF + n - 1 - J))
        (fieldBvars nF ++ recIdx.map fun i =>
          ihAppAVK (Rof (tgtsJ i)) nP k n nF i (rebit b (tls.getD i [])) (Eiss.getD i [])) := rfl

/-- **The rule core's bridge, read**. -/
theorem interp_specRuleCoreAV_leaf
    (h : ∀ i ∈ recIdx, ∀ bs : List V, bs.length = (tls.getD i []).length →
      interp V (consList bs σ) (tupleVarAV k (nP + k + n + nF + (tls.getD i []).length) (tgtsJ i))
        = interp V (consList bs σ) (Rof (tgtsJ i))) :
    interp V σ (specRuleCoreAV b k tgtsJ nP n nF J recIdx tls Eiss)
      = interp V σ (mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss) := by
  rw [specRuleCoreAV_eq_mkAppN, mutualRuleCoreAV_eq_mkAppN]
  refine interp_mkAppN_args_congr ?_
  simp only [List.map_append, List.map_map, Function.comp_def]
  refine congrArg _ (List.map_congr_left fun i hi => ?_)
  exact interp_ihAppAVK_head_congr fun bs hbs =>
    h i hi bs (by rwa [rebit_length] at hbs)

/-- **The rule core's bridge, graded**. -/
theorem WellDenoted_specRuleCoreAV_leaf
    (h : ∀ i ∈ recIdx, ∀ bs : List V, bs.length = (tls.getD i []).length →
      interp V (consList bs σ) (tupleVarAV k (nP + k + n + nF + (tls.getD i []).length) (tgtsJ i))
        = interp V (consList bs σ) (Rof (tgtsJ i)))
    (hR : ∀ i ∈ recIdx, ∀ bs : List V, bs.length = (tls.getD i []).length →
      WellDenoted V (consList bs σ) (Rof (tgtsJ i)))
    (hwd : WellDenoted V σ (specRuleCoreAV b k tgtsJ nP n nF J recIdx tls Eiss)) :
    WellDenoted V σ (mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss) := by
  rw [specRuleCoreAV_eq_mkAppN] at hwd
  rw [mutualRuleCoreAV_eq_mkAppN]
  obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hwd
  refine WellDenoted_mkAppN_args_congr ?_ ?_ hwd
  · simp only [List.map_append, List.map_map, Function.comp_def]
    refine congrArg _ (List.map_congr_left fun i hi => ?_)
    exact interp_ihAppAVK_head_congr fun bs hbs =>
      h i hi bs (by rwa [rebit_length] at hbs)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hargs a (List.mem_append_left _ ha)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      refine WellDenoted_ihAppAVK_head_congr
        (fun bs hbs => h i hi bs (by rwa [rebit_length] at hbs))
        (fun bs hbs => hR i hi bs (by rwa [rebit_length] at hbs))
        (hargs _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)))

/-- **The rule core's bridge, bit-valid**. -/
theorem AnnotValid_specRuleCoreAV_leaf
    (hR : ∀ i ∈ recIdx, ∀ bs : List V, bs.length = (tls.getD i []).length →
      AnnotValid V (consList bs σ) (Rof (tgtsJ i)))
    (hv : AnnotValid V σ (specRuleCoreAV b k tgtsJ nP n nF J recIdx tls Eiss)) :
    AnnotValid V σ (mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss) := by
  rw [specRuleCoreAV_eq_mkAppN] at hv
  rw [mutualRuleCoreAV_eq_mkAppN]
  obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hv
  refine AnnotValid_mkAppN_args_congr ?_ hv
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hargs a (List.mem_append_left _ ha)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    refine AnnotValid_ihAppAVK_head_congr
      (fun bs hbs => hR i hi bs (by rwa [rebit_length] at hbs))
      (hargs _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)))

end RuleCore

/-! ## Closedness of the leaf-headed core -/

omit [SetTheory V] in
/-- **The block's rule core is bounded**: `specRuleCoreAV_below` with
the tuple variable replaced by the target member's leaf — which is
closed, so the tower's own depth is all the bound needs. -/
theorem mutualRuleCoreAV_below {b k nP n nF J K : Nat} {Rof : Nat → AnnotTerm}
    {tgtsJ : Nat → Nat} {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eiss : List (List AnnotTerm)}
    (hR : ∀ i ∈ recIdx, Term.bvarsBelow 0 (Rof (tgtsJ i)).erase) (hk : 0 < k)
    (hrec : ∀ i ∈ recIdx, i < nF)
    (htl : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hE : ∀ i, ∀ E ∈ Eiss.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase)
    (hK : nP + k + n + nF ≤ K) :
    Term.bvarsBelow K (mutualRuleCoreAV b Rof tgtsJ nP k n nF J recIdx tls Eiss).erase := by
  unfold mutualRuleCoreAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show nF + n - 1 - J < K by omega) ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp he with he | he
  · exact fieldBvars_below (by omega) e he
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hiF : i < nF := hrec i hi
    refine ihAppAVK_below (L := (tls.getD i []).length) (rebit_length b _)
      (Term.bvarsBelow.mono (Nat.zero_le _) (hR i hi)) ?_ ?_ hiF (by omega)
    · have := ihTeleAtGo_below (nF := nF) (o := n + k) (i := i) (l := 0) (K := nP + i)
        (tl := rebit b (tls.getD i [])) (k := 0) (domsBelow_rebit (htl i))
      exact domsBelow_mono (by omega) this
    · intro E hE'
      have := ihIdxAtM_below (nF := nF) (o := n + k) (i := i) (l := 0)
        (m := (tls.getD i []).length) (hE i E hE')
      exact Term.bvarsBelow.mono (by omega) this

/-! ## A λ-tower's grading from its walk -/

/-- `UnderTowerOk` from the domains' walk and the leaf's grading,
membership and regime at every fitting spine — the `WellDenoted` twin
of `underTowerValid_of_fieldsValid`. -/
theorem underTowerOk_of_fieldsOkB {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsOkB 0 ρ (ds.map (·.2.2)) →
      (∀ as, SpineFit ρ (ds.map (·.2.2)) as →
        WellDenoted V (consList as ρ) b ∧
          interp V (consList as ρ) b ∈ˢ interp V (consList as ρ) T ∧
          (m = 0 → interp V (consList as ρ) T ∈ˢ (univZero : V))) →
      UnderTowerOk m ρ b T ds
  | [], ρ, _, hb => by
    show WellDenoted V ρ b ∧ _ ∧ _
    simpa using hb [] trivial
  | d :: ds, ρ, hv, hb => by
    rw [List.map_cons] at hv
    refine ⟨hv.1, fun a ha => underTowerOk_of_fieldsOkB (hv.2.2 a ha) fun as hsp => ?_⟩
    have := hb (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-! ## Small list and frame facts -/

/-- Below its spine a consed frame does not see the base. -/
theorem consList_agree_below (xs : List V) (ρ₁ ρ₂ : Nat → V) :
    ∀ i, i < xs.length → consList xs ρ₁ i = consList xs ρ₂ i := by
  intro i hi
  rw [consList_apply_lt' xs ρ₁ hi, consList_apply_lt' xs ρ₂ hi]

/-- A spine of the right length satisfying the reversed domains at its
own frame fits them at the base frame. -/
theorem spineFit_of_sat_len {Fs : List AnnotTerm} {as : List V} {ρ : Nat → V}
    (hlen : as.length = Fs.length) (h : Sat V Fs.reverse (consList as ρ)) :
    SpineFit ρ Fs as := by
  have h' : Sat V (Fs.reverse ++ []) (consList as ρ) := by rwa [List.append_nil]
  have hs := spineFit_of_sat (Ds := Fs) (Δ₀ := []) (ρ := consList as ρ) h'
  have hρ : (fun j => consList as ρ (j + Fs.length)) = ρ := by
    funext j
    rw [← hlen, consList_apply_add]
  have hmap : (List.range Fs.length).reverse.map (consList as ρ) = as := by
    rw [← hlen, range_reverse_map_consList]
  rwa [hρ, hmap] at hs

/-- **A rule's equation is one of the block's** — the converse of
`BlockModel.mem_specEqs`. -/
theorem BlockModel.mem_specEqs_of {env : Env} {d : BlockModel V} {m : EnvModel V env}
    {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {c j : Nat}
    {cA : ConstantVal × Nat} (hc : c < d.k) (hj : (d.ctorsM c)[j]? = some cA) :
    specEqAV (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ))
        (specLhsAV d.k d.nP d.nCtors cA.2 c (d.esF c j ψ) (m.acval cA.1.name ψ))
        (specRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) d.k (d.tgts c j) d.nP d.nCtors cA.2
          (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ))
      ∈ d.specEqs m ψ elimL Ls nIdxs pps ipss cds mots tgts := by
  have hj' : j < (d.ctorsM c).length := by
    have := List.getElem?_eq_some_iff.mp hj
    exact this.1
  have hgetD : (d.ctorsM c).getD j default = cA := by
    rw [List.getD_eq_getElem?_getD, hj]; rfl
  unfold BlockModel.specEqs
  refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_map.mpr ⟨j, ?_, ?_⟩⟩
  · exact List.mem_range.mpr hj'
  · rw [hgetD]

end ConLeche.Model
