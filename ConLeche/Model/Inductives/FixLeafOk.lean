module

public import ConLeche.Model.Inductives.FixChainFacts
public import ConLeche.Semantics.Tower.FixWire
import ConLeche.Model.Inductives.SumIntro
public section

/-!
# The fixed-point leaf's P currency (task #188)

The former's leaf `nativeTyAVI` at the P carrier: closed
(`nativeTyAVI_below`), graded and inhabiting its type's reading
(`FixLeafI.lean`'s `nativeTyAVI_wellDenoted/_mem` at the hereditary premise
`ParamsOkXI`, walked from the former's data — `fixLeafWalks`), and
bit-valid (`AnnotValid`, the annotation's second currency): the
functor's λ's are valid over the X-chains, which are valid at every
family (`fixChainWalkValid`, the walk of `FixChainsP.lean` for the
validity predicate — the entries' validity carries off the recursive
slots exactly as their grading, `AnnotValid_congr_noBVar`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Validity ignores the variables a term does not mention -/

theorem AnnotValid_congr_noBVar :
    ∀ (e : AnnotTerm) {P : Nat → Prop} {σ σ' : Nat → V},
      NoBVar P e → AgreeOff P σ σ' → (AnnotValid V σ e ↔ AnnotValid V σ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | app f a ihf iha =>
    intro P σ σ' h hag
    rw [AnnotValid_app, AnnotValid_app, ihf h.1 hag, iha h.2 hag]
  | lam v A b ihA ihb =>
    intro P σ σ' h hag
    rw [AnnotValid_lam, AnnotValid_lam, ihA h.1 hag, interp_congr_noBVar A h.1 hag]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb h.2 (agreeOff_cons hag x)))
  | pi u v A B ihA ihB =>
    intro P σ σ' h hag
    rw [AnnotValid_pi, AnnotValid_pi, ihA h.1 hag, interp_congr_noBVar A h.1 hag]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB h.2 (agreeOff_cons hag x)))
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp_congr_noBVar B h.2 (agreeOff_cons hag x)]
  | eqE a b iha ihb =>
    intro P σ σ' h hag
    rw [AnnotValid, AnnotValid, iha h.1 hag, ihb h.2 hag]
  | fst e ihe =>
    intro P σ σ' h hag
    rw [AnnotValid_fst, AnnotValid_fst, ihe h hag]
  | snd e ihe =>
    intro P σ σ' h hag
    rw [AnnotValid_snd, AnnotValid_snd, ihe h hag]
  | prf => intros; simp

/-! ## The X-chains, valid at every family -/

section Valid

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nP nF : Nat} {ks : List RecFieldKind}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm}

/-- A lifted entry is valid at the X-frame iff at the parameter frame
under the fields. -/
theorem AnnotValid_chainXI_ord (F : AnnotTerm) (as : List V) (t X : V) :
    AnnotValid V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      ↔ AnnotValid V (consList as ρp) F := by
  rw [AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
    shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]

/-- A telescope valid at the parameter frame under the fields is
valid, lifted, at the X-frame. -/
theorem fieldsValid_liftTele2 (t X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsValid (consList as ρp) (tl.map (·.2.2)) →
      FieldsValid (consList as (cons t (cons X ρp))) ((liftTele2 as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    rw [liftTele2_cons, List.map_cons]
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    refine ⟨(AnnotValid_chainXI_ord _ as t X).mpr hv, fun a ha => ?_⟩
    rw [interp_chainXI_ord] at ha
    rw [consList_snoc']
    have := fieldsValid_liftTele2 t X tl (as ++ [a]) (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- A valid telescope carried between frames agreeing off the slots
its domains do not mention. -/
theorem fieldsValid_congr_exclP {Q : Nat → Prop} :
    ∀ (Fs : List AnnotTerm) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k F, Fs[k]? = some F → NoBVar (exclP Q (d + k)) F) →
      FieldsValid σ' Fs → FieldsValid σ Fs
  | [], _, _, _, _, _, _, _ => trivial
  | F :: Fs, d, hQ, σ, σ', hag, hnb, hF => by
    obtain ⟨hv, hrest⟩ := hF
    have hnb0 : NoBVar (exclP Q d) F := by simpa using hnb 0 F rfl
    have hval : interp V σ F = interp V σ' F := interp_congr_noBVar F hnb0 hag
    refine ⟨(AnnotValid_congr_noBVar F hnb0 hag).mpr hv, fun a ha => ?_⟩
    rw [hval] at ha
    refine fieldsValid_congr_exclP Fs (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ hag a) ?_ (hrest a ha)
    intro k F' hk
    have := hnb (k + 1) F' (by simpa using hk)
    rwa [show d + 1 + k = d + (k + 1) from by omega]

/-- A Π-tower over `Prop`-regime binders is a truth value. -/
theorem interp_mkPisAV_mem_univZero {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}, (∀ d ∈ gds, d.2.1 = 0) →
      (gds = [] → interp V σ R ∈ˢ (univZero : V)) →
      interp V σ (mkPisAV gds R) ∈ˢ (univZero : V)
  | [], _, _, hR => by simpa [mkPisAV] using hR rfl
  | d :: gds, σ, hb, _ => by
    simp only [mkPisAV, interp_pi]
    rw [hb d List.mem_cons_self]
    exact piR_zero_mem_univZero

/-- **A Π-tower is valid** when its domains are along the telescope,
its body is at every fitting spine, and at the `Prop` regime the body
is a truth value there. -/
theorem AnnotValid_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ w = 0)) →
      FieldsValid σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R) →
      (w = 0 → ∀ as, SpineFit σ (gds.map (·.2.2)) as →
        interp V (consList as σ) R ∈ˢ (univZero : V)) →
      AnnotValid V σ (mkPisAV gds R)
  | [], _, _, _, hR, _ => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hb, hF, hR, h0 => by
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    simp only [mkPisAV, AnnotValid_pi]
    refine ⟨hv, fun x hx => ?_, fun hd x hx => ?_⟩
    · refine AnnotValid_mkPisAV_of (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
        (hrest x hx) (fun as hsp => ?_) (fun hw as hsp => ?_)
      · have := hR (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
      · have := h0 hw (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
    · have hw : w = 0 := (hb d List.mem_cons_self).mp hd
      refine interp_mkPisAV_mem_univZero
        (fun d' hd' => (hb d' (List.mem_cons_of_mem _ hd')).mpr hw) fun hnil => ?_
      subst hnil
      have := h0 hw [x] ⟨hx, trivial⟩
      simpa [consList] using this

/-- **A valid Π-tower's pieces**: the domains are valid along the
telescope, and the body is valid at every fitting spine. -/
theorem AnnotValid_mkPisAV_inv {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV gds R) →
      FieldsValid σ (gds.map (·.2.2)) ∧
      ∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R
  | [], σ, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [mkPisAV, consList] using h
      | cons a as => exact hsp.elim⟩
  | d :: gds, σ, h => by
    simp only [mkPisAV, AnnotValid_pi] at h
    obtain ⟨hv, hB, -⟩ := h
    refine ⟨⟨hv, fun x hx => (AnnotValid_mkPisAV_inv (hB x hx)).1⟩, fun as hsp => ?_⟩
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons]
      exact (AnnotValid_mkPisAV_inv (hB a ha)).2 as hsp'

/-- The validity facts beside `ChainFacts`: at a recursive field the
telescope is valid along the shadow spine and the index expressions
are valid under every fitting telescope spine (task #202). -/
structure ChainValidFacts (nP nF : Nat) (ρp : Nat → V) (ks : List RecFieldKind)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Fs : List AnnotTerm) (Eis : List (List AnnotTerm))
    (Es : List AnnotTerm) : Prop where
  grV : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    AnnotValid V (consList as' ρp) (Fs.getD i default) ∧
    (recAt nP ks (nP + i) →
      FieldsValid (consList as' ρp) ((tls.getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList as' ρp) ((tls.getD i []).map (·.2.2)) bs →
        ∀ E ∈ Eis.getD i [], AnnotValid V (consList (as' ++ bs) ρp) E)
  grEV : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, AnnotValid V (consList as' ρp) E

/-- The λ-tower over valid fields ending in a body valid at every
fitting spine is valid under the fields. -/
theorem underTowerValid_of_fields {b : AnnotTerm} {u : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → AnnotValid V (consList bs ρ) b) →
      UnderTowerValid ρ b (Fs.map fun F => (u, u, F))
  | [], ρ, _, hb => hb [] trivial
  | F :: Fs, ρ, hv, hb => by
    refine ⟨hv.1, fun a ha => ?_⟩
    exact underTowerValid_of_fields (hv.2 a ha) fun bs hsp => by
      have := hb (a :: bs) ⟨ha, hsp⟩
      simpa [consList_cons] using this

/-- The tupler is valid at a frame whose index telescope is valid. -/
theorem tuplerAV_validV (hI : IdxOk u ρp Ids) (hV : FieldsValid ρp Ids) :
    AnnotValid V ρp (tuplerAV u Ids) := by
  unfold tuplerAV
  apply mkLamsC_validV
  exact underTowerValid_of_fields hV fun bs hsp => mkTowerGo_validV hV (fun _ => hI.2) hsp

end Valid

/-! ## Closedness -/

section Below

variable {u w nP nIdx nF : Nat} {Ids Fs Es : List AnnotTerm} {rs : List Bool}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}

omit [SetTheory V] in
theorem domsBelow_tuplerData {k : Nat} :
    ∀ {Ids : List AnnotTerm}, FieldsBelow k Ids → DomsBelow k (Ids.map fun F => (u, u, F))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, domsBelow_tuplerData h.2⟩

omit [SetTheory V] in
theorem tuplerAV_below (hIds : FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tuplerAV u Ids).erase := by
  unfold tuplerAV
  refine mkLamsC_below (domsBelow_tuplerData hIds) ?_
  rw [List.length_map]
  exact mkTowerGo_below hIds

omit [SetTheory V] in
/-- A field's telescope, lifted to the X-frame, is below it. -/
theorem domsBelow_liftTele2 {nP : Nat} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (i : Nat), DomsBelow (nP + i) tl →
      DomsBelow (nP + 2 + i) (liftTele2 i tl)
  | [], _, _ => trivial
  | d :: tl, i, h => by
    rw [liftTele2_cons]
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN 2 d.2.2.erase (nP + i) i h.1
      rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
    · have := domsBelow_liftTele2 tl (i + 1)
        (by rw [show nP + (i + 1) = nP + i + 1 from by omega]; exact h.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 from by omega] at this

end Below

end ConLeche.Model
