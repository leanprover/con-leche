module

public import ConLeche.Model.Inductives.PsiFold
public import ConLeche.Model.Inductives.InvFold
import ConLeche.Model.Inductives.MutualChains
public section

/-!
# The forward fold `ψ`: the body (task #279 M-B′ step 3h)

`ψ_A` folds the container's recursor at the choice whose targets are
the copies' carriers at the block's parameters and whose bodies rebuild
with the copies' constructors (DESIGN §M.22).  A body's spine has three
kinds of entry, decided per field: the FIELD variable, the kit's
HYPOTHESIS (`useIh`, as ψ⁻¹'s `mixedVarsAV`), and the TRANSPORT
(`viaEntryAV`, `PsiFold.lean`) — a `J`-ordinary field that is
aux-recursive into another copy.  This module spells the spine and the
body (`psiVarsAV`, `psiBodyAV`), reads the spine at the minor's leaf
frame (`interp_psiVarsAV`), and proves the kit's body fact
(`psiBody_leaf`) from the constructor's tower at the transported
domains (`CtorAtDoms`, `InvFold.CtorAtPins` with the domains explicit)
and the ONE fact each transport consumes of the earlier copy's term.

The bridge between the fields' prefix and the replaced prefix is
`ShadowRelP`: two spines agreeing off a SET of positions (the
hypotheses' and the transports'), `InvFold.ShadowRel` with the
recursive slots replaced by a predicate — the readings that mention no
replaced position below their depth are the same at both.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Spines agreeing off a set of positions -/

/-- Two field spines agreeing off the positions `P`. -/
@[expose] def ShadowRelP (P : Nat → Prop) (as as' : List V) : Prop :=
  as'.length = as.length ∧ ∀ l, l < as.length → ¬ P l → as'.getD l pt = as.getD l pt

theorem ShadowRelP.take {P : Nat → Prop} {fs vs : List V} (h : ShadowRelP P fs vs) (i : Nat) :
    ShadowRelP P (fs.take i) (vs.take i) := by
  refine ⟨by rw [List.length_take, List.length_take, h.1], fun l hl hr => ?_⟩
  rw [List.length_take] at hl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact h.2 l (by omega) hr

/-- The excluded slots of `P` below the fields, at the parameter depth
`nP`: slot `q` is field `q - nP`. -/
@[expose] def replP (nP : Nat) (P : Nat → Prop) (n : Nat) : Nat → Prop :=
  fun q => nP ≤ q ∧ P (q - nP) ∧ q < nP + n

omit [SetTheory V] in
theorem replP_lt {nP : Nat} {P : Nat → Prop} {n : Nat} : ∀ q, replP nP P n q → q < nP + n :=
  fun _ h => h.2.2

/-- Two spines agreeing off `P` give frames agreeing off the excluded
slots (`agreeOff_shadow` at a predicate). -/
theorem agreeOff_shadowP {nP : Nat} {P : Nat → Prop} {as as' : List V}
    (h : ShadowRelP P as as') (ρp : Nat → V) :
    AgreeOff (exclP (replP nP P as.length) (nP + as.length)) (consList as ρp) (consList as' ρp) := by
  intro j hj
  by_cases hji : j < as.length
  · rw [consList_apply_lt' as ρp hji, consList_apply_lt' as' ρp (by rw [h.1]; exact hji), h.1]
    have hnr : ¬ P (as.length - 1 - j) := by
      intro hr
      apply hj
      refine ⟨nP + (as.length - 1 - j), ⟨Nat.le_add_right _ _, ?_, by omega⟩, by omega, by omega⟩
      rw [Nat.add_sub_cancel_left]; exact hr
    exact (h.2 (as.length - 1 - j) (by omega) hnr).symm
  · have h1 := consList_apply_add as ρp (j - as.length)
    have h2 := consList_apply_add as' ρp (j - as.length)
    rw [show j - as.length + as.length = j from by omega] at h1
    rw [h.1, show j - as.length + as.length = j from by omega] at h2
    rw [h1, h2]

/-- The transport under `as` more binders. -/
theorem interp_congr_shadowRelP {nP : Nat} {P : Nat → Prop} {fs vs : List V}
    (h : ShadowRelP P fs vs) (σ : Nat → V) (as : List V) {E : AnnotTerm}
    (hnb : NoBVar (exclP (replP nP P fs.length) (nP + fs.length + as.length)) E) :
    interp V (consList as (consList fs σ)) E = interp V (consList as (consList vs σ)) E :=
  interp_congr_noBVar E hnb (agreeOff_consList_exclP as replP_lt (agreeOff_shadowP h σ))

/-- The transport at a prefix of the spines. -/
theorem interp_congr_shadowRelP_at {nP : Nat} {P : Nat → Prop} {fs vs : List V}
    (h : ShadowRelP P fs vs) (σ : Nat → V) {n : Nat} (hn : n ≤ fs.length) {E : AnnotTerm}
    (hnb : NoBVar (exclP (replP nP P n) (nP + n)) E) :
    interp V (consList (fs.take n) σ) E = interp V (consList (vs.take n) σ) E := by
  have hlen : (fs.take n).length = n := by rw [List.length_take]; omega
  have := interp_congr_shadowRelP (h.take n) σ [] (E := E)
    (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnb)
  simpa using this

/-! ## The spine and the body -/

/-- The transport specification of a field: the term built for the
target copy (at the parameter frame), the field's index readings and
its telescope (both at the field's own frame, as the container
constructor's field domain shows them). -/
abbrev ViaSpec := AnnotTerm × List AnnotTerm × List (Nat × Nat × AnnotTerm)

/-- **ψ's variable spine** at a minor's leaf frame: the transport where
`via` gives one, the hypothesis where `useIh`, the field otherwise. -/
@[expose] def psiVarsAV (recIdx : List Nat) (useIh : Nat → Bool) (via : Nat → Option ViaSpec)
    (nF o : Nat) : List AnnotTerm :=
  (List.range nF).map fun i =>
    match via i with
    | some (Ψ, Eis, tl) => viaEntryAV Ψ nF o i recIdx.length tl Eis
    | none =>
      if useIh i then AnnotTerm.bvar (recIdx.length - 1 - recIdx.idxOf i)
      else AnnotTerm.bvar (nF + recIdx.length - 1 - i)

/-- The transport's VALUE at field `i`: the λ-tower over the field's
telescope of the earlier copy's term at the index values and the field
at the telescope's values (`interp_viaEntryAV`). -/
@[expose] noncomputable def viaVal (b : Nat) (ρp : Nat → V) (fs : List V) (i : Nat) : ViaSpec → V
  | (Ψ, Eis, tl) =>
    lamTower b (consList (fs.take i) ρp) tl fun σ' =>
      (Eis.map (interp V σ') ++
        [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
        SetTheory.app (interp V ρp Ψ)

/-- **ψ's values**: the transport's value, the hypothesis value, or the
field value. -/
@[expose] noncomputable def psiVals (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) : List V :=
  (List.range fs.length).map fun i =>
    match via i with
    | some v => viaVal b ρp fs i v
    | none => if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt

theorem psiVals_length (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) :
    (psiVals b ρp recIdx useIh via fs ihs).length = fs.length := by simp [psiVals]

theorem psiVals_getD (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) {i : Nat} (hi : i < fs.length) :
    (psiVals b ρp recIdx useIh via fs ihs).getD i pt
      = match via i with
        | some v => viaVal b ρp fs i v
        | none => if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt := by
  unfold psiVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **The spine reads to the values** at the leaf frame: the parameter
frame under the motives `Ms`, the earlier minors `ms`, the fields and
the hypotheses. -/
theorem interp_psiVarsAV {b o : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length) {recIdx : List Nat}
    {useIh : Nat → Bool} {via : Nat → Option ViaSpec}
    (huse : ∀ i, useIh i = true → i ∈ recIdx) {fs ihs : List V}
    (hihs : ihs.length = recIdx.length)
    (hbits : ∀ i Ψ Eis tl, via i = some (Ψ, Eis, tl) → ∀ d ∈ tl, d.2.1 = b) :
    (psiVarsAV recIdx useIh via fs.length o).map
        (interp V (consList ihs (consList fs (consList ms (consList Ms ρp)))))
      = psiVals b ρp recIdx useIh via fs ihs := by
  apply List.ext_getElem
  · simp [psiVarsAV, psiVals]
  · intro i h1 h2
    have hi : i < fs.length := by simpa [psiVarsAV] using h1
    simp only [psiVarsAV, psiVals, List.getElem_map, List.getElem_range]
    have hfr : consList ihs (consList fs (consList ms (consList Ms ρp)))
        = consList (fs ++ ihs) (consList ms (consList Ms ρp)) := by rw [consList_append]
    cases hv : via i with
    | some v =>
      obtain ⟨Ψ, Eis, tl⟩ := v
      rw [interp_viaEntryAV hms hk rfl hihs hi (hbits i Ψ Eis tl hv) Ψ Eis]
      simp only [viaVal]
    | none =>
      rw [hfr]
      dsimp only
      split
      · next hu =>
        have hmem := huse i hu
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
          List.length_append, hihs, List.getD_eq_getElem?_getD,
          show fs.length + recIdx.length - 1 - (recIdx.length - 1 - recIdx.idxOf i)
            = fs.length + recIdx.idxOf i from by omega,
          List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          ← List.getD_eq_getElem?_getD]
      · rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
          List.length_append, hihs, List.getD_eq_getElem?_getD,
          show fs.length + recIdx.length - 1 - (fs.length + recIdx.length - 1 - i) = i from by omega,
          List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

namespace IndRepData

variable (d : IndRepData V)

/-- **ψ's body** for constructor `J`: the head (the copy's constructor
at the block's parameters, lifted over the motives, the earlier
minors, the fields and the hypotheses) at ψ's spine. -/
@[expose] def psiBodyAV (head : Nat → AnnotTerm) (useIh : Nat → Nat → Bool)
    (via : Nat → Nat → Option ViaSpec) (J : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN
    ((head J).liftN
      (d.k + J + (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length) 0)
    (psiVarsAV (ConLeche.recIdxOf (d.ksR J)) (useIh J) (via J) (d.ctorsAll.getD J default).2
      (d.k + J))

end IndRepData

/-! ## The transported domains, and the constructor's tower at them -/

/-- A fit restricts to a prefix (`spineFit_take`, restated here below
its consumer). -/
theorem spineFit_take' {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

/-- The positions ψ's body replaces: the hypotheses and the transports. -/
@[expose] def replaced (useIh : Nat → Bool) (via : Nat → Option ViaSpec) (i : Nat) : Prop :=
  useIh i = true ∨ (via i).isSome = true

/-- **Field `i`'s domain in TRANSPORTED form** (at the parameter frame,
under the earlier fields): at a transport, the product over the
field's telescope of the transport's TARGET `TgV i` (the earlier
copy's carrier at the block's parameters) at the field's index
readings; at a container-recursive field the kit's target form; at an
ORDINARY field the copy's own stored domain `domA i` (DESIGN §M.31: the
copy's constructor is typed at its own domains, and the container's
reading of an ordinary field may mention a transport position — the
erasing shape — so it is the copy's domain that lives at ψ's
transported frame, and the record's `ord` moves the value across at
the container's frame). -/
@[expose] def psiDomAV (Tg TgV domA : Nat → AnnotTerm) (useIh : Nat → Bool) (via : Nat → Option ViaSpec)
    (nP b : Nat) (tgt : Nat → Nat) (_ds : List (Nat × Nat × AnnotTerm))
    (Eiss : List (List AnnotTerm)) (tls : List (List (Nat × Nat × AnnotTerm))) (i : Nat) :
    AnnotTerm :=
  match via i with
  | some (_, Eis, tl) =>
    mkPisAV (rebit b tl) (AnnotTerm.mkAppN ((TgV i).liftN (nP + i + tl.length) 0) Eis)
  | none =>
    if useIh i then
      mkPisAV (rebit b (tls.getD i []))
        (AnnotTerm.mkAppN ((Tg (tgt i)).liftN (nP + i + (tls.getD i []).length) 0) (Eiss.getD i []))
    else domA i

/-- The transported field domains. -/
@[expose] def psiDomsAV (Tg TgV domA : Nat → AnnotTerm) (useIh : Nat → Bool) (via : Nat → Option ViaSpec)
    (nP b : Nat) (tgt : Nat → Nat) (ds : List (Nat × Nat × AnnotTerm))
    (Eiss : List (List AnnotTerm)) (tls : List (List (Nat × Nat × AnnotTerm))) (nF : Nat) :
    List AnnotTerm :=
  (List.range nF).map (psiDomAV Tg TgV domA useIh via nP b tgt ds Eiss tls)

namespace IndRepData

variable (d : IndRepData V)

/-- **The constructor's tower at explicit domains** — `InvFold.CtorAtPins`
with the target-form domains a parameter: at the parameter frame the
head inhabits a graded Π-tower over `nF` binders whose binders accept
every spine fitting `doms`, and whose body at such a spine is the
member's target at the constructor's index readings. -/
@[expose] def CtorAtDoms (ρ : Nat → V) (ps : List AnnotTerm) (Tg : Nat → AnnotTerm)
    (J : Nat) (head : AnnotTerm) (nF : Nat) (doms : List AnnotTerm) (Es : List AnnotTerm) : Prop :=
  ∃ (dsC : List (Nat × Nat × AnnotTerm)) (bodyC : AnnotTerm),
    dsC.length = nF ∧
    WellDenotedV V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC) ∧
    WellDenotedV V (consList (ps.map (interp V ρ)) ρ) head ∧
    interp V (consList (ps.map (interp V ρ)) ρ) head
      ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC) ∧
    ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) doms vs →
      SpineFit (consList (ps.map (interp V ρ)) ρ) (dsC.map (·.2.2)) vs ∧
      interp V (consList vs (consList (ps.map (interp V ρ)) ρ)) bodyC
        = (Es.map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ)))).foldl
            SetTheory.app (interp V ρ (Tg (d.mems J)))

/-- `CtorAtPins` is `CtorAtDoms` at the kit's target-form domains. -/
theorem ctorAtDoms_of_ctorAtPins {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm}
    {Tg : Nat → AnnotTerm} {useIh : Nat → Bool} {J : Nat} {head : AnnotTerm} {nF : Nat}
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    (h : d.CtorAtPins ψ ρ ps Tg useIh J head nF ds Es Eiss tls) :
    d.CtorAtDoms ρ ps Tg J head nF (tgFieldsAV Tg useIh d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF)
      Es := h

set_option maxHeartbeats 3200000 in
/-- **ψ's body fact** (the kit's `hleaf`) from `CtorAtDoms` at the
transported domains: at a spine of fields and target-form hypotheses,
ψ's values fit the transported domains — each read at the REPLACED
prefix, the same as at the fields' by `ShadowRelP` at the datum's and
the transports' `NoBVar` facts — the transport's value by
`lamTower_mem_piTele` from the ONE fact of the earlier copy's term
(`hvia`); so the head at ψ's spine is graded and lands in the member's
target at the constructor's index readings.  The transports'
well-denotedness at the leaf frame (`hviaWD`) is the consumer's, from
the earlier term's and the field's domain's. -/
theorem psiBody_leaf {ψ : Name → Nat} {ρ : Nat → V} {ps Ms prior : List AnnotTerm}
    (hps : ps.length = d.nP) (hMs : Ms.length = d.k) (hk : 0 < d.k) {J : Nat}
    (hprior : prior.length = J) {Tg TgV domA : Nat → AnnotTerm} {head : Nat → AnnotTerm}
    {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec} {C : Name} {nF : Nat}
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm} {recIdx : List Nat}
    {Eiss : List (List AnnotTerm)} {tls : List (List (Nat × Nat × AnnotTerm))}
    (hcd : (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls))
    (hds : ds.length = d.nP + nF)
    -- no ordinary domain (the copy's own) mentions a replaced position,
    -- and it reads as the container's at the container's field frame
    (hnbA : ∀ i, i < nF →
      NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i)) (domA i))
    (hord : ∀ i, i < nF → ¬ replaced (useIh J) (via J) i → ∀ fs' : List V, fs'.length = i →
      SpineFit (consList (ps.map (interp V ρ)) ρ) (((ds.drop d.nP).take i).map (·.2.2)) fs' →
      interp V (consList fs' (consList (ps.map (interp V ρ)) ρ)) (domA i)
        = interp V (consList fs' (consList (ps.map (interp V ρ)) ρ)) ((ds.getD (d.nP + i) default).2.2))
    -- no later reading mentions a replaced position
    (hnbT : ∀ i, i < nF → ∀ k dd, (tls.getD i [])[k]? = some dd →
      NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + k)) dd.2.2)
    (hnbE : ∀ i, i < nF → ∀ E ∈ Eiss.getD i [],
      NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + (tls.getD i []).length)) E)
    (hnbEs : ∀ E ∈ Es, NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) nF) (d.nP + nF)) E)
    (hnbV : ∀ i, i < nF → ∀ Ψ Eis tl, via J i = some (Ψ, Eis, tl) →
      (∀ k dd, tl[k]? = some dd →
        NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + k)) dd.2.2) ∧
      ∀ E ∈ Eis, NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + tl.length)) E)
    (huse : ∀ i, useIh J i = true → i ∈ recIdx)
    (hbits : ∀ i Ψ Eis tl, via J i = some (Ψ, Eis, tl) → ∀ dd ∈ tl, dd.2.1 = d.bb ψ)
    -- the ONE fact of each transport: at every telescope spine the
    -- earlier copy's term at the index values and the field lands in the
    -- transport's target
    (hvia : ∀ i, i < nF → ∀ Ψ Eis tl, via J i = some (Ψ, Eis, tl) → ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)) (tl.map (·.2.2)) as →
        (Eis.map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V (consList (ps.map (interp V ρ)) ρ) Ψ)
          ∈ˢ (Eis.map (interp V (consList as (consList (fs.take i)
                (consList (ps.map (interp V ρ)) ρ))))).foldl SetTheory.app (interp V ρ (TgV i)))
    (hviaWD : ∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
      SpineFit (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ)
        ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
        (fs ++ ihs) →
      ∀ i Ψ Eis tl, via J i = some (Ψ, Eis, tl) →
        WellDenotedV V (consList (fs ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
          (viaEntryAV Ψ nF (d.k + J) i recIdx.length tl Eis))
    (hCAD : d.CtorAtDoms ρ ps Tg J (head J) nF
      (psiDomsAV Tg TgV domA (useIh J) (via J) d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF) Es)
    (hzero : d.bb ψ = 0 → ∀ fs : List V,
      SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
      (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
        SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)) :
    ∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
      SpineFit (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ)
        ((minorDataTg Tg (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls Eiss).map (·.2.2))
        (fs ++ ihs) →
      WellDenotedV V (consList (fs ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
        (d.psiBodyAV head useIh via J) ∧
      interp V (consList (fs ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ))
          (d.psiBodyAV head useIh via J)
        ∈ˢ (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
            SetTheory.app (interp V ρ (Tg (d.mems J))) ∧
      (d.bb ψ = 0 →
        (Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ)))).foldl
          SetTheory.app (interp V ρ (Tg (d.mems J))) ∈ˢ (univZero : V)) := by
  intro fs ihs hfs hihs hfit
  have hfit₀ := hfit
  -- the constructor's shape from the datum list
  have hcd' := hcd
  unfold cdsR at hcd'
  rw [fixCtorDataList_getElem?, Nat.zero_add] at hcd'
  obtain ⟨cA, hcA, hcAeq⟩ := Option.map_eq_some_iff.mp hcd'
  simp only [Prod.mk.injEq] at hcAeq
  obtain ⟨-, hnFc, -, -, hrec, -, -⟩ := hcAeq
  have hnFget : (d.ctorsAll.getD J default).2 = nF := by
    rw [List.getD_eq_getElem?_getD, hcA]; exact hnFc
  -- the frames
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hσ' : consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ
      = consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
          (consList (ps.map (interp V ρ)) ρ)) := by
    rw [List.map_append, List.map_append, consList_append, consList_append]
  have hshiftO : shiftE (d.k + J) 0 (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
      (consList (ps.map (interp V ρ)) ρ))) = consList (ps.map (interp V ρ)) ρ := by
    rw [← consList_append, show d.k + J = (Ms.map (interp V ρ) ++ prior.map (interp V ρ)).length from by
        rw [List.length_append, List.length_map, List.length_map, hMs, hprior]]
    exact shiftE_consList _ _
  -- the fit, split into the fields and the hypotheses
  rw [hσ'] at hfit
  unfold minorDataTg at hfit
  rw [List.map_append] at hfit
  obtain ⟨fs', ihs', heq, hfitF, hfitI⟩ := spineFit_append_inv hfit
  have hlenF' : fs'.length = nF := by
    rw [hfitF.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hds]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlenF', hfs])
  -- the fields fit their domains at the parameter frame
  have hfsFit : SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs := by
    rw [rebit_map_dom, spineFit_liftDoms, hshiftO] at hfitF
    exact hfitF
  -- a hypothesis lands in the target-form domain of its field, read at
  -- the fields' prefix
  have hih : ∀ l i, recIdx[l]? = some i → i < nF →
      ihs.getD l pt ∈ˢ interp V (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))
        (mkPisAV (rebit (d.bb ψ) (tls.getD i []))
          (AnnotTerm.mkAppN ((Tg (d.tgtsR J i)).liftN (d.nP + i + (tls.getD i []).length) 0)
            (Eiss.getD i []))) := by
    intro l i hl hi
    have hlLt : l < recIdx.length := (List.getElem?_eq_some_iff.mp hl).1
    have hmemI := spineFit_getElem? hfitI l (ihs.getD l pt)
      (tgIhDomAV Tg (d.tgtsR J i) d.nP nF (d.k + J) i l (rebit (d.bb ψ) (tls.getD i []))
        (Eiss.getD i []))
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl)
      (by simp only [List.getElem?_map, ihDataTg_getElem?, hl, Option.map_some, Nat.zero_add])
    have hbits' : ∀ dd ∈ rebit (d.bb ψ) (tls.getD i []), (dd.2.1 = 0 ↔ d.bb ψ = 0) :=
      fun dd hd => by rw [mem_rebit hd]
    rw [interp_tgIhDomAV (ps := ps.map (interp V ρ)) (Ms := Ms.map (interp V ρ))
      (ms := prior.map (interp V ρ)) hpsLen (by rw [List.length_map, List.length_map, hprior, hMs]; omega)
      (by rw [List.length_map, hMs]; exact hk) hfs (by rw [List.length_take]; omega) hi hbits'] at hmemI
    rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := d.bb ψ) (acc := [])
      (B := fun as => ((Eiss.getD i []).map
        (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))).foldl
          SetTheory.app (interp V ρ (Tg (d.tgtsR J i)))) hbits']
    · exact hmemI
    · intro as hsp
      have hasLen : as.length = (tls.getD i []).length := by
        rw [hsp.length_eq, List.length_map, rebit_length]
      rw [List.nil_append, interp_mkAppN_map, interp_liftN, ← consList_append, ← consList_append,
        show d.nP + i + (tls.getD i []).length
          = (ps.map (interp V ρ) ++ (fs.take i ++ as)).length from by
            rw [List.length_append, List.length_append, hpsLen, List.length_take, hasLen]; omega,
        shiftE_consList, consList_append, consList_append]
  -- ψ's values
  obtain ⟨vs, hvs⟩ : ∃ vs, vs = psiVals (d.bb ψ) (consList (ps.map (interp V ρ)) ρ) recIdx (useIh J)
    (via J) fs ihs := ⟨_, rfl⟩
  have hvsLen : vs.length = nF := by rw [hvs, psiVals_length, hfs]
  have hvsGet : ∀ i, i < nF → vs.getD i pt
      = match via J i with
        | some v => viaVal (d.bb ψ) (consList (ps.map (interp V ρ)) ρ) fs i v
        | none => if useIh J i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt := by
    intro i hi
    rw [hvs]
    exact psiVals_getD _ _ _ _ _ _ _ (by rw [hfs]; exact hi)
  have hSR : ShadowRelP (replaced (useIh J) (via J)) fs vs := by
    refine ⟨by rw [hvsLen, hfs], fun l hl hr => ?_⟩
    rw [hvsGet l (by omega)]
    cases hv : via J l with
    | some v => exact absurd (Or.inr (by rw [hv]; rfl)) hr
    | none =>
      dsimp only
      rw [if_neg]
      intro hu
      exact hr (Or.inl hu)
  -- ψ's values fit the transported domains
  have hvsFit : SpineFit (consList (ps.map (interp V ρ)) ρ)
      (psiDomsAV Tg TgV domA (useIh J) (via J) d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF) vs := by
    refine spineFit_of_getElem? (by rw [hvsLen]; simp [psiDomsAV]) ?_
    intro n v F hv hF
    have hn : n < nF := by
      have := (List.getElem?_eq_some_iff.mp hv).1
      rw [hvsLen] at this; exact this
    have hFeq : F = psiDomAV Tg TgV domA (useIh J) (via J) d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls n := by
      unfold psiDomsAV at hF
      rw [List.getElem?_map, List.getElem?_range hn] at hF
      exact (Option.some.inj hF).symm
    have hveq : v = vs.getD n pt := by
      rw [List.getD_eq_getElem?_getD, hv]; rfl
    subst hFeq
    rw [hveq, hvsGet n hn]
    unfold psiDomAV
    cases hvia' : via J n with
    | some sp =>
      obtain ⟨Ψ, Eis, tl⟩ := sp
      dsimp only
      obtain ⟨hnbTV, hnbEV⟩ := hnbV n hn Ψ Eis tl hvia'
      have hbitsV : ∀ dd ∈ rebit (d.bb ψ) tl, (dd.2.1 = 0 ↔ d.bb ψ = 0) :=
        fun dd hd => by rw [mem_rebit hd]
      rw [← interp_congr_shadowRelP_at hSR _ (by rw [hfs]; exact Nat.le_of_lt hn) (nP := d.nP)]
      · rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := d.bb ψ) (acc := [])
          (B := fun as => (Eis.map
            (interp V (consList as (consList (fs.take n) (consList (ps.map (interp V ρ)) ρ))))).foldl
              SetTheory.app (interp V ρ (TgV n))) hbitsV]
        · rw [rebit_map_dom]
          unfold viaVal
          refine lamTower_mem_piTele fun as hfitT => ?_
          rw [List.nil_append]
          have hfitT' := fitsS_teleOfFields.mp hfitT
          have hasLen : as.length = tl.length := by rw [hfitT'.length_eq, List.length_map]
          rw [← hasLen, frameIdx_consList' as]
          exact hvia n hn Ψ Eis tl hvia' fs hfsFit as hfitT'
        · intro as hsp
          have hasLen : as.length = tl.length := by
            rw [hsp.length_eq, List.length_map, rebit_length]
          rw [List.nil_append, interp_mkAppN_map, interp_liftN, ← consList_append, ← consList_append,
            show d.nP + n + tl.length
              = (ps.map (interp V ρ) ++ (fs.take n ++ as)).length from by
                rw [List.length_append, List.length_append, hpsLen, List.length_take, hasLen]; omega,
            shiftE_consList, consList_append, consList_append]
      · refine NoBVar_mkPisAV_exclP _ replP_lt ?_ ?_
        · intro k dd hkk
          rw [rebit_getElem?] at hkk
          obtain ⟨dd', hk', rfl⟩ := Option.map_eq_some_iff.mp hkk
          exact hnbTV k dd' hk'
        · rw [rebit_length]
          refine NoBVar_mkAppN (NoBVar_liftN _ fun i hi => ⟨Nat.zero_le _, ?_⟩) _ hnbEV
          obtain ⟨q, -, hq, rfl⟩ := hi
          omega
    | none =>
      dsimp only
      split
      · next hu =>
        have hmem := huse n hu
        have hl : recIdx[recIdx.idxOf n]? = some n := getElem?_idxOf_of_mem hmem
        have hm := hih (recIdx.idxOf n) n hl hn
        rw [interp_congr_shadowRelP_at hSR _ (by rw [hfs]; exact Nat.le_of_lt hn) (nP := d.nP)] at hm
        · exact hm
        · refine NoBVar_mkPisAV_exclP _ replP_lt ?_ ?_
          · intro k dd hkk
            rw [rebit_getElem?] at hkk
            obtain ⟨dd', hk', rfl⟩ := Option.map_eq_some_iff.mp hkk
            exact hnbT n hn k dd' hk'
          · rw [rebit_length]
            refine NoBVar_mkAppN (NoBVar_liftN _ fun i hi => ⟨Nat.zero_le _, ?_⟩) _ (hnbE n hn)
            obtain ⟨q, -, hq, rfl⟩ := hi
            omega
      · next hu =>
        have hlt : d.nP + n < ds.length := by rw [hds]; omega
        have hm := spineFit_getElem? hfsFit n (fs.getD n pt) ((ds.getD (d.nP + n) default).2.2)
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < fs.length)]; rfl)
          (by rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem hlt,
            Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
        -- the copy's own domain reads as the container's at the fields'
        -- prefix, and mentions no replaced position
        have hnr : ¬ replaced (useIh J) (via J) n := by
          rintro (h | h)
          · exact hu h
          · rw [hvia'] at h; exact nomatch h
        have hfitTake : SpineFit (consList (ps.map (interp V ρ)) ρ)
            (((ds.drop d.nP).take n).map (·.2.2)) (fs.take n) := by
          rw [List.map_take]
          exact spineFit_take' hfsFit (by rw [List.length_map, List.length_drop, hds]; omega)
        rw [← hord n hn hnr (fs.take n) (by rw [List.length_take, hfs]; omega) hfitTake,
          interp_congr_shadowRelP_at hSR _ (by rw [hfs]; exact Nat.le_of_lt hn) (nP := d.nP)
          (hnbA n hn)] at hm
        exact hm
  -- the constructor at the transported domains
  obtain ⟨dsC, bodyC, hdsC, hTC, hheadWD, hheadMem, hvsC⟩ := hCAD
  obtain ⟨hvsFitC, hbodyC⟩ := hvsC vs hvsFit
  -- the index readings at ψ's values are those at the fields
  have hEsEq : Es.map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ)))
      = Es.map (interp V (consList fs (consList (ps.map (interp V ρ)) ρ))) := by
    apply List.map_congr_left
    intro E hE
    have := interp_congr_shadowRelP hSR (consList (ps.map (interp V ρ)) ρ) [] (E := E) (nP := d.nP)
      (by rw [hfs, List.length_nil, Nat.add_zero]; exact hnbEs E hE)
    simpa using this.symm
  -- the body at the leaf frame
  have hσb : consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ)))
      = consList (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs ++ ihs)
          (consList (ps.map (interp V ρ)) ρ) := by
    rw [consList_append, consList_append, consList_append, consList_append]
  have hshiftB : shiftE (d.k + J + nF + recIdx.length) 0
      (consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ)))) = consList (ps.map (interp V ρ)) ρ := by
    rw [hσb, show d.k + J + nF + recIdx.length
        = (Ms.map (interp V ρ) ++ prior.map (interp V ρ) ++ fs ++ ihs).length from by
          simp [hMs, hprior, hfs, hihs]; omega]
    exact shiftE_consList _ _
  have hviaWD' := hviaWD fs ihs hfs hihs hfit₀
  rw [hσ'] at hviaWD'
  rw [hσ']
  unfold psiBodyAV
  rw [hnFget, hrec]
  have hvars : (psiVarsAV recIdx (useIh J) (via J) nF (d.k + J)).map
      (interp V (consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
        (consList (ps.map (interp V ρ)) ρ))))) = vs := by
    rw [← hfs, consList_append, interp_psiVarsAV (o := d.k + J) (b := d.bb ψ)
      (by rw [List.length_map, List.length_map, hprior, hMs]; omega)
      (by rw [List.length_map, hMs]; exact hk) huse hihs hbits, hvs]
  have hmain := wellDenotedV_mkAppN_of_spineFit
    (σ := consList (fs ++ ihs) (consList (prior.map (interp V ρ)) (consList (Ms.map (interp V ρ))
      (consList (ps.map (interp V ρ)) ρ))))
    (ds := liftDoms (d.k + J + nF + recIdx.length) 0 dsC)
    (C := bodyC.liftN (d.k + J + nF + recIdx.length) (0 + dsC.length))
    (f := (head J).liftN (d.k + J + nF + recIdx.length) 0)
    (as := psiVarsAV recIdx (useIh J) (via J) nF (d.k + J))
    (by rw [← liftN_mkPisAV, WellDenotedV_liftN, hshiftB]; exact hTC)
    (by rw [WellDenotedV_liftN, hshiftB]; exact hheadWD)
    (fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      cases hv : via J i with
      | some sp =>
        obtain ⟨Ψ, Eis, tl⟩ := sp
        exact hviaWD' i Ψ Eis tl hv
      | none =>
        dsimp only
        split <;> exact ⟨by simp, by simp⟩)
    (by rw [← liftN_mkPisAV, interp_liftN, interp_liftN, hshiftB]; exact hheadMem)
    (by rw [spineFit_liftDoms, hshiftB, hvars]; exact hvsFitC)
  refine ⟨hmain.1, ?_, fun h0 => hzero h0 fs hfsFit⟩
  have h2 := hmain.2
  have hlen0 : 0 + dsC.length = vs.length := by rw [Nat.zero_add, hdsC, hvsLen]
  rw [hvars, interp_liftN, hlen0, shiftE_consList_len, hshiftB, hbodyC, hEsEq] at h2
  exact h2

end IndRepData

end ConLeche.Model
