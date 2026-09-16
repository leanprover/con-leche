module

public import ConLeche.Model.Inductives.MutualData
import ConLeche.Model.Inductives.FixTeleBound
public section

/-!
# The shadow gradings of a mutual constructor (task #278, M2.4)

`FixShadow.lean`/`FixTeleBound.lean`/`SumData.lean`'s frame theorems,
restated for a mutual block's constructor: the three of them read the
run only through its SHAPE (`checkSumCtor_shape`, which the mutual
stage's `checkMutualCtor_shape` matches conjunct for conjunct) and the
constructor's data only through what `MutualCtorDataI` carries too —
the entries' head constant is never inspected, only that a reflexive
field's entry is a Pi-tower over its telescope.  The kinds travel
without their targets (`kindsOf`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

omit [SetTheory V] in
/-- A field is a recursive binder exactly when its kind says so. -/
theorem recAt_kindsOf {nP nF i : Nat} {ks : List (RecFieldKind × Nat)} (hks : ks.length = nF)
    (hi : i < nF) :
    recAt nP (kindsOf ks) (nP + i) ↔ (kindAt ks i = .recursive ∨ kindAt ks i = .reflexive) := by
  constructor
  · intro h
    have h2 := h.2
    rw [Nat.add_sub_cancel_left, kindsOf_getD (by omega)] at h2
    exact h2
  · intro h
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.add_sub_cancel_left, kindsOf_getD (by omega)]
    exact h

theorem mutualShadowGrading (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env}
    {sorts : List Level}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hProp : isProp = true → ∀ ψ : Name → Nat, Level.eval ψ resSort = Level.eval ψ Level.zero)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : MutualCtorDataI mp.base2 env₀ members T lps cvCa nP nF nIdx resSort isProp large
      idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : Name → Nat) :
    (∀ b, b < nP + nF → ∀ ρ : Nat → V,
      Sat V ((shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - b)) ρ →
      WellDenotedV V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default) ∧
      (nP ≤ b → ¬ recAt nP (kindsOf ks) b → resSort.eval ψ ≠ 0 →
        interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default)
          ∈ˢ (univ (resSort.eval ψ) : V))) ∧
    (∀ ρ : Nat → V, Sat V (shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)) ρ →
      WellDenotedV V ρ (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := by
  -- the run's pieces
  obtain ⟨⟨_, hccv⟩, -, fvsP', crest', tfvs, trest, xFvs', idxArgs', hopC, -, -, hopX, -, -, -,
    hsorts⟩ := ConLeche.checkMutualCtor_shape hCtor
  obtain ⟨crest, hopP, hopXX⟩ := hD.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxrest⟩ := Prod.mk.inj (Option.some.inj (hopXX.symm.trans hopX))
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', -, -, hst, hens, hcv⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have htyEq : cvCa.type = type' := by rw [hcv]
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  rw [← htyEq] at htf' hbt' hst
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopXX)
  obtain ⟨F', tb, vb, hib, hensb, -, -⟩ := piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll htf' hbt' (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenAll : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hD.pLen, hD.xLen]
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hD.len ψ]
  have hc := claimsAt_of hμ mp ψ F
  -- a recursive variable is a leaf of no later domain nor of the residual
  have hrecGet : ∀ i, recAt nP (kindsOf ks) (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
    · obtain ⟨-, -, -, -, hlater, hres⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, hres⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
  -- the entries, by strong induction on the binder
  have key : ∀ b, b < nP + nF → ∀ ρ : Nat → V,
      Sat V ((shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - b)) ρ →
      WellDenotedV V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default) ∧
      (nP ≤ b → ¬ recAt nP (kindsOf ks) b → resSort.eval ψ ≠ 0 →
        interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default)
          ∈ˢ (univ (resSort.eval ψ) : V)) := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
    intro hb ρ hρ
    by_cases hbP : b < nP
    · rw [shadowCtx_drop_params hΓlen (by omega)] at hρ
      exact ⟨hO.okΓ b hb ρ hρ, fun h => absurd hbP (by omega)⟩
    · obtain ⟨fv, ty, u, hfv, -, hi, hens', hleq, -⟩ := hfields (b - nP) (by omega)
      have hfvA : (fvsP ++ xFvs)[b]? = some fv := by
        rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen]
        exact hfv
      obtain ⟨-, hws, hbnd, hL, hleaf⟩ := hO.var b fv hfvA
      rw [show nP + (b - nP) = b from by omega] at hi hens'
      have hnorec : ∀ l ∈ fv.fvarTypeD.fvarLeaves, ¬ recAt nP (kindsOf ks) l.1 := by
        intro l hl hr
        have hge := hr.1
        have hlt : l.1 < b := Expr.fvarLeaves_lt_of_wscoped hws l hl
        obtain ⟨x, hx, hlater, -⟩ := hrecGet (l.1 - nP)
          (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
        have hmem : fv ∈ xFvs.drop (l.1 - nP + 1) := by
          refine List.mem_of_getElem? (i := b - nP - (l.1 - nP + 1)) ?_
          rw [List.getElem?_drop, show l.1 - nP + 1 + (b - nP - (l.1 - nP + 1)) = b - nP from by
            omega]
          exact hfv
        exact mentionsFvar_false (hlater fv hmem) l hl (by omega)
      have hC := shadowCtxOk hO hlenAll (nP := nP) (ks := kindsOf ks) (by omega) hws hleaf hnorec
        (fun i hi' hr ρ' hρ' => (ih i hi' (by omega) ρ' hρ').1)
      have hread := hO.doms b fv hfvA
      have hrow := hc.sortRow hi hens' hws hbnd hL hC hread ρ hρ
      refine ⟨hrow.1, fun _ _ hw => ?_⟩
      by_cases hnp : isProp = true
      · exfalso
        have h0 := hProp hnp ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ hrow.2
  refine ⟨key, ?_⟩
  -- the residual
  intro ρ hρ
  have hnorecR : ∀ l ∈ xrest.fvarLeaves, ¬ recAt nP (kindsOf ks) l.1 := by
    intro l hl hr
    have hge := hr.1
    have hlt : l.1 < nP + nF := Expr.fvarLeaves_lt_of_wscoped hO.bodyScoped.1 l hl
    obtain ⟨-, -, -, hres⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    exact mentionsFvar_false hres l hl (by omega)
  have hCR := shadowCtxOk hO hlenAll (nP := nP) (ks := kindsOf ks) (Nat.le_refl _) hO.bodyScoped.1
    hO.bodyScoped.2.2.2 hnorecR (fun i hi' hr ρ' hρ' => (key i hi' ρ' hρ').1)
  rw [Nat.sub_self, List.drop_zero] at hCR
  have hrow := (claimsAt_of hμ mp ψ F').sortRow hib hensb hO.bodyScoped.1 hO.bodyScoped.2.1
    hO.bodyScoped.2.2.1 hCR hO.body ρ hρ
  exact hrow.1

theorem mutualTeleBound_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env}
    {sorts : List Level}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hProp : isProp = true → ∀ ψ : Name → Nat, Level.eval ψ resSort = Level.eval ψ Level.zero)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : MutualCtorDataI mp.base2 env₀ members T lps cvCa nP nF nIdx resSort isProp large
      idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : Name → Nat) (hw : resSort.eval ψ ≠ 0) {i : Nat} (hi : i < nF)
    (hk : kindAt ks i = .reflexive) {ρp : Nat → V}
    (hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp) {as' : List V}
    (hsp' : SpineFit ρp ((shadowFs nP (kindsOf ks) nF (((ds ψ).drop nP).map (·.2.2))).take i) as') :
    ∀ k, k < ((tss ψ).getD i []).length → ∀ bs : List V,
      SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs →
      WellDenoted V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2 ∧
      interp V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2
        ∈ˢ (univ (resSort.eval ψ) : V) := by
  -- the run's pieces
  obtain ⟨⟨_, hccv⟩, -, fvsP', crest', tfvs, trest, xFvs', idxArgs', hopC, -, -, hopX, -, -, -,
    hsorts⟩ := ConLeche.checkMutualCtor_shape hCtor
  obtain ⟨crest, hopP, hopXX⟩ := hD.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxrest⟩ := Prod.mk.inj (Option.some.inj (hopXX.symm.trans hopX))
  obtain ⟨-, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.mutual_ctor_typeWF hCtor
  have hopAll : ConLeche.openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopXX)
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenDs := hD.len ψ
  have hlenAll : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hD.pLen, hD.xLen]
  -- the shadow gradings
  obtain ⟨hkey, -⟩ := mutualShadowGrading hμ mp hCtor hProp hD ψ
  -- a recursive variable is a leaf of no later domain
  have hrecGet : ∀ i, recAt nP (kindsOf ks) (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
    · obtain ⟨-, -, -, -, hlater, -⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, -⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater⟩
  -- the field: its variable, scoped, leaf-free of the recursive variables
  have hil : i < xFvs.length := by rw [hD.xLen]; exact hi
  obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
  have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
    rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
    exact hx
  obtain ⟨-, hws, hbnd, hL, hleaf⟩ := hO.var (nP + i) _ hxA
  have hnorec : ∀ l ∈ x.fvarTypeD.fvarLeaves, ¬ recAt nP (kindsOf ks) l.1 := by
    intro l hl hr
    have hge := hr.1
    have hlt : l.1 < nP + i := Expr.fvarLeaves_lt_of_wscoped hws l hl
    obtain ⟨x', hx', hlater⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    have hmem : x ∈ xFvs.drop (l.1 - nP + 1) := by
      refine List.mem_of_getElem? (i := i - (l.1 - nP + 1)) ?_
      rw [List.getElem?_drop, show l.1 - nP + 1 + (i - (l.1 - nP + 1)) = i from by omega]
      exact hx
    exact mentionsFvar_false (hlater x hmem) l hl (by omega)
  -- the context discipline at the field
  have hC : CtxOk mp.base2 ψ (nP + i)
      ((shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - (nP + i)))
      x.fvarTypeD :=
    shadowCtxOk hO hlenAll (nP := nP) (ks := kindsOf ks) (by omega) hws hleaf hnorec
      (fun i' hi' _ ρ' hρ' => (hkey i' (by omega) ρ' hρ').1)
  -- the telescope's opening and readings
  obtain ⟨afvs, body, hop, hlenPi, hdoms, -⟩ := hD.reflOpen ψ i x hx hk
  have hlenT : ((tss ψ).getD i []).length = afvs.length := (openPisAtFvars_length _ hop).symm
  -- the field's sort row
  obtain ⟨fv, ty, u, hfv, -, hinf, hens, hleq, -⟩ := hfields i hi
  obtain rfl := Option.some.inj (hx.symm.trans hfv)
  have hnp : isProp = false := by
    cases hp : isProp
    · rfl
    · exfalso
      have h0 := hProp hp ψ
      exact hw (by simpa [Level.eval] using h0)
  have hle := Level.leq_sound (hleq hnp) ψ
  -- the field's sort is nonzero: the telescope's bits are at the
  -- family's regime, and exact against the innermost body's sort
  have hu : Level.eval ψ u ≠ 0 := by
    obtain ⟨-, -, vb, -, -, hv, hbits⟩ := piBits_of_infer hμ _ hop hinf hens
    intro hu0
    have hvb : Level.eval ψ vb = 0 := (hv ψ).mp hu0
    obtain ⟨afvs', body', hop', hne, -, -, -, -, -, -, -⟩ := hD.opened.reflF i x hx hk
    have hread := hO.doms (nP + i) x hxA
    rw [reverse_getD_field hlenDs hi, drop_map_getD hlenDs hi, hD.reflEntry ψ i hk hi] at hread
    have hst := stripPisAV_mkPisAV ((tss ψ).getD i [])
      (AnnotTerm.mkAppN (mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ)
        (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))
    have hb := stripPisAV_bits _ (hbits ψ) hread hst
    have hne' : (tss ψ).getD i [] ≠ [] := by
      intro htl
      have : afvs.length = 0 := by rw [← hlenT, htl]; rfl
      have hm : afvs'.length = afvs.length := by
        rw [openPisAtFvars_length _ hop', openPisAtFvars_length _ hop, hlenPi]
      exact hne (by rw [hm, this])
    obtain ⟨d0, tl', htl⟩ := List.exists_cons_of_ne_nil hne'
    have hmem : d0 ∈ (tss ψ).getD i [] := by rw [htl]; exact List.mem_cons_self
    have h1 := hb d0 hmem
    have h2 := hD.tssBits ψ i d0 hmem
    exact hw (h2.mp (h1.mpr hvb))
  -- the domains' sorts
  have hinfD : ∀ k a, afvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u' : Level),
      ConLeche.inferTypeCore μ env F (nP + i + k) a.fvarTypeD = .ok t ∧
      ConLeche.ensureSortCore μ env F (nP + i + k) t = .ok u' ∧ Level.eval ψ u' ≤ resSort.eval ψ := by
    intro k a hka
    obtain ⟨F', t', u', h1, h2, h3⟩ := piDoms_of_infer _ hop hinf hens k a hka
    exact ⟨F', t', u', h1, h2, Nat.le_trans (h3 ψ hu) hle⟩
  -- the walk
  intro k hkT bs hbs
  have hsat : Sat V ((shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
      (nP + nF - (nP + i))) (consList as' ρp) := by
    rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
    exact sat_of_spineFit hρp' hsp'
  have hρ := sat_of_spineFit hsat hbs
  have := teleBound_walk hμ mp ψ (w := resSort.eval ψ) ((tss ψ).getD i []).length hop rfl hC hws hbnd hL
    hdoms hinfD k hkT _ hρ
  exact ⟨this.1.1, this.2⟩

theorem mutualCtorFrames (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → ∀ ψ : Name → Nat, Level.eval ψ resSort = Level.eval ψ Level.zero)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
    -- the fields' sorts, as the stage read them (task #210 Part A: the
    -- projection table's guard levels at a structure-like block): one
    -- per field, each bounded by the result sort at a non-`Prop` family,
    -- and the field's reading along a fitting prefix a member of its
    -- sort's universe
    (sorts.length = nF ∧
      (∀ j, j < nF → isProp = false → Level.leq (sorts.getD j .zero) resSort = some true) ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
  obtain ⟨⟨_, hccv⟩, -, fvsP, crest, tfvs, trest, xFvs, idxArgs', hopC, hopT, hdoms, hopX,
    -, -, -, hsorts⟩ := ConLeche.checkMutualCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopC hsorts
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hpins := ConLeche.checkStructDomsAt_inv hdoms
  have hlenX : xFvs.length = nF := openPisAtFvars_length _ hopX
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    -- the former, opened at the parameters
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hopT hTf hTb (hFD.read ψ) (hFD.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take nP (ppsAll ψ) (AnnotTerm.sort (resSort.eval ψ))
      (by rw [hFD.len ψ]; omega)
    obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
    subst hΓt
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs'))
        ((ds ψ).map (·.2.2)).reverse (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
      opened_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hlenF : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
    have hiff : ∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ := by
      intro ρ
      have := (hpf nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    have hrow : ∀ j, j < nF → ∃ u, sorts[j]? = some u ∧
        (isProp = false → Level.leq u resSort = some true) ∧
        ∀ ρ : Nat → V,
          Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + j))) ρ →
          interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD
            (nP + nF - 1 - (nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, -⟩ := hfields j hj
      refine ⟨u, hu, hleq, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
      have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
      have hread := hC.doms (nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hsortsPart : ∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) := by
      intro ρ hρ j hj as hsp
      obtain ⟨u, hu, -, hmem⟩ := hrow j hj
      have hsat := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
      have hdropj : ((((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - (nP + j))
          = ((((ds ψ).drop nP).map (·.2.2)).take j).reverse ++
            (((ds ψ).take nP).map (·.2.2)).reverse := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - (nP + j) = nF - j from by omega,
          List.drop_append_of_le_length (by rw [List.length_reverse, hlenF]; exact Nat.sub_le _ _),
          List.drop_reverse, hlenF, show nF - (nF - j) = j from by omega]
      have hentj : ((((ds ψ).map (·.2.2)).reverse)).getD (nP + nF - 1 - (nP + j)) default
          = (((ds ψ).drop nP).map (·.2.2)).getD j default := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_reverse, hlenF]; omega),
          List.getElem?_reverse (by rw [hlenF]; omega), hlenF,
          show nF - 1 - (nF - 1 - j) = j from by omega, ← List.getD_eq_getElem?_getD]
      have := hmem (consList as ρ) (by rw [hdropj]; exact hsat)
      rw [hentj] at this
      rw [List.getD_eq_getElem?_getD (l := sorts), hu]
      exact this
    refine ⟨hiff, fun ρ hρ => ?_, hsortsPart⟩
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by
      simp [hlenDs]
    have hρ' : Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      by_cases hnp : isProp = true
      · exfalso
        have h0 := hProp hnp ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · rw [← hFsEq]
      exact fieldsValid_of_frame rfl hΓlen hC.okΓ 0 (Nat.zero_le _) ρ hρ'
    · intro hnp
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      have hle := Level.leq_sound (hleq hnp) ψ
      exact univ_mono hle _ (hmem ρ hρ)
    · -- the index expressions at a fitting field spine
      intro bs hsp
      have hlenB : bs.length = nF := by rw [hsp.length_eq, hlenF]
      have hsat : Sat V (((ds ψ).map (·.2.2)).reverse) (consList bs ρ) := by
        have := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
        rwa [← reverse_map_take_drop] at this
      have hokRP := hC.okR _ hsat
      unfold ctorBodyAVI at hokRP
      have hokR := hokRP.1
      obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokR
      obtain ⟨-, hargsV⟩ := AnnotValid.mkAppN_inv hokRP.2
      refine ⟨fun E hE => ⟨hargs E (List.mem_append_right _ hE),
        hargsV E (List.mem_append_right _ hE)⟩, ?_⟩
      -- the spine fits the former's leaf
      obtain ⟨B, hB⟩ := hleafT ψ
      have hfit := spineFit_of_wellDenoted_lams (u := resSort.eval ψ + 1) (Nat.succ_ne_zero _)
        (b := B) (args := paramBvars nP nF ++ Es ψ)
        (ds := ppsAll ψ) (σ := consList bs ρ) (ρ := consList bs ρ) (f := mp.base2.acval T ψ)
        (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]) hokR (by rw [hB])
      rw [List.take_of_length_le (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]),
        ← List.take_append_drop nP (ppsAll ψ), List.map_append, List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = nP := by
        rw [h1.length_eq, List.length_map, List.length_take, hFD.len ψ]; omega
      have hps : (paramBvars nP nF).map (interp V (consList bs ρ))
          = (List.range nP).reverse.map ρ := by
        rw [paramBvars_eq_paramBvarsAt]
        exact map_paramBvarsAt_interp (fun j => by rw [← hlenB]; exact consList_apply_add bs ρ j)
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvars])
      rw [hps] at h2
      show SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) ((Es ψ).map (interp V (consList bs ρ)))
      refine spineFit_congr_below (DomsBelow.drop nP (hFD.below ψ)) ?_ h2
      intro i hi
      rw [Nat.zero_add] at hi
      exact consList_params_apply ρ _ hi
  refine ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2.1, hlenS, ?_, fun ψ => (hframes ψ).2.2⟩
  intro j hj hnp
  obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hfields j hj
  rw [List.getD_eq_getElem?_getD, hu]
  exact hleq hnp

end ConLeche.Model
