import Setlec.Model.EtaInstall
import Setlec.Model.Extend.Modeled

/-!
# Capability laws at a modeled block's family-completing member

The public-name capability laws (`EtaLaw`/`UnitLaw`, consumed through
`EnvModel.caps_ok`) are owed exactly when a family is *complete*
(`EtaFamilyStored`).  For a modeled block that happens at the member
install that stores the family's last constituent — the constructor
for a fieldless structure, the last projection function otherwise —
and the derivation there has the block's **group-local**
public↔`_model` identification in scope (`BlockInstalled`, the
projection phase's `ProjPhaseInv`), plus the pinned artifact shape
facts (`EtaPins`).  This module packages the assembly once:

* `BlockInstalled.renameOk` — the semantically pruned block renaming
  is `RenameOk` at any environment carrying the block invariant;
* `modeled_caps_eta` / `modeled_caps_unit` — the laws over an
  *extended* valuation `val₁` (one fresh constant `ci` over a base
  model `m`), derived from `eta_rule_fold`/`unit_rule_fold` and
  rewritten to the public names through the supplied identifications.

Nothing here persists: the identifications are hypotheses local to
the one block's install derivation, discharged from its fold
invariants and discarded at its end (the group-local contract; see
DESIGN.md, "Group-local identification").
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

variable {V : Type u} [SetTheory V]

open SetTheory Expr

omit [SetTheory V] in
/-- The semantically pruned block renaming is `RenameOk` at any
environment/valuation pair carrying the block-install invariant. -/
theorem BlockInstalled.renameOk {blockNames : List Name} {env₁ : Env}
    {val₁ : ConstVal V}
    (hI : BlockInstalled blockNames env₁ val₁) :
    RenameOk val₁ env₁ (fun n => if (env₁.find? n).isSome = true then
      (if blockNames.contains n then n.str "_model" else n) else n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ci₂ hf₂
    have hsome : (env₁.find? n).isSome = true := by rw [hf₂]; rfl
    simp only [hsome, if_true]
    by_cases hc : blockNames.contains n = true
    · rw [if_pos hc]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -, -⟩ := hI n hc ci₂ hf₂
      exact ⟨.defnInfo cvm₂ mval₂ hm₂, hfm₂, hlps₂⟩
    · rw [if_neg hc]
      exact ⟨ci₂, hf₂, rfl⟩
  · intro n hf₂
    simp [hf₂]
  · intro n ψ
    cases hf₂ : env₁.find? n with
    | none => simp [hf₂]
    | some ci₂ =>
      have hsome : (env₁.find? n).isSome = true := by rw [hf₂]; rfl
      simp only [hsome, if_true]
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvm₂, mval₂, -, -, -, -, hv₂⟩ := hI n hc ci₂ hf₂
        exact (hv₂ ψ).symm
      · rw [if_neg hc]

/-- `ConstValParams` of an extended valuation whose block members are
valued by their `_model` companions. -/
theorem ConstValParams.extend_head {env : Env} (m : EnvModel V env)
    {ci : ConstantInfo} {val₁ : ConstVal V} {blockNames : List Name}
    (hagree : ∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name →
      val₁ n ψ = m.val n ψ)
    (hI₁ : BlockInstalled blockNames (⟨ci :: env.consts⟩ : Env) val₁)
    (hciblock : blockNames.contains ci.name = true) :
    ConstValParams val₁ (⟨ci :: env.consts⟩ : Env) := by
  intro n ci₂ hf ψ₁ ψ₂ hψ
  by_cases hn : n = ci.name
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    obtain rfl : ci = ci₂ := Option.some.inj hf
    obtain ⟨cvm, mval, hm, hfm, hlps, -, hv⟩ := hI₁ ci.name hciblock ci
      (by rw [Env.find?_cons, if_pos rfl])
    have hfmE : env.find? (ci.name.str "_model") =
        some (.defnInfo cvm mval hm) := by
      rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci.name "_model" h.symm)] at hfm
      exact hfm
    rw [hv ψ₁, hv ψ₂,
      hagree _ ψ₁ (Name.str_ne ci.name "_model"),
      hagree _ ψ₂ (Name.str_ne ci.name "_model")]
    refine m.val_params _ _ hfmE ψ₁ ψ₂ ?_
    intro p hp
    refine hψ p ?_
    rw [show (ConstantInfo.defnInfo cvm mval hm).toConstantVal = cvm
      from rfl] at hp
    rw [← hlps]
    exact hp
  · rw [Env.find?_cons, if_neg (fun h => hn h.symm)] at hf
    rw [hagree n ψ₁ hn, hagree n ψ₂ hn]
    exact m.val_params n ci₂ hf ψ₁ ψ₂ hψ

section Laws

variable {env : Env} (m : EnvModel V env)
  {ci : ConstantInfo} {val₁ : ConstVal V} {blockNames : List Name}
  (hfresh : env.find? ci.name = none)
  (hagree : ∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name →
    val₁ n ψ = m.val n ψ)
  (hI₁ : BlockInstalled blockNames (⟨ci :: env.consts⟩ : Env) val₁)
  (hcvp : ConstValParams val₁ (⟨ci :: env.consts⟩ : Env))
  (hcinres : reservedBasisNames.contains ci.name = false)
  (hcikindT : ∀ cv2 v2, ci ≠ .thmInfo cv2 v2)

/-- A stored theorem's lookup at the extended environment lands below
a non-theorem head, and its `m`-side membership/annotation facts
transport up. -/
private theorem thm_below {nn : Name} {tcv2 : ConstantVal} {tval2 : Expr}
    (hcikindT' : ∀ cv2 v2, ci ≠ .thmInfo cv2 v2)
    (hf : (⟨ci :: env.consts⟩ : Env).find? nn = some (.thmInfo tcv2 tval2)) :
    env.find? nn = some (.thmInfo tcv2 tval2) := by
  rw [Env.find?_cons] at hf
  split at hf
  · exact absurd (Option.some.inj hf) (hcikindT' tcv2 tval2)
  · exact hf

variable {φ' : Name → Nat}

set_option maxHeartbeats 6400000 in
include m hfresh hagree hI₁ hcvp hcinres hcikindT in
/-- The public-name eta law of a stored eta-capable modeled former
`T`, at the extension of a base model by one fresh block member `ci`.
The artifact shape facts are the pins at the extended environment;
the identifications convert `eta_rule_fold`'s `_model`-valued law to
the public names. -/
theorem modeled_caps_eta
    {T : Name} {cvTa : ConstantVal} {capsT : IndCaps}
    (hcape : capsT.eta = true)
    (hpins : EtaPins mode (⟨ci :: env.consts⟩ : Env) T cvTa.levelParams capsT)
    (hren : ∀ cvmT mvalT hm,
      (⟨ci :: env.consts⟩ : Env).find? (T.str "_model") =
        some (.defnInfo cvmT mvalT hm) →
      Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n))
        cvmT.type = true)
    (htyf : cvTa.type.hasFvar = false)
    (htres₁ : cvTa.type.constsResolve (⟨ci :: env.consts⟩ : Env) = true)
    (hvT : ∀ ψ : Name → Nat, val₁ T ψ = val₁ (T.str "_model") ψ)
    (hvC : ∀ ψ : Name → Nat,
      val₁ capsT.etaCtor ψ = val₁ (capsT.etaCtor.str "_model") ψ)
    (hvP : ∀ j, j < capsT.etaFields → ∀ ψ : Name → Nat,
      val₁ (projFnName T j) ψ = val₁ (projModelName T j) ψ) :
    EtaLaw V (⟨ci :: env.consts⟩ : Env) val₁ T cvTa capsT := by
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE,
    ⟨cvmC, mvalC, hmC, hCmE, hCmlpsE⟩, hPjE, heqfE, hS_stripE,
    hTm_stripE, hsdomsE, hxdomE, hsbodyE, htySlotE, -⟩ := hpins.1 hcape
  have hagreeS : ∀ n, (env.find? n).isSome = true →
      ∀ ψ : Name → Nat, val₁ n ψ = m.val n ψ := by
    intro n hn ψ
    refine hagree n ψ ?_
    intro he
    rw [he, hfresh] at hn
    exact nomatch hn
  -- the pruned renaming and its `RenameOk`
  obtain ⟨fb, hfb⟩ : ∃ fb : Name → Name, fb = fun n =>
      if blockNames.contains n then n.str "_model" else n := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ : ∃ fS : Name → Name, fS = fun n =>
      if ((⟨ci :: env.consts⟩ : Env).find? n).isSome = true then fb n
      else n := ⟨_, rfl⟩
  have hroS : RenameOk val₁ (⟨ci :: env.consts⟩ : Env) fS := by
    rw [hfS, hfb]
    exact hI₁.renameOk
  have hfSfound : ∀ n,
      (((⟨ci :: env.consts⟩ : Env)).find? n).isSome = true →
      fS n = fb n := by
    intro n hn
    rw [hfS]
    simp only [hn, if_true]
  have hrenS : Expr.eqUpToNames (cvTa.type.renameConsts fS) cvmT.type =
      true := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) cvTa.type htres₁]
    rw [hfb]
    exact hren cvmT mvalT hmT hTmE
  -- the eq pin's value
  have heqne : eqName ≠ ci.name := by
    intro he
    rw [← he] at hcinres
    rw [show reservedBasisNames.contains eqName = true from by decide]
      at hcinres
    exact nomatch hcinres
  have heqfE₀ : env.find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (fun h => heqne h.symm)] at heqfE
    exact heqfE
  have heqval : ∀ ψ'' : Name → Nat, val₁ eqName ψ'' = eqVal V ψ'' := by
    intro ψ''
    obtain ⟨-, hpv⟩ :=
      m.ind_ok.2.2.2.1 eqName eqA heqfE₀ (by rfl) (by decide)
    rw [hagree eqName ψ'' heqne, hpv ψ'']
    simp [pinnedVal]
  -- the artifact theorem's facts, transported up
  have hthmE₀ : env.find? ((T.str "_model").str "eta") =
      some (.thmInfo tcv tval) := thm_below hcikindT hthmE
  have hSw : tcv.type.hasFvar = false := by
    obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE₀)
    exact h1
  have hSres : tcv.type.constsResolve env = true := by
    obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hthmE₀)
    exact h3
  have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val₁ (⟨ci :: env.consts⟩ : Env) ψ'' tcv.type =
        some Pv ∧ val₁ tcv.name ψ'' ∈ˢ Pv := by
    intro ψ''
    obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE₀) ψ''
    refine ⟨P, ?_, ?_⟩
    · rw [interpClosed_extend_fresh hfresh hagreeS hSres ψ'']
      exact hP
    · have hne : tcv.name ≠ ci.name := by
        have h2 : tcv.name = (T.str "_model").str "eta" := by
          have h1 := List.find?_some hthmE₀
          simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h1
        rw [h2]
        intro he
        have hs : (env.find? ((T.str "_model").str "eta")).isSome
            = true := by
          rw [hthmE₀]; rfl
        rw [he, hfresh] at hs
        exact nomatch hs
      rw [hagree _ ψ'' hne]
      exact hmem
  have hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val₁ (⟨ci :: env.consts⟩ : Env) ψ'' 0 (rho0 V)
        tcv.type := by
    intro ψ''
    exact AnnotOk.extend_fresh hfresh hagreeS hSres ψ''
      (m.annot_ok _ (find?_mem hthmE₀) ψ'').1
  -- the statement/type telescope relation
  obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
    Expr.ErasedEq.stripPis_inv capsT.etaParams
      (Expr.ErasedEq.of_eqUpToNames hrenS) hTm_stripE
  obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
    Expr.stripPis_renameConsts_inv (f := fS) capsT.etaParams hstripR
  have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      k < capsT.etaParams →
      sbinders[k]? = some b → tbinders[k]? = some b' →
      RenEq fS b'.2.1 b.2.1 := by
    intro k b b' hk hb hb'
    have hbR : bsR[k]? =
        some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
      rw [hbsmap, List.getElem?_map, hb']
      rfl
    have hklt : k < tbindersM.length := by
      have h1 : bsR[k]?.isSome = true := by rw [hbR]; rfl
      simp at h1
      omega
    have hbm : tbindersM[k]? = some tbindersM[k] :=
      List.getElem?_eq_getElem hklt
    have hrel := (hdomsR k _ _ hbR hbm).1
    have hpin : b.2.1 = tbindersM[k].2.1 :=
      hsdomsE k b _ hk hb hbm
    show Expr.ErasedEq ((b'.2.1).renameConsts fS) b.2.1
    rw [hpin]
    exact hrel
  -- assemble and rewrite to the public names
  intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
  have hx' : x ∈ˢ SpineFold V
      (val₁ (T.str "_model")
        (Level.substFn φ'' cvTa.levelParams us)) ps := by
    rw [← hvT]
    exact hx
  have h1 := eta_rule_fold hroS hcvp hTmE hTmlpsE
    (cimC := .defnInfo cvmC mvalC hmC) hCmE hCmlpsE
    (fun j hj => by
      obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPjE j hj
      exact ⟨.defnInfo cvmj mvalj hmj, hfj, hjlps⟩)
    heqfE heqval hthm_mem hthm_annot hSw hS_stripE hT_strip
    hsdomsF hxdomE hsbodyE htySlotE htyf hlen hx' hfit
  rw [hvC]
  have h2 : ((List.range capsT.etaFields).map fun j =>
      SpineFold V (val₁ (projFnName T j)
        (Level.substFn φ'' cvTa.levelParams us)) (ps ++ [x])) =
      ((List.range capsT.etaFields).map fun j =>
      SpineFold V (val₁ (projModelName T j)
        (Level.substFn φ'' cvTa.levelParams us)) (ps ++ [x])) := by
    refine List.map_congr_left ?_
    intro j hj
    rw [hvP j (List.mem_range.mp hj)]
  rw [h2]
  exact h1

set_option maxHeartbeats 6400000 in
include m hfresh hagree hI₁ hcvp hcinres hcikindT in
/-- The unit-like law, sibling of `modeled_caps_eta`. -/
theorem modeled_caps_unit
    {T : Name} {cvTa : ConstantVal} {capsT : IndCaps}
    (hcapu : capsT.unitlike = true)
    (hpins : EtaPins mode (⟨ci :: env.consts⟩ : Env) T cvTa.levelParams capsT)
    (hren : ∀ cvmT mvalT hm,
      (⟨ci :: env.consts⟩ : Env).find? (T.str "_model") =
        some (.defnInfo cvmT mvalT hm) →
      Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n))
        cvmT.type = true)
    (htyf : cvTa.type.hasFvar = false)
    (htres₁ : cvTa.type.constsResolve (⟨ci :: env.consts⟩ : Env) = true)
    (hvT : ∀ ψ : Name → Nat, val₁ T ψ = val₁ (T.str "_model") ψ) :
    UnitLaw V (⟨ci :: env.consts⟩ : Env) val₁ T cvTa capsT := by
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE, heqfE,
    hS_stripE, hTm_stripE, hsdomsE, hxdomE, hydomE, hsbodyE,
    htySlotE, -⟩ :=
    hpins.2 hcapu
  have hagreeS : ∀ n, (env.find? n).isSome = true →
      ∀ ψ : Name → Nat, val₁ n ψ = m.val n ψ := by
    intro n hn ψ
    refine hagree n ψ ?_
    intro he
    rw [he, hfresh] at hn
    exact nomatch hn
  obtain ⟨fb, hfb⟩ : ∃ fb : Name → Name, fb = fun n =>
      if blockNames.contains n then n.str "_model" else n := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ : ∃ fS : Name → Name, fS = fun n =>
      if ((⟨ci :: env.consts⟩ : Env).find? n).isSome = true then fb n
      else n := ⟨_, rfl⟩
  have hroS : RenameOk val₁ (⟨ci :: env.consts⟩ : Env) fS := by
    rw [hfS, hfb]
    exact hI₁.renameOk
  have hfSfound : ∀ n,
      (((⟨ci :: env.consts⟩ : Env)).find? n).isSome = true →
      fS n = fb n := by
    intro n hn
    rw [hfS]
    simp only [hn, if_true]
  have hrenS : Expr.eqUpToNames (cvTa.type.renameConsts fS) cvmT.type =
      true := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) cvTa.type htres₁]
    rw [hfb]
    exact hren cvmT mvalT hmT hTmE
  have heqne : eqName ≠ ci.name := by
    intro he
    rw [← he] at hcinres
    rw [show reservedBasisNames.contains eqName = true from by decide]
      at hcinres
    exact nomatch hcinres
  have heqfE₀ : env.find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (fun h => heqne h.symm)] at heqfE
    exact heqfE
  have heqval : ∀ ψ'' : Name → Nat, val₁ eqName ψ'' = eqVal V ψ'' := by
    intro ψ''
    obtain ⟨-, hpv⟩ :=
      m.ind_ok.2.2.2.1 eqName eqA heqfE₀ (by rfl) (by decide)
    rw [hagree eqName ψ'' heqne, hpv ψ'']
    simp [pinnedVal]
  have hthmE₀ : env.find? ((T.str "_model").str "unitlike") =
      some (.thmInfo tcv tval) := thm_below hcikindT hthmE
  have hSw : tcv.type.hasFvar = false := by
    obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE₀)
    exact h1
  have hSres : tcv.type.constsResolve env = true := by
    obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hthmE₀)
    exact h3
  have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
      interpClosed V val₁ (⟨ci :: env.consts⟩ : Env) ψ'' tcv.type =
        some Pv ∧ val₁ tcv.name ψ'' ∈ˢ Pv := by
    intro ψ''
    obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE₀) ψ''
    refine ⟨P, ?_, ?_⟩
    · rw [interpClosed_extend_fresh hfresh hagreeS hSres ψ'']
      exact hP
    · have hne : tcv.name ≠ ci.name := by
        have h2 : tcv.name = (T.str "_model").str "unitlike" := by
          have h1 := List.find?_some hthmE₀
          simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h1
        rw [h2]
        intro he
        have hs : (env.find? ((T.str "_model").str "unitlike")).isSome
            = true := by
          rw [hthmE₀]; rfl
        rw [he, hfresh] at hs
        exact nomatch hs
      rw [hagree _ ψ'' hne]
      exact hmem
  have hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V val₁ (⟨ci :: env.consts⟩ : Env) ψ'' 0 (rho0 V)
        tcv.type := by
    intro ψ''
    exact AnnotOk.extend_fresh hfresh hagreeS hSres ψ''
      (m.annot_ok _ (find?_mem hthmE₀) ψ'').1
  obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
    Expr.ErasedEq.stripPis_inv capsT.unitParams
      (Expr.ErasedEq.of_eqUpToNames hrenS) hTm_stripE
  obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
    Expr.stripPis_renameConsts_inv (f := fS) capsT.unitParams hstripR
  have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      k < capsT.unitParams →
      sbinders[k]? = some b → tbinders[k]? = some b' →
      RenEq fS b'.2.1 b.2.1 := by
    intro k b b' hk hb hb'
    have hbR : bsR[k]? =
        some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
      rw [hbsmap, List.getElem?_map, hb']
      rfl
    have hklt : k < tbindersM.length := by
      have h1 : bsR[k]?.isSome = true := by rw [hbR]; rfl
      simp at h1
      omega
    have hbm : tbindersM[k]? = some tbindersM[k] :=
      List.getElem?_eq_getElem hklt
    have hrel := (hdomsR k _ _ hbR hbm).1
    have hpin : b.2.1 = tbindersM[k].2.1 :=
      hsdomsE k b _ hk hb hbm
    show Expr.ErasedEq ((b'.2.1).renameConsts fS) b.2.1
    rw [hpin]
    exact hrel
  intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
  have hx' : x ∈ˢ SpineFold V
      (val₁ (T.str "_model")
        (Level.substFn φ'' cvTa.levelParams us)) ps := by
    rw [← hvT]
    exact hx
  have hy' : y ∈ˢ SpineFold V
      (val₁ (T.str "_model")
        (Level.substFn φ'' cvTa.levelParams us)) ps := by
    rw [← hvT]
    exact hy
  exact unit_rule_fold hroS hcvp hTmE hTmlpsE heqfE heqval
    hthm_mem hthm_annot hSw hS_stripE hT_strip hsdomsF hxdomE
    hydomE hsbodyE htySlotE htyf hlen hx' hy' hfit

end Laws

/-- The uniform eta head-obligation discharge for a modeled block
member's install (`checkIndMember_sound`'s forwarded `hheadEta`).  A
family completed by the member belongs either to a *block* former —
whose pins, capability-constructor blockness and projection-name
freeness the caller supplies (`hblockT`), so the law is either refuted
(fields still pending) or established through `modeled_caps_eta` with
the block identification — or to an *outside* former, whose family is
already closed (`hE1`), so the fresh member cannot participate. -/
theorem blockMember_headEta {env : Env} (m : EnvModel V env)
    {ciH : ConstantInfo} {blockNames : List Name}
    (hfresh : env.find? ciH.name = none)
    (hcinres : reservedBasisNames.contains ciH.name = false)
    (hshape : ciH.name.isProjFnShape = false)
    (hcikindT : ∀ cv2 v2, ciH ≠ .thmInfo cv2 v2)
    (hciblock : blockNames.contains ciH.name = true)
    (hE1 : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      env.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T = false →
      blockNames.contains T = false →
      ∃ cvC, env.find? capsT.etaCtor =
        some (.ctorInfo cvC capsT.etaParams capsT.etaFields))
    (hblockT : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨ciH :: env.consts⟩ : Env).find? T = some (.indInfo cvT capsT) →
      blockNames.contains T = true → capsT.eta = true →
      EtaPins mode env T cvT.levelParams capsT ∧
      blockNames.contains capsT.etaCtor = true ∧
      cvT.type.hasFvar = false ∧
      cvT.type.constsResolve env = true ∧
      ∀ j, j < capsT.etaFields → env.find? (projFnName T j) = none) :
    ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨ciH :: env.consts⟩ : Env).find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ciH :: env.consts⟩ T capsT →
      (T = ciH.name ∨ capsT.etaCtor = ciH.name ∨
        ∃ j, j < capsT.etaFields ∧ projFnName T j = ciH.name) →
      ∀ val₁ : ConstVal V,
        (∀ (n : Name) (ψ : Name → Nat), n ≠ ciH.name →
          val₁ n ψ = m.val n ψ) →
        (∀ ψ : Name → Nat,
          val₁ ciH.name ψ = m.val (ciH.name.str "_model") ψ) →
        BlockInstalled blockNames ⟨ciH :: env.consts⟩ val₁ →
        EtaLaw V ⟨ciH :: env.consts⟩ val₁ T cvT capsT := by
  intro T cvT capsT hfT hcape hresT hfam hpart val₁ he₁ hv₁ hI₁
  have hPneH : ∀ j, projFnName T j ≠ ciH.name := by
    intro j hh
    rw [← hh] at hshape
    rw [show (projFnName T j).isProjFnShape = true from rfl] at hshape
    exact nomatch hshape
  by_cases hTb : blockNames.contains T = true
  · -- a block former's family
    obtain ⟨hpinsT, hCb, htyfT, htresT, hPfree⟩ :=
      hblockT T cvT capsT hfT hTb hcape
    obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
    cases hEF : capsT.etaFields with
    | succ k =>
      -- a projection function would have to be stored already, but
      -- the family's projection names are still free
      exfalso
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP 0 (by omega)
      rw [Env.find?_cons,
        if_neg (fun hh => hPneH 0 hh.symm)] at hf2
      rw [hPfree 0 (by omega)] at hf2
      exact nomatch hf2
    | zero =>
      -- the family is complete: establish the law
      obtain ⟨cvm', mval', hm', hfm', hlps', hren', hvT'⟩ :=
        hI₁ T hTb _ hfT
      have hvC' : ∀ ψ : Name → Nat, val₁ capsT.etaCtor ψ =
          val₁ (capsT.etaCtor.str "_model") ψ := by
        intro ψ
        obtain ⟨cvmC, mvalC, hmC, hfmC, -, -, hvC⟩ :=
          hI₁ capsT.etaCtor hCb _ hfC
        exact hvC ψ
      refine modeled_caps_eta (ci := ciH) m hfresh he₁ hI₁
        (ConstValParams.extend_head m he₁ hI₁ hciblock) hcinres
        hcikindT hcape (EtaPins.step hpinsT hfresh) ?_ htyfT
        (Expr.constsResolve_mono htresT) hvT' hvC' ?_
      · intro cvmT mvalT hm2 hfm₁
        rw [hfm'] at hfm₁
        obtain h1 := Option.some.inj hfm₁
        injection h1 with e1 e2 e3
        subst e1
        exact hren'
      · intro j hj
        rw [hEF] at hj
        exact absurd hj (by omega)
  · -- an outside former: its family is closed, so the fresh head
    -- cannot participate
    exfalso
    have hTneH : T ≠ ciH.name := by
      intro he
      rw [he, hciblock] at hTb
      exact hTb rfl
    have hfT' : env.find? T = some (.indInfo cvT capsT) := by
      rw [Env.find?_cons, if_neg (fun hh => hTneH hh.symm)] at hfT
      exact hfT
    have hTbf : blockNames.contains T = false := by
      revert hTb
      cases blockNames.contains T <;> simp
    obtain ⟨cvC, hfC⟩ := hE1 T cvT capsT hfT' hcape hresT hTbf
    rcases hpart with rfl | hC | ⟨j, hj, hP⟩
    · exact hTneH rfl
    · have hsC : (env.find? capsT.etaCtor).isSome = true := by
        rw [hfC]
        rfl
      rw [hC, hfresh] at hsC
      exact nomatch hsC
    · exact hPneH j hP

end Setlec
