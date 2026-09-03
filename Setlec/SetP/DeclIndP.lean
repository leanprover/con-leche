import Setlec.SetP.ProjInstallP

/-!
# The modeled-inductive block, assembled at the reading (task #161,
IND TIER part 10)

`declIndS`'s twin, and the ind tier's summit: the four phases compose
at the P tier exactly as they do at v1's.

* `indMembersPM` — the non-recursor members (part 2);
* `indRecsP` — the recursor group, provision/fire/swap (part 10);
* `projInstallP` — the projection functions (part 10);
* `templatesP` — the elimination templates (part 10).

**Everything between them is v1's bookkeeping, unchanged**: the block
split, the freshness chains, `EtaPins.transport`, the `hidR`
identification of the stored former.  Only two facts are genuinely new,
and both are the annotated half of a v1 predicate the phases already
carry: `BlockAcvalInstalled` (vacuous at the base, for the same reason
`BlockInstalledTT` is — no block name is stored before the fold runs)
and `ProjPhaseAcvalP` at the group's output (its first two conjuncts
are `BlockAcvalInstalled` at `T` and at the constructor; its third is
vacuous, the projection slots being fresh there).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName projModelName Declaration)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

set_option maxHeartbeats 3200000 in
/-- **The modeled-inductive block install, P tier.**  The v1 carriers
are taken from the v1 phases (`indRecsS` at the group), which the
install runs anyway; the P phases carry the annotated invariants. -/
theorem declIndP (hμ : μ.verified = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} (mp : EnvS2PM V μ env)
    (hE : Setlec.EtaFamiliesClosed env)
    (h : DeclIndR μ F env mp.base.cval block env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨hsplit, hmain⟩ := h
  -- list bookkeeping about the block's split (v1's, verbatim)
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => false | _ => true),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hEC0 : Setlec.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hnostore : ∀ {caps : IndCaps} {envM envR : Env}
      {cvalM cvalR : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env mp.base.cval
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM cvalM →
      IndRecsR μ F (block.map (·.name)) envM cvalM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR cvalR →
      ∀ n, (block.map (·.name)).contains n = true →
        ∀ ci : ConstantInfo, env.find? n = some ci → False := by
    intro caps envM envR cvalM cvalR hmem hrecs n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [indMembersR_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := indMembersR_mono _ hmem _ _ hf
      rw [indRecsR_fresh hrecs ci₀ hci₀] at hup
      exact nomatch hup
  have hI0gen : ∀ {caps : IndCaps} {envM envR : Env}
      {cvalM cvalR : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env mp.base.cval
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM cvalM →
      IndRecsR μ F (block.map (·.name)) envM cvalM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR cvalR →
      BlockInstalledTT (block.map (·.name)) env mp.base.cval :=
    fun hmem hrecs n hn ci hf =>
      absurd (hnostore hmem hrecs n hn ci hf) (fun h => h)
  -- the annotated half, vacuous at the base for the same reason
  have hIA0gen : ∀ {caps : IndCaps} {envM envR : Env}
      {cvalM cvalR : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env mp.base.cval
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM cvalM →
      IndRecsR μ F (block.map (·.name)) envM cvalM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR cvalR →
      BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun hmem hrecs n hn ci hf =>
      absurd (hnostore hmem hrecs n hn ci hf) (fun h => h)
  have hallGen : ∀ {caps : IndCaps} {envM : Env} {cvalM : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env mp.base.cval
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM cvalM →
      ∀ n, (block.map (·.name)).contains n = true →
        (envM.find? n).isSome = true ∨
        ∃ ci ∈ block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
    intro caps envM cvalM hmem n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersR_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  rcases hmain with ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, harm⟩ |
    ⟨-, envM, cvalM, cval₂, hmem, hrecs⟩
  · -- the single-constructor arm
    obtain ⟨envM, cvalM, envR, cvalR, hmem, hrecs, -, hprojFresh,
      envP, cvalP, hproj, htpl⟩ := harm
    have hmemFil : ∀ {p : ConstantInfo → Bool} {x : ConstantInfo},
        block.filter p = [x] → x ∈ block := by
      intro p x hfil
      have hx : x ∈ block.filter p := by
        rw [hfil]; exact List.mem_singleton_self _
      exact (List.mem_filter.mp hx).1
    have hsingle : ∀ {p : ConstantInfo → Bool} {x y : ConstantInfo},
        block.filter p = [x] → y ∈ block → p y = true → y = x := by
      intro p x y hfil hy hpy
      have hx : y ∈ block.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
      rw [hfil, List.mem_singleton] at hx
      exact hx
    have hTin : ConstantInfo.indInfo cvT capsT ∈ block :=
      hmemFil hIfilt
    have hCin : ConstantInfo.ctorInfo cvC nP nF ∈ block :=
      hmemFil hCfilt
    have hTnon : ConstantInfo.indInfo cvT capsT ∈ block.filter
        (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true) :=
      List.mem_filter.mpr ⟨hTin, rfl⟩
    have hTblock : (block.map (·.name)).contains cvT.name = true :=
      hbnAll _ hTin
    have hCblockN : (block.map (·.name)).contains cvC.name = true :=
      hbnAll _ hCin
    have hbshape : ∀ n, (block.map (·.name)).contains n = true →
        n.isProjFnShape = false := by
      intro n hn
      have hmm : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hx | hx
      · exact (indMembersR_nameGuards _ hmem ci₀ hx).1
      · exact (indRecsR_nameGuards hrecs ci₀ hx).1
    have hTnres : Setlec.reservedBasisNames.contains cvT.name = false :=
      (indMembersR_nameGuards _ hmem _ hTnon).2
    have hmonoR : ∀ n, (env.find? n).isSome = true →
        (envR.find? n).isSome = true := by
      intro n hn
      refine indRecsR_mono hrecs n ?_
      rcases hf : env.find? n with _ | ci
      · rw [hf] at hn; exact nomatch hn
      · rw [indMembersR_mono _ hmem n ci hf]; rfl
    have hpf0 : 0 < nF → env.find? (projFnName cvT.name 0) = none := by
      intro h0
      have hnone := List.all_eq_true.mp hprojFresh 0
        (List.mem_range.mpr h0)
      rcases hf : env.find? (projFnName cvT.name 0) with _ | ci
      · rfl
      · exfalso
        have hs := hmonoR _ (by rw [hf]; rfl)
        rcases hfR : envR.find? (projFnName cvT.name 0) with _ | ci'
        · rw [hfR] at hs; exact nomatch hs
        · rw [hfR] at hnone; exact nomatch hnone
    have hBP0 : Setlec.BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    -- the member fold, both tiers
    obtain ⟨mp₁, hcval₁, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
      indMembersPM memberKeyS memberEtaLawP memberUnitLawP _ mp hbnNon
        (fun cv caps₂ hmm => by
          obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
            (hsingle hIfilt (List.mem_filter.mp hmm).1 rfl)
          exact ⟨etaPins_of_indBlockCaps, fun _ => hCblockN,
            fun _ h0 => hpf0 h0⟩)
        hmem (hI0gen hmem hrecs) (hIA0gen hmem hrecs) hEC0 hBP0
    rw [← hcval₁] at hrecs hI₁
    -- the recursor group, v1 first (for the carrier and the transports)
    obtain ⟨m₂, hm₂cval, hI₂, hnonrecUp, -, -⟩ :=
      indRecsS memberKeyS mp₁.base hI₁ hbnRec (hallGen hmem)
        hEC₁ hBP₁ hrecs
    obtain ⟨mp₂, hcval₂, hIA₂⟩ :=
      indRecsP hμ memberKeyS memberEtaLawP memberUnitLawP mp₁ hI₁ hIA₁
        hbnRec (hallGen hmem) hEC₁ hBP₁ m₂ hm₂cval hrecs
    rw [← hcval₂] at hproj hI₂
    -- the stored former, identified (v1's argument, verbatim)
    have hidR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        cvT'.levelParams = cvT.levelParams ∧
        capsT' = indBlockCaps μ env cvT cvC nP nF := by
      intro cvT' capsT' hf
      obtain ⟨cvA, hnameA, hlpsA, hfM⟩ :=
        indMembersR_indEntry _ hmem cvT capsT hTnon
      have hfR := hnonrecUp cvT.name (.indInfo cvA
        (indBlockCaps μ env cvT cvC nP nF)) hfM
        (fun cv mI rP rules hh => ConstantInfo.noConfusion hh)
      rw [hf] at hfR
      obtain ⟨h1, h2⟩ :=
        ConstantInfo.indInfo.inj (Option.some.inj hfR)
      exact ⟨by rw [h1]; exact hlpsA, h2⟩
    have hkeepR : ∀ (n : Name) (ci : ConstantInfo),
        env.find? n = some ci →
        (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
        envR.find? n = some ci := by
      intro n ci hf hnr
      exact hnonrecUp n ci (indMembersR_mono _ hmem n ci hf) hnr
    -- the projection phase's block-level premises, both tiers
    have hinvR : ProjPhaseInvS cvT.name cvC.name nF envR
        mp₂.base.cval := by
      refine ⟨?_, ?_, ?_⟩
      · intro ci hf
        obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
          hI₂ cvT.name hTblock ci hf
        exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
      · intro ci hf
        obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
          hI₂ cvC.name hCblockN ci hf
        exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
      · intro j hj ci hf
        exfalso
        have hnone := List.all_eq_true.mp hprojFresh j
          (List.mem_range.mpr hj)
        rw [hf] at hnone
        exact nomatch hnone
    have hinvAR : ProjPhaseAcvalP cvT.name cvC.name nF envR
        mp₂.base2.acval := by
      refine ⟨?_, ?_, ?_⟩
      · intro hs ψ
        rcases hf : envR.find? cvT.name with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · exact (hIA₂ cvT.name hTblock ci hf ψ).symm
      · intro hs ψ
        rcases hf : envR.find? cvC.name with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · exact (hIA₂ cvC.name hCblockN ci hf ψ).symm
      · intro j hj hs ψ
        exfalso
        have hnone := List.all_eq_true.mp hprojFresh j
          (List.mem_range.mpr hj)
        rcases hf : envR.find? (projFnName cvT.name j) with _ | ci
        · rw [hf] at hs; exact nomatch hs
        · rw [hf] at hnone; exact nomatch hnone
    have hpinsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        Setlec.EtaPins μ envR cvT.name cvT'.levelParams capsT' := by
      intro cvT' capsT' hf
      obtain ⟨hlps', rfl⟩ := hidR cvT' capsT' hf
      rw [hlps']
      exact Setlec.EtaPins.transport etaPins_of_indBlockCaps hkeepR
    have hCblockR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        capsT'.eta = true →
        (block.map (·.name)).contains capsT'.etaCtor = true := by
      intro cvT' capsT' hf _
      obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
      exact hCblockN
    have hFieldsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        capsT'.eta = true → capsT'.etaFields = nF := by
      intro cvT' capsT' hf _
      obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
      rfl
    -- the projection fold and the templates
    obtain ⟨mp₃, -, -, -, -, -⟩ :=
      projInstallP hμ hTblock hbshape (List.range nF) mp₂ hproj hinvR
        hinvAR hI₂ hIA₂ hpinsR hCblockR hFieldsR
    exact templatesP hTnres (List.range nF) mp₃ htpl
  · -- the generic arm: an empty capability record
    have hBP0 : Setlec.BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    obtain ⟨mp₁, hcval₁, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
      indMembersPM memberKeyS memberEtaLawP memberUnitLawP _ mp hbnNon
        (fun cv caps₂ _ => ⟨etaPins_empty,
          ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
        hmem (hI0gen hmem hrecs) (hIA0gen hmem hrecs) hEC0 hBP0
    rw [← hcval₁] at hrecs hI₁
    obtain ⟨m₂, hm₂cval, -, -, -, -⟩ :=
      indRecsS memberKeyS mp₁.base hI₁ hbnRec (hallGen hmem)
        hEC₁ hBP₁ hrecs
    obtain ⟨mp₂, -, -⟩ :=
      indRecsP hμ memberKeyS memberEtaLawP memberUnitLawP mp₁ hI₁ hIA₁
        hbnRec (hallGen hmem) hEC₁ hBP₁ m₂ hm₂cval hrecs
    exact ⟨mp₂⟩

end Setlec.SetR.Interp2
