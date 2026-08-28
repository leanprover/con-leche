import Setlec.SetR.Install.ProjInstallS

/-!
# The modeled-inductive block, assembled (task #148, T5)

`declIndS` discharges `DeclIndS` — the sixth and last per-kind
obligation of `declStepS`'s dispatch.  It composes the four folds:

* `indMembersS` — the non-recursor members;
* `indRecsS` — the recursor group (provision, fire, swap);
* `projInstallS` — the projection functions;
* `templatesS` — the elimination templates.

Everything between them is **bookkeeping about what the folds
preserve**, which is why they were re-signed to report it: the
member fold's `indMembersR_mono`/`_stored`/`_fresh`, the group's
non-recursor transport and `isSome` congruence.  The one genuinely new
ingredient is `etaPins_of_indBlockCaps`, which turns `indBlockCaps`'
two Booleans back into the artifacts' shape pins — the fact that makes
`caps.eta`/`caps.unitlike` mean anything at all (practice P2's second
instance).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The block's capability pins**, from the capability record's own
definition: `indBlockCaps`' two Booleans *are* `checkEtaThm` and
`checkUnitThm`, which invert to the artifacts' shape pins.  Transpose
of `Model/Extend/Decl.lean`'s `hpinsT0`. -/
theorem etaPins_of_indBlockCaps {μ : CheckMode} {env : Env}
    {cvT cvC : ConstantVal} {nP nF : Nat} :
    EtaPins μ env cvT.name cvT.levelParams
      (indBlockCaps μ env cvT cvC nP nF) := by
  refine ⟨?_, ?_⟩
  · intro hcape
    simp only [indBlockCaps, Bool.and_eq_true] at hcape
    exact checkEtaThm_inv hcape.2
  · intro hcapu
    simp only [indBlockCaps] at hcapu
    exact checkUnitThm_inv hcapu

/-- An empty capability record pins nothing, and asks nothing. -/
theorem etaPins_empty {μ : CheckMode} {env : Env} {T : Name}
    {lps : List Name} : EtaPins μ env T lps {} :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- The projection-function fold is an `ExtEta` extension: each step
is either a no-op or one fresh `.recInfo` install. -/
theorem projInstallR_ext {μ : CheckMode} {F : Nat}
    {T ctorName : Name} {lps : List Name} {nP nF : Nat} :
    ∀ (idxs : List Nat) {env' : Env} {cval : TConstVal} {env₄ : Env}
      {cval₄ : TConstVal},
      ProjInstallR μ F T ctorName lps nP nF env' cval idxs env₄ cval₄ →
      ExtEta env' env₄ := by
  intro idxs
  induction idxs with
  | nil =>
    intro env' cval env₄ cval₄ h
    obtain ⟨rfl, -⟩ := h
    exact ExtEta.refl _
  | cons i rest ih =>
    intro env' cval env₄ cval₄ h
    obtain ⟨env'', cval'', hstep, htail⟩ := h
    refine ExtEta.trans ?_ (ih htail)
    rcases hstep with ⟨hfn, -⟩ | ⟨-, rfl, -⟩
    · obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, -, -, -, hfresh, -, -,
        -, -, -, -, -, -, -, -, -, -, rfl⟩ := hfn
      exact ExtEta.cons (Option.isNone_iff_eq_none.mp hfresh)
        (fun _ _ hh => ConstantInfo.noConfusion hh)
    · exact ExtEta.refl _

/-- The elimination-template fold is an `ExtEta` extension. -/
theorem templatesR_ext {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) {env' env₂ : Env},
      DeclIndR.TemplatesR T ctorName lps nP nF env' idxs env₂ →
      ExtEta env' env₂ := by
  intro idxs
  induction idxs with
  | nil =>
    intro env' env₂ h
    rw [h]
    exact ExtEta.refl _
  | cons i rest ih =>
    intro env' env₂ h
    obtain ⟨env'', hstep, htail⟩ := h
    refine ExtEta.trans ?_ (ih htail)
    rcases hstep with rfl | ⟨entry, hst, hix, -, -, -, hfresh, rfl⟩
    · exact ExtEta.refl _
    · refine ExtEta.cons ?_ (fun _ _ hh => ConstantInfo.noConfusion hh)
      show env'.find? (projFnName entry.structName entry.idx) = none
      rw [hst, hix]
      exact Option.isNone_iff_eq_none.mp hfresh

set_option maxHeartbeats 3200000 in
/-- **The modeled-inductive block install.** -/
theorem declIndS (hkey : MemberKeyS V) : DeclIndS V := by
  intro μ F env env₂ block m hE h
  obtain ⟨hsplit, hmain⟩ := h
  -- list bookkeeping about the block's split
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
  -- the eta side invariants at the base: the outside families are
  -- closed by the fold's own invariant, and no block former is stored
  -- yet (so the stored-pins invariant is vacuous)
  have hEC0 : EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  -- the block invariant holds vacuously at the base: no block name is
  -- stored there, which is the two folds' freshness chains
  have hnostore : ∀ {caps : IndCaps} {envM envR : Env}
      {cvalM cvalR : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env m.cval
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
      IndMembersR μ F (block.map (·.name)) caps env m.cval
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true)) envM cvalM →
      IndRecsR μ F (block.map (·.name)) envM cvalM
        (block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false)) envR cvalR →
      BlockInstalledTT (block.map (·.name)) env m.cval :=
    fun hmem hrecs n hn ci hf =>
      absurd (hnostore hmem hrecs n hn ci hf) (fun h => h)
  -- every block name is stored after the member fold, or is a
  -- recursor the group installs
  have hallGen : ∀ {caps : IndCaps} {envM : Env} {cvalM : TConstVal},
      IndMembersR μ F (block.map (·.name)) caps env m.cval
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
    -- the two named members are block members
    -- generic in the filter's predicate, so unification takes the
    -- relation's own (writing it out does not match syntactically)
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
    have hTnres : reservedBasisNames.contains cvT.name = false :=
      (indMembersR_nameGuards _ hmem _ hTnon).2
    -- the run's projection freshness, pulled back to the base
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
    have hBP0 : BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    -- the member fold
    obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ := indMembersS hkey _ m hbnNon
      (fun cv caps₂ hmm => by
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
          (hsingle hIfilt (List.mem_filter.mp hmm).1 rfl)
        exact ⟨etaPins_of_indBlockCaps, fun _ => hCblockN,
          fun _ h0 => hpf0 h0⟩)
      hmem (hI0gen hmem hrecs) hEC0 hBP0
    rw [← hm₁cval] at hrecs hI₁
    -- the recursor group
    obtain ⟨m₂, hm₂cval, hI₂, hnonrecUp, -, -⟩ :=
      indRecsS hkey m₁ hI₁ hbnRec (hallGen hmem) hEC₁ hBP₁ hrecs
    rw [← hm₂cval] at hproj hI₂
    -- the stored former, identified
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
    -- the projection phase's three block-level premises
    have hinvR : ProjPhaseInvS cvT.name cvC.name nF envR m₂.cval := by
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
    have hpinsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
        envR.find? cvT.name = some (.indInfo cvT' capsT') →
        EtaPins μ envR cvT.name cvT'.levelParams capsT' := by
      intro cvT' capsT' hf
      obtain ⟨hlps', rfl⟩ := hidR cvT' capsT' hf
      rw [hlps']
      exact EtaPins.transport etaPins_of_indBlockCaps hkeepR
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
    obtain ⟨m₃, -, -, -⟩ := projInstallS hTblock hbshape
      (List.range nF) m₂ hproj hinvR hI₂ hpinsR hCblockR hFieldsR
    refine ⟨templatesS hTnres (List.range nF) m₃ htpl, ?_⟩
    -- the three post-member phases are `ExtEta`, so the only new
    -- former is the block's own, whose constructor is a member
    have hx : ExtEta envM env₂ :=
      ExtEta.trans ⟨hnonrecUp, indRecsR_noInd hrecs⟩
        (ExtEta.trans (projInstallR_ext (List.range nF) hproj)
          (templatesR_ext (List.range nF) htpl))
    have hCnon : ConstantInfo.ctorInfo cvC nP nF ∈ block.filter
        (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true) :=
      List.mem_filter.mpr ⟨hCin, rfl⟩
    intro T cvT' caps' hf he hr
    rcases indMembersR_indNew _ hmem T cvT' caps'
      (hx.2 T cvT' caps' hf) with hfE | ⟨rfl, -⟩
    · obtain ⟨cvC', hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC', hx.1 _ _ (indMembersR_mono _ hmem _ _ hfC)
        (fun _ _ _ _ hh => nomatch hh)⟩
    · obtain ⟨cvA', hfA⟩ := indMembersR_ctorEntry _ hmem cvC nP nF hCnon
      exact ⟨cvA', hx.1 _ _ hfA (fun _ _ _ _ hh => nomatch hh)⟩
  · -- the generic arm: an empty capability record
    have hBP0 : BlockEtaPinned μ (block.map (·.name)) env :=
      fun n cvS capsS hnb hf _ =>
        absurd (hnostore hmem hrecs n hnb _ hf) (fun h => h)
    obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ := indMembersS hkey _ m hbnNon
      (fun cv caps₂ _ => ⟨etaPins_empty,
        ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
      hmem (hI0gen hmem hrecs) hEC0 hBP0
    rw [← hm₁cval] at hrecs hI₁
    obtain ⟨m₂, -, -, hnonrecUp, -, -⟩ := indRecsS hkey m₁ hI₁ hbnRec
      (hallGen hmem) hEC₁ hBP₁ hrecs
    refine ⟨⟨m₂⟩, ?_⟩
    intro T cvT' caps' hf he hr
    have hfM := indRecsR_noInd hrecs T cvT' caps' hf
    rcases indMembersR_indNew _ hmem T cvT' caps' hfM with hfE | ⟨rfl, -⟩
    · obtain ⟨cvC, hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC, hnonrecUp _ _ (indMembersR_mono _ hmem _ _ hfC)
        (fun _ _ _ _ hh => nomatch hh)⟩
    · exact absurd he (by decide)

end Setlec.SetR
