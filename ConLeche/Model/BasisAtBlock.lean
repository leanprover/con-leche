module

public import ConLeche.Model.BasisRename
public import ConLeche.Model.Cover
public import ConLeche.Verify.BasisBlock
import ConLeche.Semantics.Decl
public import ConLeche.Semantics.EqTower
import ConLeche.Model.BasisEq
import ConLeche.Model.BasisBlocks
import ConLeche.Model.BasisEmpty
import ConLeche.Model.BasisFalse
import ConLeche.Model.BasisLfp

public section

/-!
# A pinned block at the stream's level-parameter names

A pinned block passes the reserved names' check only if each record is its
pin up to the record's level-parameter names (`pinListOk`), and its install
stores each installed pin at those names (`BasisKind.storedAt`,
`blockInstall_pinned`).  The P tier proves the block at the pin's own names
(`Model/BasisEq.lean`, `Model/BasisBlocks.lean`, …) and carries the result to
the record's names (`EnvModelM.renameCore`).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule IndCaps
  reservedBasisNames pinnedInfo uN eqName eqReflName eqA eqI eqReflA eqRecA
  quotA quotMkA quotName quotMkName quotAt quotPin)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The two environments -/

/-- A list of pins and its copies; under `κ`, what is no recursor is unchanged. -/
inductive PinPairs (κ : Prop) : List ConstantInfo → List ConstantInfo → Prop where
  | nil : PinPairs κ [] []
  | cons {p p' : ConstantInfo} {ps ps' : List ConstantInfo} :
      reservedBasisNames.contains p.name = true → PinCopy p (pinnedInfo p.name) →
      PinCopy p' (pinnedInfo p.name) →
      (κ → (∀ cv mI rP isK rules, p ≠ .recInfo cv mI rP isK rules) → p' = p) →
      PinPairs κ ps ps' → PinPairs κ (p :: ps) (p' :: ps')

/-- **The environments a block's two installs reach**, from the prefix `E`. -/
structure RenRel (κ : Prop) (L₀ : List ConstantInfo) (E env env' : Env) : Prop where
  ren : RenEnv env env'
  mem : ∀ c' ∈ env'.consts, ∃ c ∈ env.consts,
    (c' = c ∧ env'.find? c.name = env.find? c.name) ∨
    (env.find? c.name = some c ∧ env'.find? c.name = some c' ∧
      reservedBasisNames.contains c.name = true ∧
      PinCopy c (pinnedInfo c.name) ∧ PinCopy c' (pinnedInfo c.name))
  stE : ∀ n, (E.find? n).isSome = true → env.find? n = E.find? n ∧ env'.find? n = E.find? n
  keep : κ → ∀ n ci ci', env.find? n = some ci → env'.find? n = some ci' →
    (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) → ci' = ci
  blk : ∀ n ci, env.find? n = some ci → (E.find? n).isSome = false → ci ∈ L₀

theorem constsRen_refl : ∀ cs : List ConstantInfo, ConstsRen cs cs
  | [] => .nil
  | _ :: cs => .cons (.inl rfl) (constsRen_refl cs)

theorem RenRel.refl (κ : Prop) (L₀ : List ConstantInfo) (E : Env) : RenRel κ L₀ E E E where
  ren := ⟨constsRen_refl _, rfl⟩
  mem := fun c' hc' => ⟨c', hc', .inl ⟨rfl, rfl⟩⟩
  stE := fun _ _ => ⟨rfl, rfl⟩
  keep := fun _ n ci ci' h h' _ => by
    rw [h] at h'; exact (Option.some.inj h').symm
  blk := fun n ci hf hn => by
    rw [hf] at hn; exact nomatch hn

theorem name_ne_of_mem_of_none {env : Env} {c₀ : ConstantInfo} {n : Name} (hm : c₀ ∈ env.consts)
    (hn : env.find? n = none) : c₀.name ≠ n := by
  intro he
  have := List.find?_eq_none.mp hn c₀ hm
  simp [he] at this

theorem RenRel.cons {κ : Prop} {L₀ : List ConstantInfo} {E env env' : Env} (R : RenRel κ L₀ E env env')
    {p p' : ConstantInfo} (hres : reservedBasisNames.contains p.name = true)
    (hc : PinCopy p (pinnedInfo p.name)) (hc' : PinCopy p' (pinnedInfo p.name))
    (hk : κ → (∀ cv mI rP isK rules, p ≠ .recInfo cv mI rP isK rules) → p' = p)
    (hL : p ∈ L₀) (hf : env.find? p.name = none) :
    RenRel κ L₀ E ⟨p :: env.consts, env.tables⟩ ⟨p' :: env'.consts, env'.tables⟩ := by
  have hnm : p'.name = p.name := by rw [hc'.name, pinnedInfo_name hres]
  have hf' : env'.find? p.name = none := by
    have := R.ren.isSome p.name
    rw [hf] at this
    exact Option.isNone_iff_eq_none.mp (by simpa using this)
  have hp1 : (⟨p :: env.consts, env.tables⟩ : Env).find? p.name = some p :=
    Env.find?_cons_self _ _
  have hp2 : (⟨p' :: env'.consts, env'.tables⟩ : Env).find? p.name = some p' := by
    rw [← hnm]; exact Env.find?_cons_self _ _
  have hne1 : ∀ {n}, p.name ≠ n →
      (⟨p :: env.consts, env.tables⟩ : Env).find? n = env.find? n := fun hne => by
    rw [Env.find?_cons, ite_eq_right hne]
  have hne2 : ∀ {n}, p.name ≠ n →
      (⟨p' :: env'.consts, env'.tables⟩ : Env).find? n = env'.find? n := fun hne => by
    rw [Env.find?_cons, hnm, ite_eq_right hne]
  refine ⟨⟨.cons (.inr ⟨hres, hc, hc'⟩) R.ren.consts, R.ren.tables⟩, fun c' hm => ?_, fun n hn => ?_,
    fun hκ n ci ci' h1 h2 hnr => ?_, fun n ci h1 hn => ?_⟩
  · rcases List.mem_cons.mp hm with rfl | hm'
    · exact ⟨p, List.mem_cons_self, .inr ⟨hp1, hp2, hres, hc, hc'⟩⟩
    · obtain ⟨c, hcm, hp⟩ := R.mem c' hm'
      have hne : p.name ≠ c.name := (name_ne_of_mem_of_none hcm hf).symm
      refine ⟨c, List.mem_cons_of_mem _ hcm, ?_⟩
      rw [hne1 hne, hne2 hne]
      exact hp
  · have hne : p.name ≠ n := by
      intro he
      have := (R.stE n hn).1
      rw [← he, hf] at this
      rw [← he, ← this] at hn
      exact nomatch hn
    rw [hne1 hne, hne2 hne]
    exact R.stE n hn
  · by_cases hne : p.name = n
    · subst hne
      rw [hp1] at h1
      rw [hp2] at h2
      obtain rfl := Option.some.inj h1
      obtain rfl := Option.some.inj h2
      exact hk hκ hnr
    · rw [hne1 hne] at h1
      rw [hne2 hne] at h2
      exact R.keep hκ n ci ci' h1 h2 hnr
  · by_cases hne : p.name = n
    · subst hne
      rw [hp1] at h1
      obtain rfl := Option.some.inj h1
      exact hL
    · rw [hne1 hne] at h1
      exact R.blk n ci h1 hn

/-- **The install at the pins, from the install at the copies.** -/
theorem renRel_chain {κ : Prop} {L₀ : List ConstantInfo} {E : Env} :
    ∀ {L L' : List ConstantInfo}, PinPairs κ L L' → (∀ p ∈ L, p ∈ L₀) →
      ∀ {env env' env₂' : Env}, RenRel κ L₀ E env env' → BasisInstallRun env' L' env₂' →
      ∃ env₂, BasisInstallRun env L env₂ ∧ RenRel κ L₀ E env₂ env₂'
  | [], [], .nil, _, env, env', env₂', R, hr => by
    obtain rfl : env₂' = env' := hr
    exact ⟨env, rfl, R⟩
  | p :: ps, p' :: ps', .cons hres hc hc' hk ht, hL, env, env', env₂', R, hr => by
    obtain ⟨hf', hrest⟩ := hr
    have hnm : p'.name = p.name := by rw [hc'.name, pinnedInfo_name hres]
    have hf : (env.find? p.name).isNone = true := by
      rw [hnm] at hf'
      have := R.ren.isSome p.name
      simp only [Option.isNone_iff_eq_none] at hf' ⊢
      rw [hf'] at this
      exact Option.isNone_iff_eq_none.mp (by simpa using this.symm)
    obtain ⟨env₂, h₂, R₂⟩ := renRel_chain ht (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (R.cons hres hc hc' hk (hL p List.mem_cons_self) (Option.isNone_iff_eq_none.mp hf)) hrest
    exact ⟨env₂, ⟨hf, h₂⟩, R₂⟩

/-- A record's copies of the installed pins, position by position: the comparison is with the pins
(`pins`), the copies are of the installed ones (`ins`), at the same level parameters. -/
theorem pinPairs_of_ok {κ : Prop} :
    ∀ {block pins ins : List ConstantInfo}, ConLeche.listBeqBy ConLeche.pinCopyOk block pins = true →
      pins.map (·.toConstantVal.levelParams) = ins.map (·.toConstantVal.levelParams) →
      (∀ p ∈ ins, reservedBasisNames.contains p.name = true ∧ pinnedInfo p.name = p ∧
        (κ → (∀ cv mI rP isK rules, p ≠ .recInfo cv mI rP isK rules) →
          p.toConstantVal.levelParams = [] ∧ p.atLps [] = p)) →
      PinPairs κ ins (List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) ins block)
  | [], [], [], _, _, _ => .nil
  | c :: cs, q :: qs, p :: ps, h, hl, hp => by
    simp only [ConLeche.listBeqBy, Bool.and_eq_true] at h
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨hok, hrest⟩ := h
    obtain ⟨hres, hpi, hkp⟩ := hp p List.mem_cons_self
    simp only [ConLeche.pinCopyOk, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hnd, hlen⟩, -⟩ := hok
    rw [hl.1] at hlen
    have hlps : (p.atLps c.toConstantVal.levelParams).toConstantVal.levelParams
        = c.toConstantVal.levelParams := by
      rw [atLps_cv]; rfl
    refine .cons hres (by rw [hpi]; exact hpi ▸ pinCopy_self hres) ?_ (fun hκ hnr => ?_)
      (pinPairs_of_ok hrest hl.2 fun x hx => hp x (List.mem_cons_of_mem _ hx))
    · rw [hpi]
      exact ⟨by rw [hlps], by rw [hlps]; exact nodup_of_nameNodup hnd, by rw [hlps]; exact hlen⟩
    · obtain ⟨h0, h1⟩ := hkp hκ hnr
      have hps : c.toConstantVal.levelParams = [] :=
        List.eq_nil_of_length_eq_zero (by rw [hlen, h0]; rfl)
      show p.atLps c.toConstantVal.levelParams = p
      rw [hps]; exact h1
  | [], _ :: _, _, h, _, _ => nomatch h
  | _ :: _, [], _, h, _, _ => nomatch h
  | [], [], _ :: _, _, hl, _ => nomatch hl
  | _ :: _, _ :: _, [], _, hl, _ => nomatch hl

/-! ## What the block does not touch -/

/-- A constructor's family reads the former's lookup. -/
theorem ctorFamily_ind_congr {find₁ find₂ : Name → Option ConstantInfo} {cvj : ConstantVal}
    (h : ∀ T us', cvj.type.piResult.getAppFn = .const T us' →
      ∀ cv caps, find₁ T = some (.indInfo cv caps) ↔ find₂ T = some (.indInfo cv caps)) :
    ConLeche.ctorFamily find₁ cvj = ConLeche.ctorFamily find₂ cvj := by
  unfold ConLeche.ctorFamily
  split
  · next T us' heq =>
    have hT := h T us' heq
    by_cases hx : ∃ cv caps, find₁ T = some (.indInfo cv caps)
    · obtain ⟨cv, caps, h1⟩ := hx
      rw [h1, (hT cv caps).mp h1]
    · have h1 : ∀ cv caps, find₁ T ≠ some (.indInfo cv caps) := fun cv caps he => hx ⟨cv, caps, he⟩
      have h2 : ∀ cv caps, find₂ T ≠ some (.indInfo cv caps) :=
        fun cv caps he => h1 cv caps ((hT cv caps).mpr he)
      generalize find₁ T = x at h1
      generalize find₂ T = y at h2
      refine Eq.trans (b := none) ?_ (Eq.symm ?_)
      · cases x with
        | none => rfl
        | some c => cases c <;> first | rfl | exact absurd rfl (h1 _ _)
      · cases y with
        | none => rfl
        | some c => cases c <;> first | rfl | exact absurd rfl (h2 _ _)
  · rfl

/-- **A recorded block whose names the renaming keeps stays recorded.** -/
theorem lfp_keep {env env' : Env} (mp : EnvModelM V env) (h : RenEnv env env') {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks)
    (hm : ∀ mm, mm < D.k → env'.find? (D.member mm) = env.find? (D.member mm))
    (hC : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      env'.find? (D.ctorName c j) = env.find? (D.ctorName c j)) :
    LfpClause (renAcval mp.base2.acval env env') D ∧ LfpStored env' D ∧
      LfpReads (renAcval mp.base2.acval env env') env' D ∧
      LfpCtorReads (renAcval mp.base2.acval env env') env' D ∧ LfpCaps env' D := by
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote (renAcval mp.base2.acval env env') env' φ d e = denote mp.base2.acval env φ d e :=
    fun φ d e => denote_ren h mp.base2.acval_params φ d e
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := mp.lfp_ok D hD
  have hC' : ∀ c, c < D.k → ∀ j, j < D.nctors c →
      env'.find? (D.ctorName c j) = env.find? (D.ctorName c j) :=
    fun c hc => hC c (Nat.lt_of_lt_of_le hc hL.kN)
  refine ⟨hL.congr (fun mm hmm => renAcval_same (hm mm hmm))
      (fun c hc j hj => renAcval_same (hC c hc j hj)),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc j hj => ?_⟩,
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, (hm mm hmm).trans hf⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, (hC c hc j hj).trans hf⟩
  · obtain ⟨cv, caps, hf, ⟨hfl, hsh⟩, hab⟩ := hrd mm hmm
    refine ⟨cv, caps, (hm mm hmm).trans hf, ⟨hfl, ?_⟩, fun ψ => ?_⟩
    · rcases hsh with hs | ⟨f, hs, h1, h2, h3, h4, hb, hdl, hin⟩
      · exact .inl hs
      · refine .inr ⟨f, hs, h1, h2, h3, h4, ConstsBound.of_isSome (fun n hn => by
          rw [h.isSome]; exact hn) hb, hdl, fun ψ => ?_⟩
        obtain ⟨ta, ta₀, hta, hta₀, hmem⟩ := hin ψ
        refine ⟨ta, ta₀, by rw [hde]; exact hta, by rw [hde]; exact hta₀, fun ρ => ?_⟩
        rw [renAcval_same (hm mm hmm)]
        exact hmem ρ
    · obtain ⟨ab, hta, h1⟩ := hab ψ
      exact ⟨ab, by rw [hde]; exact hta, h1⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc j hj
    refine ⟨cv, nPc, nF, (hC' c hc j hj).trans hf, hcf, fun mm hmm => ?_,
      fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc, fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      exact ⟨cvm, caps, (hm mm hmm).trans hfm, hl⟩
    · rw [hde] at hrd'
      exact hpars ψ dsC bodyC hrd' hle
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, by rw [hde]; exact hta, hlab, hlT, fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, ty, hfm, hty, hr⟩ := hTys mm hmm
      exact ⟨cvm, caps, ty, (hm mm hmm).trans hfm, hty, by rw [hde]; exact hr⟩
  · obtain ⟨cv, caps, hf, hz⟩ := hcK mm hmm
    exact ⟨cv, caps, (hm mm hmm).trans hf, hz⟩
  · obtain ⟨cv, nPc, nF, hf, hsh⟩ := hcC c hc j hj
    exact ⟨cv, nPc, nF, (hC' c hc j hj).trans hf, hsh⟩

/-- A constructor's entry is the same for two copies, away from their head. -/
theorem ctorLook_congr {env env' : Env} {C : Name}
    (h : ∀ n, ∃ c c', (env.find? n = none ∧ env'.find? n = none) ∨
      (env.find? n = some c ∧ env'.find? n = some c' ∧ ctorEntry C c' = ctorEntry C c)) (n : Name) :
    ctorLook env'.find? C n = ctorLook env.find? C n := by
  obtain ⟨c, c', h1 | ⟨h1, h2, h3⟩⟩ := h n
  · simp [ctorLook, h1.1, h1.2]
  · simp [ctorLook, h1, h2, h3]

/-! ## A block whose non-recursors are unchanged -/

theorem coverStep_keep {E env env' : Env} {L₀ : List ConstantInfo}
    (mpE : EnvModelM V E) (mp : EnvModelM V env) (R : RenRel True L₀ E env env') (hwf : EnvWF env')
    (hlf : ∀ p ∈ L₀, ∀ cv mI rP isK rules, p = .recInfo cv mI rP isK rules →
      ∀ r ∈ rules, (pinnedInfo (RecRule.ctor r)).toConstantVal.levelParams = []) :
    ∃ mp' : EnvModelM V env', mp'.base2.acval = renAcval mp.base2.acval env env' ∧
      (∀ D ∈ mp'.lfpBlocks, D ∈ mp.lfpBlocks ∨ ∀ mm, D.telescope mm = none) ∧
      (LfpCover mp [] → LfpCover mp' []) := by
  have h := R.ren
  have hfwd : ∀ n ci, env.find? n = some ci →
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) → env'.find? n = some ci := by
    intro n ci hf hnr
    rcases h.find n with ⟨h1, -⟩ | ⟨c, c', h1, h2, -⟩
    · rw [h1] at hf; exact nomatch hf
    · rw [h1] at hf
      obtain rfl := Option.some.inj hf
      rw [h2, R.keep trivial n c c' h1 h2 hnr]
  have hback : ∀ n ci, env'.find? n = some ci →
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) → env.find? n = some ci := by
    intro n ci hf hnr
    rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h2] at hf; exact nomatch hf
    · rw [h2] at hf
      obtain rfl := Option.some.inj hf
      have hnrc : ∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules := by
        intro cv mI rP isK rules he
        subst he
        rcases hr with rfl | ⟨hrs, h3, h4⟩
        · exact hnr _ _ _ _ _ rfl
        · obtain ⟨_, _, he, -⟩ := h3.recr h4 (pinnedInfo_wf hrs).2
          exact hnr _ _ _ _ _ he
      rw [h1, R.keep trivial n c c' h1 h2 hnrc]
  have hsameN : ∀ {n cv a b}, env'.find? n = some (.ctorInfo cv a b) → env'.find? n = env.find? n :=
    fun hf => by
      rw [hf, hback _ _ hf fun _ _ _ _ _ he => nomatch he]
  have hindB : ∀ T cv caps, env.find? T = some (.indInfo cv caps) ↔
      env'.find? T = some (.indInfo cv caps) := fun T cv caps =>
    ⟨fun hf => hfwd _ _ hf (fun _ _ _ _ _ he => nomatch he),
      fun hf => hback _ _ hf fun _ _ _ _ _ he => (nomatch he)⟩
  have hctors := recCtors_ren mp.base2 h
  -- the links: an old recursor's by the prefix's, a new one's are level-free
  have hlink : ∀ n ci, env'.find? n = some ci → reservedBasisNames.contains n = true →
      PinLinked env' n ci := by
    intro n ci hf hres cv mI rP isK rules hci rl hrl hpl cvj cnP cnF hfc us hus
    subst hci
    have hfc0 := hback _ _ hfc fun _ _ _ _ _ he => nomatch he
    rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h2] at hf; exact nomatch hf
    · rw [h2] at hf
      obtain rfl := Option.some.inj hf
      have hnmc : c.name = n := by simpa using Env.find?_name h1
      obtain ⟨-, hlk, -⟩ := mp.base2.basis_pinned n c h1 hres
      have hlen : c.toConstantVal.levelParams.length = cv.levelParams.length := hr.len.symm
      have h3 : PinCopy c (pinnedInfo c.name) := by
        rw [hnmc]; exact (mp.base2.basis_pinned n c h1 hres).1
      have h4 : PinCopy (.recInfo cv mI rP isK rules) (pinnedInfo c.name) := by
        rcases hr with rfl | ⟨-, -, h'⟩
        · exact h3
        · exact h'
      cases c with
      | recInfo cv₀ mI0 rP0 isK0 rules₀ =>
        have hrs : reservedBasisNames.contains (ConstantInfo.recInfo cv₀ mI0 rP0 isK0 rules₀).name = true :=
          hnmc ▸ hres
        obtain ⟨cv₂, rules₂, he, hrl₂⟩ := h3.recr h4 (pinnedInfo_wf hrs).2
        injection he with e0 e1 e2 e3 e4
        subst e0; subst e1; subst e2; subst e3; subst e4
        obtain ⟨rl₀, hrl0, hct, -, hfr, -⟩ := hrl₂ rl hrl
        by_cases hst : (E.find? n).isSome = true
        · -- the old recursor's own link: its copy is the prefix's
          have hEe := (R.stE n hst)
          have hci : E.find? n = some (.recInfo cv mI rP isK rules) := by
            rw [← hEe.2]; exact h2
          obtain ⟨-, hlkE, -⟩ := mpE.base2.basis_pinned n _ hci hres
          obtain ⟨cj, a, b, hcj⟩ := mpE.base2.rec_ctors n _ _ _ _ _ hci rl hrl
          have hfE : E.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) := by
            rw [← (R.stE _ (by rw [hcj]; rfl)).2]; exact hfc
          exact hlkE cv mI rP isK rules rfl rl hrl hpl cvj cnP cnF hfE us hus
        · have hmem : ConstantInfo.recInfo cv₀ mI rP isK rules₀ ∈ L₀ :=
            R.blk n _ h1 (by simpa using hst)
          have hLF := hlf _ hmem cv₀ mI rP isK rules₀ rfl rl₀ hrl0
          have hpl₀ : RecRule.fire rl₀ = .plain := by
            rcases hfr with ⟨-, h₁⟩ | ⟨ls, -, h₁, -⟩
            · exact h₁
            · rw [h₁] at hpl; exact nomatch hpl
          have hmap := hlk cv₀ mI rP isK rules₀ rfl rl₀ hrl0 hpl₀ cvj cnP cnF (hct ▸ hfc0) us
            (by rw [← hlen] at hus; exact hus)
          rw [hLF] at hmap
          have hnil : cvj.levelParams = [] := List.map_eq_nil_iff.mp hmap
          rw [hct, hLF, hnil]
          rfl
      | _ => exact nomatch h3.kind.trans h4.kind.symm
  have hstable : ∀ n cv mI rP isK rules,
      env'.find? n = some (.recInfo cv mI rP isK rules) →
      (reservedBasisNames.contains n = false ∨ isK = false) →
      ∀ r ∈ rules, env'.find? (RecRule.ctor r) = env.find? (RecRule.ctor r) ∧
        ∀ cvj a b, env.find? (RecRule.ctor r) = some (.ctorInfo cvj a b) →
          ConLeche.ctorFamily env'.find? cvj = ConLeche.ctorFamily env.find? cvj := by
    intro n cv mI rP isK rules hf _ r hr
    obtain ⟨cvj, a, b, hc⟩ := hctors n cv mI rP isK rules hf r hr
    exact ⟨hsameN hc, fun _ _ _ _ => ctorFamily_ind_congr fun T _ _ cv caps => (hindB T cv caps).symm⟩
  have hkeepD : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks →
      (∀ mm, mm < D.k → env'.find? (D.member mm) = env.find? (D.member mm)) ∧
      (∀ c, c < D.N → ∀ j, j < D.nctors c →
        env'.find? (D.ctorName c j) = env.find? (D.ctorName c j)) := by
    intro D hD
    obtain ⟨-, ⟨hst, hstC⟩, -⟩ := mp.lfp_ok D hD
    refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
    · obtain ⟨cv, caps, hf⟩ := hst mm hmm
      rw [hf]; exact hfwd _ _ hf fun _ _ _ _ _ he => nomatch he
    · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
      rw [hf]; exact hfwd _ _ hf fun _ _ _ _ _ he => nomatch he
  obtain ⟨mp', hacR, hbl⟩ := mp.renameCore h hwf R.mem hlink hstable mp.lfpBlocks (fun D hD =>
    lfp_keep mp h hD (hkeepD hD).1 (hkeepD hD).2)
  refine ⟨mp', hacR, fun D hD => .inl (hbl ▸ hD), fun hc => ?_⟩
  have hlook : ∀ C n, ctorLook env'.find? C n = ctorLook env.find? C n := by
    intro C n
    rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
    · simp [ctorLook, h1, h2]
    · refine ctorLook_congr (env := env) (env' := env') (fun x => ?_) n
      rcases h.find x with ⟨g1, g2⟩ | ⟨d, d', g1, g2, hrd⟩
      · exact ⟨default, default, .inl ⟨g1, g2⟩⟩
      · refine ⟨d, d', .inr ⟨g1, g2, ?_⟩⟩
        by_cases hd : ∀ cv mI rP isK rules, d ≠ .recInfo cv mI rP isK rules
        · rw [R.keep trivial x d d' g1 g2 hd]
        · obtain ⟨cv, mI, rP, isK, rules, rfl⟩ :
              ∃ cv mI rP isK rules, d = .recInfo cv mI rP isK rules := by
            cases d <;> first
              | exact ⟨_, _, _, _, _, rfl⟩
              | exact absurd (fun _ _ _ _ _ he => nomatch he) hd
          rcases hrd with rfl | ⟨hrs, h3, h4⟩
          · rfl
          · obtain ⟨_, _, he, -⟩ := h3.recr h4 (pinnedInfo_wf hrs).2
            rw [he]; rfl
  exact {
    cover := fun n cv caps hf hn hq => by
      rw [hbl]
      exact hc.cover n cv caps (hback _ _ hf (fun _ _ _ _ _ he => nomatch he)) hn hq
    nodup := fun D hD => hc.nodup D (hbl ▸ hD)
    len := fun D hD => hc.len D (hbl ▸ hD)
    all := fun D hD mm hmm cv caps hf => by
      rw [hbl] at hD
      rw [(hkeepD hD).1 mm hmm] at hf
      exact hc.all D hD mm hmm cv caps hf
    fresh := fun _ _ _ _ hin => absurd hin List.not_mem_nil
    own := fun D hD => by
      rw [hbl] at hD
      have hkk := hc.wid D hD
      exact (hc.own D hD).monoOn (hkeepD hD).1 (fun c hc' j hj => (hkeepD hD).2 c (hkk ▸ hc') j hj)
        fun c hc' => nestContainer_congr ((hkeepD hD).1 c hc') (hlook _)
    wid := fun D hD => hc.wid D (hbl ▸ hD) }

/-! ## The `Eq` block -/

/-- `Eq`'s block at the record's names: the former and the constructor at one
parameter, the recursor's motive at another. -/
theorem coverStep_eq {E env' : Env} {L₀ : List ConstantInfo} {p p1 : Name} (hne : p1 ≠ p)
    (mpE : EnvModelM V E)
    (mp : EnvModelM V ⟨eqRecA :: eqReflA :: eqI :: E.consts, E.tables⟩)
    (hEv : ∀ ψ : Name → Nat, mp.base2.acval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, mp.base2.acval eqReflName ψ = eqReflValT ψ)
    (R : RenRel False L₀ E ⟨eqRecA :: eqReflA :: eqI :: E.consts, E.tables⟩ env') (hwf : EnvWF env')
    (henv' : env' = ⟨eqRecA.atLps [p1, p] :: eqReflA.atLps [p] :: eqI.atLps [p] :: E.consts, E.tables⟩) :
    ∃ mp' : EnvModelM V env', mp'.base2.acval = renAcval mp.base2.acval
        ⟨eqRecA :: eqReflA :: eqI :: E.consts, E.tables⟩ env' ∧
      (∀ D ∈ mp'.lfpBlocks, D ∈ mp.lfpBlocks ∨ ∀ mm, D.telescope mm = none) ∧
      (LfpCover mp [] → LfpCover mp' []) := by
  subst henv'
  have h := R.ren
  generalize henv : (⟨eqRecA :: eqReflA :: eqI :: E.consts, E.tables⟩ : Env) = env at mp R h
  generalize hen' : (⟨eqRecA.atLps [p1, p] :: eqReflA.atLps [p] :: eqI.atLps [p] :: E.consts,
    E.tables⟩ : Env) = env' at R h hwf
  -- the block's lookups
  have f3 : env.find? (eqName.str "rec") = some eqRecA := by
    subst henv
    rw [Env.find?_cons]; exact ite_eq_left rfl
  have f2 : env.find? eqReflName = some eqReflA := by
    subst henv
    rw [Env.find?_cons, ite_eq_right (by decide), Env.find?_cons]; exact ite_eq_left rfl
  have f1 : env.find? eqName = some eqI := by
    subst henv
    rw [Env.find?_cons, ite_eq_right (by decide), Env.find?_cons, ite_eq_right (by decide),
      Env.find?_cons]
    exact ite_eq_left rfl
  have f3' : env'.find? (eqName.str "rec") = some (eqRecA.atLps [p1, p]) := by
    subst hen'
    rw [Env.find?_cons]; exact ite_eq_left rfl
  have f2' : env'.find? eqReflName = some (eqReflA.atLps [p]) := by
    subst hen'
    rw [Env.find?_cons, ite_eq_right (by rw [atLps_name]; decide), Env.find?_cons]
    exact ite_eq_left rfl
  have f1' : env'.find? eqName = some (eqI.atLps [p]) := by
    subst hen'
    rw [Env.find?_cons, ite_eq_right (by rw [atLps_name]; decide), Env.find?_cons,
      ite_eq_right (by rw [atLps_name]; decide), Env.find?_cons]
    exact ite_eq_left rfl
  have haway : ∀ {n : Name}, eqName ≠ n → eqReflName ≠ n → eqName.str "rec" ≠ n →
      env.find? n = E.find? n ∧ env'.find? n = E.find? n := by
    intro n h1 h2 h3
    constructor
    · subst henv
      rw [Env.find?_cons, ite_eq_right (show ¬ eqRecA.name = n from h3), Env.find?_cons,
        ite_eq_right (show ¬ eqReflA.name = n from h2), Env.find?_cons,
        ite_eq_right (show ¬ eqI.name = n from h1)]
    · subst hen'
      rw [Env.find?_cons, ite_eq_right (by rw [atLps_name]; exact h3), Env.find?_cons,
        ite_eq_right (by rw [atLps_name]; exact h2), Env.find?_cons,
        ite_eq_right (by rw [atLps_name]; exact h1)]
  have hnd1 : ([p] : List Name).Nodup := by simp
  have hpairE : ConstRen eqI (eqI.atLps [p]) :=
    .inr ⟨by decide, ⟨rfl, by decide, rfl⟩, ⟨rfl, hnd1, rfl⟩⟩
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote (renAcval mp.base2.acval env env') env' φ d e = denote mp.base2.acval env φ d e :=
    fun φ d e => denote_ren h mp.base2.acval_params φ d e
  -- the leaves at the new names
  have htr : ∀ ψ : Name → Nat, Level.substFn ψ [uN] [Level.param p] uN = ψ p := fun ψ => by
    simp [Level.substFn, Level.eval]
  have hEv' : ∀ ψ : Name → Nat, renAcval mp.base2.acval env env' eqName ψ
      = eqValT (Level.substFn ψ [uN] [Level.param p]) := fun ψ => by
    show mp.base2.acval eqName (renTr env env' eqName ψ) = _
    rw [renTr_pair f1 f1', hEv]; rfl
  have hRv' : ∀ ψ : Name → Nat, renAcval mp.base2.acval env env' eqReflName ψ
      = eqReflValT (Level.substFn ψ [uN] [Level.param p]) := fun ψ => by
    show mp.base2.acval eqReflName (renTr env env' eqReflName ψ) = _
    rw [renTr_pair f2 f2', hRv]; rfl
  -- the prefix's recursors
  have hold : ∀ {n : Name} {cv mI rP isK rules}, E.find? n = some (.recInfo cv mI rP isK rules) →
      ∀ r ∈ rules, ∃ cvj a b, E.find? (RecRule.ctor r) = some (.ctorInfo cvj a b) :=
    fun hf r hr => mpE.base2.rec_ctors _ _ _ _ _ _ hf r hr
  -- the links
  have hlink : ∀ n ci, env'.find? n = some ci → reservedBasisNames.contains n = true →
      PinLinked env' n ci := by
    intro n ci hf hres cv mI rP isK rules hci rl hrl hpl cvj cnP cnF hfc us hus
    subst hci
    by_cases he3 : eqName.str "rec" = n
    · subst he3
      rw [f3'] at hf
      have hf3 := Option.some.inj hf
      change ConstantInfo.recInfo _ _ _ _ _ = _ at hf3
      injection hf3 with e0 e1 e2 e3 e4
      subst e0; subst e1; subst e2; subst e3; subst e4
      obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrl
      obtain rfl := List.mem_singleton.mp hrp
      change env'.find? eqReflName = _ at hfc
      rw [f2'] at hfc
      have hc3 := Option.some.inj hfc
      change ConstantInfo.ctorInfo _ _ _ = _ at hc3
      injection hc3 with e5 _ _
      subst e5
      change _ = 2 at hus
      match us, hus with
      | [a, b], _ =>
        change [Level.subst [p1, p] [a, b] (.param p)] = [Level.subst [ConLeche.u1N, uN] [a, b] (.param uN)]
        have hu : ConLeche.u1N ≠ uN := by decide
        simp [Level.subst, Level.subst.go, hne, hu]
    · by_cases he2 : eqReflName = n
      · subst he2
        rw [f2'] at hf
        exact nomatch Option.some.inj hf
      · by_cases he1 : eqName = n
        · subst he1
          rw [f1'] at hf
          exact nomatch Option.some.inj hf
        · have ha := haway he1 he2 he3
          have hE : E.find? n = some (.recInfo cv mI rP isK rules) := by rw [← ha.2]; exact hf
          obtain ⟨-, hlkE, -⟩ := mpE.base2.basis_pinned n _ hE hres
          obtain ⟨cj, a, b, hcj⟩ := hold hE rl hrl
          have hst := R.stE (RecRule.ctor rl) (by rw [hcj]; rfl)
          exact hlkE cv mI rP isK rules rfl rl hrl hpl cvj cnP cnF (by rw [← hst.2]; exact hfc) us hus
  -- what a rule reads stays
  have hstable : ∀ n cv mI rP isK rules,
      env'.find? n = some (.recInfo cv mI rP isK rules) →
      (reservedBasisNames.contains n = false ∨ isK = false) →
      ∀ r ∈ rules, env'.find? (RecRule.ctor r) = env.find? (RecRule.ctor r) ∧
        ∀ cvj a b, env.find? (RecRule.ctor r) = some (.ctorInfo cvj a b) →
          ConLeche.ctorFamily env'.find? cvj = ConLeche.ctorFamily env.find? cvj := by
    intro n cv mI rP isK rules hf hprem r hr
    by_cases he3 : eqName.str "rec" = n
    · subst he3
      rw [f3'] at hf
      have hf3 := Option.some.inj hf
      change ConstantInfo.recInfo _ _ _ _ _ = _ at hf3
      injection hf3 with _ _ _ e3 _
      subst e3
      simp only [show reservedBasisNames.contains (eqName.str "rec") = true by decide] at hprem
      simp at hprem
    · by_cases he2 : eqReflName = n
      · subst he2
        rw [f2'] at hf
        exact nomatch Option.some.inj hf
      · by_cases he1 : eqName = n
        · subst he1
          rw [f1'] at hf
          exact nomatch Option.some.inj hf
        · have ha := haway he1 he2 he3
          have hE : E.find? n = some (.recInfo cv mI rP isK rules) := by rw [← ha.2]; exact hf
          obtain ⟨cj, a, b, hcj⟩ := hold hE r hr
          have hst := R.stE (RecRule.ctor r) (by rw [hcj]; rfl)
          refine ⟨by rw [hst.1, hst.2], fun cvj a' b' hfj => ctorFamily_ind_congr
            fun T us' hT cvT capsT => ?_⟩
          have hfE : E.find? (RecRule.ctor r) = some (.ctorInfo cvj a' b') := by
            rw [← hst.1]; exact hfj
          have hres := (mpE.base2.wf.consts _ (Env.find?_mem hfE)).2.2.1
          have hTs := Expr.find?_isSome_of_piResult_getAppFn_const hres hT
          have hsT := R.stE T hTs
          rw [hsT.1, hsT.2]
  rcases Classical.em (LfpCover mp []) with hcov | hcov
  case inr =>
    obtain ⟨mp', hacR, hbl⟩ := mp.renameCore h hwf R.mem hlink hstable [] (fun _ hD => nomatch hD)
    exact ⟨mp', hacR, (fun D hD => by rw [hbl] at hD; exact nomatch hD), fun hc => absurd hc hcov⟩
  -- the recorded blocks but `Eq`'s keep their names
  have hkeepD : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → eqName ∉ D.names →
      (∀ mm, mm < D.k → env'.find? (D.member mm) = env.find? (D.member mm)) ∧
      (∀ c, c < D.N → ∀ j, j < D.nctors c →
        env'.find? (D.ctorName c j) = env.find? (D.ctorName c j)) := by
    intro D hD hnot
    obtain ⟨-, ⟨hst, hstC⟩, -⟩ := mp.lfp_ok D hD
    have hkk := hcov.wid D hD
    have hmemb : ∀ mm, mm < D.k → D.member mm ∈ D.names := by
      intro mm hmm
      have hl : mm < D.names.length := by rw [hcov.len D hD]; exact hmm
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_mem hl
    refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
    · obtain ⟨cv, caps, hf⟩ := hst mm hmm
      have h1 : eqName ≠ D.member mm := fun he => hnot (he ▸ hmemb mm hmm)
      have h2 : eqReflName ≠ D.member mm := fun he => by
        rw [← he, f2] at hf; exact nomatch Option.some.inj hf
      have h3 : eqName.str "rec" ≠ D.member mm := fun he => by
        rw [← he, f3] at hf; exact nomatch Option.some.inj hf
      have ha := haway h1 h2 h3
      rw [ha.1, ha.2]
    · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
      have h1 : eqName ≠ D.ctorName c j := fun he => by
        rw [← he, f1] at hf; exact nomatch Option.some.inj hf
      have h3 : eqName.str "rec" ≠ D.ctorName c j := fun he => by
        rw [← he, f3] at hf; exact nomatch Option.some.inj hf
      have h2 : eqReflName ≠ D.ctorName c j := fun he => by
        have hck : c < D.k := hkk ▸ hc
        obtain ⟨cv₀, nPc, nF, hf₀, bs, args, hs, -⟩ := (hcov.own D hD).ctorConcl c hck j hj
        rw [← he, f2] at hf₀
        have hc3 := Option.some.inj hf₀
        change ConstantInfo.ctorInfo _ _ _ = _ at hc3
        injection hc3 with e5 e6 e7
        subst e5; subst e6; subst e7
        change some (_, Expr.app (Expr.app (Expr.app (Expr.const eqName [Level.param uN]) _) _) _)
          = _ at hs
        have hb := Option.some.inj hs
        have hx := congrArg (fun x : List Expr × Expr => x.2.getAppFn) hb
        simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hx
        injection hx with e8 _
        exact hnot (e8 ▸ hmemb c hck)
      have ha := haway h1 h2 h3
      rw [ha.1, ha.2]
  -- `Eq`'s block at the record's names
  have hty : ∀ ψ : Name → Nat, denote (renAcval mp.base2.acval env env') env' ψ 0
      (eqI.atLps [p]).toConstantVal.type
        = some (.pi (.sort (ψ p)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := fun ψ => by
    rw [hde, denote_pair mp.base2 hpairE, denote_eqA_type]
    show some (eqTy _) = _
    unfold eqTy
    rw [show Level.substFn ψ eqI.toConstantVal.levelParams
        ((eqI.atLps [p]).toConstantVal.levelParams.map Level.param) uN = ψ p from htr ψ]
  have hrefty : (eqReflA.atLps [p]).toConstantVal.type
      = Expr.forallE (.sort (.param p))
          (Expr.forallE (.bvar 0)
            (.app (.app (.app (.const eqName [.param p]) (.bvar 1)) (.bvar 0)) (.bvar 0))) := by
    rfl
  have hcanon : ConLeche.nestCanonCrest [eqName] ((eqReflA.atLps [p]).toConstantVal.levelParams.map .param)
      2 (eqReflA.atLps [p]).toConstantVal.type
        = some (.app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero))) := by
    rw [hrefty]
    show ConLeche.nestCanonCrest [eqName] [.param p] 2 _ = _
    have hI : ConLeche.instPisWith (ConLeche.nestPhs 2) (Expr.forallE (.sort (.param p))
        (Expr.forallE (.bvar 0)
          (.app (.app (.app (.const eqName [.param p]) (.bvar 1)) (.bvar 0)) (.bvar 0))))
        = some (.app (.app (.app (.const eqName [.param p]) (.fvar 0 (.sort .zero)))
            (.fvar 1 (.sort .zero))) (.fvar 1 (.sort .zero))) := rfl
    unfold ConLeche.nestCanonCrest
    rw [hI]
    simp [Expr.replaceApps, Expr.appHole?, Expr.phApp?, ConLeche.nestCanonSub]
  have hnd2 : ([p] : List Name).Nodup := hnd1
  let eqD : LfpDatum V := eqLfp eqName eqReflName fun ψ => ψ p
  have hstoredE : LfpStored env' eqD := eqLfp_stored ⟨_, _, f1'⟩ ⟨_, _, _, f2'⟩
  have hclause : LfpClause (renAcval mp.base2.acval env env') eqD :=
    eqLfp_clause
      (fun ψ ρ A a b hA ha hb => by
        show SetTheory.app (SetTheory.app (SetTheory.app (interp V ρ _) A) a) b = _
        rw [hEv']
        exact eqValT_app₃ _ ρ A a b (by rw [htr]; exact hA) ha hb)
      (fun ψ ρ => by rw [hRv']; exact eqReflValT_interp _ ρ)
  have hreads : LfpReads (renAcval mp.base2.acval env env') env' eqD := eqLfp_reads f1' rfl hty
  have hcaps : LfpCaps env' eqD := eqLfp_caps f1'
    (fun ψ => by
      show ConLeche.PropWhen.holds ψ (ConLeche.PropWhen.ifAllZero []) = true
      rw [ConLeche.PropWhen.holds_ifAllZero]; rfl)
    rfl
    ⟨_, _, _, f2', _, [.bvar 0], rfl⟩
  have hctorReads : LfpCtorReads (renAcval mp.base2.acval env env') env' eqD := by
    refine ⟨rfl, fun c hc j hj => ?_⟩
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    refine ⟨(eqReflA.atLps [p]).toConstantVal, 2, 0, f2', rfl,
      fun mm hmm => ⟨(eqI.atLps [p]).toConstantVal, _, by
        obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
        exact f1', rfl⟩,
      (fun ψ dsC bodyC hrd hle ρ hsat => by
        match dsC, hle with
        | d0 :: d1 :: rest, _ =>
          rw [hrefty] at hrd
          obtain ⟨ta, ba, hta, hba, he⟩ := denote_forallE_inv hrd
          obtain ⟨tb, bb, htb, -, he'⟩ := denote_forallE_inv hba
          simp only [mkPisAV] at he
          injection he with h0 h1
          rw [← h1] at he'
          injection he' with h2 _
          rw [denote_sort] at hta
          simp only [ConLeche.Expr.instantiate1, ite_true] at htb
          rw [denote_fvar] at htb
          obtain rfl := Option.some.inj hta
          obtain rfl := Option.some.inj htb
          simp only [List.take_succ_cons, List.take_zero, h0, h2]
          exact hsat),
      .app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)), hcanon,
      (by decide : Expr.nestOcc [eqName] 0 0 (.app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)))
        = false),
      fun ψ => ⟨rfl, rfl, [], [.pi (.bvar 1) (.sort 0)], ?_, rfl, rfl,
        fun mm hmm => by
          obtain rfl : mm = 0 := Nat.lt_one_iff.mp hmm
          refine ⟨(eqI.atLps [p]).toConstantVal, _, .forallE (.fvar 0 (.sort .zero)) (.sort .zero),
            f1', rfl, ?_⟩
          simp [denote_forallE, denote_sort, denote_fvar, Expr.instantiate1, Level.eval],
        trivial⟩⟩
    show denote _ _ ψ (2 + 1) (.app (.fvar 2 (.sort .zero)) (.fvar 1 (.sort .zero)))
      = some (mkPisAV [] (Term.mkAppN (.bvar (0 + (1 - 1 - 0))) [.bvar 1]))
    simp [denote_app, denote_fvar, mkPisAV]
  let kept := mp.lfpBlocks.filter fun D => decide (eqName ∉ D.names)
  have hkept : ∀ {D : LfpDatum V}, D ∈ kept → D ∈ mp.lfpBlocks ∧ eqName ∉ D.names := fun hD => by
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hD
    exact ⟨h1, by simpa using h2⟩
  obtain ⟨mp', hacR, hbl⟩ := mp.renameCore h hwf R.mem hlink hstable (eqD :: kept) (fun D hD => by
    rcases List.mem_cons.mp hD with rfl | hD'
    · exact ⟨hclause, hstoredE, hreads, hctorReads, hcaps⟩
    · obtain ⟨h1, h2⟩ := hkept hD'
      exact lfp_keep mp h h1 (hkeepD h1 h2).1 (hkeepD h1 h2).2)
  refine ⟨mp', hacR, fun D hD => ?_, fun _ => ?_⟩
  · rw [hbl] at hD
    rcases List.mem_cons.mp hD with rfl | hD'
    · exact .inr fun _ => rfl
    · exact .inl (hkept hD').1
  -- a block with `Eq` among its names is `Eq`'s
  have hnotE : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → eqName ∈ D.names → D.names = [eqName] := by
    intro D hD hin
    obtain ⟨m, hm, he⟩ := List.getElem_of_mem hin
    have hmk : m < D.k := by rw [← hcov.len D hD]; exact hm
    have hmem : D.member m = eqName := by
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some, he]
    have hall := hcov.all D hD m hmk (eqI.toConstantVal) _ (by rw [hmem]; exact f1)
    exact hall.symm
  have hlookC : ∀ {C : Name}, C ≠ eqName → ∀ n,
      ctorLook env'.find? C n = ctorLook env.find? C n := by
    intro C hC n
    refine ctorLook_congr (fun x => ?_) n
    by_cases he3 : eqName.str "rec" = x
    · subst he3
      exact ⟨_, _, .inr ⟨f3, f3', rfl⟩⟩
    · by_cases he2 : eqReflName = x
      · subst he2
        refine ⟨_, _, .inr ⟨f2, f2', ?_⟩⟩
        have hb : (eqName == C) = false := by
          rw [beq_eq_false_iff_ne]; exact hC.symm
        show (if (eqName == C) = true then _ else _) = if (eqName == C) = true then _ else _
        rw [hb]; rfl
      · by_cases he1 : eqName = x
        · subst he1
          exact ⟨_, _, .inr ⟨f1, f1', rfl⟩⟩
        · have ha := haway he1 he2 he3
          cases hf : E.find? x with
          | none => exact ⟨default, default, .inl ⟨by rw [ha.1, hf], by rw [ha.2, hf]⟩⟩
          | some d => exact ⟨d, d, .inr ⟨by rw [ha.1, hf], by rw [ha.2, hf], rfl⟩⟩
  exact {
    cover := fun n cv caps hf hn hq => by
      rw [hbl]
      by_cases he1 : eqName = n
      · subst he1
        exact ⟨eqD, List.mem_cons_self, 0, Nat.one_pos, rfl⟩
      · have he2 : eqReflName ≠ n := fun he => by
          rw [← he, f2'] at hf; exact nomatch Option.some.inj hf
        have he3 : eqName.str "rec" ≠ n := fun he => by
          rw [← he, f3'] at hf; exact nomatch Option.some.inj hf
        have ha := haway he1 he2 he3
        have hf0 : env.find? n = some (.indInfo cv caps) := by rw [ha.1, ← ha.2]; exact hf
        obtain ⟨D, hD, mm, hmm, he⟩ := hcov.cover n cv caps hf0 hn hq
        refine ⟨D, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hD, ?_⟩), mm, hmm, he⟩
        have hnot : eqName ∉ D.names := fun hin => by
          have hnm := hnotE hD hin
          have hk1 : D.k = 1 := by rw [← hcov.len D hD, hnm]; rfl
          obtain rfl : mm = 0 := by omega
          apply he1
          rw [← he]
          unfold LfpDatum.member
          rw [hnm]; rfl
        simpa using hnot
    nodup := fun D hD => by
      rw [hbl] at hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact nodup_one _
      · exact hcov.nodup D (hkept hD').1
    len := fun D hD => by
      rw [hbl] at hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · rfl
      · exact hcov.len D (hkept hD').1
    all := fun D hD mm hmm cv caps hf => by
      rw [hbl] at hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact lfpAll_one (n := eqName) (c := eqI.atLps [p]) rfl rfl f1'
          (fun _ _ h => by injection h with _ h; subst h; rfl) mm hmm cv caps hf
      · obtain ⟨h1, h2⟩ := hkept hD'
        rw [(hkeepD h1 h2).1 mm hmm] at hf
        exact hcov.all D h1 mm hmm cv caps hf
    fresh := fun _ _ _ _ hin => absurd hin List.not_mem_nil
    own := fun D hD => by
      rw [hbl] at hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact lfpOwn_one (T := eqName) (cs := [((eqReflA.atLps [p]).toConstantVal, 2, 0)]) rfl rfl f1'
          (by
            show List.filterMap (ctorLook env'.find? eqName) [eqReflName] = _
            simp only [List.filterMap_cons, List.filterMap_nil, ctorLook, f2']
            rfl)
          ⟨2, [((eqReflA.atLps [p]).toConstantVal, 0)], rfl, rfl, fun j hj => by
            obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
            exact f2'⟩
          (fun _ h => by simp [nestPick] at h) hnd1
          (fun nP' L h j hj => by
            simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain rfl : j = 0 := by simp at hj; omega
            exact ⟨_, [.bvar 1, .bvar 0, .bvar 0], rfl, fun _ => rfl⟩)
      · obtain ⟨h1, h2⟩ := hkept hD'
        have hkk := hcov.wid D h1
        have hmne : ∀ c, c < D.k → D.member c ≠ eqName := by
          intro c hc he
          apply h2
          rw [← he]
          have hl : c < D.names.length := by rw [hcov.len D h1]; exact hc
          unfold LfpDatum.member
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
          exact List.getElem_mem hl
        exact (hcov.own D h1).monoOn (hkeepD h1 h2).1
          (fun c hc j hj => (hkeepD h1 h2).2 c (hkk ▸ hc) j hj)
          fun c hc => nestContainer_congr ((hkeepD h1 h2).1 c hc) (hlookC (hmne c hc))
    wid := fun D hD => by
      rw [hbl] at hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · rfl
      · exact hcov.wid D (hkept hD').1 }

/-! ## The block's step -/

/-- What a pin's rules read of their constructors' parameters: nothing. -/
@[expose] def pinRulesLF : ConstantInfo → Bool
  | .recInfo _ _ _ _ rules => rules.all fun r =>
    (pinnedInfo (RecRule.ctor r)).toConstantVal.levelParams.isEmpty
  | _ => true

theorem hlf_of {L₀ : List ConstantInfo} (h : ∀ p ∈ L₀, pinRulesLF p = true) :
    ∀ p ∈ L₀, ∀ cv mI rP isK rules, p = .recInfo cv mI rP isK rules →
      ∀ r ∈ rules, (pinnedInfo (RecRule.ctor r)).toConstantVal.levelParams = [] := by
  intro p hp cv mI rP isK rules he r hr
  have := h p hp
  subst he
  simp only [pinRulesLF, List.all_eq_true, List.isEmpty_iff] at this
  exact this r hr

/-- What a record's agreement with its pin says. -/
theorem pinAgrees_cv {c c' : ConstantInfo} (h : ConLeche.pinAgrees c c' = true) :
    c.toConstantVal = c'.toConstantVal ∧ conKind c = conKind c' := by
  unfold ConLeche.pinAgrees at h
  split at h
  · exact ⟨ConLeche.ConstantVal.eq_of_beqP h, rfl⟩
  · have he := ConLeche.ConstantInfo.eq_of_beqP h
    rw [he]; exact ⟨rfl, rfl⟩

/-- The relation across a renaming of the block just installed. -/
theorem CoverRel.ren {κ : Prop} {L₀ : List ConstantInfo} {E env env' : Env} {m₀ : EnvModelM V E}
    {m₁ : EnvModelM V env} {m' : EnvModelM V env'} (r : CoverRel m₀ m₁) (R : RenRel κ L₀ E env env')
    (hac : m'.base2.acval = renAcval m₁.base2.acval env env')
    (hb : ∀ D ∈ m'.lfpBlocks, D ∈ m₁.lfpBlocks ∨ ∀ mm, D.telescope mm = none) : CoverRel m₀ m' :=
  ⟨fun n ci hn => by
    have hs : (E.find? n).isSome = true := by rw [hn]; rfl
    rw [(R.stE n hs).2]; exact hn,
   fun n hn => by
    rw [hac, renAcval_same ((R.stE n hn).2.trans (R.stE n hn).1.symm)]
    exact r.leaf n hn,
   fun ψ d e ta hb hta => by
    rw [hac, denote_ren R.ren m₁.base2.acval_params ψ d e]
    exact r.read ψ d e ta hb hta,
   fun D hD => (hb D hD).elim (fun h => r.blocks D h) .inr⟩

/-- **A pinned block, at the record's names, at the P tier.** -/
theorem declBasisPB_at {E env₂ : Env} (mp : EnvModelM V E) {kind : ConLeche.BasisKind}
    {block : List ConstantInfo} (hk : kind ≠ .quotK) (hOk : ConLeche.pinListOk block kind.decls = true)
    (hrun : BasisInstallRun E (kind.storedAt block) env₂) (hwf : EnvWF env₂) :
    CoverStep mp env₂ := by
  simp only [ConLeche.pinListOk, Bool.and_eq_true] at hOk
  obtain ⟨hlist, hlinks⟩ := hOk
  cases kind with
  | quotK => exact absurd rfl hk
  | natK =>
    have pairs := pinPairs_of_ok (κ := True) (ins := ConLeche.BasisKind.natK.installed) hlist rfl (by
      intro p hp
      simp only [show ConLeche.BasisKind.natK.installed = [ConLeche.natI, ConLeche.natZeroA,
        ConLeche.natSuccA, ConLeche.natRecA] from rfl, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨by decide, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      · exact ⟨by decide, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      · exact ⟨by decide, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      · exact ⟨by decide, rfl, fun _ hnr => absurd rfl (hnr _ _ _ _ _)⟩)
    obtain ⟨env₁, hrs, R⟩ := renRel_chain pairs (fun _ hp => hp) (RenRel.refl True _ E) hrun
    obtain ⟨mp₁, r₁, hc₁⟩ := declBasisPB_natK mp hrs
    obtain ⟨mp', hac', hb', hc'⟩ := coverStep_keep mp mp₁ R hwf (hlf_of (by decide))
    exact ⟨mp', r₁.ren R hac' hb', hc' ∘ hc₁⟩
  | emptyK =>
    have pairs := pinPairs_of_ok (κ := True) (ins := ConLeche.BasisKind.emptyK.installed) hlist rfl (by
      intro p hp
      simp only [show ConLeche.BasisKind.emptyK.installed = [ConLeche.emptyI, ConLeche.emptyRecA] from rfl,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨by decide, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      · exact ⟨by decide, rfl, fun _ hnr => absurd rfl (hnr _ _ _ _ _)⟩)
    obtain ⟨env₁, hrs, R⟩ := renRel_chain pairs (fun _ hp => hp) (RenRel.refl True _ E) hrun
    obtain ⟨mp₁, r₁, hc₁⟩ := declBasisPB_emptyK mp hrs
    obtain ⟨mp', hac', hb', hc'⟩ := coverStep_keep mp mp₁ R hwf (hlf_of (by decide))
    exact ⟨mp', r₁.ren R hac' hb', hc' ∘ hc₁⟩
  | falseK =>
    have pairs := pinPairs_of_ok (κ := True) (ins := ConLeche.BasisKind.falseK.installed) hlist rfl (by
      intro p hp
      simp only [show ConLeche.BasisKind.falseK.installed = [ConLeche.falseI, ConLeche.falseRecA] from rfl,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨by decide, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      · exact ⟨by decide, rfl, fun _ hnr => absurd rfl (hnr _ _ _ _ _)⟩)
    obtain ⟨env₁, hrs, R⟩ := renRel_chain pairs (fun _ hp => hp) (RenRel.refl True _ E) hrun
    obtain ⟨mp₁, r₁, hc₁⟩ := declBasisPB_falseK mp hrs
    obtain ⟨mp', hac', hb', hc'⟩ := coverStep_keep mp mp₁ R hwf (hlf_of (by decide))
    exact ⟨mp', r₁.ren R hac' hb', hc' ∘ hc₁⟩
  | eqK =>
    rw [show ConLeche.BasisKind.eqK.decls = [eqA, eqReflA, eqRecA] from rfl] at hlist hlinks
    match block, hlist with
    | [], h => simp [ConLeche.listBeqBy] at h
    | [_], h => simp [ConLeche.listBeqBy] at h
    | [_, _], h => simp [ConLeche.listBeqBy] at h
    | _ :: _ :: _ :: _ :: _, h => simp [ConLeche.listBeqBy] at h
    | [b1, b2, b3], hlist =>
      have hlist0 := hlist
      simp only [ConLeche.listBeqBy, Bool.and_true, Bool.and_eq_true, ConLeche.pinCopyOk,
        beq_iff_eq] at hlist
      obtain ⟨⟨⟨hn1, hl1⟩, ha1⟩, ⟨⟨hn2, hl2⟩, ha2⟩, ⟨⟨hn3, hl3⟩, ha3⟩⟩ := hlist
      obtain ⟨c1, k1⟩ := pinAgrees_cv ha1
      obtain ⟨c2, k2⟩ := pinAgrees_cv ha2
      obtain ⟨c3, k3⟩ := pinAgrees_cv ha3
      rw [conKind_atLps] at k1 k2 k3
      obtain ⟨v1, cp1, rfl⟩ : ∃ v c, b1 = .indInfo v c := by
        cases b1 <;> first | exact ⟨_, _, rfl⟩ | (simp [conKind, eqA] at k1)
      obtain ⟨v2, a2, b2', rfl⟩ : ∃ v a b, b2 = .ctorInfo v a b := by
        cases b2 <;> first | exact ⟨_, _, _, rfl⟩ | (simp [conKind, eqReflA] at k2)
      obtain ⟨v3, mI, rP, isK, rs, rfl⟩ : ∃ v m r k rs, b3 = .recInfo v m r k rs := by
        cases b3 <;> first | exact ⟨_, _, _, _, _, rfl⟩ | (simp [conKind, eqRecA] at k3)
      have hn1' : v1.name = eqName := congrArg ConstantVal.name c1
      have hn2' : v2.name = eqReflName := congrArg ConstantVal.name c2
      simp [ConLeche.blockLinksOk, ConLeche.constNamed?, List.find?, ConstantInfo.name,
        ConstantInfo.toConstantVal, hn1', hn2', eqRecA, eqA, eqReflA, ConLeche.BasisDSL.rule, ConLeche.pinLinkOk,
        show (eqName == eqReflName) = false by decide] at hlinks
      obtain ⟨he12, a, hv2, hsub⟩ := hlinks
      have hl3' : v3.levelParams.length = 2 := hl3
      obtain ⟨p1, q, hv3⟩ : ∃ p1 q, v3.levelParams = [p1, q] := by
        match hq : v3.levelParams, hl3' with
        | [p1, q], _ => exact ⟨p1, q, rfl⟩
      have hq : a = q := by
        rw [hv3] at hsub
        have hu : ConLeche.BasisDSL.u1N ≠ ConLeche.BasisDSL.uN := by decide
        simp [Level.subst, Level.subst.go, hu] at hsub
        exact hsub
      subst hq
      have hv1 : v1.levelParams = [a] := by rw [← he12]; exact hv2
      have hnd3 : ([p1, a] : List Name).Nodup := by
        have : (ConstantInfo.recInfo v3 mI rP isK rs).toConstantVal.levelParams = [p1, a] := hv3
        rw [this] at hn3
        exact nodup_of_nameNodup hn3
      have hne : p1 ≠ a := by
        intro he
        have := (List.nodup_cons.mp hnd3).1
        exact this (by rw [he]; exact List.mem_cons_self)
      have pairs := pinPairs_of_ok (κ := False) (ins := [eqI, eqReflA, eqRecA]) hlist0 rfl (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨by decide, rfl, fun hf => hf.elim⟩
        · exact ⟨by decide, rfl, fun hf => hf.elim⟩
        · exact ⟨by decide, rfl, fun hf => hf.elim⟩)
      obtain ⟨env₁, hrs, R⟩ := renRel_chain pairs (fun _ hp => hp) (RenRel.refl False _ E) hrun
      have hrs₀ := hrs
      obtain ⟨-, -, -, rfl⟩ := hrs
      obtain ⟨mp₁, r₁, hc₁, hEv, hRv⟩ := declBasisPB_eqK mp hrs₀
      have hrun' := hrun
      rw [show ConLeche.BasisKind.eqK.storedAt [ConstantInfo.indInfo v1 cp1, ConstantInfo.ctorInfo v2 a2 b2',
          ConstantInfo.recInfo v3 mI rP isK rs]
          = [eqI.atLps v1.levelParams, eqReflA.atLps v2.levelParams, eqRecA.atLps v3.levelParams] from rfl,
        hv1, hv2, hv3] at hrun'
      obtain ⟨-, -, -, henv₂⟩ := hrun'
      obtain ⟨mp', hac', hb', hc'⟩ := coverStep_eq hne mp mp₁ hEv hRv R hwf henv₂
      exact ⟨mp', r₁.ren R hac' hb', hc' ∘ hc₁⟩

/-! ## A quotient record -/

/-- **One new constant at other names**: a quotient record's.  Nothing older
reads the head's level-parameter names (a reference is positional, `denote_ren`),
so only the head differs. -/
theorem coverStep_head {E env env' : Env} {pin p' : ConstantInfo} {L₀ : List ConstantInfo}
    (mpE : EnvModelM V E) (mp : EnvModelM V env) (R : RenRel False L₀ E env env') (hwf : EnvWF env')
    (henv : env = ⟨pin :: E.consts, E.tables⟩) (henv' : env' = ⟨p' :: E.consts, E.tables⟩)
    (hnm : p'.name = pin.name) (hrename : p' = pin.atLps p'.toConstantVal.levelParams)
    (hfresh : E.find? pin.name = none)
    -- a recursor's rules do not read a constructor's names
    (hrules : ∀ cv mI rP isK rules, p' = .recInfo cv mI rP isK rules →
      ∀ r ∈ rules, RecRule.fire r ≠ .plain)
    -- the head is no recorded block's
    (hind : ∀ cv caps, pin = .indInfo cv caps → pin = quotA)
    (hctor : ∀ cv a b, pin = .ctorInfo cv a b →
      pin = quotMkA ∧ ∃ q, E.find? quotName = some (quotA.atLps [q])) :
    ∃ mp' : EnvModelM V env', mp'.base2.acval = renAcval mp.base2.acval env env' ∧
      (∀ D ∈ mp'.lfpBlocks, D ∈ mp.lfpBlocks ∨ ∀ mm, D.telescope mm = none) ∧
      (LfpCover mp [] → LfpCover mp' []) := by
  have h := R.ren
  have fh : env.find? pin.name = some pin := by
    subst henv
    rw [Env.find?_cons]; exact ite_eq_left rfl
  have fh' : env'.find? pin.name = some p' := by
    subst henv'
    rw [Env.find?_cons]; exact ite_eq_left hnm
  have haway : ∀ {n : Name}, pin.name ≠ n →
      env.find? n = E.find? n ∧ env'.find? n = E.find? n := by
    intro n hn
    constructor
    · subst henv
      rw [Env.find?_cons, ite_eq_right hn]
    · subst henv'
      rw [Env.find?_cons, ite_eq_right (by rw [hnm]; exact hn)]
  have hsameN : ∀ {n : Name}, pin.name ≠ n → env'.find? n = env.find? n := fun hn => by
    rw [(haway hn).1, (haway hn).2]
  -- a prefix's constant's name is not the head's
  have hstored : ∀ {n : Name}, (E.find? n).isSome = true → pin.name ≠ n := by
    intro n hs he
    rw [← he, hfresh] at hs
    exact nomatch hs
  have hold : ∀ {n : Name} {cv mI rP isK rules}, E.find? n = some (.recInfo cv mI rP isK rules) →
      ∀ r ∈ rules, ∃ cvj a b, E.find? (RecRule.ctor r) = some (.ctorInfo cvj a b) :=
    fun hf r hr => mpE.base2.rec_ctors _ _ _ _ _ _ hf r hr
  have hlink : ∀ n ci, env'.find? n = some ci → reservedBasisNames.contains n = true →
      PinLinked env' n ci := by
    intro n ci hf hres cv mI rP isK rules hci rl hrl hpl cvj cnP cnF hfc us hus
    subst hci
    by_cases he : pin.name = n
    · subst he
      rw [fh'] at hf
      exact absurd hpl (hrules _ _ _ _ _ (Option.some.inj hf) rl hrl)
    · have ha := haway he
      have hE : E.find? n = some (.recInfo cv mI rP isK rules) := by rw [← ha.2]; exact hf
      obtain ⟨-, hlkE, -⟩ := mpE.base2.basis_pinned n _ hE hres
      obtain ⟨cj, a, b, hcj⟩ := hold hE rl hrl
      have hne := hstored (n := RecRule.ctor rl) (by rw [hcj]; rfl)
      exact hlkE cv mI rP isK rules rfl rl hrl hpl cvj cnP cnF
        (by rw [← (haway hne).2]; exact hfc) us hus
  have hstable : ∀ n cv mI rP isK rules,
      env'.find? n = some (.recInfo cv mI rP isK rules) →
      (reservedBasisNames.contains n = false ∨ isK = false) →
      ∀ r ∈ rules, env'.find? (RecRule.ctor r) = env.find? (RecRule.ctor r) ∧
        ∀ cvj a b, env.find? (RecRule.ctor r) = some (.ctorInfo cvj a b) →
          ConLeche.ctorFamily env'.find? cvj = ConLeche.ctorFamily env.find? cvj := by
    intro n cv mI rP isK rules hf _ r hr
    obtain ⟨cvj₀, a₀, b₀, hc₀⟩ := recCtors_ren mp.base2 h n cv mI rP isK rules hf r hr
    have hne : pin.name ≠ RecRule.ctor r := by
      intro he
      rw [← he, fh'] at hc₀
      have hp := Option.some.inj hc₀
      by_cases hn : pin.name = n
      · subst hn
        rw [fh', hp] at hf
        exact nomatch Option.some.inj hf
      · have hE : E.find? n = some (.recInfo cv mI rP isK rules) := by
          rw [← (haway hn).2]; exact hf
        obtain ⟨_, _, _, hc⟩ := hold hE r hr
        exact hstored (n := RecRule.ctor r) (by rw [hc]; rfl) he
    refine ⟨hsameN hne, fun cvj a' b' hfj => ctorFamily_ind_congr fun T us' hT cvT capsT => ?_⟩
    have hfE : E.find? (RecRule.ctor r) = some (.ctorInfo cvj a' b') := by
      rw [← (haway hne).1]; exact hfj
    have hres := (mpE.base2.wf.consts _ (Env.find?_mem hfE)).2.2.1
    have hTs := Expr.find?_isSome_of_piResult_getAppFn_const hres hT
    rw [hsameN (hstored hTs)]
  rcases Classical.em (LfpCover mp []) with hcov | hcov
  case inr =>
    obtain ⟨mp', hacR, hbl⟩ := mp.renameCore h hwf R.mem hlink hstable [] (fun _ hD => nomatch hD)
    exact ⟨mp', hacR, (fun D hD => by rw [hbl] at hD; exact nomatch hD), fun hc => absurd hc hcov⟩
  -- no recorded block has the head among its names
  have hmemb : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ mm, mm < D.k → D.member mm ≠ quotName := by
    intro D hD mm hmm he
    have hl : mm < D.names.length := by rw [hcov.len D hD]; exact hmm
    obtain ⟨cv, caps, hf⟩ := LfpCover.member_find hD hmm
    have hall := hcov.all D hD mm hmm cv caps hf
    rw [he] at hf
    -- a stored `Quot` records no block
    have hc := (mp.base2.basis_pinned quotName _ hf (by decide)).1
    have hk := hc.1
    simp only [show pinnedInfo quotName = quotA from rfl, quotA, ConstantInfo.atLps] at hk
    injection hk with _ hcaps
    rw [hcaps] at hall
    have hnil : D.names = [] := hall.symm
    rw [hnil] at hl
    exact absurd hl (Nat.not_lt_zero _)
  have hkeepD : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks →
      (∀ mm, mm < D.k → env'.find? (D.member mm) = env.find? (D.member mm)) ∧
      (∀ c, c < D.N → ∀ j, j < D.nctors c →
        env'.find? (D.ctorName c j) = env.find? (D.ctorName c j)) := by
    intro D hD
    obtain ⟨-, ⟨hst, hstC⟩, -⟩ := mp.lfp_ok D hD
    have hkk := hcov.wid D hD
    refine ⟨fun mm hmm => hsameN fun he => ?_, fun c hc j hj => hsameN fun he => ?_⟩
    · obtain ⟨cv, caps, hf⟩ := hst mm hmm
      rw [← he, fh] at hf
      have hq := hind _ _ (Option.some.inj hf)
      exact hmemb hD mm hmm (by
        rw [← he, hq]; rfl)
    · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
      rw [← he, fh] at hf
      obtain ⟨hpm, -⟩ := hctor _ _ _ (Option.some.inj hf)
      have hck : c < D.k := hkk ▸ hc
      obtain ⟨cv₀, nPc, nF, hf₀, bs, args, hs, -⟩ := (hcov.own D hD).ctorConcl c hck j hj
      rw [← he, fh, hpm] at hf₀
      have hc3 := Option.some.inj hf₀
      change ConstantInfo.ctorInfo _ _ _ = _ at hc3
      injection hc3 with e5 e6 e7
      subst e5; subst e6; subst e7
      change some (_, Expr.app (Expr.app (Expr.const quotName [Level.param uN]) _) _)
        = _ at hs
      have hb := Option.some.inj hs
      have hx := congrArg (fun x : List Expr × Expr => x.2.getAppFn) hb
      simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hx
      injection hx with e8 _
      exact hmemb hD c hck e8.symm
  obtain ⟨mp', hacR, hbl⟩ := mp.renameCore h hwf R.mem hlink hstable mp.lfpBlocks (fun D hD =>
    lfp_keep mp h hD (hkeepD hD).1 (hkeepD hD).2)
  have hlook : ∀ {C : Name}, C ≠ quotName → ∀ n,
      ctorLook env'.find? C n = ctorLook env.find? C n := by
    intro C hC n
    refine ctorLook_congr (fun y => ?_) n
    by_cases he : pin.name = y
    · subst he
      refine ⟨_, _, .inr ⟨fh, fh', ?_⟩⟩
      have hkind : conKind p' = conKind pin := by rw [hrename, conKind_atLps]
      cases hp : pin with
      | ctorInfo cv a b =>
        obtain ⟨hpm, -⟩ := hctor _ _ _ hp
        rw [hp] at hrename
        rw [← hp, hpm] at hrename ⊢
        have hb : (quotName == C) = false := by
          rw [beq_eq_false_iff_ne]; exact hC.symm
        rw [hrename]
        show (if (quotName == C) = true then _ else _) = if (quotName == C) = true then _ else _
        rw [hb]; rfl
      | _ =>
        rw [hp] at hkind
        cases p' <;> first | rfl | exact nomatch hkind
    · have ha := haway he
      cases hf : E.find? y with
      | none => exact ⟨default, default, .inl ⟨by rw [ha.1, hf], by rw [ha.2, hf]⟩⟩
      | some d => exact ⟨d, d, .inr ⟨by rw [ha.1, hf], by rw [ha.2, hf], rfl⟩⟩
  refine ⟨mp', hacR, fun D hD => .inl (hbl ▸ hD), fun _ => ?_⟩
  exact {
    cover := fun n cv caps hf hn hq => by
      rw [hbl]
      by_cases he : pin.name = n
      · subst he
        rw [fh'] at hf
        have hkind : conKind p' = conKind pin := by rw [hrename, conKind_atLps]
        rw [Option.some.inj hf] at hkind
        cases hp : pin with
        | indInfo cvp cp =>
          exact absurd (show pin.name = quotName by rw [hind _ _ hp]; rfl) hq
        | _ => rw [hp] at hkind; exact nomatch hkind
      · have hf0 : env.find? n = some (.indInfo cv caps) := by
          rw [← hsameN he]; exact hf
        exact hcov.cover n cv caps hf0 hn hq
    nodup := fun D hD => hcov.nodup D (hbl ▸ hD)
    len := fun D hD => hcov.len D (hbl ▸ hD)
    all := fun D hD mm hmm cv caps hf => by
      rw [hbl] at hD
      rw [(hkeepD hD).1 mm hmm] at hf
      exact hcov.all D hD mm hmm cv caps hf
    fresh := fun _ _ _ _ hin => absurd hin List.not_mem_nil
    own := fun D hD => by
      rw [hbl] at hD
      have hkk := hcov.wid D hD
      exact (hcov.own D hD).monoOn (hkeepD hD).1
        (fun c hc' j hj => (hkeepD hD).2 c (hkk ▸ hc') j hj)
        fun c hc' => nestContainer_congr ((hkeepD hD).1 c hc') (hlook (hmemb hD c hc'))
    wid := fun D hD => hcov.wid D (hbl ▸ hD) }

/-- **A quotient record, at its names, at the P tier.** -/
theorem declQuotPB_at {E env₂ : Env} (mp : EnvModelM V E) {k : ConLeche.QuotKind} {cv : ConstantVal}
    (h : DeclQuotRun E k cv env₂) (hwf : EnvWF env₂) : CoverStep mp env₂ := by
  obtain ⟨hhit, hp, hfr, rfl⟩ := h
  simp only [ConLeche.quotPinHit, Bool.and_eq_true, beq_iff_eq] at hhit
  obtain ⟨⟨hnd, hlen⟩, hagree⟩ := hhit
  have hname : (quotAt k cv).name = (quotPin k).name := atLps_name _ _
  have hfr₀ : (E.find? (quotPin k).name).isNone = true := hname ▸ hfr
  obtain ⟨mp₁, r₁, hc₁⟩ := declQuotPB mp hp hfr₀
  have hres : reservedBasisNames.contains (quotPin k).name = true := by cases k <;> decide
  have hpi : pinnedInfo (quotPin k).name = quotPin k := by cases k <;> rfl
  have hlps : (quotAt k cv).toConstantVal.levelParams = cv.levelParams := by
    unfold quotAt; rw [atLps_cv]; rfl
  have hc : PinCopy (quotPin k) (pinnedInfo (quotPin k).name) := by
    rw [hpi]; exact hpi ▸ pinCopy_self hres
  have hc' : PinCopy (quotAt k cv) (pinnedInfo (quotPin k).name) := by
    rw [hpi]
    exact ⟨by rw [hlps]; rfl, by rw [hlps]; exact nodup_of_nameNodup hnd, by rw [hlps]; exact hlen⟩
  have hfE : E.find? (quotPin k).name = none := Option.isNone_iff_eq_none.mp hfr₀
  have R := (RenRel.refl False [quotPin k] E).cons hres hc hc' (fun hf => hf.elim)
    List.mem_cons_self hfE
  obtain ⟨mp', hac', hb', hc'₂⟩ := coverStep_head (p' := quotAt k cv) mp mp₁ R hwf rfl rfl hname
    (by rw [hlps]; rfl) hfE
    (fun cv₂ mI rP isK rules he r hr hpl => by
      -- the eliminators' rules carry their levels
      cases k with
      | type | ctor | sound => exact nomatch he
      | lift | ind =>
        have he' := he
        change ConstantInfo.recInfo _ _ _ _ _ = _ at he'
        injection he' with _ _ _ _ e4
        subst e4
        obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hr
        obtain rfl := List.mem_singleton.mp hrp
        exact nomatch hpl)
    (fun cv₂ caps he => by
      cases k with
      | type => rfl
      | _ => exact nomatch he)
    (fun cv₂ a b he => by
      cases k with
      | ctor =>
        refine ⟨rfl, ?_⟩
        exact quotStored_of mp hp
      | _ => exact nomatch he)
  exact ⟨mp', r₁.ren R hac' hb', hc'₂ ∘ hc₁⟩

end ConLeche.Model
