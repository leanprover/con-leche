module

public import ConLeche.Model.Inductives.BlockLeafOk
import ConLeche.Model.Inductives.FixKit
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The k type formers' conses

`checkBlockInds` stores **all `k` formers before any constructor is
looked at** (official's `declare_inductive_types`), so the Model tier's
first block stage is a LOOP over `consBlockInds`, not a single cons.
Two things follow, and they are the whole content of this module.

* **`blockLeafWalks`** — member `mm`'s leaf `blockTyG … mm` has two
  hereditary premises (`ParamsOkG`, the tower's bit-validity), walked from the
  former's telescope down to the frame below the parameters and the
  member's index variables, where the block-wide base facts — the `k`
  index telescopes graded (`BlockIdxOk`), the `k` X-chain families
  graded (`BlockChainsOkG`) and valid — are the base.  The base facts
  are block-wide but the walk is member-local: the target enters
  nowhere.

* **`stageBlockFormers`** — the loop.  It is **abstract in the leaves**
  (`AOf : Nat → (Name → Nat) → AnnotTerm`), exactly as `ctorsLoopEta`
  is abstract in `leafT`: what a member's cons needs of its leaf is the
  five currency facts, and `blockLeafWalks` + the `blockTyG` capstones
  supply them for the fixpoint leaf.  The one structural novelty at `k`
  is the η invariant: between the formers' conses and the last member's
  constructors up to `k` families are η-pending, so the loop threads
  `EtaFamiliesClosedExceptL env names` (`ConLeche/Verify/EnvGuards.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The block leaf's two hereditary premises -/

section Walks

variable {k nP nIdx : Nat} {resSort : Level}
  {uf : Nat → Nat} {Idss : Nat → List AnnotTerm} {Chs : Nat → List (List AnnotTerm)}

/-- **A member's parameter frame and index spine**, at a frame
satisfying its whole parameter-and-index telescope: the frame below the
index binders satisfies the parameters, and the index variables fit the
index telescope there. -/
theorem blockParamFrame_of_sat {pps : List (Nat × Nat × AnnotTerm)} {Ids : List AnnotTerm}
    (hIds : Ids = (pps.drop nP).map (·.2.2)) {ρ : Nat → V}
    (hρ : Sat V ((pps.map (·.2.2)).reverse) ρ) :
    Sat V ((pps.take nP).map (·.2.2)).reverse (shiftE Ids.length 0 ρ) ∧
      SpineFit (shiftE Ids.length 0 ρ) Ids (frameIdx Ids.length ρ) := by
  rw [reverse_map_take_drop pps nP] at hρ
  -- the parameter frame (at the MEMBER's index count: `hIds` is what
  -- makes the block-wide facts land at the member's own frame)
  have hle : Ids.length ≤ (((pps.drop nP).map (·.2.2)).reverse).length := by
    rw [List.length_reverse, ← hIds]; exact Nat.le_refl _
  have hle2 : (((pps.drop nP).map (·.2.2)).reverse).length ≤ Ids.length := by
    rw [List.length_reverse, ← hIds]; exact Nat.le_refl _
  have hsh : shiftE Ids.length 0 ρ = fun j => ρ (j + Ids.length) := by
    rw [shiftE_zero]
  have hρp : Sat V ((pps.take nP).map (·.2.2)).reverse (fun j => ρ (j + Ids.length)) := by
    have := Sat_drop hρ Ids.length
    rwa [List.drop_append_of_le_length hle, List.drop_eq_nil_of_le hle2,
      List.nil_append] at this
  -- the index spine
  have hspI := spineFit_of_sat (Δ₀ := ((pps.take nP).map (·.2.2)).reverse)
    (Ds := (pps.drop nP).map (·.2.2)) hρ
  rw [← hIds, ← frameIdx_eq_reverse_map] at hspI
  rw [hsh]
  exact ⟨hρp, hspI⟩

/-- **The block leaf's two hereditary premises**, from the former's
data and the block-wide base facts at the parameter frame. -/
theorem blockLeafWalks {pps : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hlen : pps.length = nP + nIdx) (hbits : ∀ d ∈ pps, d.2.1 ≠ 0)
    (hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps (.sort w)))
    {mm : Nat} (hmm : mm < k)
    (hIdsm : Idss mm = ((pps.drop nP).map (·.2.2)))
    (hIdx : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      BlockIdxOk (V := V) k uf ρp Idss ∧ ∀ c, c < k → FieldsValid ρp (Idss c))
    (hX : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      BlockChainsOkG k w ρp uf Idss Chs)
    (hXV : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp)) (Chs c))
    (ρ : Nat → V) :
    ParamsOkG k w ρ uf Idss Chs mm pps ∧
      UnderTowerValid ρ
        (.app (projAV mm ((blockBodyG k w uf Idss Chs).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) pps := by
  have hst := stripPisAV_mkPisAV pps (.sort w)
  rw [hlen] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hokTy ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : ((pps.map (·.2.2)).reverse).length = nP + nIdx := by simp [hlen]
  have hent : ∀ i, i < nP + nIdx → ∃ p, pps[i]? = some p ∧
      p.2.2 = ((pps.map (·.2.2)).reverse).getD (nP + nIdx - 1 - i) default := by
    intro i hi
    have hil : i < pps.length := by rw [hlen]; exact hi
    refine ⟨pps[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel hlen hi (List.getElem?_eq_getElem hil)]
  have hΓnil : ((pps.map (·.2.2)).reverse).drop (nP + nIdx - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  have hIdsLen : (Idss mm).length = nIdx := by rw [hIdsm]; simp [hlen]
  -- the base facts at a frame satisfying the whole telescope
  have hbase : ∀ ρ : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρ →
      BlockBaseG k w ρ uf Idss Chs mm ∧
      AnnotValid V ρ
        (.app (projAV mm ((blockBodyG k w uf Idss Chs).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) := by
    intro ρ hρ
    obtain ⟨hρp, hspI⟩ := blockParamFrame_of_sat hIdsm hρ
    have hsh : shiftE (Idss mm).length 0 ρ = fun j => ρ (j + (Idss mm).length) := by
      rw [shiftE_zero]
    rw [hsh] at hρp hspI
    obtain ⟨hI, hIV⟩ := hIdx _ hρp
    refine ⟨⟨by rw [hsh]; exact hI, by rw [hsh]; exact hX _ hρp, by rw [hsh]; exact hspI⟩, ?_⟩
    have hfr : consList (frameIdx (Idss mm).length ρ) (fun j => ρ (j + (Idss mm).length)) = ρ := by
      have := consList_frameIdx (Idss mm).length ρ
      rwa [hsh] at this
    have hv := blockLeafBody_validV hI hIV (hXV _ hρp) hmm
      (is := frameIdx (Idss mm).length ρ) hspI
    rwa [hfr] at hv
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkG k w ρ uf Idss Chs mm ds)
      hlenΓ hlen hent okΓ
      (fun ρ hρ => (hbase ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hbits d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ
        (.app (projAV mm ((blockBodyG k w uf Idss Chs).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) ds)
      hlenΓ hlen hent okΓ
      (fun ρ hρ => (hbase ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

end Walks

/-! ## The `k` members' parameter frames, identified -/

section Agree

/-- One member's parameter telescope, opened: the `Opened` frame at the
block's parameter count, with the context the former's data read
(`ctorFramesGen`'s opening of the former, at a TELESCOPE longer than the
opening — a member's type has its own indices after the parameters). -/
private theorem openedParams (mp : EnvModelM V μ env) {F : Nat}
    {cvT cvTa : ConstantVal} {nP nFull : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hFD : FormerData mp.base2 cvTa nFull resSort pps) (hle : nP ≤ nFull)
    {tfvs : List Expr} {trest : Expr}
    (hop : ConLeche.openPisAtFvars nP cvTa.type 0 = some (tfvs, trest))
    (ψ : Name → Nat) :
    ∃ R, Opened mp.base2 ψ nP cvTa.type tfvs trest
      ((((pps ψ).take nP).map (·.2.2)).reverse) R := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hop
  obtain ⟨Γ, R, htele, hO⟩ := opened_of hop htf' hbt' (hFD.read ψ) (hFD.okTy ψ)
  obtain ⟨pps', hst', hΓ⟩ := stripPisAV_of_piTeleAV htele
  have hst'' := stripPisAV_mkPisAV_take nP (pps ψ) (AnnotTerm.sort (resSort.eval ψ))
    (by rw [hFD.len ψ]; exact hle)
  obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
  exact ⟨R, by rw [hΓ]; exact hO⟩

/-- **The `k` members' PARAMETER telescopes are interchangeable at a
frame.**  This is official's `check_inductive_types` agreement —
`checkBlockAgree`, every member's parameter domains definitionally
member 0's — read semantically, and it is the one base fact the block
needs that a single family never did: `blockLeafWalks`'s `hIdx`/`hX`/
`hXV` are stated at a frame satisfying MEMBER `mm`'s parameter
telescope, while `Idss c` for `c ≠ mm` is read off member `c`'s own
type.  The producer is defeq soundness at the opened fvar frame
(`paramFrames` at `nF = 0`, between two `nP`-binder openings). -/
theorem blockParamsIff (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env) {F : Nat}
    {p : ConLeche.BlockParts} {isRec : Bool} {envI : Env} {cvTas : List ConstantVal}
    {p₁ : ConLeche.BlockShape}
    (h : ConLeche.checkBlockInds (ConLeche.fueledOps μ F) env p isRec
      = .ok (envI, cvTas, p₁))
    {nPOf : Nat → Nat} {resSort : Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hle : ∀ j, p.nP ≤ nPOf j)
    (hFD : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      FormerData mp.base2 cvTa (nPOf j) resSort (ppsOf j)) :
    ∀ m₁ m₂, m₁ < cvTas.length → m₂ < cvTas.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf m₁ ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ppsOf m₂ ψ).take p.nP).map (·.2.2)).reverse ρ := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, rfl, -, -, htele0, hteles, hagree⟩ :=
    ConLeche.checkBlockInds_shape h
  obtain ⟨cvT0, -, -, hccv0, -⟩ := ConLeche.checkBlockTele_shape htele0
  obtain ⟨hlencvs, hteleAt⟩ := ConLeche.checkBlockTeles_inv hteles
  -- every member's frame is member 0's
  have hkey : ∀ m, m < (cvTa0 :: cvs.map (·.1)).length →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf m ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ppsOf 0 ψ).take p.nP).map (·.2.2)).reverse ρ := by
    intro m hm ψ ρ
    match m with
    | 0 => exact Iff.rfl
    | j + 1 =>
      have hjlen : j < cvs.length := by simpa using hm
      have hjq : cvs[j]? = some cvs[j] := List.getElem?_eq_getElem hjlen
      have hjc : (cvTa0 :: cvs.map (·.1))[j + 1]? = some (cvs[j]).1 := by
        simp [List.getElem?_map, hjq]
      -- member `j + 1`'s own `checkConstantVal` run
      obtain ⟨q, hq, hteleq⟩ := hteleAt j rest[j] (List.getElem?_eq_getElem (by omega))
      obtain rfl : q = cvs[j] := Option.some.inj (hq.symm.trans hjq)
      obtain ⟨cvTq, -, -, hccvq, -⟩ := ConLeche.checkBlockTele_shape hteleq
      -- the agreement's two openings and its per-binder pins
      obtain ⟨-, tfvs0, trest0, tfvs, trest, hop0, hopq, -, hdoms⟩ :=
        ConLeche.checkBlockAgree_inv hagree cvs[j] (List.getElem_mem hjlen)
      obtain ⟨R0, hO0⟩ := openedParams mp hccv0 (hFD 0 cvTa0 (by simp)) (hle 0) hop0 ψ
      obtain ⟨Rq, hOq⟩ := openedParams mp hccvq (hFD (j + 1) _ hjc) (hle (j + 1)) hopq ψ
      have hpin : ∀ i, i < p.nP → ∃ a b, tfvs[i]? = some a ∧ tfvs0[i]? = some b ∧
          ConLeche.isDefEqCore μ env F i (Expr.fvarTypeD a) (Expr.fvarTypeD b) = .ok true := by
        intro i hi
        obtain ⟨a, b, ha, hb, hdeq⟩ := ConLeche.checkBlockDomsAt_inv hdoms i hi
        rw [List.getElem?_map] at hb
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
        exact ⟨a, b', ha, hb', by rw [Nat.zero_add] at hdeq; exact hdeq⟩
      have hpf := paramFrames (nF := 0) (claimsAt_of (V := V) hμ mp ψ F) hO0 hOq hpin
        p.nP (Nat.le_refl _)
      simpa using (hpf).1 ρ
  intro m₁ m₂ h₁ h₂ ψ ρ
  exact (hkey m₁ h₁ ψ ρ).trans (hkey m₂ h₂ ψ ρ).symm

end Agree

/-! ## The k formers' conses -/

/-- **The P step at one block member's former cons**: the leaf's five
currency facts and the capability laws, at the environment holding the
EARLIER members' formers: the former's `checkConstantVal` run is
replaced by the facts it yields (the run happened
at the PRE-block environment, not at this one) and the η closure taken
over the block's whole member list. -/
theorem stageBlockFormer (mp : EnvModelM V μ env) {names : List Name}
    (hE : ConLeche.EtaFamiliesClosedExceptL env names)
    {cvTa : ConstantVal} {caps : IndCaps} {A : (Name → Nat) → AnnotTerm}
    {nP : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hfresh : env.find? cvTa.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvTa.name = false)
    (hpshape : cvTa.name.isProjFnShape = false)
    (hcb : ConstsBound env cvTa.type)
    (hwfI : ConLeche.EnvWF ⟨.indInfo cvTa caps :: env.consts⟩)
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ))
    (hAmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ))))
    (hTlaws : ∀ m₂ : EnvModel V ⟨.indInfo cvTa caps :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvTa.name A →
      CapsLawsAt m₂ cvTa.name cvTa caps) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa caps :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name A := by
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa caps :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa caps) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa caps).name = false := hnres
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa caps)
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI hAbelow hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ kk => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le kk) (hAbelow ψ)) 1)
    hAparams hAok hAvalid (fun ψ => ⟨_, hreadI ψ⟩) ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hAmem ψ ρ
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa caps)
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshape
      (Or.inl ⟨cvTa, caps, rfl, rfl⟩) ?_ m₂ hac ?_
    · -- the OTHER stored families: outside the block they are closed;
      -- a still-pending MEMBER's η constructor is a `ctorInfo`, which
      -- this cons — a former — is not
      intro T' cvT' caps' hf hne hres hcape hfam
      by_cases hmemT : T' ∈ names
      · obtain ⟨-, ⟨cvC', cnP, cnF, hfC'⟩, -⟩ := hfam
        intro hh
        rw [hh, ConLeche.Env.find?_cons_self] at hfC'
        exact nomatch (Option.some.inj hfC')
      · exact etaCtor_ne_of_closed hfresh (hE T' cvT' caps' hf hmemT hcape hres)
    · intro cvT caps' hf _
      have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa caps) env
      obtain ⟨rfl, rfl⟩ :=
        ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
      exact hTlaws m₂ hac

/-- **The `k` type formers' conses, in order** (`checkBlockInds`'s
`consBlockInds`).  Abstract in the leaves, as `ctorsLoopEta` is abstract
in `leafT`: the leaf's five currency facts (`hAbelowOf` … `hAmemOf`) and
the member's capability laws (`hTlawsOf`) are the per-member inputs, and
`blockLeafWalks` with the `blockTyG` capstones supplies them for the
fixpoint leaf.  The η invariant is threaded over the block's whole
member list, because all `k` formers are stored before any constructor. -/
theorem stageBlockFormers {p₁ : BlockShape} {isRec : Bool} {names : List Name}
    {cvTasAll : List ConstantVal} {A : Nat → (Name → Nat) → AnnotTerm}
    {nPOf : Nat → Nat} {resSort : Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hnames : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.name ∈ names)
    (hndN : ∀ (j j' : Nat) (c c' : ConstantVal), cvTasAll[j]? = some c →
      cvTasAll[j']? = some c' → j ≠ j' → c.name ≠ c'.name)
    (hnresOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ConLeche.reservedBasisNames.contains cvTa.name = false)
    (hpshapeOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.name.isProjFnShape = false)
    (htyWF : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.type.hasFvar = false ∧
      cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
      cvTa.type.looseBVarsBounded 0 = true ∧
      (cvTa.type.stripPis p₁.nP).isSome = true)
    (hAbelowOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A j ψ).erase)
    (hAparamsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A j ψ₁ = A j ψ₂)
    (hAokOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A j ψ))
    (hAvalidOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A j ψ))
    (hAmemOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A j ψ) ∈ˢ interp V ρ (mkPisAV (ppsOf j ψ) (.sort (resSort.eval ψ))))
    -- no member's former is named by any member's η constructor (the
    -- constructors are checked at the environment holding ALL the
    -- formers, so a constructor's name is not a former's)
    (hetaNe : ∀ (j j' : Nat) (cvTa cvTb : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTasAll[j']? = some cvTb → (ConLeche.blockCapsAt p₁ j isRec).eta = true →
      cvTb.name ≠ (ConLeche.blockCapsAt p₁ j isRec).etaCtor)
    -- **the member's capability laws**, at the loop's own carrier: its
    -- telescope reading, the former's freshness and its type's bound,
    -- and the η constructors' freshness (what makes the η claim
    -- vacuous before any constructor is stored)
    (hTlawsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ {env' : Env} (m' : EnvModel V env'),
      FormerData m' cvTa (nPOf j) resSort (ppsOf j) →
      env'.find? cvTa.name = none → ConstsBound env' cvTa.type →
      (∀ (j' : Nat) (cvTb : ConstantVal), cvTasAll[j']? = some cvTb →
        (ConLeche.blockCapsAt p₁ j' isRec).eta = true →
        env'.find? (ConLeche.blockCapsAt p₁ j' isRec).etaCtor = none) →
      ∀ m₂ : EnvModel V ⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec) :: env'.consts⟩,
      m₂.acval = acvalWith m'.acval cvTa.name (A j) →
      CapsLawsAt m₂ cvTa.name cvTa (ConLeche.blockCapsAt p₁ j isRec)) :
    ∀ (rest : List ConstantVal) (i : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ j, rest[j]? = cvTasAll[i + j]?) → i + rest.length = cvTasAll.length →
      ConLeche.EtaFamiliesClosedExceptL env names →
      (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
        cvTa.type.constsResolve env = true) →
      (∀ (j : Nat) (cvTa : ConstantVal), i ≤ j → cvTasAll[j]? = some cvTa →
        env.find? cvTa.name = none) →
      (∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        (ConLeche.blockCapsAt p₁ j isRec).eta = true →
        env.find? (ConLeche.blockCapsAt p₁ j isRec).etaCtor = none) →
      (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
        FormerData mp.base2 cvTa (nPOf j) resSort (ppsOf j)) →
      (∀ (j : Nat) (cvTa : ConstantVal), j < i → cvTasAll[j]? = some cvTa →
        env.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mp.base2.acval cvTa.name ψ = A j ψ) →
      ∃ mp' : EnvModelM V μ (ConLeche.consBlockInds p₁ isRec rest i env),
        ConLeche.EtaFamiliesClosedExceptL (ConLeche.consBlockInds p₁ isRec rest i env) names ∧
        (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
          FormerData mp'.base2 cvTa (nPOf j) resSort (ppsOf j)) ∧
        (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
          (ConLeche.consBlockInds p₁ isRec rest i env).find? cvTa.name
            = some (.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) ∧
          ∀ ψ, mp'.base2.acval cvTa.name ψ = A j ψ) ∧
        -- OFF the members consed here the carrier reads as before
        (∀ n : Name, (∀ cvTb ∈ rest, n ≠ cvTb.name) →
          mp'.base2.acval n = mp.base2.acval n)
  | [], i, env, mp, _, hk, hE, _, _, _, hFD, hcons => by
    simp only [List.length_nil, Nat.add_zero] at hk
    refine ⟨mp, hE, hFD, ?_, fun _ _ => rfl⟩
    intro j cvTa hj
    exact hcons j cvTa (by rw [hk]; exact (List.getElem?_eq_some_iff.mp hj).1) hj
  | cvTa :: rest, i, env, mp, hrest, hk, hE, hres, hfreshOf, hfreshC, hFD, hcons => by
    have hi : cvTasAll[i]? = some cvTa := by
      have := hrest 0; simpa using this.symm
    have hfresh : env.find? cvTa.name = none := hfreshOf i cvTa (Nat.le_refl _) hi
    have hcb : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (hres i cvTa hi)
    obtain ⟨hhf, hlp, hlb, hspi⟩ := htyWF i cvTa hi
    have hwfI : ConLeche.EnvWF
        ⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ :=
      ConLeche.envWF_cons_blockInd mp.base2.wf hhf hlp (hres i cvTa hi) hlb hspi
    obtain ⟨mpI, hacI⟩ := stageBlockFormer mp (names := names) hE hfresh
      (hnresOf i cvTa hi) (hpshapeOf i cvTa hi) hcb hwfI (hFD i cvTa hi)
      (hAbelowOf i cvTa hi) (hAparamsOf i cvTa hi) (hAokOf i cvTa hi) (hAvalidOf i cvTa hi)
      (hAmemOf i cvTa hi)
      (fun m₂ hac => hTlawsOf i cvTa hi mp.base2 (hFD i cvTa hi) hfresh hcb hfreshC m₂ hac)
    -- the invariants at the extension
    have hne : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb → j ≠ i →
        cvTb.name ≠ cvTa.name := fun j cvTb hj hji => hndN j i cvTb cvTa hj hi hji
    have hE' : ConLeche.EtaFamiliesClosedExceptL
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env) names :=
      hE.cons hfresh (fun _ _ heq _ => by
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
        exact Or.inr (hnames i cvTa hi))
    have hres' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        cvTb.type.constsResolve
          (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env) = true :=
      fun j cvTb hj => Expr.constsResolve_mono (hres j cvTb hj)
    have hfreshOf' : ∀ (j : Nat) (cvTb : ConstantVal), i + 1 ≤ j → cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env).find?
          cvTb.name = none := by
      intro j cvTb hij hj
      rw [ConLeche.Env.find?_cons,
        if_neg (fun hh => hne j cvTb hj (by omega) hh.symm)]
      exact hfreshOf j cvTb (by omega) hj
    have hFD' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        FormerData mpI.base2 cvTb (nPOf j) resSort (ppsOf j) := by
      intro j cvTb hj
      exact (hFD j cvTb hj).cross (c₀ := .indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec))
        hfresh (ConsCrossAt.ofNtc fun _ h => nomatch h)
        (constsBound_of_constsResolve _ (hres j cvTb hj)) mpI.base2 hacI
    have hcons' : ∀ (j : Nat) (cvTb : ConstantVal), j < i + 1 → cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env).find? cvTb.name
          = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mpI.base2.acval cvTb.name ψ = A j ψ := by
      intro j cvTb hji hj
      rcases Nat.lt_or_ge j i with hlt | hge
      · obtain ⟨hfj, hleafj⟩ := hcons j cvTb hlt hj
        refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfj, fun ψ => ?_⟩
        rw [hacI]
        show acvalWith mp.base2.acval cvTa.name (A i) cvTb.name ψ = _
        rw [acvalWith_ne (hne j cvTb hj (by omega))]
        exact hleafj ψ
      · have hij : j = i := by omega
        subst hij
        obtain rfl := Option.some.inj (hi.symm.trans hj)
        refine ⟨ConLeche.Env.find?_cons_self _ env, fun ψ => ?_⟩
        rw [hacI]
        exact congrFun acvalWith_self ψ
    have hrest' : ∀ j, rest[j]? = cvTasAll[i + 1 + j]? := by
      intro j
      have := hrest (j + 1)
      rwa [show i + (j + 1) = i + 1 + j from by omega] at this
    have hfreshC' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        (ConLeche.blockCapsAt p₁ j isRec).eta = true →
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env).find?
          (ConLeche.blockCapsAt p₁ j isRec).etaCtor = none := by
      intro j cvTb hj he
      rw [ConLeche.Env.find?_cons,
        if_neg (fun hh => hetaNe j i cvTb cvTa hj hi he (by
          show cvTa.name = (ConLeche.blockCapsAt p₁ j isRec).etaCtor
          exact hh))]
      exact hfreshC j cvTb hj he
    obtain ⟨mp', hE₂, hFD₂, hcons₂, hag₂⟩ :=
      stageBlockFormers hnames hndN hnresOf hpshapeOf htyWF hAbelowOf hAparamsOf hAokOf
        hAvalidOf hAmemOf hetaNe hTlawsOf rest (i + 1) _ mpI hrest' (by simp at hk; omega) hE'
        hres' hfreshOf' hfreshC' hFD' hcons'
    refine ⟨mp', hE₂, hFD₂, hcons₂, fun n hn => ?_⟩
    rw [hag₂ n (fun cvTb hcvTb => hn cvTb (List.mem_cons_of_mem _ hcvTb)), hacI]
    exact acvalWith_ne (hn cvTa List.mem_cons_self)

end ConLeche.Model
