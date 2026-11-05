module

import ConLeche.Model.OpenedCtx
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

* **`blockLeafWalks`** — member `mm`'s leaf `blockTyG … mm` has one
  hereditary premise (`ParamsOkG`), walked from the former's telescope
  down to the frame below the parameters and the member's index
  variables, where the block-wide base facts — the `k` index telescopes
  graded (`BlockIdxOk`) and the `k` X-chain families graded
  (`BlockChainsOkG`) — are the base.  The base facts
  are block-wide but the walk is member-local: the target enters
  nowhere.

* **`stageBlockFormers`** — the loop.  It is **abstract in the leaves**
  (`AOf : Nat → (Name → Nat) → Term`), exactly as `ctorsLoopEta`
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

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The block leaf's two hereditary premises -/

section Walks

variable {k nP nIdx : Nat} {resSort : Level}
  {uf : Nat → Nat} {Idss : Nat → List Term} {Chs : Nat → List (List Term)}

/-- **A member's parameter frame and index spine**, at a frame
satisfying its whole parameter-and-index telescope: the frame below the
index binders satisfies the parameters, and the index variables fit the
index telescope there. -/
theorem blockParamFrame_of_sat {pps : List Term} {Ids : List Term}
    (hIds : Ids = (pps.drop nP)) {ρ : Nat → V}
    (hρ : Sat V ((pps).reverse) ρ) :
    Sat V ((pps.take nP)).reverse (shiftE Ids.length 0 ρ) ∧
      SpineFit (shiftE Ids.length 0 ρ) Ids (frameIdx Ids.length ρ) := by
  rw [reverse_map_take_drop pps nP] at hρ
  -- the parameter frame (at the MEMBER's index count: `hIds` is what
  -- makes the block-wide facts land at the member's own frame)
  have hle : Ids.length ≤ (((pps.drop nP)).reverse).length := by
    rw [List.length_reverse, ← hIds]; exact Nat.le_refl _
  have hle2 : (((pps.drop nP)).reverse).length ≤ Ids.length := by
    rw [List.length_reverse, ← hIds]; exact Nat.le_refl _
  have hsh : shiftE Ids.length 0 ρ = fun j => ρ (j + Ids.length) := by
    rw [shiftE_zero]
  have hρp : Sat V ((pps.take nP)).reverse (fun j => ρ (j + Ids.length)) := by
    have := Sat_drop hρ Ids.length
    rwa [List.drop_append_of_le_length hle, List.drop_eq_nil_of_le hle2,
      List.nil_append] at this
  -- the index spine
  have hspI := spineFit_of_sat (Δ₀ := ((pps.take nP)).reverse)
    (Ds := (pps.drop nP)) hρ
  rw [← hIds, ← frameIdx_eq_reverse_map] at hspI
  rw [hsh]
  exact ⟨hρp, hspI⟩

/-- **The block leaf's hereditary premise**, from the former's data and
the block-wide base facts at the parameter frame. -/
theorem blockLeafWalks {pps : List Term} {w : Nat}
    (hlen : pps.length = nP + nIdx)
    (hokTy : ∀ ρ : Nat → V, WellDenoted V ρ (mkPisAV pps (.sort w)))
    {mm : Nat}
    (hIdsm : Idss mm = ((pps.drop nP)))
    (hIdx : ∀ ρp : Nat → V, Sat V ((pps.take nP)).reverse ρp →
      BlockIdxOk (V := V) k uf ρp Idss)
    (hX : ∀ ρp : Nat → V, Sat V ((pps.take nP)).reverse ρp →
      BlockChainsOkG k w ρp uf Idss Chs)
    (ρ : Nat → V) :
    ParamsOkG k w ρ uf Idss Chs mm pps := by
  have hst := stripPisAV_mkPisAV pps (.sort w)
  rw [hlen] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hokTy ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : ((pps).reverse).length = nP + nIdx := by simp [hlen]
  have hent : ∀ i, i < nP + nIdx → ∃ p, pps[i]? = some p ∧
      p = ((pps).reverse).getD (nP + nIdx - 1 - i) default := by
    intro i hi
    have hil : i < pps.length := by rw [hlen]; exact hi
    refine ⟨pps[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel hlen hi (List.getElem?_eq_getElem hil)]
  have hΓnil : ((pps).reverse).drop (nP + nIdx - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  -- the base facts at a frame satisfying the whole telescope
  have hbase : ∀ ρ : Nat → V, Sat V ((pps).reverse) ρ →
      BlockBaseG k w ρ uf Idss Chs mm := by
    intro ρ hρ
    obtain ⟨hρp, hspI⟩ := blockParamFrame_of_sat hIdsm hρ
    have hsh : shiftE (Idss mm).length 0 ρ = fun j => ρ (j + (Idss mm).length) := by
      rw [shiftE_zero]
    rw [hsh] at hρp hspI
    exact ⟨by rw [hsh]; exact hIdx _ hρp, by rw [hsh]; exact hX _ hρp, by rw [hsh]; exact hspI⟩
  have hw := hereditaryWalk (V := V)
    (Q := fun ρ ds => ParamsOkG k w ρ uf Idss Chs mm ds)
    hlenΓ hlen hent okΓ
    (fun ρ hρ => hbase ρ hρ)
    (fun ρ d ds _ hok hrec => ⟨hok.1, hok.2, hrec⟩)
    0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
  simpa using hw

end Walks

/-! ## The `k` members' parameter frames, identified -/

section Agree

/-- One member's parameter telescope, opened: the `Opened` frame at the
block's parameter count, with the context the former's data read
(`ctorFramesGen`'s opening of the former, at a TELESCOPE longer than the
opening — a member's type has its own indices after the parameters). -/
private theorem openedParams (mp : EnvModelM V env) {F : Nat}
    {cvT cvTa : ConstantVal} {nP nFull : Nat} {resSort : Level}
    {pps : (Name → Nat) → List Term}
    (hccv : cvTa = cvT ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps .verified F) env cvT = .ok ())
    (hFD : FormerData mp.base2 cvTa nFull resSort pps) (hle : nP ≤ nFull)
    {tfvs : List Expr} {trest : Expr}
    (hop : ConLeche.openPisAtFvars nP cvTa.type 0 = some (tfvs, trest))
    (ψ : Name → Nat) :
    ∃ R, Opened mp.base2 ψ nP cvTa.type tfvs trest
      ((((pps ψ).take nP)).reverse) R := by
  obtain ⟨rfl, hccv⟩ := hccv
  obtain ⟨-, -, -, hlbt, hitf, -, -, -, -⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨Γ, R, htele, hO⟩ := opened_of hop hitf hlbt (hFD.read ψ) (hFD.okTy ψ)
  obtain ⟨pps', hst', hΓ⟩ := stripPisAV_of_piTeleAV htele
  have hst'' := stripPisAV_mkPisAV_take nP (pps ψ) (Term.sort (resSort.eval ψ))
    (by rw [hFD.len ψ]; exact hle)
  obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
  exact ⟨R, by rw [hΓ]; exact hO⟩

/-- **The `k` members' PARAMETER telescopes are interchangeable at a
frame.**  This is official's `check_inductive_types` agreement —
`checkBlockAgree`, every member's parameter domains definitionally
member 0's — read semantically, and it is the one base fact the block
needs that a single family never did: `blockLeafWalks`'s `hIdx`/`hX`
are stated at a frame satisfying MEMBER `mm`'s parameter
telescope, while `Idss c` for `c ≠ mm` is read off member `c`'s own
type.  The producer is defeq soundness at the opened fvar frame
(`paramFrames` at `nF = 0`, between two `nP`-binder openings). -/
theorem blockParamsIff (mp : EnvModelM V env) {F : Nat}
    {p : ConLeche.BlockParts} {isRec : Bool} {envI : Env} {cvTas : List ConstantVal}
    {p₁ : ConLeche.BlockShape}
    (h : ConLeche.checkBlockInds (ConLeche.fueledOps .verified F) env p isRec
      = .ok (envI, cvTas, p₁))
    {nPOf : Nat → Nat} {resSort : Level}
    {ppsOf : Nat → (Name → Nat) → List Term}
    (hle : ∀ j, p.nP ≤ nPOf j)
    (hFD : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      FormerData mp.base2 cvTa (nPOf j) resSort (ppsOf j)) :
    ∀ m₁ m₂, m₁ < cvTas.length → m₂ < cvTas.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf m₁ ψ).take p.nP)).reverse ρ ↔
        Sat V (((ppsOf m₂ ψ).take p.nP)).reverse ρ := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, rfl, -, -, htele0, hteles, hagree⟩ :=
    ConLeche.checkBlockInds_shape h
  obtain ⟨cvT0, -, -, heq0, hccv0, -⟩ := ConLeche.checkBlockTele_shape htele0
  obtain ⟨hlencvs, hteleAt⟩ := ConLeche.checkBlockTeles_inv hteles
  -- every member's frame is member 0's
  have hkey : ∀ m, m < (cvTa0 :: cvs.map (·.1)).length →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf m ψ).take p.nP)).reverse ρ ↔
        Sat V (((ppsOf 0 ψ).take p.nP)).reverse ρ := by
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
      obtain ⟨cvTq, -, -, heqq, hccvq, -⟩ := ConLeche.checkBlockTele_shape hteleq
      -- the agreement's two openings and its per-binder pins
      obtain ⟨-, tfvs0, trest0, tfvs, trest, hop0, hopq, -, hdoms⟩ :=
        ConLeche.checkBlockAgree_inv hagree cvs[j] (List.getElem_mem hjlen)
      obtain ⟨R0, hO0⟩ := openedParams mp ⟨heq0, hccv0⟩ (hFD 0 cvTa0 (by simp)) (hle 0) hop0 ψ
      obtain ⟨Rq, hOq⟩ := openedParams mp ⟨heqq, hccvq⟩ (hFD (j + 1) _ hjc) (hle (j + 1)) hopq ψ
      have hpin : ∀ i, i < p.nP → ∃ a b, tfvs[i]? = some a ∧ tfvs0[i]? = some b ∧
          ConLeche.isDefEqCore .verified false env F i (Expr.fvarTypeD a) (Expr.fvarTypeD b) = .ok true :=
              by
        intro i hi
        obtain ⟨a, b, ha, hb, hdeq⟩ := ConLeche.checkBlockDomsAt_inv hdoms i hi
        rw [List.getElem?_map] at hb
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
        exact ⟨a, b', ha, hb', by rw [Nat.zero_add] at hdeq; exact hdeq⟩
      have hpf := paramFrames (nF := 0) (claimsAt_of (V := V) mp ψ F) hO0 hOq hpin
        p.nP (Nat.le_refl _)
      simpa using (hpf).1 ρ
  intro m₁ m₂ h₁ h₂ ψ ρ
  exact (hkey m₁ h₁ ψ ρ).trans (hkey m₂ h₂ ψ ρ).symm

end Agree

/-! ## The k formers' conses -/

/-- **A member's declared former against the telescope its check read**: the two name one
family, the declared type is closed and resolves, and the two read as one value. -/
structure FormerDeclared {env : Env} (m : EnvModel V env) (cvS cvTa : ConstantVal) : Prop where
  name : cvS.name = cvTa.name
  lps : cvS.levelParams = cvTa.levelParams
  fvar : cvS.type.hasFvar = false
  defined : cvS.type.allLevelParamsDefined cvS.levelParams = true
  bounded : cvS.type.looseBVarsBounded 0 = true
  resolve : cvS.type.constsResolve env = true
  read : ∀ ψ : Name → Nat, ∃ Ts Tr : Term, denote m.acval env ψ 0 cvS.type = some Ts ∧
    denote m.acval env ψ 0 cvTa.type = some Tr ∧
    ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr ∧ WellDenotedTy V ρ Ts

/-- A former that shows its telescope, against itself. -/
theorem FormerDeclared.refl {env : Env} {m : EnvModel V env} {cv : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List Term} (hFD : FormerData m cv nP resSort pps)
    (hf : cv.type.hasFvar = false) (hd : cv.type.allLevelParamsDefined cv.levelParams = true)
    (hb : cv.type.looseBVarsBounded 0 = true) (hr : cv.type.constsResolve env = true) :
    FormerDeclared m cv cv :=
  ⟨rfl, rfl, hf, hd, hb, hr, fun ψ => ⟨_, _, hFD.read ψ, hFD.read ψ, fun ρ =>
    ⟨rfl, hFD.okTy ψ ρ, IsTy_mkPisAV_sort _ _ _⟩⟩⟩

/-- A declared former's facts across a cons of a fresh constant. -/
theorem FormerDeclared.cross {env : Env} {m : EnvModel V env} {cvS cvTa : ConstantVal}
    (h : FormerDeclared m cvS cvTa) (hbR : ConstsBound env cvTa.type) {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    {A : (Name → Nat) → Term} (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerDeclared m₂ cvS cvTa := by
  refine ⟨h.name, h.lps, h.fvar, h.defined, h.bounded, Expr.constsResolve_mono h.resolve, fun ψ => ?_⟩
  obtain ⟨Ts, Tr, h₁, h₂, h₃⟩ := h.read ψ
  refine ⟨Ts, Tr, ?_, ?_, h₃⟩
  · rw [hac]; exact denote_cons_mono hfresh ψ 0 (constsBound_of_constsResolve _ h.resolve) h₁
  · rw [hac]; exact denote_cons_mono hfresh ψ 0 hbR h₂

/-- **The P step at one block member's former cons**: the leaf's five
currency facts and the capability laws, at the environment holding the
EARLIER members' formers: the former's `checkConstantVal` run is
replaced by the facts it yields (the run happened
at the PRE-block environment, not at this one) and the η closure taken
over the block's whole member list.  What is consed is the declared former. -/
theorem stageBlockFormer (mp : EnvModelM V env) {names : List Name}
    (hE : ConLeche.EtaFamiliesClosedExceptL env names)
    {cvS cvTa : ConstantVal} {caps : IndCaps} {A : (Name → Nat) → Term}
    {nP : Nat} {resSort : Level} {pps : (Name → Nat) → List Term}
    (hfresh : env.find? cvS.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvS.name = false)
    (hop : natOpName cvS.name = false)
    (hDS : FormerDeclared mp.base2 cvS cvTa)
    (hwfI : ConLeche.EnvWF ⟨.indInfo cvS caps :: env.consts, env.tables⟩)
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ))
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvS.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ))))
    (hTlaws : ∀ m₂ : EnvModel V ⟨.indInfo cvS caps :: env.consts, env.tables⟩,
      m₂.acval = acvalWith mp.base2.acval cvS.name A →
      CapsLawsAt m₂ cvS.name cvS caps) :
    ∃ mp' : EnvModelM V ⟨.indInfo cvS caps :: env.consts, env.tables⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvS.name A := by
  have hcb : ConstsBound env cvS.type := constsBound_of_constsResolve _ hDS.resolve
  have hreadS : ∀ ψ : Name → Nat, ∃ Ts : Term,
      denote (acvalWith mp.base2.acval cvS.name A)
        ⟨.indInfo cvS caps :: env.consts, env.tables⟩ ψ 0 cvS.type = some Ts ∧
      denote mp.base2.acval env ψ 0 cvS.type = some Ts := fun ψ => by
    obtain ⟨Ts, -, h₁, -, -⟩ := hDS.read ψ
    exact ⟨Ts, denote_cons_mono (c₀ := .indInfo cvS caps) hfresh ψ 0 hcb h₁, h₁⟩
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvS caps).name = false := hnres
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvS caps)
    (A := A) hfresh hnresI hop (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI hAbelow hnresI
      (fun _ _ _ _ _ h => nomatch h))
    hAparams hAok (fun ψ => (hreadS ψ).elim fun Ts h => ⟨Ts, h.1⟩) ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain ⟨Ts, h, h₀⟩ := hreadS ψ
    obtain rfl := Option.some.inj (h.symm.trans hta)
    obtain ⟨Ts', Tr, h₁, -, h₃⟩ := hDS.read ψ
    obtain rfl := Option.some.inj (h₀.symm.trans h₁)
    exact (h₃ ρ).2
  · intro ψ ta hta ρ
    obtain ⟨Ts, h, h₀⟩ := hreadS ψ
    obtain rfl := Option.some.inj (h.symm.trans hta)
    obtain ⟨Ts', Tr, h₁, h₂, h₃⟩ := hDS.read ψ
    obtain rfl := Option.some.inj (h₀.symm.trans h₁)
    obtain rfl := Option.some.inj (h₂.symm.trans (hFD.read ψ))
    rw [(h₃ ρ).1]
    exact hAmem ψ ρ
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvS caps)
      (A := A) (T := cvS.name) hfresh
      (Or.inl ⟨cvS, caps, rfl, rfl⟩) ?_ m₂ hac ?_
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
      have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvS caps) env
      obtain ⟨rfl, rfl⟩ :=
        ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
      exact hTlaws m₂ hac

/-- **The `k` type formers' conses, in order** (`checkBlockInds`'s
`consBlockInds`, of the declared formers `declAll`; `cvTasAll` the telescopes the check read).
Abstract in the leaves, as `ctorsLoopEta` is abstract
in `leafT`: the leaf's five currency facts (`hAbelowOf` … `hAmemOf`) and
the member's capability laws (`hTlawsOf`) are the per-member inputs, and
`blockLeafWalks` with the `blockTyG` capstones supplies them for the
fixpoint leaf.  The η invariant is threaded over the block's whole
member list, because all `k` formers are stored before any constructor. -/
theorem stageBlockFormers {p₁ : BlockShape} {isRec : Bool} {names : List Name}
    {declAll cvTasAll : List ConstantVal} {A : Nat → (Name → Nat) → Term}
    {nPOf : Nat → Nat} {resSort : Level}
    {ppsOf : Nat → (Name → Nat) → List Term}
    (hlenD : declAll.length = cvTasAll.length)
    (hnames : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.name ∈ names)
    (hndN : ∀ (j j' : Nat) (c c' : ConstantVal), cvTasAll[j]? = some c →
      cvTasAll[j']? = some c' → j ≠ j' → c.name ≠ c'.name)
    (hnresOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ConLeche.reservedBasisNames.contains cvTa.name = false)
    (hopOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      natOpName cvTa.name = false)
    (hAbelowOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A j ψ))
    (hAparamsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A j ψ₁ = A j ψ₂)
    (hAokOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A j ψ))
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
    (hTlawsOf : ∀ (j : Nat) (cvS cvTa : ConstantVal), declAll[j]? = some cvS →
      cvTasAll[j]? = some cvTa →
      ∀ {env' : Env} (m' : EnvModel V env'),
      FormerData m' cvTa (nPOf j) resSort (ppsOf j) →
      env'.find? cvTa.name = none → ConstsBound env' cvTa.type →
      (∀ (j' : Nat) (cvTb : ConstantVal), cvTasAll[j']? = some cvTb →
        (ConLeche.blockCapsAt p₁ j' isRec).eta = true →
        env'.find? (ConLeche.blockCapsAt p₁ j' isRec).etaCtor = none) →
      ∀ m₂ : EnvModel V ⟨.indInfo cvS (ConLeche.blockCapsAt p₁ j isRec) :: env'.consts, env'.tables⟩,
      m₂.acval = acvalWith m'.acval cvS.name (A j) →
      CapsLawsAt m₂ cvS.name cvS (ConLeche.blockCapsAt p₁ j isRec)) :
    ∀ (rest : List ConstantVal) (i : Nat) (env : Env) (mp : EnvModelM V env),
      (∀ j, rest[j]? = declAll[i + j]?) → i + rest.length = declAll.length →
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
      (∀ (j : Nat) (cvS cvTa : ConstantVal), declAll[j]? = some cvS → cvTasAll[j]? = some cvTa →
        FormerDeclared mp.base2 cvS cvTa) →
      (∀ (j : Nat) (cvS cvTa : ConstantVal), j < i → declAll[j]? = some cvS →
        cvTasAll[j]? = some cvTa →
        env.find? cvTa.name = some (.indInfo cvS (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mp.base2.acval cvTa.name ψ = A j ψ) →
      ∃ mp' : EnvModelM V (ConLeche.consBlockInds p₁ isRec rest i env),
        ConLeche.EtaFamiliesClosedExceptL (ConLeche.consBlockInds p₁ isRec rest i env) names ∧
        (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
          FormerData mp'.base2 cvTa (nPOf j) resSort (ppsOf j)) ∧
        (∀ (j : Nat) (cvS cvTa : ConstantVal), declAll[j]? = some cvS → cvTasAll[j]? = some cvTa →
          FormerDeclared mp'.base2 cvS cvTa) ∧
        (∀ (j : Nat) (cvS cvTa : ConstantVal), declAll[j]? = some cvS → cvTasAll[j]? = some cvTa →
          (ConLeche.consBlockInds p₁ isRec rest i env).find? cvTa.name
            = some (.indInfo cvS (ConLeche.blockCapsAt p₁ j isRec)) ∧
          ∀ ψ, mp'.base2.acval cvTa.name ψ = A j ψ) ∧
        -- OFF the members consed here the carrier reads as before
        (∀ n : Name, (∀ cvTb ∈ rest, n ≠ cvTb.name) →
          mp'.base2.acval n = mp.base2.acval n)
  | [], i, env, mp, _, hk, hE, _, _, _, hFD, hDS, hcons => by
    simp only [List.length_nil, Nat.add_zero] at hk
    refine ⟨mp, hE, hFD, hDS, ?_, fun _ _ => rfl⟩
    intro j cvS cvTa hjS hj
    exact hcons j cvS cvTa (by rw [hk]; exact (List.getElem?_eq_some_iff.mp hjS).1) hjS hj
  | cvS :: rest, i, env, mp, hrest, hk, hE, hres, hfreshOf, hfreshC, hFD, hDS, hcons => by
    have hiS : declAll[i]? = some cvS := by
      have := hrest 0; simpa using this.symm
    obtain ⟨cvTa, hi⟩ : ∃ cvTa, cvTasAll[i]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [← hlenD]; exact (List.getElem?_eq_some_iff.mp hiS).1)⟩
    have hD := hDS i cvS cvTa hiS hi
    have hfresh : env.find? cvS.name = none := by
      rw [hD.name]; exact hfreshOf i cvTa (Nat.le_refl _) hi
    have hcb : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (hres i cvTa hi)
    have hwfI : ConLeche.EnvWF
        ⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ :=
      ConLeche.envWF_cons_blockInd mp.base2.wf hD.fvar hD.defined hD.resolve hD.bounded
    obtain ⟨mpI, hacI⟩ := stageBlockFormer mp (names := names) hE hfresh
      (by rw [hD.name]; exact hnresOf i cvTa hi) (by rw [hD.name]; exact hopOf i cvTa hi) hD hwfI
      (hFD i cvTa hi)
      (hAbelowOf i cvTa hi) (fun ψ₁ ψ₂ h => hAparamsOf i cvTa hi ψ₁ ψ₂ (fun q hq => h q (by
        rw [hD.lps]; exact hq))) (hAokOf i cvTa hi)
      (hAmemOf i cvTa hi)
      (fun m₂ hac => hTlawsOf i cvS cvTa hiS hi mp.base2 (hFD i cvTa hi)
        (hfreshOf i cvTa (Nat.le_refl _) hi) hcb hfreshC m₂ hac)
    -- the invariants at the extension
    have hne : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb → j ≠ i →
        cvTb.name ≠ cvS.name := fun j cvTb hj hji => by
      rw [hD.name]; exact hndN j i cvTb cvTa hj hi hji
    have hE' : ConLeche.EtaFamiliesClosedExceptL
        (⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ : Env) names :=
      hE.cons hfresh (fun _ _ heq _ => by
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
        exact Or.inr (by show cvS.name ∈ names; rw [hD.name]; exact hnames i cvTa hi))
    have hres' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        cvTb.type.constsResolve
          (⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ : Env) = true :=
      fun j cvTb hj => Expr.constsResolve_mono (hres j cvTb hj)
    have hfreshOf' : ∀ (j : Nat) (cvTb : ConstantVal), i + 1 ≤ j → cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ : Env).find?
          cvTb.name = none := by
      intro j cvTb hij hj
      rw [ConLeche.Env.find?_cons,
        ite_eq_right (fun hh => hne j cvTb hj (by omega) hh.symm)]
      exact hfreshOf j cvTb (by omega) hj
    have hFD' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        FormerData mpI.base2 cvTb (nPOf j) resSort (ppsOf j) := by
      intro j cvTb hj
      exact (hFD j cvTb hj).cross (c₀ := .indInfo cvS (ConLeche.blockCapsAt p₁ i isRec))
        hfresh (constsBound_of_constsResolve _ (hres j cvTb hj)) mpI.base2 hacI
    have hDS' : ∀ (j : Nat) (cvS' cvTb : ConstantVal), declAll[j]? = some cvS' →
        cvTasAll[j]? = some cvTb → FormerDeclared mpI.base2 cvS' cvTb := fun j cvS' cvTb hjS hj =>
      (hDS j cvS' cvTb hjS hj).cross (constsBound_of_constsResolve _ (hres j cvTb hj))
        (c₀ := .indInfo cvS (ConLeche.blockCapsAt p₁ i isRec)) hfresh mpI.base2 hacI
    have hcons' : ∀ (j : Nat) (cvS' cvTb : ConstantVal), j < i + 1 → declAll[j]? = some cvS' →
        cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ : Env).find? cvTb.name
          = some (.indInfo cvS' (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mpI.base2.acval cvTb.name ψ = A j ψ := by
      intro j cvS' cvTb hji hjS hj
      rcases Nat.lt_or_ge j i with hlt | hge
      · obtain ⟨hfj, hleafj⟩ := hcons j cvS' cvTb hlt hjS hj
        refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfj, fun ψ => ?_⟩
        rw [hacI]
        show acvalWith mp.base2.acval cvS.name (A i) cvTb.name ψ = _
        rw [acvalWith_ne (hne j cvTb hj (by omega))]
        exact hleafj ψ
      · have hij : j = i := by omega
        subst hij
        obtain rfl := Option.some.inj (hi.symm.trans hj)
        obtain rfl := Option.some.inj (hiS.symm.trans hjS)
        rw [← hD.name]
        refine ⟨ConLeche.Env.find?_cons_self _ env, fun ψ => ?_⟩
        rw [hacI]
        exact congrFun acvalWith_self ψ
    have hrest' : ∀ j, rest[j]? = declAll[i + 1 + j]? := by
      intro j
      have := hrest (j + 1)
      rwa [show i + (j + 1) = i + 1 + j from by omega] at this
    have hfreshC' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        (ConLeche.blockCapsAt p₁ j isRec).eta = true →
        (⟨.indInfo cvS (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩ : Env).find?
          (ConLeche.blockCapsAt p₁ j isRec).etaCtor = none := by
      intro j cvTb hj he
      rw [ConLeche.Env.find?_cons,
        ite_eq_right (fun hh => hetaNe j i cvTb cvTa hj hi he (by
          show cvTa.name = (ConLeche.blockCapsAt p₁ j isRec).etaCtor
          rw [← hD.name]; exact hh))]
      exact hfreshC j cvTb hj he
    obtain ⟨mp', hE₂, hFD₂, hDS₂, hcons₂, hag₂⟩ :=
      stageBlockFormers hlenD hnames hndN hnresOf hopOf hAbelowOf hAparamsOf hAokOf
        hAmemOf hetaNe hTlawsOf rest (i + 1) _ mpI hrest' (by simp at hk; omega) hE'
        hres' hfreshOf' hfreshC' hFD' hDS' hcons'
    refine ⟨mp', hE₂, hFD₂, hDS₂, hcons₂, fun n hn => ?_⟩
    rw [hag₂ n (fun cvTb hcvTb => hn cvTb (List.mem_cons_of_mem _ hcvTb)), hacI]
    exact acvalWith_ne (hn cvS List.mem_cons_self)

end ConLeche.Model
