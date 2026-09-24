module

public import ConLeche.Model.Annot.LfpHoleWitness
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.FixWitness
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Semantics.Tower.FixFamI

public section

/-!
# The fields with holes are FLAT at the install (lane HOLE2, stage D)

The producer of `LfpDatum.FlatAt` (`Model/Annot/LfpHoleWitness.lean`) at
a uniform block's datum: the constructors' fields with holes
(`BlockData.absF`) present themselves — a field reading a member is the
Π-tower of its telescope, lifted over the holes, over the member's hole
applied to the parameters and its index readings; every other field is
its stored reading lifted over the holes — and

* **U4** (no later field reads a recursive field) is the install's
  `NoBVar` facts on the stored readings, lifted over the holes;
* **a recursive call's indices fit** its member's index telescope,
  read off the GRADING of the hole application at the hole frame of
  every tuple (`spineFit_of_wellDenoted_holeFam`: an application graded
  against a λ-tower of graphs fits its domains) — no slot fit;
* **the fields are sets of the level** by the same grading.

So `closed_of_flat` gives the hole operator its closed tuple at every
`Type`-valued parameter frame (`blockHoleClosed_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory.Tower (projS mkTower)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Variables a lifted term does not read -/

omit [SetTheory V] in
theorem noBVar_bot : ∀ e : AnnotTerm, NoBVar (fun _ => False) e := by
  intro e
  induction e with
  | bvar i => exact id
  | sort u => trivial
  | const c us => trivial
  | prf => trivial
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | eqE a b iha ihb => exact ⟨iha, ihb⟩
  | fst e ihe => exact ihe
  | snd e ihe => exact ihe
  | lam v A b ihA ihb => exact ⟨ihA, NoBVar.mono (fun i hi => by cases i <;> exact hi) ihb⟩
  | pi u v A B ihA ihB => exact ⟨ihA, NoBVar.mono (fun i hi => by cases i <;> exact hi) ihB⟩

omit [SetTheory V] in
/-- **A lifted term reads a variable only through the unlifted one.** -/
theorem noBVar_liftN_of :
    ∀ (e : AnnotTerm) {P : Nat → Prop} {n c : Nat},
      NoBVar (fun i => if i < c then P i else P (i + n)) e → NoBVar P (e.liftN n c) := by
  intro e
  induction e with
  | bvar i =>
    intro P n c h
    show ¬ P (if i < c then i else i + n)
    by_cases hi : i < c
    · rw [if_pos hi]; have := h; simp only [NoBVar, if_pos hi] at this; exact this
    · rw [if_neg hi]; have := h; simp only [NoBVar, if_neg hi] at this; exact this
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P n c h; exact ⟨ihf h.1, iha h.2⟩
  | eqE a b iha ihb => intro P n c h; exact ⟨iha h.1, ihb h.2⟩
  | fst e ihe => intro P n c h; exact ihe h
  | snd e ihe => intro P n c h; exact ihe h
  | lam v A b ihA ihb =>
    intro P n c h
    refine ⟨ihA h.1, ihb (NoBVar.mono (fun i hi => ?_) h.2)⟩
    cases i with
    | zero => simp [shiftP] at hi
    | succ i =>
      show (if i < c then P i else P (i + n))
      by_cases hic : i < c
      · rw [if_pos hic]; simpa [shiftP, show i + 1 < c + 1 from by omega] using hi
      · rw [if_neg hic]
        have : ¬ i + 1 < c + 1 := by omega
        simp only [this, if_false, shiftP] at hi
        rwa [show i + 1 + n = (i + n) + 1 from by omega] at hi
  | pi u v A B ihA ihB =>
    intro P n c h
    refine ⟨ihA h.1, ihB (NoBVar.mono (fun i hi => ?_) h.2)⟩
    cases i with
    | zero => simp [shiftP] at hi
    | succ i =>
      show (if i < c then P i else P (i + n))
      by_cases hic : i < c
      · rw [if_pos hic]; simpa [shiftP, show i + 1 < c + 1 from by omega] using hi
      · rw [if_neg hic]
        have : ¬ i + 1 < c + 1 := by omega
        simp only [this, if_false, shiftP] at hi
        rwa [show i + 1 + n = (i + n) + 1 from by omega] at hi

omit [SetTheory V] in
/-- The inserted variables are read by no lifted term. -/
theorem noBVar_liftN_range (e : AnnotTerm) (n c : Nat) :
    NoBVar (fun i => c ≤ i ∧ i < c + n) (e.liftN n c) :=
  noBVar_liftN_of e (NoBVar.mono (fun i hi => by
    by_cases hic : i < c
    · rw [if_pos hic] at hi; omega
    · rw [if_neg hic] at hi; omega) (noBVar_bot e))

omit [SetTheory V] in
/-- A variable below the cut is read by the lifted term only if by the
term. -/
theorem noBVar_liftN_below {e : AnnotTerm} {P : Nat → Prop} {n c : Nat}
    (hP : ∀ i, P i → i < c) (h : NoBVar P e) : NoBVar P (e.liftN n c) :=
  noBVar_liftN_of e (NoBVar.mono (fun i hi => by
    by_cases hic : i < c
    · rw [if_pos hic] at hi; exact hi
    · rw [if_neg hic] at hi; exact absurd (hP _ hi) (by omega)) h)

/-- The variables `P` seen `n` binders deeper. -/
@[expose] def shiftPN (n : Nat) (P : Nat → Prop) : Nat → Prop := fun i => n ≤ i ∧ P (i - n)

omit [SetTheory V] in
/-- **A Π-tower reads no variable of `P`** when its domains and body
read none, each at its depth. -/
theorem noBVar_mkPisAV_of :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm} {P : Nat → Prop},
      (∀ q dd, tl[q]? = some dd → NoBVar (shiftPN q P) dd.2.2) →
      NoBVar (shiftPN tl.length P) B → NoBVar P (mkPisAV tl B)
  | [], B, P, _, hB => NoBVar.mono (fun i hi => ⟨Nat.zero_le _, by simpa using hi⟩) hB
  | dd :: tl, B, P, hT, hB => by
    refine ⟨NoBVar.mono (fun i hi => ⟨Nat.zero_le _, by simpa using hi⟩) (hT 0 dd rfl), ?_⟩
    refine noBVar_mkPisAV_of (fun q dd' hq => NoBVar.mono (fun i hi => ?_) (hT (q + 1) dd' hq))
      (NoBVar.mono (fun i hi => ?_) hB)
    · obtain ⟨hqi, hP⟩ := hi
      cases hk : i - q with
      | zero => rw [hk] at hP; exact hP.elim
      | succ k =>
        rw [hk] at hP
        exact ⟨by omega, by rw [show i - (q + 1) = k by omega]; exact hP⟩
    · obtain ⟨hqi, hP⟩ := hi
      cases hk : i - tl.length with
      | zero => rw [hk] at hP; exact hP.elim
      | succ k =>
        rw [hk] at hP
        refine ⟨by simp; omega, ?_⟩
        simp only [List.length_cons]
        rw [show i - (tl.length + 1) = k by omega]
        exact hP

omit [SetTheory V] in
theorem noBVar_mkAppN_of {P : Nat → Prop} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm},
      NoBVar P f → (∀ a ∈ args, NoBVar P a) → NoBVar P (AnnotTerm.mkAppN f args)
  | [], _, hf, _ => hf
  | a :: args, f, hf, ha => by
    rw [AnnotTerm.mkAppN_cons]
    exact noBVar_mkAppN_of ⟨hf, ha a List.mem_cons_self⟩ fun b hb => ha b (List.mem_cons_of_mem _ hb)

/-! ## A graded application against a λ-tower of graphs fits its domains -/

/-- **A spine graded against a λ-tower of graphs (`holeFam`) fits its
domains** — `spineFit_of_wellDenoted_lams` for the hole values. -/
theorem spineFit_of_wellDenoted_holeFam :
    ∀ {args Ts : List AnnotTerm} {σ ρ : Nat → V} {f : AnnotTerm} {g : List V → V},
      args.length ≤ Ts.length →
      WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = holeFam σ Ts g →
      SpineFit σ (Ts.take args.length) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, hlen, _, _ => by simp at hlen
  | a :: args, T :: Ts, σ, ρ, f, g, hlen, hok, hf => by
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hf' : interp V ρ f
        = lamR 1 (interp V σ T) fun x => holeFam (cons x σ) Ts fun as => g (x :: as) := hf
    rw [hf'] at hfm
    have hA : A = interp V σ T := lamR_mem_piR_dom (by decide) hfm
    rw [hA] at ham
    have happ : interp V ρ (.app f a)
        = holeFam (cons (interp V ρ a) σ) Ts fun as => g (interp V ρ a :: as) := by
      rw [interp_app, hf', app_lamR_pos (by decide) ham]
    have ih := spineFit_of_wellDenoted_holeFam (args := args) (Ts := Ts)
      (σ := cons (interp V ρ a) σ) (ρ := ρ) (f := .app f a) (by simpa using hlen) hok happ
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    exact ⟨ham, ih⟩

/-! ## Small readings -/

omit [SetTheory V] in
theorem paramBvarsAt_eq_holeParams (k nP lo : Nat) :
    paramBvarsAt nP (nP + k + lo) = holeParams k nP lo := by
  unfold paramBvarsAt holeParams
  refine List.map_congr_left fun p _ => ?_
  congr 1; omega

omit [SetTheory V] in
theorem holeParamVals_consList_add (k nP : Nat) :
    ∀ (L : List V) (lo : Nat) (σ : Nat → V),
      holeParamVals k nP (lo + L.length) (consList L σ) = holeParamVals k nP lo σ
  | [], lo, σ => by simp
  | a :: L, lo, σ => by
    rw [consList_cons, List.length_cons, show lo + (L.length + 1) = (lo + 1) + L.length by omega,
      holeParamVals_consList_add k nP L (lo + 1) (cons a σ), holeParamVals_cons]

/-- The per-position bound of `FieldsOkB`. -/
theorem FieldsOkB.bound_at {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      ∀ i, i < Fs.length → ∀ as : List V, SpineFit ρ (Fs.take i) as →
        interp V (consList as ρ) (Fs.getD i default) ∈ˢ (univ w : V)
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | F :: Fs, ρ, h, 0, _, [], _ => h.2.1 hw
  | _ :: _, _, _, 0, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, _ + 1, _, [], hsp => hsp.elim
  | F :: Fs, ρ, h, i + 1, hi, a :: as, hsp => by
    simp only [consList_cons, List.getD_cons_succ]
    exact FieldsOkB.bound_at hw (h.2.2 a hsp.1) i (by simpa using hi) as hsp.2

omit [SetTheory V] in
theorem liftTeleK_getElem?_eq (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (q : Nat),
      (BlockData.liftTeleK n i tl)[q]? = (tl[q]?).map fun dd => (dd.1, dd.2.1, dd.2.2.liftN n (i + q))
  | _, [], _ => rfl
  | i, d0 :: tl, 0 => by simp [BlockData.liftTeleK]
  | i, d0 :: tl, q + 1 => by
    simp only [BlockData.liftTeleK, List.getElem?_cons_succ]
    rw [liftTeleK_getElem?_eq n (i + 1) tl q, show i + 1 + q = i + (q + 1) by omega]

omit [SetTheory V] in
theorem noBVar_holeParams {P : Nat → Prop} {k nP lo : Nat}
    (hP : ∀ i, P i → i < lo + k) : ∀ a ∈ holeParams k nP lo, NoBVar P a := by
  intro a ha
  unfold holeParams at ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hp
  exact fun hPi => absurd (hP _ hPi) (by omega)

/-! ## The producer -/

section Producer

variable {env : Env} {mo : EnvModel V env} {d : BlockData V} {lps : List Name}

set_option maxHeartbeats 1600000 in
/-- **A uniform block's constructor presents its fields with holes flat**
(see the module docstring) at a `Type`-valued parameter frame: from the
constructors' reading facts, the U4 `NoBVar` facts of the stored
readings (`hnb`, `hnbT`, `hnbE`: a recursive field's variable is read by
no later field, telescope domain or index reading — the kernel's
guard), and the grading of the fields with holes at the hole frame of
every tuple (`hG`, U2). -/
theorem blockFlatAt_of (hH : BlockHoleFacts mo d lps) {ψ : Name → Nat} {ρp : Nat → V}
    (hw : d.w ψ ≠ 0)
    (hlenIds : ∀ m, m < d.k → (d.IdsM m ψ).length = d.nIdxAt m)
    {c : Nat} (hc : c < d.N) {j : Nat} (hj : j < (d.ctorsM c).length)
    (hG : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j))
    (hnb : ∀ i, i < ((d.Fss c ψ).getD j []).length →
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i) (d.nP + i))
        (((d.Fss c ψ).getD j []).getD i default))
    (hnbT : ∀ i, i < ((d.Fss c ψ).getD j []).length → recAt d.nP (d.ksF c j) (d.nP + i) →
      ∀ q dd, (((d.tlss c ψ).getD j []).getD i [])[q]? = some dd →
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i) (d.nP + i + q)) dd.2.2)
    (hnbE : ∀ i, i < ((d.Fss c ψ).getD j []).length → recAt d.nP (d.ksF c j) (d.nP + i) →
      ∀ E ∈ ((d.Eiss c ψ).getD j []).getD i [],
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i)
        (d.nP + i + (((d.tlss c ψ).getD j []).getD i []).length)) E) :
    ∃ fas rec, d.toLfp.FlatAt ψ ρp c j fas rec := by
  classical
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  have hD : BlockCtorRead mo d lps c j (d.ctorsM c)[j] := hH.facts c hc j _ hcj
  have hD' := hD
  unfold BlockCtorRead at hD'
  have hnF : ((d.Fss c ψ).getD j []).length = ((d.ctorsM c)[j]).2 := hD.nF hcj ψ
  have hksLen : (d.ksF c j).length = ((d.Fss c ψ).getD j []).length := by
    rw [hnF]; exact hD'.ksLen
  have hrs : (d.rss c).getD j [] = rsOf (d.ksF c j) := rssOfK_getD hj
  have hTlD : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hEiD : (d.Eiss c ψ).getD j [] = d.eissF c j ψ := eissOfR_fixCtorDataList_getD hcj
  -- the recursive flags, their range, and the kinds
  have hrsLt : ∀ l, ((d.rss c).getD j []).getD l false = true →
      l < ((d.Fss c ψ).getD j []).length := by
    intro l hl
    refine Nat.lt_of_not_le fun hge => ?_
    rw [hrs, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [rsOf]; omega)] at hl
    exact Bool.false_ne_true hl
  have hrecAt : ∀ l, ((d.rss c).getD j []).getD l false = true →
      recAt d.nP (d.ksF c j) (d.nP + l) := fun l hl =>
    (recAt_iff_rsOf (by rw [hksLen]; exact hrsLt l hl)).mpr (by rw [← hrs]; exact hl)
  -- the fields with holes, by position
  have habsGet : ∀ l, l < ((d.Fss c ψ).getD j []).length →
      (d.absF ψ c j).getD l default = d.absField ψ c j l := by
    intro l hl
    unfold BlockData.absF
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
    rfl
  have hlenA : (d.absF ψ c j).length = ((d.Fss c ψ).getD j []).length := by
    simp [BlockData.absF]
  let tlOf : Nat → List (Nat × Nat × AnnotTerm) := fun l => ((d.tlss c ψ).getD j []).getD l []
  let rec_ : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm) := fun l =>
    if ((d.rss c).getD j []).getD l false = true then
      some (BlockData.liftTeleK d.k l (tlOf l), d.tgts c j l,
        (((d.Eiss c ψ).getD j []).getD l []).map (·.liftN d.k (l + (tlOf l).length)))
    else none
  have hrecSome : ∀ l tl m es, rec_ l = some (tl, m, es) →
      ((d.rss c).getD j []).getD l false = true ∧ tl = BlockData.liftTeleK d.k l (tlOf l) ∧
        m = d.tgts c j l ∧
        es = (((d.Eiss c ψ).getD j []).getD l []).map (·.liftN d.k (l + (tlOf l).length)) := by
    intro l tl m es h
    simp only [rec_] at h
    split at h
    · rename_i hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hr, rfl, rfl, rfl⟩
    · exact nomatch h
  have hlenP : (d.params ψ).length = d.nP := hH.lenP ψ
  -- a field reading a member, spelled out
  have habsRec : ∀ l, ((d.rss c).getD j []).getD l false = true →
      d.absField ψ c j l
        = mkPisAV (BlockData.liftTeleK d.k l (tlOf l))
            (AnnotTerm.mkAppN
              (.bvar (l + (BlockData.liftTeleK d.k l (tlOf l)).length + (d.k - 1 - d.tgts c j l)))
              (holeParams d.k (d.params ψ).length (l + (BlockData.liftTeleK d.k l (tlOf l)).length)
                ++ (((d.Eiss c ψ).getD j []).getD l []).map
                  (·.liftN d.k (l + (tlOf l).length)))) := by
    intro l hl
    unfold BlockData.absField
    rw [if_pos hl, liftTeleK_length', hlenP,
      show d.nP + d.k + l + (tlOf l).length = d.nP + d.k + (l + (tlOf l).length) by omega,
      paramBvarsAt_eq_holeParams]
  have habsOrd : ∀ l, ¬ ((d.rss c).getD j []).getD l false = true →
      d.absField ψ c j l = (((d.Fss c ψ).getD j []).getD l default).liftN d.k l := by
    intro l hl
    unfold BlockData.absField
    rw [if_neg hl]
  -- the U4 slot, as an excluded slot of the stored readings
  have hexcl : ∀ l l' e, l < l' → ((d.rss c).getD j []).getD l false = true → ∀ i,
      i = l' - 1 - l + e →
      exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + l') (d.nP + l' + e) i := by
    intro l l' e hll hr i hi
    exact ⟨d.nP + l, ⟨hrecAt l hr, by omega⟩, by omega, by omega⟩
  have hrecNone : ∀ l, rec_ l = none → ¬ ((d.rss c).getD j []).getD l false = true := by
    intro l h hr
    simp only [rec_, if_pos hr] at h
    exact nomatch h
  have hrecNe : ∀ l, rec_ l ≠ none → ((d.rss c).getD j []).getD l false = true := by
    intro l h
    cases hb : ((d.rss c).getD j []).getD l false
    · exact absurd (by simp only [rec_, hb]; rfl) h
    · rfl
  refine ⟨d.absF ψ c j, rec_, rfl, fun _ _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- the recursive shape
    intro l tl m es h
    obtain ⟨hr, rfl, rfl, rfl⟩ := hrecSome l tl m es h
    have hl := hrsLt l hr
    have hlC : l < ((d.ctorsM c)[j]).2 := by rw [← hnF]; exact hl
    refine ⟨by rw [BlockData.toLfp]; simpa [BlockData.absF] using hl,
      hH.tgt c hc j _ hcj l hlC, ?_, fun q dd hq => ?_, fun e he => ?_⟩
    · show (d.absF ψ c j).getD l default = _
      rw [habsGet l hl, habsRec l hr, liftTeleK_length']
      rfl
    · rw [liftTeleK_getElem?_eq] at hq
      obtain ⟨dd', hdd', rfl⟩ := Option.map_eq_some_iff.mp hq
      refine ⟨fun h0 => hw ((hD'.tssBits ψ l dd' (by
        rw [← hTlD]; exact List.mem_of_getElem? hdd')).mp h0), ?_⟩
      exact noBVar_liftN_range _ d.k (l + q)
    · obtain ⟨E, -, rfl⟩ := List.mem_map.mp he
      rw [liftTeleK_length']
      exact noBVar_liftN_range E d.k (l + (tlOf l).length)
  · -- an ordinary field: hole-free
    intro l hl hnone
    have hr := hrecNone l hnone
    have hl' : l < ((d.Fss c ψ).getD j []).length := by rwa [← hlenA]
    show NoBVar _ ((d.absF ψ c j).getD l default)
    rw [habsGet l hl', habsOrd l hr]
    exact noBVar_liftN_range _ d.k l
  · -- U4
    intro l hl hrec l' hll' hl'
    have hr := hrecNe l hrec
    have hl'' : l' < ((d.Fss c ψ).getD j []).length := by rwa [← hlenA]
    show NoBVar _ ((d.absF ψ c j).getD l' default)
    rw [habsGet l' hl'']
    by_cases hr' : ((d.rss c).getD j []).getD l' false = true
    · rw [habsRec l' hr']
      have hrA := hrecAt l' hr'
      refine noBVar_mkPisAV_of (fun q dd hq => ?_) ?_
      · rw [liftTeleK_getElem?_eq] at hq
        obtain ⟨dd', hdd', rfl⟩ := Option.map_eq_some_iff.mp hq
        refine noBVar_liftN_below (fun i hi => by
          obtain ⟨h1, h2⟩ := hi; simp only [LfpDatum.fieldSlot] at h2; omega) ?_
        exact NoBVar.mono (fun i hi => hexcl l l' q hll' hr i (by
          obtain ⟨h1, h2⟩ := hi; simp only [LfpDatum.fieldSlot] at h2; omega))
          (hnbT l' hl'' hrA q dd' hdd')
      · refine noBVar_mkAppN_of ?_ fun a ha => ?_
        · show ¬ _
          rintro ⟨h1, h2⟩
          simp only [LfpDatum.fieldSlot, liftTeleK_length'] at h1 h2
          omega
        · rcases List.mem_append.mp ha with ha | ha
          · refine noBVar_holeParams (fun i hi => ?_) a ha
            obtain ⟨h1, h2⟩ := hi
            simp only [LfpDatum.fieldSlot, liftTeleK_length'] at h1 h2 ⊢
            omega
          · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
            refine noBVar_liftN_below (fun i hi => by
              obtain ⟨h1, h2⟩ := hi
              simp only [LfpDatum.fieldSlot, liftTeleK_length'] at h1 h2; omega) ?_
            exact NoBVar.mono (fun i hi => hexcl l l' (tlOf l').length hll' hr i (by
              obtain ⟨h1, h2⟩ := hi
              simp only [LfpDatum.fieldSlot, liftTeleK_length'] at h1 h2; omega))
              (hnbE l' hl'' hrA E hE)
    · rw [habsOrd l' hr']
      refine noBVar_liftN_below (fun i hi => by
        simp only [LfpDatum.fieldSlot] at hi; omega) ?_
      exact NoBVar.mono (fun i hi => hexcl l l' 0 hll' hr i (by
        simp only [LfpDatum.fieldSlot] at hi; omega)) (hnb l' hl'')
  · -- a recursive call's indices fit its member's index telescope: the
    -- hole application is graded at the hole frame of every tuple
    intro X hX l tl m es h as has bs hbs
    obtain ⟨hr, rfl, rfl, rfl⟩ := hrecSome l tl m es h
    have hl := hrsLt l hr
    have hlC : l < ((d.ctorsM c)[j]).2 := by rw [← hnF]; exact hl
    have hmk : d.tgts c j l < d.k := hH.tgt c hc j _ hcj l hlC
    have hwd := FieldsOkB.wellDenoted_at (hG X hX) l (by rw [hlenA]; exact hl) as has
    rw [habsGet l hl, habsRec l hr] at hwd
    have hbody := (WellDenoted_mkPisAV_inv hwd).2 bs hbs
    have hasLen : as.length = l := by
      rw [has.length_eq, List.length_take]
      show min l (d.absF ψ c j).length = l
      rw [hlenA]; omega
    have hbsLen : bs.length = (tlOf l).length := by
      rw [hbs.length_eq, List.length_map, liftTeleK_length']
    rw [← consList_append] at hbody
    have hfr : d.toLfp.frame ψ ρp X = consList (d.holeList ψ ρp X) ρp := rfl
    rw [hfr] at hbody ⊢
    have hH' : interp V (consList (as ++ bs) (consList (d.holeList ψ ρp X) ρp))
        (.bvar (l + (BlockData.liftTeleK d.k l (tlOf l)).length + (d.k - 1 - d.tgts c j l)))
        = d.toLfp.holeVal ψ ρp X (d.tgts c j l) := by
      rw [liftTeleK_length', show l + (tlOf l).length = (as ++ bs).length by
        rw [List.length_append, hasLen, hbsLen]]
      exact BlockData.interp_hole_bvar hmk (as ++ bs)
    -- the index readings' count: the target's index count
    have hkind := (rsOf_getD_iff (by rw [hksLen]; exact hl)).mp (by rw [← hrs]; exact hr)
    have hEsLen : (((d.Eiss c ψ).getD j []).getD l []).length = d.nIdxAt (d.tgts c j l) := by
      rw [hEiD]
      rcases hkind with hk | hk
      · exact hD'.eisLen ψ l hk hlC
      · exact hD'.eisLenRefl ψ l hk hlC
    have hparsLen : (d.toLfp.pars (d.tgts c j l) ψ).length = d.nP := hH.parsLen ψ _ hmk
    have hidsLen : (d.toLfp.ids (d.tgts c j l) ψ).length = d.nIdxAt (d.tgts c j l) :=
      hlenIds _ hmk
    have hlenArgs : (holeParams d.k (d.params ψ).length
          (l + (BlockData.liftTeleK d.k l (tlOf l)).length) ++
        (((d.Eiss c ψ).getD j []).getD l []).map (·.liftN d.k (l + (tlOf l).length))).length
        = (d.toLfp.pars (d.tgts c j l) ψ ++ d.toLfp.ids (d.tgts c j l) ψ).length := by
      simp only [List.length_append, List.length_map, holeParams, List.length_range]
      rw [hlenP, hEsLen, hparsLen, hidsLen]
    have hfit := spineFit_of_wellDenoted_holeFam (Nat.le_of_eq hlenArgs) hbody hH'
    rw [hlenArgs, List.take_of_length_le (Nat.le_refl _), List.map_append] at hfit
    obtain ⟨v₁, v₂, heq, h₁, h₂⟩ := spineFit_append_inv hfit
    have hl₁ : v₁.length = ((holeParams d.k (d.params ψ).length
        (l + (BlockData.liftTeleK d.k l (tlOf l)).length)).map
          (interp V (consList (as ++ bs) (consList (d.holeList ψ ρp X) ρp)))).length := by
      rw [h₁.length_eq, hparsLen]; simp [holeParams, hlenP]
    obtain ⟨hv₁, rfl⟩ := List.append_inj heq.symm hl₁
    rw [map_interp_holeParams, hlenP, liftTeleK_length',
      show l + (tlOf l).length = 0 + (as ++ bs).length by
        rw [List.length_append, hasLen, hbsLen]; omega,
      holeParamVals_consList_add, holeParamVals_consList _ _ _ BlockData.holeList_length] at hv₁
    rw [hv₁, hparsLen, consList_frameIdx] at h₂
    exact h₂
  · -- the fields are sets of the level
    intro X hX l hl as has
    exact FieldsOkB.bound_at hw (hG X hX) l hl as has

/-- **The hole operator has a closed tuple** at a `Type`-valued parameter
frame (stage D: (W) from the flat presentation, `closed_of_flat`). -/
theorem blockHoleClosed_of (hH : BlockHoleFacts mo d lps) {ψ : Name → Nat} {ρp : Nat → V}
    (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hIdx : ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ))
    (hlenIds : ∀ m, m < d.k → (d.IdsM m ψ).length = d.nIdxAt m)
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j))
    (hnb : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ i, i < ((d.Fss c ψ).getD j []).length →
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i) (d.nP + i))
        (((d.Fss c ψ).getD j []).getD i default))
    (hnbT : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ i, i < ((d.Fss c ψ).getD j []).length → recAt d.nP (d.ksF c j) (d.nP + i) →
      ∀ q dd, (((d.tlss c ψ).getD j []).getD i [])[q]? = some dd →
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i) (d.nP + i + q)) dd.2.2)
    (hnbE : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ i, i < ((d.Fss c ψ).getD j []).length → recAt d.nP (d.ksF c j) (d.nP + i) →
      ∀ E ∈ ((d.Eiss c ψ).getD j []).getD i [],
      NoBVar (exclP (fun q => recAt d.nP (d.ksF c j) q ∧ q < d.nP + i)
        (d.nP + i + (((d.tlss c ψ).getD j []).getD i []).length)) E) :
    ∃ L, IsClosedTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) (d.toLfp.holeOp ψ ρp) L := by
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hok : d.toLfp.HoleTmOk ψ ρp := fun m hm =>
    ⟨⟨(hH.parsLen ψ m hm).trans (hH.lenP ψ).symm, hH.parsSat ψ m hm ρp hs⟩,
      fun _ => (hIdx m (Nat.lt_of_lt_of_le hm hkN)).2⟩
  refine LfpDatum.closed_of_flat hw hkN hok _ (fun X _ c hc t ht x hx => ?_)
    (fun c hc j hj => blockFlatAt_of hH hw hlenIds hc hj (hG c hc j hj) (hnb c hc j hj)
      (hnbT c hc j hj) (hnbE c hc j hj))
  have happ : ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun j hj => blockHolesApplied hH ψ hc hj
  have hres : ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  obtain ⟨j, fs, hf, rfl⟩ := (LfpDatum.holeOp_fibre hok hkN X happ hres ht x).mp hx
  exact ⟨j, fs, hf, if_neg hw⟩

end Producer

end ConLeche.Model
