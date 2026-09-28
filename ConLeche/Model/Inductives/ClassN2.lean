module

public import ConLeche.Model.Inductives.HoleKit
import ConLeche.Semantics.Inductives.HoleMono
import ConLeche.Model.Annot.EnvModelM
import ConLeche.Semantics.SubstAV
public import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.InstTypeInv
import ConLeche.Verify.Inductives.ScopeKit

public section

/-!
# N2 read semantically: a container instance's index telescope is hole-free

(Re-homed from the delete-listed `ContN2.lean`, which now re-exports this
module for the old route; the class facts read it — CLASSCHECK / P2D4.)

`nestInstType` (`Kernel/Inductives/Positivity.lean`) checks, for a key
`C.{us} ds` at the walk's hole bound `hi`, that the instantiated type
`instPisWith ds (C's type at us)` is a syntactic Π-telescope ending in a
sort whose binder domains mention no hole (N2, official's "unknown
constant").  Read: every domain of the instantiated type's reading
mentions no hole position (`noBVarTele_of_piDomsFree`), so two valuations
agreeing off the holes read the same index telescope — the container's
index sets, and its hole values applied to the key's parameters, are the
same at both sides of a hole relation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The syntactic side -/

/-- A Π-telescope ending in a sort whose domains mention no hole. -/
@[expose] def PiDomsFree (names : List Name) (lo hi : Nat) : Expr → Prop
  | .forallE ty b _ => ty.nestOcc names lo hi = false ∧ PiDomsFree names lo hi b
  | .sort _ => True
  | _ => False

/-- The number of leading `∀` binders. -/
@[expose] def piCount : Expr → Nat
  | .forallE _ b _ => piCount b + 1
  | _ => 0

theorem piDomsFree_of_binders {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr) {s : Level}, e.piBinders.2 = .sort s →
      (e.piBinders.1.any fun b => b.1.nestOcc names lo hi) = false → PiDomsFree names lo hi e := by
  intro e
  induction e with
  | forallE ty b mb _ ihb =>
    intro s hs hany
    simp only [ConLeche.Expr.piBinders, List.any_cons, Bool.or_eq_false_iff] at hs hany
    exact ⟨hany.1, ihb hs hany.2⟩
  | sort u => intro _ _ _; trivial
  | bvar => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | fvar => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | const => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | app => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | lam => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | letE => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | lit => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | proj => intro s hs; simp [ConLeche.Expr.piBinders] at hs

theorem PiDomsFree.instantiate1 {names : List Name} {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi))
    (ty : Expr) : ∀ (e : Expr) (k : Nat), PiDomsFree names lo hi e →
      PiDomsFree names lo hi (e.instantiate1 (.fvar d ty) k) := by
  intro e
  induction e with
  | forallE t b mb _ ihb =>
    intro k h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [nestOcc_instantiate1_fvar hd ty t k]; exact h1, ihb (k + 1) h2⟩
  | sort u => intro _ _; trivial
  | bvar => intro _ h; exact h.elim
  | fvar => intro _ h; exact h.elim
  | const => intro _ h; exact h.elim
  | app => intro _ h; exact h.elim
  | lam => intro _ h; exact h.elim
  | letE => intro _ h; exact h.elim
  | lit => intro _ h; exact h.elim
  | proj => intro _ h; exact h.elim

theorem piCount_instantiate1_fvar {d : Nat} (ty : Expr) :
    ∀ (e : Expr) (k : Nat), piCount (e.instantiate1 (.fvar d ty) k) = piCount e := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro k; simp only [ConLeche.Expr.instantiate1, piCount, ihb]
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; rfl

/-! ## The reading -/

theorem NoBVarTele.mono :
    ∀ {Fs : List AnnotTerm} {P Q : Nat → Prop}, (∀ i, Q i → P i) → NoBVarTele P Fs →
      NoBVarTele Q Fs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, ⟨h1, h2⟩ => ⟨NoBVar.mono h h1, NoBVarTele.mono (shiftP_mono h) h2⟩

/-- **A hole-free telescope reads hole-free**: the reading of a
Π-telescope ending in a sort whose domains mention no hole is a Π-tower
ending in a sort whose every domain mentions no hole position. -/
theorem noBVarTele_of_piDomsFree {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : AnnotTerm}, piCount e = n →
      PiDomsFree names lo hi e → Expr.WScoped d e → hi ≤ d →
      denoteMeta m.acval env φ d e = some ea →
      ∃ (ab : List (Nat × Nat × AnnotTerm)) (u : Nat), ea = mkPisAV ab (.sort u) ∧
        NoBVarTele (holeP d lo hi) (ab.map (·.2.2)) ∧ ab.length = n := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hf _ _ h
    match e, hn, hf, h with
    | .sort s, _, _, h =>
      rw [denoteMeta_sort] at h
      exact ⟨[], _, (Option.some.inj h).symm, trivial, rfl⟩
  | succ n ih =>
    intro e d ea hn hf hws hd h
    match e, hn, hf, hws, h with
    | .forallE ty b mb, hn, hf, hws, h =>
      obtain ⟨hty, hb⟩ := hf
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
      simp only [Expr.WScoped] at hws
      have hA : NoBVar (holeP d lo hi) ta := denoteMeta_noBVar_of_nestOcc d ty hws.1 hd hty hta
      have hnot : ¬ (lo ≤ d ∧ d < hi) := by omega
      obtain ⟨ab, u, rfl, hab, hlen⟩ := ih (b.instantiate1 (.fvar d ty))
        (by rw [piCount_instantiate1_fvar]; exact hn)
        (PiDomsFree.instantiate1 hnot ty b 0 hb)
        (Expr.WScoped.instantiate1 hws.1 0 hws.2) (by omega) hba
      exact ⟨(_, _, ta) :: ab, u, rfl, ⟨hA, NoBVarTele.mono holeP_succ hab⟩, by simp [hlen]⟩

/-! ## Telescopes read the same at two frames -/

/-- Two frames read a telescope the same, progressively (at every value
of the earlier binders). -/
@[expose] def TeleEq (ρ ρ' : Nat → V) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => interp V ρ F = interp V ρ' F ∧ ∀ a, TeleEq (cons a ρ) (cons a ρ') Fs

theorem TeleEq.teleOfFields : ∀ {Fs : List AnnotTerm} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    teleOfFields ρ Fs = teleOfFields ρ' Fs
  | [], _, _, _ => rfl
  | _ :: Fs, _, _, ⟨h1, h2⟩ => by
    simp only [teleOfFields_cons, h1]
    congr 1
    funext a
    exact TeleEq.teleOfFields (Fs := Fs) (h2 a)

theorem TeleEq.idxSet {u : Nat} {Fs : List AnnotTerm} {ρ ρ' : Nat → V} (h : TeleEq ρ ρ' Fs) :
    idxSet u ρ Fs = idxSet u ρ' Fs := by
  unfold ConLeche.Semantics.idxSet
  rw [h.teleOfFields]

theorem TeleEq.spineFit : ∀ {Fs : List AnnotTerm} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    ∀ as : List V, SpineFit ρ Fs as ↔ SpineFit ρ' Fs as
  | [], _, _, _, [] => Iff.rfl
  | [], _, _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, _, [] => Iff.rfl
  | _ :: Fs, _, _, ⟨h1, h2⟩, a :: as => by
    show (_ ∧ _) ↔ (_ ∧ _)
    rw [h1, TeleEq.spineFit (Fs := Fs) (h2 a) as]

theorem TeleEq.holeFam : ∀ {Fs : List AnnotTerm} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    ∀ g : List V → V, holeFam ρ Fs g = holeFam ρ' Fs g
  | [], _, _, _, _ => rfl
  | _ :: Fs, _, _, ⟨h1, h2⟩, g => by
    simp only [ConLeche.Model.holeFam, h1]
    congr 1
    funext a
    exact TeleEq.holeFam (Fs := Fs) (h2 a) _

/-- A telescope mentioning no position of `P` reads the same at frames
agreeing off `P`. -/
theorem teleEq_of_noBVarTele : ∀ {Fs : List AnnotTerm} {P : Nat → Prop} {ρ ρ' : Nat → V},
    NoBVarTele P Fs → AgreeOff P ρ ρ' → TeleEq ρ ρ' Fs
  | [], _, _, _, _, _ => trivial
  | F :: _, _, _, _, ⟨h1, h2⟩, hag =>
    ⟨interp_congr_noBVar F h1 hag, fun a => teleEq_of_noBVarTele h2 (agreeOff_cons hag a)⟩

/-- A substituted telescope reads the same exactly where the telescope
does at the substituted frames. -/
theorem teleEq_substTele (τ : Nat → AnnotTerm) : ∀ (ab : List (Nat × Nat × AnnotTerm)) (k : Nat)
    {ρ ρ' : Nat → V}, TeleEq ρ ρ' ((AnnotTerm.substTele τ k ab).map (·.2.2)) →
    TeleEq (substE V τ k ρ) (substE V τ k ρ') (ab.map (·.2.2))
  | [], _, _, _, _ => trivial
  | d :: ab, k, ρ, ρ', ⟨h1, h2⟩ => by
    refine ⟨?_, fun a => ?_⟩
    · have := h1
      simp only [interp_substAV] at this
      exact this
    · have := teleEq_substTele τ ab (k + 1) (h2 a)
      rwa [← cons_substE, ← cons_substE] at this

/-! ## Small syntactic facts -/

theorem replaceConsts_none {f : Name → List Level → Option Expr} (hf : ∀ c us, f c us = none) :
    ∀ e : Expr, e.replaceConsts f = e := by
  intro e
  induction e <;> simp_all [Expr.replaceConsts]

theorem nestOcc_nil_zero : ∀ e : Expr, e.nestOcc [] 0 0 = false := by
  intro e
  induction e <;> simp_all [ConLeche.Expr.nestOcc]

theorem piCount_eq_length : ∀ e : Expr, piCount e = e.piBinders.1.length := by
  intro e
  induction e with
  | forallE t b mb _ ihb => simp [piCount, ConLeche.Expr.piBinders, ihb]
  | _ => simp [piCount, ConLeche.Expr.piBinders]

theorem mkPisAV_sort_eq : ∀ {ab ab' : List (Nat × Nat × AnnotTerm)} {u u' : Nat},
    mkPisAV ab (.sort u) = mkPisAV ab' (.sort u') → ab = ab' ∧ u = u'
  | [], [], _, _, h => ⟨rfl, by simpa [mkPisAV] using h⟩
  | [], _ :: _, _, _, h => by simp [mkPisAV] at h
  | _ :: _, [], _, _, h => by simp [mkPisAV] at h
  | d :: ab, d' :: ab', u, u', h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_sort_eq h4
    exact ⟨by rw [Prod.ext h1 (Prod.ext h2 h3)], rfl⟩

/-- The parameter frame of a key: its parameters' values over the frame
seen from the walk's hole bound. -/
theorem consList_map_apply (vs : List V) (τ : Nat → V) (q : Nat) :
    consList vs τ q = if q < vs.length then vs.getD (vs.length - 1 - q) pt
      else τ (q - vs.length) := by
  by_cases hq : q < vs.length
  · rw [if_pos hq]
    induction vs generalizing τ q with
    | nil => exact absurd hq (Nat.not_lt_zero _)
    | cons a as ih =>
      rw [consList_cons]
      rcases Nat.lt_or_ge q as.length with h | h
      · rw [ih _ _ h]
        simp only [List.length_cons, List.getD_eq_getElem?_getD]
        rw [show as.length + 1 - 1 - q = (as.length - 1 - q) + 1 by omega, List.getElem?_cons_succ]
      · obtain rfl : q = as.length := by simp at hq; omega
        have := consList_apply_add as (cons a τ) 0
        rw [Nat.zero_add] at this
        rw [this]
        simp [cons]
  · rw [if_neg hq]
    obtain ⟨j, rfl⟩ : ∃ j, q = j + vs.length := ⟨q - vs.length, by omega⟩
    rw [consList_apply_add, Nat.add_sub_cancel]

theorem substTele_length (τ : Nat → AnnotTerm) :
    ∀ (k : Nat) (ab : List (Nat × Nat × AnnotTerm)), (AnnotTerm.substTele τ k ab).length = ab.length
  | _, [] => rfl
  | k, _ :: ab => by simp [AnnotTerm.substTele, substTele_length τ (k + 1) ab]

/-- The parameter frame of a key at a walk valuation `ρ` (the walk's
hole bound `hi`): the key's parameter readings over the frame below. -/
@[expose] noncomputable def keyFrame (dsa : List AnnotTerm) (hi : Nat) (ρ : Nat → V) : Nat → V :=
  consList (dsa.map (interp V ρ)) (fun j => ρ (j + hi))

theorem keyFrame_eq_substE {dsa : List AnnotTerm} {hi nP : Nat} (hl : dsa.length = nP)
    (ρ : Nat → V) :
    keyFrame dsa hi ρ = substE V (substTau nP hi fun i => dsa.getD i default) 0 ρ := by
  have h0 := substE_substTau (V := V) (nP := nP) (k := 0) (D' := hi)
    (fun i => dsa.getD i default) ρ
  simp only [Nat.add_zero] at h0
  rw [h0]
  funext q
  unfold keyFrame
  rw [consList_map_apply]
  simp only [List.range_zero, List.map_nil, consList_nil, List.length_map, hl]
  split
  · rename_i hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rfl

/-- **An instantiated container FORMER, read** (the group-free
`frameCrest_read` at the former's type): the type of `D`'s member `mm`
at the levels `us` with its parameters instantiated at `ds` (depth `hi`)
reads at `hi` as the recorded index telescope, substituted at the
parameters' readings, ending in the recorded sort. -/
theorem instFormer_read {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {hi : Nat} {us : List Level}
    {ds : List Expr} {cvC : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cvC caps))
    (hnd : cvC.levelParams.Nodup) (hul : us.length = cvC.levelParams.length)
    (hlenP : (D.params (Level.substFn φ cvC.levelParams us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
    (hstrip : (cvC.type.stripPis ds.length).isSome = true) {ty : Expr}
    (hty : ConLeche.instPisWith ds (cvC.type.instantiateLevelParams cvC.levelParams us) = some ty) :
    ∃ ab : List (Nat × Nat × AnnotTerm),
      ab.map (·.2.2) = D.ids mm (Level.substFn φ cvC.levelParams us) ∧
      denoteMeta mp.base2.acval env φ hi ty
        = some (mkPisAV (AnnotTerm.substTele (substTau ds.length hi fun i => dsa.getD i default) 0 ab)
            (.sort (D.w (Level.substFn φ cvC.levelParams us)))) := by
  obtain ⟨h, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hmm
  rw [hf] at hf₂
  obtain ⟨rfl, rfl⟩ : cvC = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  generalize hψ : Level.substFn φ cvC.levelParams us = ψ at hlenP ⊢
  obtain ⟨ab, hta, hmap, -⟩ := hab ψ
  have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hcl : cvC.type.hasFvar = false := hwf.1
  have hpl : (D.pars mm ψ).length = ds.length := (h.parsLen mm hmm ψ).trans hlenP
  have habl : ab.length = ds.length + (D.ids mm ψ).length := by
    have := congrArg List.length hmap
    simpa [hpl] using this
  -- the canonical opening of the container's parameters
  obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis_isSome ds.length 0 hstrip
  have hio := instPisWith_of_openPis ds.length hop
  have hEq : Expr.ErasedEqL fvs (canonParams ds.length) :=
    erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ConLeche.openPisAtFvars_index _ _ _ hop i x hx)
      (fun i x hx => ⟨.sort .zero, by rw [canonParams_getElem? hx, Nat.zero_add]⟩)
      (by rw [openPisAtFvars_length _ hop, canonParams_length])
  obtain ⟨A, hA, hoA⟩ := instPisWith_erasedEq hEq (Expr.ErasedEq.rfl _) hio
  obtain ⟨pps, b, hst, hb, -, -⟩ := denoteMeta_openPis ds.length hop hta
  rw [stripPisAV_mkPisAV_take _ _ _ (by omega)] at hst
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hAr : denoteMeta mp.base2.acval env ψ (ds.length + ([] : List Name).length) A
      = some (mkPisAV (ab.drop ds.length) (.sort (D.w ψ))) := by
    rw [← denoteMeta_erasedEq hoA]; simpa using hb
  have hAw : Expr.WScoped (ds.length + ([] : List Name).length) A := by
    refine ConLeche.wscoped_instPisWith (fun x hx => ?_)
      (Expr.WScoped.of_not_hasFvar hcl) hA
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hx
    have hlt : i < ds.length := by
      have := (List.getElem?_eq_some_iff.mp hi').1; rwa [canonParams_length] at this
    rw [canonParams_getElem? hi']
    simp [Expr.WScoped, hlt]
  have hnA : ConLeche.nestAbstract (canonCtx [] cvC.levelParams ds.length) [] cvC.type = cvC.type :=
    replaceConsts_none (fun c us => by
      by_cases h : (us == List.map Level.param cvC.levelParams) = true <;> simp [canonCtx, h]) _
  obtain ⟨crest, hcr, hcrd⟩ := frameCrest_read mp.base2 (φ := φ)
    (ctx := canonCtx [] cvC.levelParams ds.length) (holes := []) (us := us)
    (sub := fun _ _ => none) (ds := ds) (D' := hi) (s := fun i => ds.getD i default)
    (x := fun i => dsa.getD i default)
    (fun mm h => absurd h (Nat.not_lt_zero _)) hnd hul (canonParams_length _)
    (fun mm h => absurd h (Nat.not_lt_zero _)) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun i hi' => ⟨.sort .zero, by
      show (canonParams ds.length)[i]? = _
      simp [canonParams, List.getElem?_range (show i < ds.length from hi')]⟩) rfl
    (fun i hi' => by
      have hi'' : i < ds.length := by simpa [canonCtx] using hi'
      have hmem : ds.getD i default ∈ ds := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'']; exact List.getElem_mem _
      obtain ⟨hw, hb⟩ := hds _ hmem
      exact ⟨hw, hb, DenoteMetaSpine.getD hdsa default i hi''⟩)
    hcl hAw (by rw [hnA]; exact nestOcc_nil_zero _) (by rw [hnA]; exact hA)
    (by
      change denoteMeta mp.base2.acval env (Level.substFn φ cvC.levelParams us)
        (ds.length + ([] : List Name).length) A = _
      rw [hψ]; exact hAr)
  have hcr' : ConLeche.instPisWith ds
      ((cvC.type.instantiateLevelParams cvC.levelParams us).replaceConsts (fun _ _ => none))
      = some crest := hcr
  rw [replaceConsts_none (fun _ _ => rfl), hty] at hcr'
  obtain rfl := Option.some.inj hcr'
  refine ⟨ab.drop ds.length, ?_, ?_⟩
  · rw [List.map_drop, hmap, ← hpl, List.drop_left' rfl]
  · rw [hcrd]
    simp only [canonCtx, List.length_nil, Nat.add_zero, AnnotTerm.substAV]

/-- **N2 linked to the clause**.  A container instance's type former, checked by `nestInstType` at the
key `C.{us} ds` below the hole bound `hi`, has the recorded member's index
telescope (M4) as its index telescope: as many indices, and — because
the instantiated index telescope mentions no hole (N2) — read the same at
the key's parameter frames of any two walk valuations agreeing off the
holes (`TeleEq`).  So the container's index sets, the fit of an index
spine, and a hole value applied to the key's parameters are the same at
both sides of a hole relation. -/
theorem n2_link {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {hi : Nat} {us : List Level} {ds : List Expr}
    {nI : Nat} {cty : Expr}
    (hrun : ConLeche.nestInstType (m := ConLeche.CheckM) ctx hi ⟨D.member mm, us, ds⟩
      = .ok (nI, cty))
    {cvC : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cvC caps))
    (hnd : cvC.levelParams.Nodup) (hul : us.length = cvC.levelParams.length)
    (hlenP : (D.params (Level.substFn φ cvC.levelParams us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa) :
    cty = cvC.type.instantiateLevelParams cvC.levelParams us ∧
    (D.ids mm (Level.substFn φ cvC.levelParams us)).length = nI ∧
    ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
      TeleEq (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') (D.ids mm (Level.substFn φ cvC.levelParams us)) := by
  obtain ⟨cv', caps', hf', hstrip, hcty, ty, s, hty, hs, hocc, hnI, -⟩ :=
    ConLeche.nestInstType_inv hrun
  rw [hfind] at hf'
  change env.find? (D.member mm) = _ at hf'
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cvC = cv' ∧ caps = caps' := by simpa using hf'
  refine ⟨hcty, ?_⟩
  obtain ⟨ab, hmap, hcrd⟩ := instFormer_read mp hD hmm hf hnd hul hlenP hds hdsa hstrip hty
  generalize hψ : Level.substFn φ cvC.levelParams us = ψ at hlenP hmap hcrd ⊢
  have hdl : dsa.length = ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hcl : cvC.type.hasFvar = false := hwf.1
  -- N2: the index telescope's reading mentions no hole
  have hPDF := piDomsFree_of_binders ty hs hocc
  have hWty : Expr.WScoped hi ty :=
    ConLeche.wscoped_instPisWith (fun x hx => (hds x hx).1)
      (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl)) hty
  obtain ⟨ab'', u, hread, hnob, hlen''⟩ :=
    noBVarTele_of_piDomsFree (m := mp.base2) (φ := φ) _ ty rfl hPDF hWty (Nat.le_refl _) hcrd
  obtain ⟨rfl, -⟩ := mkPisAV_sort_eq hread
  refine ⟨?_, fun ρ ρ' hag => ?_⟩
  · rw [hnI, ← piCount_eq_length, ← hlen'', substTele_length, ← hmap, List.length_map]
  · have hte := teleEq_substTele _ _ 0 (teleEq_of_noBVarTele hnob hag)
    rw [← keyFrame_eq_substE hdl, ← keyFrame_eq_substE hdl] at hte
    rwa [hmap] at hte

/-! ## The level link -/

/-- A Π-telescope ending in the sort `s`. -/
@[expose] def PiEndsSort (s : Level) : Expr → Prop
  | .forallE _ b _ => PiEndsSort s b
  | .sort s' => s' = s
  | _ => False

theorem piEndsSort_of_binders {s : Level} :
    ∀ (e : Expr), e.piBinders.2 = .sort s → PiEndsSort s e := by
  intro e
  induction e with
  | forallE ty b mb _ ihb =>
    intro hs
    simp only [ConLeche.Expr.piBinders] at hs
    exact ihb hs
  | sort u =>
    intro hs
    show u = s
    simpa [ConLeche.Expr.piBinders] using hs
  | _ => intro hs; simp [ConLeche.Expr.piBinders] at hs

theorem PiEndsSort.instantiate1 {s : Level} (v : Expr) :
    ∀ (e : Expr) (k : Nat), PiEndsSort s e → PiEndsSort s (e.instantiate1 v k) := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro k h; exact ihb (k + 1) h
  | sort u => intro _ h; exact h
  | _ => intro _ h; exact h.elim

/-- **A Π-telescope ending in the sort `s` reads as a Π-tower ending in
`s`'s value.** -/
theorem denoteMeta_piEndsSort {s : Level} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : AnnotTerm}, piCount e = n → PiEndsSort s e →
      denoteMeta m.acval env φ d e = some ea →
      ∃ ab : List (Nat × Nat × AnnotTerm), ea = mkPisAV ab (.sort (s.eval φ)) := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hf h
    match e, hn, hf, h with
    | .sort s', _, hf, h =>
      rw [denoteMeta_sort] at h
      obtain rfl : s' = s := hf
      exact ⟨[], (Option.some.inj h).symm⟩
  | succ n ih =>
    intro e d ea hn hf h
    match e, hn, hf, h with
    | .forallE ty b mb, hn, hf, h =>
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
      obtain ⟨ab, rfl⟩ := ih (b.instantiate1 (.fvar d ty))
        (by rw [piCount_instantiate1_fvar]; exact hn) (PiEndsSort.instantiate1 _ b 0 hf) hba
      exact ⟨(_, _, ta) :: ab, rfl⟩

/-- **The level link** (the kernel's N3): a
container instance checked by `nestInstType` lives at the block's sort —
the recorded block's level at the key's levels is the value of the walk
context's sort. -/
theorem n2_sort {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {hi : Nat} {us : List Level} {ds : List Expr}
    {nI : Nat} {cty : Expr}
    (hrun : ConLeche.nestInstType (m := ConLeche.CheckM) ctx hi ⟨D.member mm, us, ds⟩
      = .ok (nI, cty))
    {cvC : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cvC caps))
    (hnd : cvC.levelParams.Nodup) (hul : us.length = cvC.levelParams.length)
    (hlenP : (D.params (Level.substFn φ cvC.levelParams us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa) :
    D.w (Level.substFn φ cvC.levelParams us) = ctx.sort.eval φ := by
  obtain ⟨cv', caps', hf', hstrip, -, ty, s, hty, hs, -, -, hequiv⟩ :=
    ConLeche.nestInstType_inv hrun
  rw [hfind] at hf'
  change env.find? (D.member mm) = _ at hf'
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cvC = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨ab, -, hcrd⟩ := instFormer_read mp hD hmm hf hnd hul hlenP hds hdsa hstrip hty
  obtain ⟨ab', hread⟩ := denoteMeta_piEndsSort (m := mp.base2) (φ := φ) _ ty rfl
    (piEndsSort_of_binders ty hs) hcrd
  obtain ⟨-, hw⟩ := mkPisAV_sort_eq hread
  rw [hw]
  exact ConLeche.Level.isEquiv_sound hequiv φ

end ConLeche.Model
