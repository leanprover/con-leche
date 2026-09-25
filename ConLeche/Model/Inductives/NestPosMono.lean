module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.Inductives.HoleMono
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.CtxOkP
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitShift
import ConLeche.Semantics.Frame
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.InferLemmas
import ConLeche.Model.IndPointKit

public section

/-!
# The hole relation and the positivity kit (lanes POSPROOF, POSDERIV)

The semantic vocabulary of the positivity theorem: the hole positions
(`holeP`), a term free of holes reads without them
(`denoteMeta_noBVar_of_nestOcc`), spines, the HOLE RELATION (`HoleRel`:
related frames satisfy the context, agree off the holes, and every
member and frame hole grows), `PiPosThen`/`ResultAt`/`ResultIdxConst`.
The theorem itself — every judgment of the positivity DERIVATION reads
monotonically — is proved by induction on the derivation
(`PosDerivMono.lean`, lane POSDERIV); the run is inverted once
(`Verify/Inductives/PosDerivInv.lean`).

The holes are the free variables `nP ..< hiAt |prog|`: the members, then
one per frame (`nestPos`'s own layout).  A hole at variable `i` reads,
at depth `d`, as the bound position `d - 1 - i` (`holeP`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The hole positions -/

/-- The bound positions, at depth `d`, of the hole variables `lo ..< hi`. -/
@[expose] def holeP (d lo hi : Nat) : Nat → Prop :=
  fun j => j < d ∧ lo ≤ d - 1 - j ∧ d - 1 - j < hi

theorem holeP_succ {d lo hi : Nat} : ∀ i, shiftP (holeP d lo hi) i → holeP (d + 1) lo hi i
  | 0, h => h.elim
  | i + 1, h => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, ?_⟩ <;> omega

/-! ## Occurrences and readings -/

/-- Instantiating a bound variable by a non-hole variable changes no
occurrence. -/
theorem nestOcc_instantiate1_fvar {names : List Name} {lo hi d : Nat}
    (hd : ¬ (lo ≤ d ∧ d < hi)) (ty : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).nestOcc names lo hi = e.nestOcc names lo hi := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1]
    split
    · simp [ConLeche.Expr.nestOcc, hd]
    · split <;> simp [ConLeche.Expr.nestOcc]
  | fvar i t _ => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, iht, ihv, ihb]
  | proj s i e ih =>
    intro k; simp [ConLeche.Expr.instantiate1, ConLeche.Expr.nestOcc, ih]

/-- A reading whose erasure is closed mentions no position at all. -/
theorem noBVar_of_closed {ea : AnnotTerm} (h : Term.bvarsBelow 0 ea.erase) (P : Nat → Prop) :
    NoBVar P ea :=
  NoBVar_of_bvarsBelow h fun _ _ => Nat.zero_le _

theorem noBVar_projAV {P : Nat → Prop} : ∀ (k : Nat) {e : AnnotTerm}, NoBVar P e →
    NoBVar P (projAV k e)
  | 0, _, h => h
  | k + 1, _, h => noBVar_projAV (P := P) k (e := .snd _) h

/-- **A term mentioning no hole reads without the holes' positions.** -/
theorem denoteMeta_noBVar_of_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm}, Expr.WScoped d e → hi ≤ d →
      e.nestOcc names lo hi = false →
      denoteMeta m.acval env φ d e = some ea → NoBVar (holeP d lo hi) ea := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    cases h; trivial
  | case2 d idx ty =>
    intro ea hws _ hocc h
    rw [denoteMeta] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, decide_eq_false_iff_not] at hocc
    show ¬ holeP d lo hi (d - 1 - idx)
    rintro ⟨-, h2, h3⟩
    exact hocc ⟨by omega, by omega⟩
  | case3 d n us ci hf hlen =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    cases h
    exact noBVar_of_closed (m.cval_closedL _ _) _
  | case4 d n us ci hf hlen =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ea hws hd hocc h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    refine ⟨ihty hws.1 hd hocc.1 hta, ?_⟩
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hocc' : (body.instantiate1 (.fvar d ty)).nestOcc names lo hi = false := by
      rw [nestOcc_instantiate1_fvar (by omega) ty body 0]; exact hocc.2
    exact NoBVar.mono holeP_succ (ihbody hws' (by omega) hocc' hba)
  | case7 d ty body mb ihty ihbody =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hta : denoteMeta m.acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta m.acval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    refine ⟨ihty hws.1 hd hocc.1 hta, ?_⟩
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hocc' : (body.instantiate1 (.fvar d ty)).nestOcc names lo hi = false := by
      rw [nestOcc_instantiate1_fvar (by omega) ty body 0]; exact hocc.2
    exact NoBVar.mono holeP_succ (ihbody hws' (by omega) hocc' hba)
  | case8 d fe a ihf iha =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hfa : denoteMeta m.acval env φ d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteMeta m.acval env φ d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hocc
    exact ⟨ihf hws.1 hd hocc.1 hfa, iha hws.2 hd hocc.2 haa⟩
  | case9 d ty val body =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea hws hd hocc h
    rw [denoteMeta] at h
    rcases hea : denoteMeta m.acval env φ d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.nestOcc] at hocc
    have hsub := ihe hws hd hocc hea
    replace h : (match env.findProj? sn i with
        | some entry => some (projAV (i + entry.off) ea')
        | none => AnnotTerm.projPair? i ea') = some ea := h
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at h
      cases h
      exact noBVar_projAV _ hsub
    | none =>
      rw [hfp] at h
      rcases i with _ | _ | i
      · cases h; exact hsub
      · cases h; exact hsub
      · exact nomatch h
  | case11 d k hsup =>
    intro ea _ _ _ h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.natVal k)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    exact noBVar_of_closed (denote_bvarsBelow m.cval_closedL 0 _ (by simp [Expr.WScoped]) rfl
      (denoteMeta_erase m.acval_erase 0 _ h0)) _
  | case12 d k hsup =>
    intro ea _ _ _ h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea _ _ _ h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.strVal s)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    exact noBVar_of_closed (denote_bvarsBelow m.cval_closedL 0 _ (by simp [Expr.WScoped]) rfl
      (denoteMeta_erase m.acval_erase 0 _ h0)) _
  | case14 d s hsup =>
    intro ea _ _ _ h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea _ _ _ h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-! ## Spines -/

theorem wScoped_mkAppN {d : Nat} :
    ∀ (as : List Expr) {f : Expr}, Expr.WScoped d (Expr.mkAppN f as) →
      Expr.WScoped d f ∧ ∀ a ∈ as, Expr.WScoped d a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hfa, has⟩ := wScoped_mkAppN as (f := .app f a) h
    simp only [Expr.WScoped] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfa.2
    · exact has x hx

theorem DenoteMetaSpine.length_eq {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [DenoteMetaSpine.length_eq h]

theorem DenoteMetaSpine.split {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ (as : List Expr) {bs : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as ++ bs) vs →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ DenoteMetaSpine acval env φ d as vs₁ ∧
        DenoteMetaSpine acval env φ d bs vs₂
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | a :: as, bs, _, .cons ha h => by
    obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := DenoteMetaSpine.split as h
    exact ⟨_ :: vs₁, vs₂, rfl, .cons ha h₁, h₂⟩

/-- Hole-free arguments read hole-free. -/
theorem constOn_spine {names : List Name} {lo hi d : Nat} {R : FrameRel V}
    (hR : R.AgreesOff (holeP d lo hi)) (hd : hi ≤ d) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine m.acval env φ d as vs →
      (∀ a ∈ as, Expr.WScoped d a ∧ a.nestOcc names lo hi = false) →
      ∀ v ∈ vs, ConstOn R v
  | _, _, .nil, _ => fun _ hv => nomatch hv
  | a :: _, _ :: _, .cons ha h, hall => fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨hw, ho⟩ := hall a (List.mem_cons_self ..)
      exact ConstOn.of_noBVar hR (denoteMeta_noBVar_of_nestOcc d a hw hd ho ha)
    · exact constOn_spine hR hd h (fun b hb => hall b (List.mem_cons_of_mem _ hb)) x hx

/-! ## The relation the run is proved along -/

/-- A spine of `d`-scoped terms read one level deeper is its depth-`d`
reading, lifted. -/
theorem DenoteMetaSpine.weaken_top {d : Nat} :
    ∀ {as : List Expr} {vs' : List AnnotTerm}, (∀ x ∈ as, Expr.WScoped d x) →
      DenoteMetaSpine m.acval env φ (d + 1) as vs' →
      ∃ vs, DenoteMetaSpine m.acval env φ d as vs ∧ vs' = vs.map (AnnotTerm.liftN 1 · 0)
  | _, _, _, .nil => ⟨[], .nil, rfl⟩
  | a :: as, _ :: _, hws, .cons ha h => by
    obtain ⟨vs, hvs, rfl⟩ :=
      DenoteMetaSpine.weaken_top (fun x hx => hws x (List.mem_cons_of_mem _ hx)) h
    rw [denoteMeta_weaken_top m.acval_closed (hws a List.mem_cons_self)] at ha
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨v :: vs, .cons hv hvs, rfl⟩

/-- **The hole relation** at depth `d` under the frames `prog`: related
frames satisfy the context, agree off the hole positions, the member
holes grow (at their full arity), and every frame's hole grows at its
instantiation's own parameters (`HoleOnArgs`: the key's parameter terms,
read at the depth, then any indices). -/
structure HoleRel (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  member : ∀ t, t < ctx.names.length →
    HoleOn R (d - 1 - (ctx.nP + t)) (ctx.nP + ctx.nIdxs.getD t 0)
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ dsa,
    DenoteMetaSpine m.acval env φ d hk.key.ds dsa → ∀ ni,
    HoleOnArgs R (d - 1 - (ctx.hiAt 0 + i)) dsa ni
  /-- the frames' parameter terms are scoped below the frames' holes (the
  kernel checks `fvarB ≤ hiAt` at each frame's entry) -/
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

/-- **Under a positive binder** (a hole-free domain, or an earlier field)
the relation is the same one level deeper. -/
theorem HoleRel.under {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRel m φ ctx prog d Δa R) (hd : ctx.hiAt prog.length ≤ d)
    {ta : AnnotTerm} (hA : MonoOn R ta) :
    HoleRel m φ ctx prog (d + 1) (ta :: Δa) (R.under ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 (hA ρ ρ' hR x hx)⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.under ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  member := by
    intro t ht
    have hlt : ctx.nP + t < d := by
      simp only [NestCtx.hiAt] at hd; omega
    rw [show d + 1 - 1 - (ctx.nP + t) = d - 1 - (ctx.nP + t) + 1 by omega]
    exact (h.member t ht).under ta
  frame := by
    intro i key hk dsa' hsp ni
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < d := by
      simp only [NestCtx.hiAt] at hd ⊢; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped i key hk x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + i) = d - 1 - (ctx.hiAt 0 + i) + 1 by omega]
    exact (h.frame i key hk dsa hdsa ni).under ta
  dsScoped := h.dsScoped

/-! ## A constructor's field telescope -/

/-- **The first `n` Π-domains of a reading positive**, each under the
earlier ones, and `P` of the relation and the reading below them. -/
@[expose] def PiPosThen (P : FrameRel V → AnnotTerm → Prop) :
    Nat → FrameRel V → AnnotTerm → Prop
  | 0, R, r => P R r
  | n + 1, R, .pi _ _ A B => MonoOn R A ∧ PiPosThen P n (R.under A) B
  | _ + 1, _, _ => False

/-- What a telescope walk leaves at its result `res`, at depth `D`: the
relation still agrees off the hole positions, and the result reads. -/
@[expose] def ResultAt (m : EnvModel V env) (φ : Name → Nat) (lo hi D : Nat) (res : Expr)
    (R : FrameRel V) (r : AnnotTerm) : Prop :=
  R.AgreesOff (holeP D lo hi) ∧ denoteMeta m.acval env φ D res = some r ∧ Expr.WScoped D res

theorem PiPosThen.mono {P Q : FrameRel V → AnnotTerm → Prop}
    (hPQ : ∀ R r, P R r → Q R r) :
    ∀ (n : Nat) (R : FrameRel V) (r : AnnotTerm), PiPosThen P n R r → PiPosThen Q n R r
  | 0, R, r, h => hPQ R r h
  | n + 1, R, .pi _ _ A B, h => ⟨h.1, PiPosThen.mono hPQ n (R.under A) B h.2⟩
  | _ + 1, _, .bvar _, h | _ + 1, _, .sort _, h | _ + 1, _, .const _ _, h
  | _ + 1, _, .app _ _, h | _ + 1, _, .lam _ _ _, h | _ + 1, _, .eqE _ _, h
  | _ + 1, _, .fst _, h | _ + 1, _, .snd _, h | _ + 1, _, .prf, h => h.elim

/-- A Π-tower positive along a relation is positive field by field, and
its body satisfies the predicate under the fields. -/
theorem piPosThen_mkPisAV {P : FrameRel V → AnnotTerm → Prop} :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (R : FrameRel V) (b : AnnotTerm),
      PiPosThen P ab.length R (mkPisAV ab b) →
      TeleMonoOn R (ab.map (·.2.2)) ∧ P (R.underTele (ab.map (·.2.2))) b
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: ab, R, b, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ht, hp⟩ := piPosThen_mkPisAV ab _ b h2
    exact ⟨⟨h1, ht⟩, hp⟩

/-- The number of applications on a spine. -/
def spineLenAV : AnnotTerm → Nat
  | .app f _ => spineLenAV f + 1
  | _ => 0

theorem spineLenAV_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    spineLenAV (AnnotTerm.mkAppN f as) = spineLenAV f + as.length
  | [], _ => rfl
  | a :: as, f => by
    rw [ConLeche.Semantics.AnnotTerm.mkAppN_cons, spineLenAV_mkAppN as]
    simp [spineLenAV]; omega

/-- Spines headed by a variable are equal only at equal variables and
arguments. -/
theorem mkAppN_bvar_inj {i j : Nat} {as bs : List AnnotTerm}
    (h : AnnotTerm.mkAppN (.bvar i) as = AnnotTerm.mkAppN (.bvar j) bs) : i = j ∧ as = bs := by
  have hl := congrArg spineLenAV h
  rw [spineLenAV_mkAppN, spineLenAV_mkAppN] at hl
  simp only [spineLenAV, Nat.zero_add] at hl
  obtain ⟨h1, h2⟩ := AnnotTerm.mkAppN_inj h hl
  injection h1 with h1
  exact ⟨h1, h2⟩

/-- **A member constructor's result**: its reading is a spine whose
arguments after the parameters (the result's indices) are hole-free. -/
@[expose] def ResultIdxConst (nP : Nat) (R : FrameRel V) (r : AnnotTerm) : Prop :=
  ∃ i vs, r = AnnotTerm.mkAppN (.bvar i) vs ∧ ∀ v ∈ vs.drop nP, ConstOn R v

end ConLeche.Model
