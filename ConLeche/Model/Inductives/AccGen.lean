module

public import ConLeche.Model.Inductives.ContAccFrame
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge

public section

/-!
# Accessibility, generic in the admissible items (PRIMREC / NESTKN-M4)

The accessibility vocabulary of `NestPosAcc.lean` and the frame's
accessibility of `ContAccFrame.lean` are stated along a path of frames
(`prog`): the admissible items are `HoleQ ctx prog d`, the hole range ends at
`ctx.hiAt prog.length`.  The key-named positivity check has LAYOUTS instead of
paths.  This file restates the pieces with the admissible items `Qd`
(a function of the depth) and the hole bound `hb` as parameters — the proofs
are the path ones, which never read `prog` beyond those two:

* `AccConclG`, `OutOkG`, `PiAccThenG`, `OutTeleG` (a field's and a
  telescope's conclusions);
* `teleAccP_of_piAccThenG`, `walkTele_accG` (a walked telescope over its
  normal form);
* `CtorWalkedAG`, `FrameAccOutG`, `frameCtor_accG`, `frameAccOut_ofG` and
  `frameIterAccG` — a container frame's accessibility from its constructors'
  walk, generic in the enclosing admissible items `Q₀` and the frame's `Qf`
  (which splits into the frame's own holes and `Q₀` moved up), the walk
  given AT the frame relation (the accessibility twin of `frameIterGen`).

`PiAccThenG.toOld` reads the generic telescope back as the path one where
the items agree (the member layout, whose items are `HoleQ ctx []`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole NestState NestFieldKind CheckError CheckM
  ConstantVal BinderMeta instPisWith)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The conclusions -/

/-- **What a field proves of its reading** (`AccConcl`, generic): the type
regime, and accessibility with a bound of the level reading only the non-hole
positions the output mentions, along the admissible items `Qd dep`. -/
@[expose] def AccConclG (w nP hb : Nat) (Qd : Nat → Nat → Nat → Prop) (dep : Nat) (e nf : Expr)
    (R : FrameRel V) (ea : AnnotTerm) : Prop :=
  TypeReg R ea ∧ (∃ A, AccOn w (Qd dep) R A ea ∧ SizeOn w R A ∧
    InvOn (MentP nP hb dep nf) A) ∧ OutMent dep e nf

/-- **What a field proves of its OUTPUT** (`OutOk`, generic). -/
@[expose] def OutOkG (m : EnvModel V env) (φ : Name → Nat) (names : List Name) (nP hb dep : Nat)
    (Δa : List AnnotTerm) (k : ConLeche.PosKind) (nf : Expr) (ea : AnnotTerm) : Prop :=
  nf.looseBVarsBounded 0 = true ∧ Expr.WScoped dep nf ∧
  (k = .ordinary → nf.nestOcc names nP hb = false) ∧
  ∃ na, denoteMeta m.acval env φ dep nf = some na ∧
    ∀ ρ, Sat V Δa ρ → interp V ρ na = interp V ρ ea

theorem OutOkG.congr_read {names : List Name} {nP hb dep : Nat}
    {Δa : List AnnotTerm} {k : ConLeche.PosKind} {nf : Expr} {ea ea' : AnnotTerm}
    (h : OutOkG m φ names nP hb dep Δa k nf ea)
    (heq : ∀ ρ, Sat V Δa ρ → interp V ρ ea = interp V ρ ea') :
    OutOkG m φ names nP hb dep Δa k nf ea' := by
  obtain ⟨h1, h2, h3, na, hna, hr⟩ := h
  exact ⟨h1, h2, h3, na, hna, fun ρ hρ => (hr ρ hρ).trans (heq ρ hρ)⟩

/-- **The first `n` Π-domains of a reading accessible** (`PiAccThen`,
generic). -/
@[expose] def PiAccThenG (w nP hb : Nat) (Qd : Nat → Nat → Nat → Prop)
    (Q : FrameRel V → AnnotTerm → Prop) :
    Nat → Nat → List Expr → FrameRel V → AnnotTerm → Prop
  | 0, _, _, R, r => Q R r
  | n + 1, d, nd :: nds, R, .pi _ _ A B =>
    (∃ Af, AccOn w (Qd d) R Af A ∧ SizeOn w R Af ∧ InvOn (MentP nP hb d nd) Af) ∧
      PiAccThenG w nP hb Qd Q n (d + 1) nds (R.underBoth A) B
  | _ + 1, _, _, _, _ => False

/-- **The walked fields' outputs, field by field** (`OutTele`, generic). -/
@[expose] def OutTeleG (m : EnvModel V env) (φ : Name → Nat) (names : List Name) (nP hb : Nat) :
    List ConLeche.PosKind → List Expr → Nat → List AnnotTerm → AnnotTerm → Prop
  | [], [], _, _, _ => True
  | k :: ks, nd :: nds, d, Δ, .pi _ _ A B =>
    OutOkG m φ names nP hb d Δ k nd A ∧ OutTeleG m φ names nP hb ks nds (d + 1) (A :: Δ) B
  | _, _, _, _, _ => False

theorem PiAccThenG.mono {w nP hb : Nat} {Qd : Nat → Nat → Nat → Prop}
    {Q Q' : FrameRel V → AnnotTerm → Prop} (hQ : ∀ R r, Q R r → Q' R r) :
    ∀ (n d : Nat) (nds : List Expr) (R : FrameRel V) (r : AnnotTerm),
      PiAccThenG w nP hb Qd Q n d nds R r → PiAccThenG w nP hb Qd Q' n d nds R r
  | 0, _, _, R, r, h => hQ R r h
  | n + 1, d, _ :: nds, _, .pi _ _ _ B, h => ⟨h.1, PiAccThenG.mono hQ n (d + 1) nds _ B h.2⟩
  | _ + 1, _, [], _, _, h => h.elim
  | _ + 1, _, _ :: _, _, .bvar _, h | _ + 1, _, _ :: _, _, .sort _, h
  | _ + 1, _, _ :: _, _, .const _ _, h | _ + 1, _, _ :: _, _, .app _ _, h
  | _ + 1, _, _ :: _, _, .lam _ _ _, h | _ + 1, _, _ :: _, _, .eqE _ _, h
  | _ + 1, _, _ :: _, _, .fst _, h | _ + 1, _, _ :: _, _, .snd _, h
  | _ + 1, _, _ :: _, _, .prf, h => h.elim

/-- **The generic telescope, read along a path** where the admissible items
and the hole bound are the path's. -/
theorem PiAccThenG.toOld {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {Qd : Nat → Nat → Nat → Prop} {Q : FrameRel V → AnnotTerm → Prop}
    (hQd : ∀ d i n, Qd d i n ↔ HoleQ ctx prog d i n) :
    ∀ (n d : Nat) (nds : List Expr) (R : FrameRel V) (r : AnnotTerm),
      PiAccThenG w ctx.nP (ctx.hiAt prog.length) Qd Q n d nds R r →
      PiAccThen w ctx prog Q n d nds R r
  | 0, _, _, _, _, h => h
  | n + 1, d, _ :: nds, _, .pi _ _ _ B, ⟨⟨Af, hA, hsz, hinv⟩, h⟩ =>
    ⟨⟨Af, AccOn.congrQ (hQd d) hA, hsz, hinv⟩, PiAccThenG.toOld hQd n (d + 1) nds _ B h⟩
  | _ + 1, _, [], _, _, h => h.elim
  | _ + 1, _, _ :: _, _, .bvar _, h | _ + 1, _, _ :: _, _, .sort _, h
  | _ + 1, _, _ :: _, _, .const _ _, h | _ + 1, _, _ :: _, _, .app _ _, h
  | _ + 1, _, _ :: _, _, .lam _ _ _, h | _ + 1, _, _ :: _, _, .eqE _ _, h
  | _ + 1, _, _ :: _, _, .fst _, h | _ + 1, _, _ :: _, _, .snd _, h
  | _ + 1, _, _ :: _, _, .prf, h => h.elim

/-! ## A walked telescope, over its normal form -/

section Tele

variable {nP hb : Nat} {Qd : Nat → Nat → Nat → Prop}
  (hsh : ∀ d, hb ≤ d → ∀ i n, shiftQ (Qd d) i n ↔ Qd (d + 1) i n)

include hsh in
/-- **The walked fields' accessibility moves onto the datum's fields**
(`teleAccP_of_piAccThen`, generic). -/
theorem teleAccP_of_piAccThenG {w : Nat} (hw : w ≠ 0) {Qf : FrameRel V → AnnotTerm → Prop} :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (d l : Nat) (nds : List Expr)
      (Δ : List AnnotTerm) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abN.map (·.2.2))) →
      (∀ i n, Qd d i n ↔ Q i n) → hb ≤ d →
      PiAccThenG w nP hb Qd Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN.map (·.2.2)) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP nP hb (d + i) nd) (Af (l + i))) ∧
        Qf (R.underBothTele (abN.map (·.2.2))) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    have hE' := hE
    simp only [List.map_cons] at hE'
    obtain ⟨h0, hrest⟩ := hE'
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0⟩, hP'⟩ =>
      have hUE : R.underBoth x.2.2 = R.underBoth y.2.2 := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x.2.2 σ σ₀ → FieldsBound w σ (abN.map (·.2.2)) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
        have hok0 := hok ρ ρ₀ hR
        simp only [List.map_cons] at hok0
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, Qd (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← hsh d hd i n]
        exact shiftQ_congr hQ i n
      obtain ⟨Af', htele', hinv', hQf⟩ :=
        teleAccP_of_piAccThenG hw abD abN B (d + 1) (l + 1) nds' (x.2.2 :: Δ)
          (R.underBoth x.2.2) (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_⟩
      · simp only [List.map_cons]
        refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · have hok0 := hok ρ ρ₀ hR
          simp only [List.map_cons] at hok0
          exact hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [if_neg (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [if_neg (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · show Qf ((R.underBoth y.2.2).underBothTele (abN.map (·.2.2))) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

/-- **The walked outputs' readings, as a telescope** (`outTele_list`,
generic). -/
theorem outTele_listG {names : List Name} :
    ∀ (ks : List ConLeche.PosKind) (nds : List Expr) (d : Nat) (Δ : List AnnotTerm)
      (abD : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      abD.length = nds.length →
      OutTeleG m φ names nP hb ks nds d Δ (mkPisAV abD B) →
      ∃ N : List AnnotTerm, N.length = nds.length ∧ FieldsEqOn V Δ (abD.map (·.2.2)) N ∧
        ∀ (i : Nat) (nd : Expr), nds[i]? = some nd → ∃ na, N[i]? = some na ∧
          denoteMeta m.acval env φ (d + i) nd = some na ∧ nd.looseBVarsBounded 0 = true ∧
          Expr.WScoped (d + i) nd ∧
          (ks.getD i .ordinary = .ordinary → nd.nestOcc names nP hb = false)
  | [], [], _, _, [], _, _, _ => ⟨[], rfl, trivial, fun _ _ h => by simp at h⟩
  | k :: ks, nd :: nds, d, Δ, x :: abD, B, hl, hO => by
    obtain ⟨⟨hcl, hws, hord, na, hna, hr⟩, hrest⟩ := hO
    obtain ⟨N, hNl, hE, hN⟩ := outTele_listG ks nds (d + 1) (x.2.2 :: Δ) abD B
      (by simpa using hl) hrest
    refine ⟨na :: N, by simp [hNl], ⟨fun ρ hρ => (hr ρ hρ).symm, hE⟩, fun i nd' hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨na, rfl, by simpa using hna, hcl, by simpa using hws, fun h => hord (by simpa using h)⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨na', h1, h2, h3, h4, h5⟩ := hN i nd' hi
      refine ⟨na', by simpa using h1, by rw [show d + (i + 1) = d + 1 + i by omega]; exact h2, h3,
        by rw [show d + (i + 1) = d + 1 + i by omega]; exact h4, fun h => h5 (by simpa using h)⟩
  | [], _ :: _, _, _, _, _, _, hO => hO.elim
  | _ :: _, [], _, _, _, _, _, hO => by cases hO
  | [], [], _, _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, _, _, [], _, hl, _ => by simp at hl

set_option maxHeartbeats 800000 in
include hsh in
/-- **A walked telescope is accessible over its normal form**
(`walkTele_acc`, generic): at the hole bound `hb`, which is the walk's base
depth. -/
theorem walkTele_accG {w : Nat} (hw : w ≠ 0) {names : List Name} (hnPb : nP ≤ hb) {nF : Nat}
    {res : Expr} {ks : List ConLeche.PosKind} {nds : List (Expr × BinderMeta)}
    (hnl : nds.length = nF) (hrescl : res.looseBVarsBounded 0 = true)
    (hU4 : ∀ i, i < nF → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds hb res) 0 i = false)
    {Δ : List AnnotTerm} {R : FrameRel V} {abD : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hlen : abD.length = nF)
    (hdom : ∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀)
    (hbd : ∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abD.map (·.2.2)))
    (hP : PiAccThenG w nP hb Qd (ResultAt m φ nP hb (hb + nF) res) nF hb (nds.map (·.1)) R
      (mkPisAV abD B))
    (hO : OutTeleG m φ names nP hb ks (nds.map (·.1)) hb Δ (mkPisAV abD B)) :
    ∃ (Af : Nat → (Nat → V) → V) (N : List AnnotTerm),
      FieldsEqOn V Δ (abD.map (·.2.2)) N ∧
      TeleAccP w Af 0 (Qd hb) R N ∧
      (∀ l τ τ', TAgrM 0 (ParamPos hb nP) (fun l => ks.getD l .ordinary == .ordinary) l τ τ' →
        Af l τ = Af l τ') ∧
      (∀ (i : Nat) (G : AnnotTerm), N[i]? = some G → (ks.getD i .ordinary == .ordinary) = true →
        ∀ τ τ', TAgrM 0 (ParamPos hb nP) (fun l => ks.getD l .ordinary == .ordinary) i τ τ' →
          interp V τ G = interp V τ' G) ∧
      ResultAt m φ nP hb (hb + nF) res (R.underBothTele N) B := by
  classical
  have hnl' : (nds.map (·.1)).length = nF := by rw [List.length_map, hnl]
  obtain ⟨N, hNl, hE, hN⟩ := outTele_listG (m := m) (φ := φ) (nP := nP) (hb := hb) ks
    (nds.map (·.1)) hb Δ abD B (by rw [hnl', hlen]) hO
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨na, -, -, h3, -⟩ := hN i nds[i].1 (by simp [List.getElem?_eq_getElem hi])
    exact h3
  obtain ⟨xs, rest, hop, hxs⟩ := fields_open hrescl hnl hndcl
  let abN : List (Nat × Nat × AnnotTerm) := N.map fun a => (0, 0, a)
  have habN : abN.map (·.2.2) = N := by simp only [abN, List.map_map]; exact List.map_id N
  rw [← hlen] at hP
  obtain ⟨Af, htele, hinv, hQf⟩ := teleAccP_of_piAccThenG hsh hw abD abN B hb 0 (nds.map (·.1)) Δ R
    (Qd hb) (by rw [habN]; exact hE) hdom
    (fun ρ ρ₀ h => by rw [habN]; exact FieldsBound.of_eqOn hE (hdom ρ ρ₀ h).1 (hbd ρ ρ₀ h))
    (fun _ _ => Iff.rfl) (Nat.le_refl _) hP
  rw [habN] at htele hQf
  rw [hlen] at hQf
  have hNn : N.length = nF := hNl.trans hnl'
  -- the closed normal form is scoped at the base
  have hW : Expr.WScoped hb (ConLeche.closeTelescope nds hb res) := by
    refine ConLeche.Cached.closeTelescope_wscoped nds hb res (fun k nd hk => ?_) ?_
    · obtain ⟨na, -, -, -, h4, -⟩ := hN k nd.1 (by simp [hk])
      exact h4
    · rw [hnl]; exact hQf.2.2
  let ord : Nat → Bool := fun l => ks.getD l .ordinary == .ordinary
  -- U4: a later output mentions no non-ordinary field
  have hu4 : ∀ l j x, j < l → xs[l]? = some x → ord j = false →
      x.fvarTypeD.nestOcc [] (hb + j) (hb + j + 1) = false := by
    intro l j x hjl hx hoj
    have hlx : l < nF := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [ConLeche.Verify.openPisAtFvars_length nF hop] at this; exact this
    have hne : ks.getD j .ordinary ≠ .ordinary := by simpa [ord] using hoj
    exact u4_nestOccAt hop hW (hU4 j (by omega) hne) (by omega) hjl hx
  refine ⟨fun l => if l < nF then Af l else fun _ => empty, N, hE, ?_, ?_, ?_, hQf⟩
  · refine TeleAccP.congr _ 0 _ _ (fun l' _ hl' => ?_) htele
    have : l' < nF := by simp at hl'; omega
    simp only [if_pos this]
  · -- the bounds read the ordinary slots and the parameters
    intro l τ τ' hag
    by_cases hl : l < nF
    · simp only [if_pos hl]
      obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hl)⟩
      obtain ⟨nd, hnd, hEx⟩ := hxs l x hx
      have hinvl := hinv l nd (by rw [hlen]; exact hl) (by rw [List.getElem?_map]; exact hnd)
      rw [Nat.zero_add] at hinvl
      refine hinvl τ τ' fun i hi => ?_
      by_cases hil : i < l
      · by_cases hoj : ord (l - 1 - i) = true
        · exact (hag i).1 hil hoj
        · exfalso
          rcases hi with ⟨hlt, hocc, -⟩ | ⟨hlt, hpar⟩
          · have hfree := hu4 l (l - 1 - i) x (by omega) hx (by simpa using hoj)
            rw [erasedEq_nestOcc _ _ hEx] at hfree
            rw [show hb + l - 1 - i = hb + (l - 1 - i) by omega,
              show hb + l - i = hb + (l - 1 - i) + 1 by omega, hfree] at hocc
            exact Bool.false_ne_true hocc
          · omega
      · refine (hag i).2 (by omega) ?_
        rcases hi with ⟨hlt, -, hnh⟩ | ⟨hlt, hpar⟩
        · refine ⟨by omega, Nat.lt_of_not_le fun hge => hnh ⟨hlt, ?_, ?_⟩⟩ <;> omega
        · exact ⟨by omega, by omega⟩
    · simp only [if_neg hl]
  · -- the ordinary readings read the ordinary slots and the parameters
    intro i G hGi hoi τ τ' hag
    have hi : i < nF := by
      have := (List.getElem?_eq_some_iff.mp hGi).1
      rw [hNl, hnl'] at this; exact this
    obtain ⟨p, hp⟩ : ∃ p, nds[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨na, hna, hden, hcln, hws, hord⟩ := hN i p.1 (by simp [hp])
    rw [hGi] at hna
    obtain rfl := Option.some.inj hna
    have hkord : ks.getD i .ordinary = .ordinary := by simpa using hoi
    have hholes : NoBVar (holeP (hb + i) nP hb) G :=
      denoteMeta_noBVar_of_nestOcc (m := m) (names := names) _ _ hws (by omega) (hord hkord) hden
    obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hi)⟩
    obtain ⟨nd, hnd, hEx⟩ := hxs i x hx
    have hndp : nd = p.1 := by rw [hp] at hnd; simpa using hnd.symm
    subst hndp
    have hxread : denoteMeta m.acval env φ (hb + i) x.fvarTypeD = some G := by
      rw [denoteMeta_erasedEq hEx]; exact hden
    have hslots : NoBVar (fun q => ∃ jj, jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q) G := by
      refine noBVar_exists' (P := fun jj q => jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        fun jj => ?_
      by_cases hjj : jj < i ∧ ord jj = false
      · have hne : ks.getD jj .ordinary ≠ .ordinary := by simpa [ord] using hjj.2
        exact NoBVar.mono (fun q hq => hq.2.2)
          (u4_fieldSlotAt (m := m) hop hW (hU4 jj (by omega) hne) (by omega) hjj.1 hx hxread)
      · exact NoBVar.mono (fun q hq => absurd ⟨hq.1, hq.2.1⟩ hjj) hholes
    have hbeyond : NoBVar (fun q => hb + i ≤ q) G :=
      NoBVar_of_bvarsBelow (denote_bvarsBelow m.cval_closedL (hb + i) _ hws hcln
        (denoteMeta_erase m.acval_erase (hb + i) _ hden)) fun _ h => h
    refine interp_congr_noBVar _ (noBVar_or (noBVar_or hholes hslots) hbeyond) fun q hq => ?_
    by_cases hqi : q < i
    · refine (hag q).1 hqi (Classical.byContradiction fun hqo => ?_)
      exact hq (Or.inl (Or.inr ⟨i - 1 - q, by omega, Bool.eq_false_iff.mpr hqo, by
        simp only [LfpDatum.fieldSlot]; omega⟩))
    · refine (hag q).2 (by omega) ⟨?_, ?_⟩
      · exact Nat.lt_of_not_le fun hge => hq (Or.inr (by omega))
      · refine Nat.lt_of_not_le fun hge => hq (Or.inl (Or.inl ⟨?_, ?_, ?_⟩))
        · exact Nat.lt_of_not_le fun hge' => hq (Or.inr hge')
        · omega
        · omega

end Tele

/-! ## A frame's constructors, walked -/

/-- What a frame's walk leaves of one constructor, for accessibility
(`CtorWalkedA`, generic): at the frame's depth `hi`, the admissible items
`Qd` and the hole bound `hi`. -/
@[expose] def CtorWalkedAG (m : EnvModel V env) (φ : Name → Nat) (w : Nat) (names : List Name)
    (nP : Nat) (Qd : Nat → Nat → Nat → Prop) (hi : Nat) (us : List Level) (ds : List Expr)
    (nPc : Nat) (sub : Name → List Level → Option Expr) (Δ : List AnnotTerm) (R : FrameRel V)
    (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca, ∃ ks : List ConLeche.PosKind, ∃ nds cur,
    ConLeche.instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
      = some crest ∧
    crest.looseBVarsBounded 0 = true ∧
    denoteMeta m.acval env φ hi crest = some ca ∧
    nds.length = x.2 ∧ cur.looseBVarsBounded 0 = true ∧
    (∀ i, i < x.2 → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds hi cur) 0 i = false) ∧
    ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop nPc).all (fun a => !a.nestOcc names nP hi) = true ∧
    PiAccThenG w nP hi Qd (ResultAt m φ nP hi (hi + x.2) cur) x.2 hi (nds.map (·.1)) R ca ∧
    OutTeleG m φ names nP hi ks (nds.map (·.1)) hi Δ ca

/-- **A frame's accessibility** (`FrameAccOut`, generic): a bound of the
level reading only the parameter positions at the key's depth, and every
group member's carrier at the key frame accessible along the enclosing
relation with enclosing items admissible by `Q₀`. -/
@[expose] def FrameAccOutG (w nP hi : Nat) (Q₀ : Nat → Nat → Prop) (R₀ : FrameRel V)
    (D : LfpDatum V) (ψ : Name → Nat) (dsa : List AnnotTerm) (G : Nat → Prop) : Prop :=
  ∃ A : (Nat → V) → V, (∀ ρ, A ρ ∈ˢ (univ w : V)) ∧ InvOn (ParamPos hi nP) A ∧
    ∀ c, G c → ∀ ρ ρ₀, R₀ ρ ρ₀ → ∀ i, i ∈ˢ D.idx ψ (keyFrame dsa hi ρ) c →
      ∀ x, x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ) c) i →
        ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧
          (∀ b, b ∈ˢ B → Adm Q₀ (g b) ∧ Holds ρ (g b)) ∧
          ∀ ρ', R₀ ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) →
            x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ') c) i

theorem FrameAccOutG.mono {w nP hi : Nat} {Q₀ : Nat → Nat → Prop} {R₀ : FrameRel V}
    {D : LfpDatum V} {ψ : Name → Nat} {dsa : List AnnotTerm} {G G' : Nat → Prop}
    (h : FrameAccOutG w nP hi Q₀ R₀ D ψ dsa G) (hG : ∀ c, G' c → G c) :
    FrameAccOutG w nP hi Q₀ R₀ D ψ dsa G' := by
  obtain ⟨A, hA, hinv, hacc⟩ := h
  exact ⟨A, hA, hinv, fun c hc => hacc c (hG c hc)⟩

section Frame

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

/-- **The frame relation's pairs satisfy the frame's context**: the
enclosing pair satisfies the enclosing context, the group's hole values
their members' former types. -/
theorem frameRelA_dom {Δh : List AnnotTerm} {R₀ : FrameRel V}
    (hdom₀ : ∀ ρ ρ', R₀ ρ ρ' → Sat V Δh ρ ∧ Sat V Δh ρ') :
    ∀ σ σ', frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi σ σ' →
      Sat V ((grpTys mp.base2 φ grp).reverse ++ Δh) σ ∧
      Sat V ((grpTys mp.base2 φ grp).reverse ++ Δh) σ' := by
  rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
  obtain ⟨h1, h2⟩ := hdom₀ ρ ρ' hr
  exact ⟨sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY ρ),
    sat_of_spineFit h2 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY' ρ')⟩

set_option maxHeartbeats 1600000 in
/-- **One constructor of a frame's group is accessible** (`frameCtor_acc`,
generic): the frame's items `Qf` at depth `hi + |grp|`. -/
theorem frameCtor_accG {w : Nat} (hw : w ≠ 0) (hwD : D.w (Level.substFn φ lps us) = w)
    {Qf : Nat → Nat → Nat → Prop}
    (hsh : ∀ d, hi + grp.length ≤ d → ∀ i n, shiftQ (Qf d) i n ↔ Qf (d + 1) i n)
    (hnPhi : ctx.nP ≤ hi)
    {Δh : List AnnotTerm} {R₀ : FrameRel V}
    (hdom₀ : ∀ ρ ρ', R₀ ρ ρ' → Sat V Δh ρ ∧ Sat V Δh ρ')
    (hlrefl₀ : ∀ ρ ρ₀, R₀ ρ ρ₀ → R₀ ρ ρ)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {g j : Nat} (hG : InGrp D grp g) (hj : j < D.nctors g) {cv : ConstantVal} {nF : Nat}
    (hfc : env.find? (D.ctorName g j) = some (.ctorInfo cv ds.length nF))
    (hwk : CtorWalkedAG mp.base2 φ w ctx.names ctx.nP Qf (hi + grp.length)
      us ds ds.length (grpSub us hi grp) ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) (cv, nF)) :
    FrameCtorAcc w (hi + grp.length) ctx.nP (Qf (hi + grp.length)) R₀ D
      (Level.substFn φ lps us) grp dsa hi g j := by
  classical
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD]; exact hw
  obtain ⟨-, crest, ca, ks, nds, cur, hcr, -, hca, hnl, hcurcl, hU4, hres, hidx, hPi, hO⟩ :=
    hwk
  obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
    crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  rw [hca] at hrd
  obtain rfl := Option.some.inj hrd
  have hRAdom := frameRelA_dom mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hdom₀
  have hha := h.holeApp (Level.substFn φ lps us) g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj
  -- the substituted valuation and the hole agreement at a frame and a tuple
  have hvals : ∀ ρ Y, Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) →
      InTupleSpace (D.w (Level.substFn φ lps us)) D.N
        (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
      ∃ vs : List V, substE V (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0
          (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) = consList vs (keyFrame dsa hi ρ) ∧
        HoleAgree D.k ds.length 0
          (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y))
          (consList vs (keyFrame dsa hi ρ)) ∧
        Sat V (D.params (Level.substFn φ lps us) ++ Tys).reverse
          (consList vs (keyFrame dsa hi ρ)) := by
    intro ρ Y hs hY
    have hS := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
      (keyFrame dsa hi ρ) Y ρ
    refine ⟨_, hS, ?_, ?_⟩
    · have hagS := holeAgree_instance mp hD hs ρ (fun mm => decide (InGrp D grp mm)) Y
        (vs := (List.range D.k).map fun mm =>
          if decide (InGrp D grp mm) = true then
            D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y mm
          else interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
        (by simp) (fun m hm => by simp)
      rw [mixT_grp_eq, hlenP] at hagS
      exact hagS
    · exact frameVals_sat mp hD hs hlT hTys (fun mm => decide (InGrp D grp mm)) Y hY ρ
  -- the walked fields are small at every related frame
  have hbd := frame_fieldsBound mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hwD hw hfit hG hj
    hlT hTys hEqF
  have hlenW : (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab).length = nF := by
    rw [substTele_length, hlen]
  obtain ⟨Af, N, hEN, htele, hAf, hF, hRes⟩ := walkTele_accG (m := mp.base2) (φ := φ) hsh hw
    (names := ctx.names) (by omega) hnl hcurcl hU4 hlenW hRAdom hbd hPi hO
  let ord : Nat → Bool := fun l => ks.getD l .ordinary == .ordinary
  -- the substituted result head is the member's hole
  have hhead : ∃ p, ((substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) (D.k - 1 - g)).liftN nF 0
        = .bvar p := by
    have hgk := hG.1
    simp only [substTau, if_pos (show D.k - 1 - g < ds.length + D.k by omega)]
    rw [show ds.length + D.k - 1 - (D.k - 1 - g) = ds.length + g by omega]
    have hr' := (grpS_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (ds.length + g)
      (by omega)).2.2
    unfold grpS at hr'
    rw [if_neg (by omega), show ds.length + g - ds.length = g by omega] at hr'
    obtain ⟨i, hi', hgi⟩ : ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member g := by
      obtain ⟨i, hi', h'⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hG.2)
      exact ⟨i, by simpa using hi', by simpa using h'⟩
    rw [← hgi, grpSub_mem hg.1 hi', Option.getD_some, denoteMeta_fvar] at hr'
    rw [← Option.some.inj hr']
    exact ⟨hi + grp.length - 1 - (hi + i) + nF, by simp⟩
  obtain ⟨p, hp⟩ := hhead
  refine ⟨teleBound w ord Af 0 N, fun σ => teleBound_mem hw _ _ _ _ _, fun σ σ' hq => ?_, ?_⟩
  · refine teleBound_agrM (k := 0) (M0 := ParamPos (hi + grp.length) ctx.nP) hAf N 0
      (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by simpa using ho) τ τ'
        (by simpa using hτ)) σ σ' fun i => ⟨fun h => absurd h (Nat.not_lt_zero _),
          fun _ hm => hq i (by simpa using hm)⟩
  intro ρ ρ₀ Y hR hY t fs hf
  have hRσ : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) :=
    ⟨ρ, ρ, Y, Y, hlrefl₀ ρ ρ₀ hR, hY, hY, rfl, rfl⟩
  obtain ⟨vs, hS, hag, hsat⟩ := hvals ρ Y (hfit ρ ρ₀ hR).1 hY
  have hspN := spineFitN_of_hfits hEqF hEN hha hS (by rw [hlenP]; exact hag) hsat
    (hRAdom _ _ hRσ).1 hf
  obtain ⟨B, gi, hB, hgi, hs⟩ := teleBound_support hw (k := 0) (ord := ord)
    (fun l τ τ' hτ => hAf l τ τ' (hτ.toM _)) N 0 _ _
    (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by rw [Nat.zero_add] at ho; exact ho)
      τ τ' (by rw [Nat.zero_add] at hτ; exact hτ.toM _))
    htele _ hRσ fs hspN
  refine ⟨B, gi, hB, hgi, fun ρ' Y' hR' hY' hheld => ?_⟩
  have hRσL : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := ⟨ρ, ρ', Y, Y', hR', hY, hY', rfl, rfl⟩
  have hL := hs _ hRσL hheld
  obtain ⟨vsL, hSL, hagL, hsatL⟩ := hvals ρ' Y' (hfit ρ ρ' hR').2 hY'
  exact hfits_of_spineFitN hEqF hlen hlenP hp hEN hRes hres hidx hha hRσL hS hSL hag hagL hsat hsatL
    (hRAdom _ _ hRσL).1 (hRAdom _ _ hRσL).2 hf hL

/-- **A frame item is a group occurrence or an enclosing item**
(`frame_item_fwd`, generic): the frame's items split into its own holes and
the enclosing items `Q₀` moved up. -/
theorem frame_item_fwdG {Qf₀ Q₀ : Nat → Nat → Prop}
    (hsplit : ∀ i n, Qf₀ i n → (∃ j, ∃ _ : j < grp.length, i = grp.length - 1 - j ∧
        n = ConLeche.nestArity ctx grp[j].1) ∨ (grp.length ≤ i ∧ Q₀ (i - grp.length) n))
    {ρ Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)
    {o : Occ V} (hQ : Adm Qf₀ o)
    (hH : Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) o) :
    (o.1 < grp.length ∧ InGrp D grp (frameOcc D (Level.substFn φ lps us) grp o).1 ∧
      InTup D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y
        (frameOcc D (Level.substFn φ lps us) grp o) ∧
      SpineFit (fun j => ρ (j + hi))
        (D.pars (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)
          ++ D.ids (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)) o.2.1) ∨
    (grp.length ≤ o.1 ∧ Adm Q₀ (o.1 - grp.length, o.2) ∧ Holds ρ (o.1 - grp.length, o.2)) := by
  obtain ⟨i, vs, y⟩ := o
  have hkNN := (mp.lfp_ok D hD).1.kN
  rcases hsplit i vs.length hQ with ⟨j, hjl, rfl, hn⟩ | ⟨hle, hQo⟩
  · -- a new hole
    have hjk : (grp.getD (grp.length - 1 - (grp.length - 1 - j)) default) = grp[j] := by
      rw [show grp.length - 1 - (grp.length - 1 - j) = j by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    have hmem : grp[j] ∈ grp := List.getElem_mem hjl
    have hck := grp_idx_lt mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hmem
    have har := grp_arity mp hD hnN hkN hfind hg (Level.substFn φ lps us) _ hmem
    unfold Holds at hH
    simp only at hH
    rw [frameVal_lt ρ Y (by omega), hjk] at hH
    unfold frameOcc
    simp only
    rw [hjk]
    refine Or.inl ⟨by omega, grp_inGrp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hmem, ?_⟩
    rcases grp_hole_full mp hD hdsa hlenP hck ρ Y (vs := vs) (by rw [← har, hn]) with
      ⟨hfit, he⟩ | he
    · rw [he] at hH
      refine ⟨⟨by omega, Classical.byContradiction fun hni => ?_, hH⟩, hfit⟩
      rw [app_off_dom_of_mem_piSet (hY _ (by omega)) hni] at hH
      exact not_mem_empty _ hH
    · rw [he] at hH; exact absurd hH (not_mem_empty _)
  · exact Or.inr ⟨hle, hQo, (holds_frameVal_ge hle).mp hH⟩

set_option maxHeartbeats 1600000 in
/-- **The frame's accessibility from its constructors'** (`frameAccOut_of`,
generic). -/
theorem frameAccOut_ofG {w : Nat} (hw : w ≠ 0) (hnPhi : ctx.nP ≤ hi)
    {Qf₀ Q₀ : Nat → Nat → Prop}
    (hsplit : ∀ i n, Qf₀ i n → (∃ j, ∃ _ : j < grp.length, i = grp.length - 1 - j ∧
        n = ConLeche.nestArity ctx grp[j].1) ∨ (grp.length ≤ i ∧ Q₀ (i - grp.length) n))
    {R₀ : FrameRel V} (hagree : R₀.AgreesOff (holeP hi ctx.nP hi)) (hsymm₀ : R₀.Symm)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    (hper : ∀ g j, InGrp D grp g → j < D.nctors g →
      FrameCtorAcc w (hi + grp.length) ctx.nP Qf₀ R₀ D (Level.substFn φ lps us) grp dsa hi g j) :
    FrameAccOutG w ctx.nP hi Q₀ R₀ D (Level.substFn φ lps us) dsa (InGrp D grp) := by
  classical
  haveI : Nonempty (Occ V) := ⟨(0, [], empty)⟩
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  -- the constructors' bounds, as functions
  let TBt : Nat → Nat → (Nat → V) → V := fun g j =>
    if hgj : InGrp D grp g ∧ j < D.nctors g then Classical.choose (hper g j hgj.1 hgj.2)
    else fun _ => empty
  have hTB : ∀ g j (hG : InGrp D grp g) (hj : j < D.nctors g),
      (∀ σ, TBt g j σ ∈ˢ (univ w : V)) ∧
      (∀ σ σ', (∀ q, ParamPos (hi + grp.length) ctx.nP q → σ q = σ' q) → TBt g j σ = TBt g j σ') ∧
      ∀ ρ ρ₀ Y, R₀ ρ ρ₀ → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
        ∀ t fs, D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y) t g j fs →
          ∃ (B : V) (gi : V → Occ V),
            B ⊆ˢ TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) ∧
            (∀ b, b ∈ˢ B → Adm Qf₀ (gi b) ∧
              Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) (gi b)) ∧
            ∀ ρ' Y', R₀ ρ ρ' → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
                (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y' →
              (∀ b, b ∈ˢ B → Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') (gi b)) →
              D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
                (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y')
                t g j fs := by
    intro g j hG hj
    have e : TBt g j = Classical.choose (hper g j hG hj) := by
      simp only [TBt, dif_pos (show InGrp D grp g ∧ j < D.nctors g from ⟨hG, hj⟩)]
    rw [e]
    exact Classical.choose_spec (hper g j hG hj)
  have hTBsz : ∀ g j σ, TBt g j σ ∈ˢ (univ w : V) := by
    intro g j σ
    by_cases hgj : InGrp D grp g ∧ j < D.nctors g
    · exact (hTB g j hgj.1 hgj.2).1 σ
    · simp only [TBt, dif_neg hgj]; exact empty_mem_univ w
  -- the frame valuations of two frames agreeing at the parameters agree at the parameters
  have hpar : ∀ (ρ ρ' Y Y' : Nat → V), (∀ q, ParamPos hi ctx.nP q → ρ q = ρ' q) →
      ∀ q, ParamPos (hi + grp.length) ctx.nP q →
        frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y q
          = frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y' q := by
    intro ρ ρ' Y Y' hag q hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + grp.length := ⟨q - grp.length, by omega⟩
    rw [frameVal_ge, frameVal_ge]
    exact hag r ⟨by omega, by omega⟩
  have hTBeq : ∀ g j (ρ ρ' Y Y' : Nat → V), (∀ q, ParamPos hi ctx.nP q → ρ q = ρ' q) →
      TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
        = TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := by
    intro g j ρ ρ' Y Y' hag
    by_cases hgj : InGrp D grp g ∧ j < D.nctors g
    · exact (hTB g j hgj.1 hgj.2).2.1 _ _ (hpar ρ ρ' Y Y' hag)
    · simp only [TBt, dif_neg hgj]
  -- the bound
  let A0 : (Nat → V) → V := fun ρ =>
    LfpDatum.finUnion (fun c => LfpDatum.finUnion (fun j => TBt c j
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))) (D.nctors c)) D.N
  have hA0 : ∀ ρ, A0 ρ ∈ˢ (univ w : V) := fun ρ =>
    LfpDatum.finUnion_mem hw fun c _ => LfpDatum.finUnion_mem hw fun j _ => hTBsz c j _
  -- the relation's tails and index sets
  have hagree' : ∀ ρ ρ', R₀ ρ ρ' → AgreeOff (holeP hi ctx.nP hi) ρ ρ' := hagree
  have htail : ∀ ρ ρ', R₀ ρ ρ' → (fun j => ρ (j + hi)) = (fun j => ρ' (j + hi)) := by
    intro ρ ρ' hr; funext j
    exact hagree' ρ ρ' hr (j + hi) fun hp => by have := hp.1; omega
  have hIs : ∀ p p', R₀ p p' → ∀ m, InGrp D grp m →
      D.idx (Level.substFn φ lps us) (keyFrame dsa hi p) m
        = D.idx (Level.substFn φ lps us) (keyFrame dsa hi p') m :=
    fun p p' hr m hm => grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hm
      (hagree' p p' hr)
  -- the joint accessibility
  have hacc : AccJointG (D.w (Level.substFn φ lps us)) D.N
      (fun p => D.idx (Level.substFn φ lps us) (keyFrame dsa hi p)) (fun p => ∃ p₀, R₀ p p₀) R₀
      (fun p o => Adm Q₀ o ∧ Holds p o) (InGrp D grp)
      (fun p Y => D.Φ (Level.substFn φ lps us) (keyFrame dsa hi p)
        (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)) Y)) A0 := by
    rintro p Y ⟨p₀, hp⟩ hY m hm hGm i hiI x hx
    have hs := (hfit p p₀ hp).1
    have hmixS := mixT_mem (G := InGrp D grp)
      (C := D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)) (lfpTuple_mem _ _ _ _) hY
    obtain ⟨j, fs, hf, rfl⟩ := (h.fibre _ _ hs _ hmixS m hm i hiI x).mp hx
    have hj := hf.1
    obtain ⟨-, -, hsup⟩ := hTB m j hGm hj
    obtain ⟨B, gi, hB, hgi, htr⟩ := hsup p p₀ Y hp hY i fs hf
    let item : V → Occ V ⊕ (Nat × V × V) := fun b =>
      if (gi b).1 < grp.length then .inr (frameOcc D (Level.substFn φ lps us) grp (gi b))
      else .inl ((gi b).1 - grp.length, (gi b).2)
    refine ⟨B, item, fun b hb => ?_, fun b hb => ?_, ?_⟩
    · have hb' := hB b hb
      rw [hTBeq m j p p Y (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p))
        fun _ _ => rfl] at hb'
      exact LfpDatum.subset_finUnion (f := fun c => LfpDatum.finUnion (fun j => TBt c j
        (frameVal D (Level.substFn φ lps us) grp dsa hi p
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)))) (D.nctors c)) hm _
        (LfpDatum.subset_finUnion (f := fun j => TBt m j
          (frameVal D (Level.substFn φ lps us) grp dsa hi p
            (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)))) hj _ hb')
    · obtain ⟨hQ, hH⟩ := hgi b hb
      rcases frame_item_fwdG mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hsplit hY hQ hH with
        ⟨hlt, hGc, hin, -⟩ | ⟨hge, hQo, hHo⟩
      · simp only [item, if_pos hlt]; exact ⟨hGc, hin⟩
      · simp only [item, if_neg (show ¬ (gi b).1 < grp.length by omega)]; exact ⟨hQo, hHo⟩
    · rintro p' Y' hR' ⟨p₀', hp'⟩ hY' hitems
      have hf' := htr p' Y' hR' hY' fun b hb => by
        obtain ⟨hQ, hH⟩ := hgi b hb
        have hib := hitems b hb
        rcases frame_item_fwdG mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hsplit hY hQ hH
          with ⟨hlt, hGc, -, hfit0⟩ | ⟨hge, -, -⟩
        · simp only [item, if_pos hlt] at hib
          refine frame_item_bwd mp hD hdsa hlenP hlt hGc.1 ?_ hib.2
          rw [← htail p p' hR']; exact hfit0
        · simp only [item, if_neg (show ¬ (gi b).1 < grp.length by omega)] at hib
          exact (holds_frameVal_ge hge).mpr hib.2
      have hmixS' := mixT_mem (G := InGrp D grp)
        (C := D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p')) (lfpTuple_mem _ _ _ _) hY'
      exact (h.fibre _ _ (hfit p' p₀' hp').1 _ hmixS' m hm i
        (by rw [← hIs p p' hR' m hGm]; exact hiI) _).mpr ⟨j, fs, hf', rfl⟩
  have hmain := lfpP_acc_group (O := Occ V) hIs
    (fun p ⟨p₀, hp⟩ => ⟨_, mixT_isClosed (G := InGrp D grp)
      (h.functor _ _ (hfit p p₀ hp).1).2.2 (h.functor _ _ (hfit p p₀ hp).1).1⟩)
    (fun p ⟨p₀, hp⟩ => mixT_monoTuple (G := InGrp D grp) (h.functor _ _ (hfit p p₀ hp).1).1
      (lfpTuple_mem _ _ _ _)) hacc
  -- the carrier on the group is the mixed operator's least tuple
  have hcarr : ∀ ρ ρ₀, R₀ ρ ρ₀ → ∀ c, InGrp D grp c →
      lfpTuple (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ))
          (fun Y => D.Φ (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)) c
        = D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ) c := by
    intro ρ ρ₀ hr c hc
    obtain ⟨hmono0, -, hcl0⟩ := h.functor _ _ (hfit ρ ρ₀ hr).1
    exact lfpTuple_mixT hcl0 hmono0 c (Nat.lt_of_lt_of_le hc.1 hkNN) hc
  refine ⟨fun ρ => accPaths (A0 ρ), fun ρ => accPaths_mem hw (hA0 ρ), fun ρ ρ' hag => ?_, ?_⟩
  · show accPaths (A0 ρ) = accPaths (A0 ρ')
    have : A0 ρ = A0 ρ' := by
      show LfpDatum.finUnion _ _ = LfpDatum.finUnion _ _
      congr 1; funext c; congr 1; funext j
      exact hTBeq c j ρ ρ' _ _ hag
    rw [this]
  · intro c hc ρ ρ₀ hr i hiI x hx
    rw [← hcarr ρ ρ₀ hr c hc] at hx
    obtain ⟨B, g, hB, hg', htr⟩ := hmain ρ ⟨ρ₀, hr⟩ c (Nat.lt_of_lt_of_le hc.1 hkNN) hc i hiI x hx
    refine ⟨B, g, hB, hg', fun ρ' hr' hheld => ?_⟩
    have hx' := htr ρ' hr' ⟨ρ, hsymm₀ ρ ρ' hr'⟩ fun b hb => ⟨(hg' b hb).1, hheld b hb⟩
    rwa [hcarr ρ' ρ (hsymm₀ ρ ρ' hr') c hc] at hx'

set_option maxHeartbeats 1600000 in
/-- **A frame's constructors make it accessible** (`frameIterAcc`, generic;
the accessibility twin of `frameIterGen`): the enclosing relation read
through its context, its agreement off the holes, symmetry and left
reflexivity; the admissible items of the frame `Qf` (shifting under binders,
splitting into the frame's own holes and the enclosing `Q₀`); the
constructors' walk given AT the frame relation. -/
theorem frameIterAccG (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0)
    (hwD : D.w (Level.substFn φ lps us) = w) {F : Nat}
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2))
    (hnPhi : ctx.nP ≤ hi) {Qf : Nat → Nat → Nat → Prop} {Q₀ : Nat → Nat → Prop}
    (hsh : ∀ d, hi + grp.length ≤ d → ∀ i n, shiftQ (Qf d) i n ↔ Qf (d + 1) i n)
    (hsplit : ∀ i n, Qf (hi + grp.length) i n → (∃ j, ∃ _ : j < grp.length,
        i = grp.length - 1 - j ∧ n = ConLeche.nestArity ctx grp[j].1) ∨
      (grp.length ≤ i ∧ Q₀ (i - grp.length) n))
    {Δh : List AnnotTerm} {R₀ : FrameRel V}
    (hdom₀ : ∀ ρ ρ', R₀ ρ ρ' → Sat V Δh ρ ∧ Sat V Δh ρ')
    (hagree : R₀.AgreesOff (holeP hi ctx.nP hi)) (hsymm₀ : R₀.Symm)
    (hlrefl₀ : ∀ ρ ρ₀, R₀ ρ ρ₀ → R₀ ρ ρ) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hwalk : ∀ (Q : ConstantVal × Nat → Prop),
      (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
        instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
          (grpSub us hi grp)) = some crest →
        (∃ ty, ConLeche.inferTypeCore .verified env F (hi + grp.length) crest = .ok ty) →
        ∃ ca, Frame (hi + grp.length) crest ∧
          CtxOkP mp.base2 φ (hi + grp.length) ((grpTys mp.base2 φ grp).reverse ++ Δh) crest ∧
          denoteMeta mp.base2.acval env φ (hi + grp.length) crest = some ca ∧
          Graded V ((grpTys mp.base2 φ grp).reverse ++ Δh) ca ∧
          TeleSmall w x.2 (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) ca) →
      (∀ x ∈ ctors, Q x) →
      ∀ x ∈ ctors, CtorWalkedAG mp.base2 φ w ctx.names ctx.nP Qf (hi + grp.length) us ds
        ds.length (grpSub us hi grp) ((grpTys mp.base2 φ grp).reverse ++ Δh)
        (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) x) :
    FrameAccOutG w ctx.nP hi Q₀ R₀ D (Level.substFn φ lps us) dsa (InGrp D grp) := by
  have hQ := grpCtors_found hg hcov hgc
  have hRAdom := frameRelA_dom mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hdom₀
  have hwalked := hwalk
    (fun x => ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2))
    (fun x crest hQx hcr hinf => by
      obtain ⟨c, j, hGc, hj, hfc⟩ := hQx
      have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
      have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
      have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0 = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      obtain ⟨hfr, hC⟩ := crest_frame mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hΔ hCds hLds
        hcl hbb hcr
      obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
        crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hGc.1 hj hfc
      rw [hcr] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨ty, hty⟩ := hinf
      have hIS : InferSemFull mp.base2 φ (hi + grp.length) crest ty :=
        infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty)
      obtain ⟨-, -, -, -, hgr, -⟩ := hIS hfr hC.toCtxOk hrd
      refine ⟨_, hfr, hC, hrd, hgr, ?_⟩
      have hlW : (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab).length = x.2 := by
        rw [substTele_length, hlen]
      rw [← hlW]
      exact teleSmall_mkPisAV hw _ _ _ _ _ (FieldsEqOn.refl _ _) hRAdom
        (frame_fieldsBound mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hwD hw hfit hGc hj
          hlT hTys hEqF))
    hQ
  refine frameAccOut_ofG mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hw hnPhi hsplit hagree
    hsymm₀ hfit fun g j hG hj => ?_
  obtain ⟨x, hxmem, hfc⟩ := grpCtor_found hcov hgc hG hj
  exact frameCtor_accG mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hw hwD hsh hnPhi hdom₀
    hlrefl₀ hfit hG hj hfc (hwalked _ hxmem)

end Frame

end ConLeche.Model
