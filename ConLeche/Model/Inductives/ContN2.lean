module

import ConLeche.Model.OpenedCtx
import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Env.EnvModelM
import ConLeche.Semantics.SubstAV
public import ConLeche.Model.Reading.SubstFvars
public import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Reading.Levels
public import ConLeche.Model.Inductives.FamilyRun
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# N2 read semantically: a container instance's index telescope is hole-free

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

open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The syntactic side -/

/-- A Π-telescope ending in a sort whose domains mention no hole. -/
@[expose] def PiDomsFree (names : List Name) (lo hi : Nat) : Expr → Prop
  | .forallE ty b => ty.nestOcc names lo hi = false ∧ PiDomsFree names lo hi b
  | .sort _ => True
  | _ => False

/-- The number of leading `∀` binders. -/
@[expose] def piCount : Expr → Nat
  | .forallE _ b => piCount b + 1
  | _ => 0

theorem piDomsFree_of_binders {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr) {s : Level}, e.piBinders.2 = .sort s →
      (e.piBinders.1.any fun b => b.nestOcc names lo hi) = false → PiDomsFree names lo hi e := by
  intro e
  induction e with
  | forallE ty b _ ihb =>
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
  | forallE t b _ ihb =>
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
  | forallE t b _ ihb => intro k; simp only [ConLeche.Expr.instantiate1, piCount, ihb]
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; rfl

/-! ## The reading -/

theorem NoBVarTele.mono :
    ∀ {Fs : List Term} {P Q : Nat → Prop}, (∀ i, Q i → P i) → NoBVarTele P Fs →
      NoBVarTele Q Fs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, ⟨h1, h2⟩ => ⟨NoBVar.mono h h1, NoBVarTele.mono (shiftP_mono h) h2⟩

/-- **A hole-free telescope reads hole-free**: the reading of a
Π-telescope ending in a sort whose domains mention no hole is a Π-tower
ending in a sort whose every domain mentions no hole position. -/
theorem noBVarTele_of_piDomsFree {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : Term}, piCount e = n →
      PiDomsFree names lo hi e → Expr.WScoped d e → hi ≤ d →
      denote m.acval env φ d e = some ea →
      ∃ (ab : List Term) (u : Nat), ea = mkPisAV ab (.sort u) ∧
        NoBVarTele (holeP d lo hi) ab ∧ ab.length = n := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hf _ _ h
    match e, hn, hf, h with
    | .sort s, _, _, h =>
      rw [denote_sort] at h
      exact ⟨[], _, (Option.some.inj h).symm, trivial, rfl⟩
  | succ n ih =>
    intro e d ea hn hf hws hd h
    match e, hn, hf, hws, h with
    | .forallE ty b, hn, hf, hws, h =>
      obtain ⟨hty, hb⟩ := hf
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv h
      simp only [Expr.WScoped] at hws
      have hA : NoBVar (holeP d lo hi) ta := denote_noBVar_of_nestOcc d ty hws.1 hd hty hta
      have hnot : ¬ (lo ≤ d ∧ d < hi) := by omega
      obtain ⟨ab, u, rfl, hab, hlen⟩ := ih (b.instantiate1 (.fvar d ty))
        (by rw [piCount_instantiate1_fvar]; exact hn)
        (PiDomsFree.instantiate1 hnot ty b 0 hb)
        (Expr.WScoped.instantiate1 hws.1 0 hws.2) (by omega) hba
      exact ⟨ta :: ab, u, rfl, ⟨hA, NoBVarTele.mono holeP_succ hab⟩, by simp [hlen]⟩

/-! ## Telescopes read the same at two frames -/

/-- Two frames read a telescope the same, progressively (at every value
of the earlier binders). -/
@[expose] def TeleEq (ρ ρ' : Nat → V) : List Term → Prop
  | [] => True
  | F :: Fs => interp V ρ F = interp V ρ' F ∧ ∀ a, TeleEq (cons a ρ) (cons a ρ') Fs

theorem TeleEq.teleOfFields : ∀ {Fs : List Term} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    teleOfFields ρ Fs = teleOfFields ρ' Fs
  | [], _, _, _ => rfl
  | _ :: Fs, _, _, ⟨h1, h2⟩ => by
    simp only [teleOfFields_cons, h1]
    congr 1
    funext a
    exact TeleEq.teleOfFields (Fs := Fs) (h2 a)

private theorem hasSigmaPairs_idxSet (u : Nat) (ρ : Nat → V) (F : Term) (Fs : List Term) :
    HasSigmaPairs (interp V ρ F) fun a => idxSet u (cons a ρ) Fs :=
  hasSigmaPairs_of_defFun1
    (DefFun.towerSet_apply u ((defTeleS_teleOfFields ρ Fs 1).congr fun v => by
      rw [Semantics.prepend_one]))

private theorem idxSet_cons (u : Nat) (ρ : Nat → V) (F : Term) (Fs : List Term) :
    idxSet u ρ (F :: Fs) = sigmaSet u (interp V ρ F) (fun a => idxSet u (cons a ρ) Fs)
      (hasSigmaPairs_idxSet u ρ F Fs) :=
  Tower.towerSet_cons (fun a => hasTeleS_teleOfFields u (cons a ρ) Fs)
    (hasSigmaPairs_idxSet u ρ F Fs)

theorem TeleEq.idxSet {u : Nat} : ∀ {Fs : List Term} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    idxSet u ρ Fs = idxSet u ρ' Fs
  | [], _, _, _ => rfl
  | F :: Fs, ρ, ρ', ⟨h1, h2⟩ => by
    rw [idxSet_cons, idxSet_cons]
    exact sigmaSet_ext h1 _ _ fun x _ => TeleEq.idxSet (h2 x)

theorem TeleEq.spineFit : ∀ {Fs : List Term} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    ∀ as : List V, SpineFit ρ Fs as ↔ SpineFit ρ' Fs as
  | [], _, _, _, [] => Iff.rfl
  | [], _, _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, _, [] => Iff.rfl
  | _ :: Fs, _, _, ⟨h1, h2⟩, a :: as => by
    show (_ ∧ _) ↔ (_ ∧ _)
    rw [h1, TeleEq.spineFit (Fs := Fs) (h2 a) as]

theorem TeleEq.holeFam : ∀ {Fs : List Term} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    ∀ (g : List V → V) {hg : DefHoleFn Fs.length g}, holeFam ρ Fs g hg = holeFam ρ' Fs g hg
  | [], _, _, _, _, _ => by rw [holeFam_nil, holeFam_nil]
  | _ :: Fs, _, _, ⟨h1, h2⟩, g, hg => by
    rw [holeFam_cons, holeFam_cons]
    exact lamV_ext h1 _ _ fun a _ => TeleEq.holeFam (Fs := Fs) (h2 a) _ (hg := hg.cons a)

/-! ## Telescopes of one tower value at two frames

The block's index telescope and a run's are compared by value only (`familyRead`): two Π-towers
over sorts of one value have one set of fits (`spineFit_iff_of_mkPisAV_eq`), and what a hole value
or an index set reads of a telescope is fixed by its fits and by its domains along them. -/

/-- **A λ-tower over a telescope with no fit is the point.** -/
theorem holeFam_of_noFit : ∀ {ρ : Nat → V} {Fs : List Term} (g : List V → V)
    {hg : DefHoleFn Fs.length g}, (∀ vs, ¬ SpineFit ρ Fs vs) → holeFam ρ Fs g hg = pt
  | _, [], _, _, h => absurd trivial (h [])
  | _, _ :: _, g, hg, h => by
    rw [holeFam_cons]
    exact lamV_eq_pt fun x hx =>
      holeFam_of_noFit (fun as => g (x :: as)) (hg := hg.cons x) fun vs hvs => h (x :: vs) ⟨hx, hvs⟩

/-- **Hole values over telescopes of one tower value are one**: along a fit the domains and the
fibres agree (`mkPisAV_cons_eq`), elsewhere both are the point. -/
theorem holeFam_of_mkPisAV_eq : ∀ {Fs Fs' : List Term} {ρ ρ' : Nat → V} {n n' : Nat}
    (hl : Fs.length = Fs'.length),
    interp V ρ (mkPisAV Fs (.sort n)) = interp V ρ' (mkPisAV Fs' (.sort n')) →
    ∀ (g : List V → V) {hg : DefHoleFn Fs.length g},
      holeFam ρ Fs g hg = holeFam ρ' Fs' g (hl ▸ hg)
  | [], [], _, _, _, _, _, _, _, _ => by rw [holeFam_nil, holeFam_nil]
  | F :: Fs, F' :: Fs', ρ, ρ', n, n', hl, h, g, hg => by
    by_cases hfit : ∃ vs, SpineFit ρ (F :: Fs) vs
    · obtain ⟨vs, hvs⟩ := hfit
      obtain ⟨hA, hfib⟩ := mkPisAV_cons_eq h hvs
      rw [holeFam_cons, holeFam_cons]
      refine lamV_ext hA _ _ fun x hx => ?_
      exact holeFam_of_mkPisAV_eq (Fs := Fs) (Fs' := Fs')
        (by simpa using hl) (hfib x hx) (fun as => g (x :: as)) (hg := hg.cons x)
    · have hfit' : ∀ vs, ¬ SpineFit ρ' (F' :: Fs') vs := fun vs hvs =>
        hfit ⟨vs, (spineFit_of_mkPisAV_eq hl.symm h.symm hvs).1⟩
      rw [holeFam_of_noFit g (hg := hg) fun vs hvs => hfit ⟨vs, hvs⟩,
        holeFam_of_noFit g (hg := hl ▸ hg) hfit']
  | [], _ :: _, _, _, _, _, hl, _, _, _ => nomatch hl
  | _ :: _, [], _, _, _, _, hl, _, _, _ => nomatch hl

/-- **An index set over a telescope with no fit is empty.** -/
theorem not_mem_idxSet_of_noFit {u : Nat} : ∀ {ρ : Nat → V} {Fs : List Term},
    (∀ vs, ¬ SpineFit ρ Fs vs) → ∀ z, ¬ z ∈ˢ idxSet u ρ Fs
  | _, [], h, _, _ => h [] trivial
  | ρ, F :: Fs, h, z, hz => by
    have hB : ∀ x, x ∈ˢ interp V ρ F → ∀ y, ¬ y ∈ˢ idxSet u (cons x ρ) Fs := fun x hx =>
      not_mem_idxSet_of_noFit fun vs hvs => h (x :: vs) ⟨hx, hvs⟩
    rw [idxSet_cons] at hz
    by_cases hu : u = 0
    · subst hu
      rw [sigmaSet_zero, mem_truthVal] at hz
      obtain ⟨⟨x, hx, y, hy⟩, -⟩ := hz
      exact hB x hx y hy
    · rw [sigmaSet_pos hu, mem_sigmaPairs] at hz
      obtain ⟨x, hx, y, hy, -⟩ := hz
      exact hB x hx y hy

/-- **Index sets over telescopes of one tower value are one.** -/
theorem idxSet_of_mkPisAV_eq {u : Nat} : ∀ {Fs Fs' : List Term} {ρ ρ' : Nat → V} {n n' : Nat},
    Fs.length = Fs'.length →
    interp V ρ (mkPisAV Fs (.sort n)) = interp V ρ' (mkPisAV Fs' (.sort n')) →
    idxSet u ρ Fs = idxSet u ρ' Fs'
  | [], [], _, _, _, _, _, _ => rfl
  | F :: Fs, F' :: Fs', ρ, ρ', n, n', hl, h => by
    by_cases hfit : ∃ vs, SpineFit ρ (F :: Fs) vs
    · obtain ⟨vs, hvs⟩ := hfit
      obtain ⟨hA, hfib⟩ := mkPisAV_cons_eq h hvs
      rw [idxSet_cons, idxSet_cons]
      exact sigmaSet_ext hA _ _ fun x hx => idxSet_of_mkPisAV_eq (by simpa using hl) (hfib x hx)
    · have hfit' : ∀ vs, ¬ SpineFit ρ' (F' :: Fs') vs := fun vs hvs =>
        hfit ⟨vs, (spineFit_of_mkPisAV_eq hl.symm h.symm hvs).1⟩
      exact SetTheory.ext fun z =>
        ⟨fun hz => absurd hz (not_mem_idxSet_of_noFit (fun vs hvs => hfit ⟨vs, hvs⟩) z),
         fun hz => absurd hz (not_mem_idxSet_of_noFit hfit' z)⟩
  | [], _ :: _, _, _, _, _, hl, _ => nomatch hl
  | _ :: _, [], _, _, _, _, hl, _ => nomatch hl

/-- **A telescope read the same at two frames has one tower value there.** -/
theorem TeleEq.tower {B : Term} : ∀ {Fs : List Term} {ρ ρ' : Nat → V}, TeleEq ρ ρ' Fs →
    (∀ σ σ', interp V σ B = interp V σ' B) →
    interp V ρ (mkPisAV Fs B) = interp V ρ' (mkPisAV Fs B)
  | [], ρ, ρ', _, hB => hB ρ ρ'
  | F :: Fs, ρ, ρ', ⟨h1, h2⟩, hB => by
    show interp V ρ (.pi F (mkPisAV Fs B)) = interp V ρ' (.pi F (mkPisAV Fs B))
    rw [interp_pi, interp_pi, h1]
    exact piV_congr _ _ fun x _ => TeleEq.tower (h2 x) hB

/-- A telescope mentioning no position of `P` reads the same at frames
agreeing off `P`. -/
theorem teleEq_of_noBVarTele : ∀ {Fs : List Term} {P : Nat → Prop} {ρ ρ' : Nat → V},
    NoBVarTele P Fs → AgreeOff P ρ ρ' → TeleEq ρ ρ' Fs
  | [], _, _, _, _, _ => trivial
  | F :: _, _, _, _, ⟨h1, h2⟩, hag =>
    ⟨interp_congr_noBVar F h1 hag, fun a => teleEq_of_noBVarTele h2 (agreeOff_cons hag a)⟩

/-- A substituted telescope reads the same exactly where the telescope
does at the substituted frames. -/
theorem teleEq_substTele (τ : Nat → Term) : ∀ (ab : List Term) (k : Nat)
    {ρ ρ' : Nat → V}, TeleEq ρ ρ' (Term.substTele τ k ab) →
    TeleEq (substE V τ k ρ) (substE V τ k ρ') ab
  | [], _, _, _, _ => trivial
  | d :: ab, k, ρ, ρ', ⟨h1, h2⟩ => by
    refine ⟨?_, fun a => ?_⟩
    · have := h1
      simp only [interp_substAV] at this
      exact this
    · have := teleEq_substTele τ ab (k + 1) (h2 a)
      rwa [← cons_substE, ← cons_substE] at this

/-! ## Small syntactic facts -/

theorem piCount_eq_length : ∀ e : Expr, piCount e = e.piBinders.1.length := by
  intro e
  induction e with
  | forallE t b _ ihb => simp [piCount, ConLeche.Expr.piBinders, ihb]
  | _ => simp [piCount, ConLeche.Expr.piBinders]

/-- A Π-tower over a sort determines its domains and its sort. -/
theorem mkPisAV_sort_eq : ∀ {ab ab' : List Term} {u u' : Nat},
    mkPisAV ab (.sort u) = mkPisAV ab' (.sort u') →
      ab = ab' ∧ u = u'
  | [], [], _, _, h => ⟨rfl, by simpa [mkPisAV] using h⟩
  | [], _ :: _, _, _, h => by simp [mkPisAV] at h
  | _ :: _, [], _, _, h => by simp [mkPisAV] at h
  | d :: ab, d' :: ab', u, u', h => by
    simp only [mkPisAV, Term.pi.injEq] at h
    obtain ⟨h1, h4⟩ := h
    obtain ⟨h2, rfl⟩ := mkPisAV_sort_eq h4
    exact ⟨by rw [h1, h2], rfl⟩

/-- The parameter frame of a key: its parameters' values over the frame
seen from the walk's hole bound. -/
theorem consList_map_apply (vs : List V) (τ : Nat → V) (q : Nat) :
    consList vs τ q = if q < vs.length then vs.getD (vs.length - 1 - q) pt
      else τ (q - vs.length) := by
  by_cases hq : q < vs.length
  · rw [ite_eq_left hq]
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
  · rw [ite_eq_right hq]
    obtain ⟨j, rfl⟩ : ∃ j, q = j + vs.length := ⟨q - vs.length, by omega⟩
    rw [consList_apply_add, Nat.add_sub_cancel]

theorem substTele_length (τ : Nat → Term) :
    ∀ (k : Nat) (ab : List Term), (Term.substTele τ k ab).length = ab.length
  | _, [] => rfl
  | k, _ :: ab => by simp [Term.substTele, substTele_length τ (k + 1) ab]

theorem substFvars_of_not_hasFvar {b D : Nat} {s : Nat → Expr} :
    ∀ {e : Expr}, e.hasFvar = false → Expr.substFvars b D s e = e := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.substFvars, Expr.hasFvar]

/-- The parameter frame of a key at a walk valuation `ρ` (the walk's
hole bound `hi`): the key's parameter readings over the frame below. -/
@[expose] noncomputable def keyFrame (dsa : List Term) (hi : Nat) (ρ : Nat → V) : Nat → V :=
  consList (dsa.map (interp V ρ)) (fun j => ρ (j + hi))

theorem keyFrame_eq_substE {dsa : List Term} {hi nP : Nat} (hl : dsa.length = nP)
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

/-- A Π-telescope instantiated at variables strips as many binders. -/
theorem stripPis_isSome_of_instPisWith_fvars :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ∃ i ty, a = .fvar i ty) →
      ConLeche.instPisWith as e = some r → (e.stripPis as.length).isSome = true
  | [], _, _, _, _ => rfl
  | a :: as, e, r, hv, h => by
    match e, h with
    | .forallE t b, h =>
      have h' : ConLeche.instPisWith as (b.instantiate1 a) = some r := h
      obtain ⟨i, ty, rfl⟩ := hv a List.mem_cons_self
      have ih := stripPis_isSome_of_instPisWith_fvars
        (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h'
      have hb := ConLeche.Verify.stripPis_instantiate1_fvar_isSome_rev _ 0 ih
      simp only [List.length_cons, Expr.stripPis]
      cases hs : b.stripPis as.length with
      | none => rw [hs] at hb; exact nomatch hb
      | some _ => rfl

/-- **A closed telescope, instantiated, read** (the canonical opening, substituted at the key's
parameters — one `Expr.substFvars`, read by `denote_substFvars`): a closed type reading at the
levels `us` as a Π-tower over a sort, with its first binders instantiated at `ds` (depth `hi`),
reads at `hi` as the rest of the tower substituted at the parameters' readings. -/
theorem instTele_read (mp : EnvModelM V env) {ty : Expr} (hcl : ty.hasFvar = false)
    {lps : List Name} {hi : Nat} {us : List Level} {ds : List Expr}
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List Term} (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
    {ab : List Term} {u : Nat}
    (hta : denote mp.base2.acval env (Level.substFn φ lps us) 0 ty = some (mkPisAV ab (.sort u)))
    (habl : ds.length ≤ ab.length)
    (hstrip : (ty.stripPis ds.length).isSome = true) {cty : Expr}
    (hty : ConLeche.instPisWith ds (ty.instantiateLevelParams lps us) = some cty) :
    denote mp.base2.acval env φ hi cty
      = some (mkPisAV (Term.substTele (substTau ds.length hi fun i => dsa.getD i default) 0
          (ab.drop ds.length)) (.sort u)) := by
  generalize hψ : Level.substFn φ lps us = ψ at hta
  -- the canonical opening of the container's parameters
  obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis_isSome ds.length 0 hstrip
  have hio := instPisWith_of_openPis ds.length hop
  have hEq : Expr.ErasedEqL fvs (canonParams ds.length) :=
    erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ConLeche.openPisAtFvars_index _ _ _ hop i x hx)
      (fun i x hx => ⟨.sort .zero, by rw [canonParams_getElem? hx, Nat.zero_add]⟩)
      (by rw [openPisAtFvars_length _ hop, canonParams_length])
  obtain ⟨A, hA, hoA⟩ := instPisWith_erasedEq hEq (Expr.ErasedEq.rfl _) hio
  obtain ⟨pps, b, hst, hb, -, -⟩ := denote_openPis ds.length hop hta
  rw [stripPisAV_mkPisAV_take _ _ _ habl] at hst
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hAr : denote mp.base2.acval env ψ (ds.length + ([] : List Name).length) A
      = some (mkPisAV (ab.drop ds.length) (.sort u)) := by
    rw [← denote_erasedEq hoA]; simpa using hb
  have hAw : Expr.WScoped (ds.length + ([] : List Name).length) A := by
    refine ConLeche.wscoped_instPisWith (fun x hx => ?_)
      (Expr.WScoped.of_not_hasFvar hcl) hA
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hx
    have hlt : i < ds.length := by
      have := (List.getElem?_eq_some_iff.mp hi').1; rwa [canonParams_length] at this
    rw [canonParams_getElem? hi']
    simp [Expr.WScoped, hlt]
  -- the key's type is the canonical opening, level-instantiated, with the canonical
  -- parameters replaced by the key's parameters
  have hphs : ∀ x ∈ canonParams ds.length, ∃ i ty, x = .fvar i ty := fun x hx => by
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hx
    exact ⟨_, _, canonParams_getElem? hi'⟩
  have hAL := Expr.instPisWith_instantiateLevelParams lps us _ hphs hA
  rw [show canonParams ds.length = ConLeche.nestPhs ds.length from rfl,
    Expr.nestPhs_instantiateLevelParams] at hAL
  have hsb : ∀ i, i < ds.length → (ds.getD i default).looseBVarsBounded 0 = true := fun i hi' =>
    (hds _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact
      List.getElem_mem _)).2
  have hsub := Expr.substFvars_instPisWith (D := hi) (s := fun i => ds.getD i default) hsb _ hAL
  have hphsD : (ConLeche.nestPhs ds.length).map
      (Expr.substFvars ds.length hi fun i => ds.getD i default) = ds := by
    apply List.ext_getElem (by simp [ConLeche.nestPhs])
    intro i h1 h2
    simp only [ConLeche.nestPhs, List.getElem_map, List.getElem_range] at h1 ⊢
    rw [Expr.substFvars_fvar_lt h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  have hcl' : (ty.instantiateLevelParams lps us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hcl
  rw [hphsD, substFvars_of_not_hasFvar hcl', hty] at hsub
  obtain rfl := Option.some.inj hsub
  have hAf : Expr.fvarsBelow (ds.length + 0) (A.instantiateLevelParams lps us) := by
    rw [Nat.add_zero]
    exact fvarsBelow_instantiateLevelParams _ _ (by simpa using hAw.fvarsBelow)
  have h := denote_substFvars (φ := φ) mp.base2 (b := ds.length) (D := hi)
    (s := fun i => ds.getD i default) (x := fun i => dsa.getD i default)
    (fun i hi' => by
      have hmem : ds.getD i default ∈ ds := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem _
      obtain ⟨hw, hb⟩ := hds _ hmem
      exact ⟨hw, hb, DenoteSpine.getD hdsa default i hi'⟩)
    (A.instantiateLevelParams lps us) 0 hAf
  rw [Nat.add_zero, Nat.add_zero, denotePInstLevels mp.base2 φ lps us, hψ,
    show ds.length = ds.length + ([] : List Name).length by simp, hAr] at h
  simp only [List.length_nil, Nat.add_zero] at h
  rw [h, Option.map_some, Term.substAV_mkPisAV, Nat.zero_add]
  rfl

/-- **A tower substituted at a key's parameters, read**: its value at a valuation is the
tower's at the key frame. -/
theorem interp_substTele_key {dsa : List Term} {hi : Nat} (X : List Term) (u : Nat)
    (ρ : Nat → V) :
    interp V ρ (mkPisAV (Term.substTele (substTau dsa.length hi fun i => dsa.getD i default) 0 X)
        (.sort u))
      = interp V (keyFrame dsa hi ρ) (mkPisAV X (.sort u)) := by
  have e := Term.substAV_mkPisAV (substTau dsa.length hi fun i => dsa.getD i default)
    (.sort u) X 0
  rw [show Term.substAV (substTau dsa.length hi fun i => dsa.getD i default) (.sort u)
    (0 + X.length) = .sort u from rfl] at e
  rw [← e, interp_substAV, keyFrame_eq_substE rfl]

/-- **A member's hole type at a key, by a run** (`familyRead`): the run's result instantiated at
the key's parameters reads as the rest of the run's tower substituted at the parameters'
readings, and where the key's parameters fit both the run's parameter binders and the block's
(the frame's key check, and the block's parameter telescope), that rest has the value of the
block's index telescope over its sort at the key frame (`mkPisAV_tail_eq`). -/
theorem runHoleTy_read (mp : EnvModelM V env) {D : LfpDatum V} {mm : Nat} {ty : Expr}
    (hR : FormerRead mp D mm ty) {lps : List Name} {hi : Nat} {us : List Level} {ds : List Expr}
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List Term} (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
    (hpl : (D.pars mm (Level.substFn φ lps us)).length = ds.length)
    (hstrip : (ty.stripPis ds.length).isSome = true) {cty : Expr}
    (hty : ConLeche.instPisWith ds (ty.instantiateLevelParams lps us) = some cty) :
    ∃ (ab : List Term) (u : Nat),
      denote mp.base2.acval env (Level.substFn φ lps us) 0 ty = some (mkPisAV ab (.sort u)) ∧
      ab.length = (D.pars mm (Level.substFn φ lps us) ++ D.ids mm (Level.substFn φ lps us)).length ∧
      (∀ ρ : Nat → V, WellDenotedTy V ρ (mkPisAV ab (.sort u))) ∧
      denote mp.base2.acval env φ hi cty
        = some (mkPisAV (Term.substTele (substTau ds.length hi fun i => dsa.getD i default) 0
            (ab.drop ds.length)) (.sort u)) ∧
      ∀ ρ : Nat → V,
        SpineFit (fun j => ρ (j + hi)) (ab.take ds.length) (dsa.map (interp V ρ)) →
        SpineFit (fun j => ρ (j + hi)) (D.pars mm (Level.substFn φ lps us))
          (dsa.map (interp V ρ)) →
        interp V (keyFrame dsa hi ρ) (mkPisAV (ab.drop ds.length) (.sort u))
          = interp V (keyFrame dsa hi ρ)
              (mkPisAV (D.ids mm (Level.substFn φ lps us))
                (.sort (D.w (Level.substFn φ lps us)))) := by
  obtain ⟨hcl, -, -, hrd⟩ := hR
  obtain ⟨ab, u, hta, hl, hv⟩ := hrd (Level.substFn φ lps us)
  refine ⟨ab, u, hta, hl, fun ρ => (hv ρ).2, instTele_read mp hcl hds hdsa hta
    (by rw [hl, List.length_append, hpl]; omega) hstrip hty, fun ρ hfR hfD => ?_⟩
  have htl : (ab.take ds.length).length = (D.pars mm (Level.substFn φ lps us)).length := by
    rw [List.length_take, hl, List.length_append, hpl]; omega
  have e := hv (fun j => ρ (j + hi))
  rw [← List.take_append_drop ds.length ab] at e
  exact mkPisAV_tail_eq htl (by simp only [List.length_drop, hl, List.length_append, hpl]; omega)
    e.1 hfR hfD

/-- **A run's hole type at a key, by value, across the holes** (N2): `runHoleTy_read`'s rest of
the run's tower, read at the key frames of two walk valuations agreeing off the holes, has one
value — the run's instantiated index telescope mentions no hole. -/
theorem runRest_agree (mp : EnvModelM V env) {D : LfpDatum V} {mm : Nat} {ty : Expr}
    (hR : FormerRead mp D mm ty) {ctx : NestCtx} {hi : Nat} {lps : List Name} {us : List Level}
    {ds : List Expr} {nI : Nat} {cty : Expr} {c : Name}
    (hF : ConLeche.NestInstFacts ctx hi ⟨c, us, ds⟩ lps ty nI cty)
    (hpl : (D.pars mm (Level.substFn φ lps us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List Term} (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa) :
    ∃ (ab : List Term) (u : Nat),
      denote mp.base2.acval env (Level.substFn φ lps us) 0 ty = some (mkPisAV ab (.sort u)) ∧
      ab.length = (D.pars mm (Level.substFn φ lps us) ++ D.ids mm (Level.substFn φ lps us)).length ∧
      (∀ ρ : Nat → V, WellDenotedTy V ρ (mkPisAV ab (.sort u))) ∧
      (D.ids mm (Level.substFn φ lps us)).length = nI ∧
      (∀ ρ : Nat → V,
        SpineFit (fun j => ρ (j + hi)) (ab.take ds.length) (dsa.map (interp V ρ)) →
        SpineFit (fun j => ρ (j + hi)) (D.pars mm (Level.substFn φ lps us))
          (dsa.map (interp V ρ)) →
        interp V (keyFrame dsa hi ρ) (mkPisAV (ab.drop ds.length) (.sort u))
          = interp V (keyFrame dsa hi ρ)
              (mkPisAV (D.ids mm (Level.substFn φ lps us))
                (.sort (D.w (Level.substFn φ lps us))))) ∧
      ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
        interp V (keyFrame dsa hi ρ) (mkPisAV (ab.drop ds.length) (.sort u))
          = interp V (keyFrame dsa hi ρ') (mkPisAV (ab.drop ds.length) (.sort u)) := by
  obtain ⟨-, hstrip, hty, ⟨s, hs, -⟩, hocc, hnI⟩ := hF
  obtain ⟨ab, u, hta, hl, hwd, hcrd, hval⟩ := runHoleTy_read mp hR hds hdsa hpl hstrip hty
  have hdl : dsa.length = ds.length := (DenoteSpine.length_eq hdsa).symm
  -- N2: the run's index telescope's reading mentions no hole
  have hPDF := piDomsFree_of_binders cty hs hocc
  have hWty : Expr.WScoped hi cty :=
    ConLeche.wscoped_instPisWith (fun x hx => (hds x hx).1)
      (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hR.1)) hty
  obtain ⟨ab'', u', hread, hnob, hlen''⟩ :=
    noBVarTele_of_piDomsFree (m := mp.base2) (φ := φ) _ cty rfl hPDF hWty (Nat.le_refl _) hcrd
  obtain ⟨hdoms, -⟩ := mkPisAV_sort_eq hread
  rw [← hdoms] at hnob
  refine ⟨ab, u, hta, hl, hwd, ?_, hval, fun ρ ρ' hag => ?_⟩
  · have hl' := congrArg List.length hdoms
    simp only [substTele_length, List.length_drop] at hl'
    rw [hnI, ← piCount_eq_length, ← hlen'', ← hl', hl, List.length_append, hpl]
    omega
  · have hte := TeleEq.tower (B := .sort u) (teleEq_of_noBVarTele hnob hag) (fun _ _ => rfl)
    rw [← hdl, interp_substTele_key, interp_substTele_key] at hte
    rw [← hdl]
    exact hte

/-- **N2 by value**.  A container instance's type former, checked by `nestInstType` at the key
`C.{us} ds` below the hole bound `hi` against a run's result, has as many indices as the
recorded member, and — because the run's instantiated index telescope mentions no hole (N2) — the
recorded index telescope has one tower value at the key frames of two walk valuations agreeing off
the holes, wherever the key's parameters fit the run's parameter binders and the block's there
(`runHoleTy_read`).  So the container's index sets, the fits of an index spine, and a hole value
applied to the key's parameters are the same at both sides of a hole relation
(`idxSet_of_mkPisAV_eq`, `spineFit_iff_of_mkPisAV_eq`, `holeFam_of_mkPisAV_eq`). -/
theorem n2_tower (mp : EnvModelM V env) {D : LfpDatum V} {mm : Nat} {ty : Expr}
    (hR : FormerRead mp D mm ty) {ctx : NestCtx} {hi : Nat} {lps : List Name} {us : List Level}
    {ds : List Expr} {nI : Nat} {cty : Expr} {c : Name}
    (hF : ConLeche.NestInstFacts ctx hi ⟨c, us, ds⟩ lps ty nI cty)
    (hpl : (D.pars mm (Level.substFn φ lps us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List Term} (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa) :
    ∃ ab : List Term,
      (∃ u, denote mp.base2.acval env (Level.substFn φ lps us) 0 ty = some (mkPisAV ab (.sort u))) ∧
      (D.ids mm (Level.substFn φ lps us)).length = nI ∧
      ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
        SpineFit (fun j => ρ (j + hi)) (ab.take ds.length) (dsa.map (interp V ρ)) →
        SpineFit (fun j => ρ (j + hi)) (D.pars mm (Level.substFn φ lps us))
          (dsa.map (interp V ρ)) →
        SpineFit (fun j => ρ' (j + hi)) (ab.take ds.length) (dsa.map (interp V ρ')) →
        SpineFit (fun j => ρ' (j + hi)) (D.pars mm (Level.substFn φ lps us))
          (dsa.map (interp V ρ')) →
        interp V (keyFrame dsa hi ρ)
            (mkPisAV (D.ids mm (Level.substFn φ lps us)) (.sort (D.w (Level.substFn φ lps us))))
          = interp V (keyFrame dsa hi ρ')
            (mkPisAV (D.ids mm (Level.substFn φ lps us))
              (.sort (D.w (Level.substFn φ lps us)))) := by
  obtain ⟨ab, u, hta, -, -, hnI, hval, hag⟩ := runRest_agree mp hR hF hpl hds hdsa
  refine ⟨ab, ⟨u, hta⟩, hnI, fun ρ ρ' hagr hfR hfD hfR' hfD' => ?_⟩
  rw [← hval ρ hfR hfD, ← hval ρ' hfR' hfD']
  exact hag ρ ρ' hagr

/-! ## The level link -/

/-- A Π-telescope ending in the sort `s`. -/
@[expose] def PiEndsSort (s : Level) : Expr → Prop
  | .forallE _ b => PiEndsSort s b
  | .sort s' => s' = s
  | _ => False

theorem piEndsSort_of_binders {s : Level} :
    ∀ (e : Expr), e.piBinders.2 = .sort s → PiEndsSort s e := by
  intro e
  induction e with
  | forallE ty b _ ihb =>
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
  | forallE t b _ ihb => intro k h; exact ihb (k + 1) h
  | sort u => intro _ h; exact h
  | _ => intro _ h; exact h.elim

/-- **A Π-telescope ending in the sort `s` reads as a Π-tower ending in
`s`'s value.** -/
theorem denote_piEndsSort {s : Level} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : Term}, piCount e = n → PiEndsSort s e →
      denote m.acval env φ d e = some ea →
      ∃ ab : List Term, ea = mkPisAV ab (.sort (s.eval φ)) := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hf h
    match e, hn, hf, h with
    | .sort s', _, hf, h =>
      rw [denote_sort] at h
      obtain rfl : s' = s := hf
      exact ⟨[], (Option.some.inj h).symm⟩
  | succ n ih =>
    intro e d ea hn hf h
    match e, hn, hf, h with
    | .forallE ty b, hn, hf, h =>
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv h
      obtain ⟨ab, rfl⟩ := ih (b.instantiate1 (.fvar d ty))
        (by rw [piCount_instantiate1_fvar]; exact hn) (PiEndsSort.instantiate1 _ b 0 hf) hba
      exact ⟨ta :: ab, rfl⟩

/-- **The level link by value** (the kernel's N3): a container instance checked by `nestInstType`
against a run's result lives at the walk context's sort, and where the key's parameters fit the
run's parameter binders and the block's and extend to a full fit of the block's index telescope,
the recorded block's level at the key's levels is that sort's value (`spineFit_of_mkPisAV_eq`:
along a fit two towers of one value end in one sort). -/
theorem n2_sortV (mp : EnvModelM V env) {D : LfpDatum V} {mm : Nat} {ty : Expr}
    (hR : FormerRead mp D mm ty) {ctx : NestCtx} {hi : Nat} {lps : List Name} {us : List Level}
    {ds : List Expr} {nI : Nat} {cty : Expr} {c : Name}
    (hF : ConLeche.NestInstFacts ctx hi ⟨c, us, ds⟩ lps ty nI cty)
    (hpl : (D.pars mm (Level.substFn φ lps us)).length = ds.length)
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List Term} (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa) :
    ∃ ab : List Term,
      (∃ u, denote mp.base2.acval env (Level.substFn φ lps us) 0 ty = some (mkPisAV ab (.sort u))) ∧
      ∀ ρ : Nat → V,
        SpineFit (fun j => ρ (j + hi)) (ab.take ds.length) (dsa.map (interp V ρ)) →
        SpineFit (fun j => ρ (j + hi)) (D.pars mm (Level.substFn φ lps us))
          (dsa.map (interp V ρ)) →
        ∀ is, SpineFit (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us)) is →
        D.w (Level.substFn φ lps us) = ctx.sort.eval φ := by
  obtain ⟨-, hstrip, hty, ⟨s, hs, hequiv⟩, -, -⟩ := hF
  obtain ⟨ab, u, hta, hl, -, hcrd, hval⟩ := runHoleTy_read mp hR hds hdsa hpl hstrip hty
  refine ⟨ab, ⟨u, hta⟩, fun ρ hfR hfD is hfI => ?_⟩
  -- the run's instantiated former ends in the context's sort
  obtain ⟨ab', hread⟩ := denote_piEndsSort (m := mp.base2) (φ := φ) _ cty rfl
    (piEndsSort_of_binders cty hs) hcrd
  obtain ⟨-, hu⟩ := mkPisAV_sort_eq hread
  -- and, along the fit, in the block's
  have hlen : (D.ids mm (Level.substFn φ lps us)).length = (ab.drop ds.length).length := by
    rw [List.length_drop, hl, List.length_append, hpl]; omega
  obtain ⟨-, hw⟩ := spineFit_of_mkPisAV_eq hlen (hval ρ hfR hfD).symm hfI
  rw [hw, hu]
  exact ConLeche.Level.isEquiv_sound hequiv φ

end ConLeche.Model
