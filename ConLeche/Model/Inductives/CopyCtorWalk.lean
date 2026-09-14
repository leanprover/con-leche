module

public import ConLeche.Model.Inductives.CopyCtorRun
public import ConLeche.Verify.Inductives.NestedRestore
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedRestoreWalk
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels

public section

/-!
# The copies' constructors, READ off the walk (task #279 M-B′ step 3o, DESIGN §M.41)

`CopyCtors.lean` states the record `CopyCtorAsRead` — a copy's
constructor read through the container's, field by field — and
`CopyCtorRun.lean` closes ψ under it as a premise (`CopyCtorsRead`).
`Verify/Inductives/NestedFields.lean` gives the SYNTACTIC half
(`copyCtorFields_of_walk`: every field of a walked copy constructor is
unfired or a fire at the top).  This module is the MODEL half: the
readings of the instantiated container constructor at the block's
parameter frame, and the record's clauses from the walk's per-field
disjunction.

* **`ctor_peel`** — the constructor twin of `former_peel`
  (`CopyPins.lean`): the container's stored constructor, level
  instantiated and `instPis`'d at the pin's annotated components, reads
  at the block's parameter depth as `instSeq DsA` of the container's
  own reading below its parameters (`CtorDataI.read`,
  `denoteMeta_instLevels`, `denoteMeta_instPisAt_peel`);
* **`ctorInst_fields`** — that reading opened at the copy's field
  variables (`denoteMeta_openPis`): field `i` reads as
  `instSeq DsA (nPJ - 1 + i)` of the container's field `i`, the residual
  as `instSeq DsA (nPJ - 1 + nF)` of the container's body.

What the record's clauses are then read from is stated in §M.41 and
carried below as `CopyCtorWalkFacts`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The constructor, peeled at the pin -/

/-- **The container's constructor, peeled at the pin**: at the level
instantiation the pin names, `instPis` of the stored constructor type at
the pin's annotated components reads (at the block's parameter depth)
as the container's field telescope and body instantiated at the
components' readings — `former_peel`'s constructor twin.  The
container's data are at the pin's assignment `ψ'`, which agrees with
the level substitution on the constructor's level parameters
(`CtorDataI.params`) and reads the family's leaf alike (`hacv`). -/
theorem ctor_peel {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {ψ ψ' : Name → Nat}
    {T : Name} {lps : List Name} {cvC : ConstantVal} {nPJ nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (hfind : env.find? cvC.name = some (.ctorInfo cvC nPJ nF)) (hlpsC : cvC.levelParams = lps)
    (hc : CtorDataI mp.base2 T lps cvC nPJ nF nIdx resSort isProp large idxArgs ds Es srcs)
    {lvls : List Level} (hag : ∀ q ∈ lps, ψ' q = Level.substFn ψ lps lvls q)
    (hacv : mp.base2.acval T ψ' = mp.base2.acval T (Level.substFn ψ lps lvls))
    {nP : Nat} {argsA : List Expr} {DsA : List AnnotTerm} (hlenA : argsA.length = nPJ)
    (hargs : ∀ a ∈ argsA, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hsp : DenoteMetaSpine mp.base2.acval env ψ nP argsA DsA)
    {rest : Expr}
    (hrest : Expr.instPis (cvC.type.instantiateLevelParams lps lvls) argsA = some rest) :
    denoteMeta mp.base2.acval env ψ nP rest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1)
          (mkPisAV ((ds ψ').drop nPJ) (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ')))) := by
  have hwf := mp.base2.wf _ (ConLeche.find?_mem hfind)
  have hnf : (cvC.type.instantiateLevelParams lps lvls).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hb : (cvC.type.instantiateLevelParams lps lvls).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
  -- the reading at depth 0: the container's own, at the pin's assignment
  have hagree : ∀ q ∈ cvC.levelParams, Level.substFn ψ lps lvls q = ψ' q := by
    rw [hlpsC]; exact fun q hq => (hag q hq).symm
  obtain ⟨hds, hEs⟩ := hc.params _ _ hagree
  have hread0 : denoteMeta mp.base2.acval env ψ 0 (cvC.type.instantiateLevelParams lps lvls)
      = some (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mp.base2) ψ, hc.read, hds, hEs]
    unfold ctorBodyAVI
    rw [hacv]
  have hreadN : denoteMeta mp.base2.acval env ψ nP (cvC.type.instantiateLevelParams lps lvls)
      = some (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hnf
      (fun k => denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hnf hb hread0 1 k)
      hread0 nP
  -- the peel
  obtain ⟨dsI, hpr⟩ := instPisAt_of_instPis argsA hrest
  obtain ⟨restA, hrestA, hpeel⟩ := denoteMeta_instPisAt_peel mp.base2.acval_closed
    (acval_inst_self mp.base2) argsA hpr (Expr.WScoped.of_not_hasFvar hnf) hargs hreadN hsp
  have hlenD : DsA.length = nPJ := by rw [← DenoteMetaSpine.length hsp, hlenA]
  have hle : nPJ ≤ (ds ψ').length := by rw [hc.len ψ']; omega
  have htele : PiTeleAV nPJ (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ')))
      ((((ds ψ').take nPJ).map (·.2.2)).reverse)
      (mkPisAV ((ds ψ').drop nPJ) (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) :=
    piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take nPJ (ds ψ') _ hle)
  rw [peelPis_of_piTeleAV nPJ htele hlenD] at hpeel
  rw [hrestA, Option.some.inj hpeel]

/-! ## The instantiated constructor's fields, opened -/

/-- **The instantiated constructor's fields read as the container's
substituted**: the peeled reading (`ctor_peel`'s shape) opened at the
copy's `nF` field variables (`denoteMeta_openPis`) gives, at field `i`,
`instSeq DsA (nPJ - 1 + i)` of the container's field `i` entry, and at
the residual `instSeq DsA (nPJ - 1 + nF)` of the container's body. -/
theorem ctorInst_fields {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {ψ : Name → Nat}
    {nP nPJ nF : Nat} {DsA : List AnnotTerm} (hlenD : DsA.length = nPJ)
    {Γ : List (Nat × Nat × AnnotTerm)} (hΓ : Γ.length = nF) {B : AnnotTerm} {rest : Expr}
    (hread : denoteMeta mp.base2.acval env ψ nP rest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1) (mkPisAV Γ B)))
    {xFvs : List Expr} {xrest : Expr} (hop : ConLeche.openPisAtFvars nF rest nP = some (xFvs, xrest)) :
    (∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      denoteMeta mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1 + i) (Γ.getD i default).2.2)) ∧
    denoteMeta mp.base2.acval env ψ (nP + nF) xrest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1 + nF) B) := by
  have hle : DsA.length ≤ nPJ - 1 + 1 := by omega
  rw [instSeq_mkPisAV DsA (nPJ - 1) Γ B hle] at hread
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis nF hop hread
  have hlenI : nF ≤ (instSeqDoms DsA (nPJ - 1) Γ).length := by
    rw [instSeqDoms_length, hΓ]; exact Nat.le_refl _
  rw [stripPisAV_mkPisAV_take nF _ _ hlenI] at hst
  simp only [Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨hpps, hbE⟩ := hst
  have hdrop : (instSeqDoms DsA (nPJ - 1) Γ).drop nF = [] := by
    rw [List.drop_eq_nil_iff, instSeqDoms_length, hΓ]; exact Nat.le_refl _
  rw [hdrop] at hbE
  simp only [mkPisAV] at hbE
  refine ⟨fun i x hx => ?_, by rw [hb, ← hbE, hΓ]⟩
  obtain ⟨p, hp, -, hpd⟩ := hbind i x hx
  rw [hpd]
  congr 1
  have hi : i < nF := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hp).1
  rw [← hpps, List.getElem?_take_of_lt hi, instSeqDoms_getElem?] at hp
  have hiΓ : i < Γ.length := by rw [hΓ]; exact hi
  rw [List.getElem?_eq_getElem hiΓ, Option.map_some, Option.some.injEq] at hp
  rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiΓ]
  rfl


/-! ## Kit: erasure equality through an opening -/

omit [SetTheory V] in
/-- Erasure-equal telescopes open to erasure-equal pieces: the openers
agree pairwise on their annotations (up to erasure) and the bodies are
erasure-equal. -/
theorem openPisAtFvars_erasedEq :
    ∀ (n : Nat) {e₁ e₂ : Expr} {d : Nat} {fvs₁ : List Expr} {b₁ : Expr},
      Expr.ErasedEq e₁ e₂ → ConLeche.openPisAtFvars n e₁ d = some (fvs₁, b₁) →
      ∃ (fvs₂ : List Expr) (b₂ : Expr), ConLeche.openPisAtFvars n e₂ d = some (fvs₂, b₂) ∧
        fvs₂.length = fvs₁.length ∧
        (∀ (k : Nat) (x₁ x₂ : Expr), fvs₁[k]? = some x₁ → fvs₂[k]? = some x₂ →
          Expr.ErasedEq x₁.fvarTypeD x₂.fvarTypeD) ∧
        Expr.ErasedEq b₁ b₂
  | 0, e₁, e₂, d, fvs₁, b₁, he, h => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], e₂, rfl, rfl, ?_, he⟩
    intro k x₁ x₂ h
    simp at h
  | n + 1, .forallE ty bd m, e₂, d, fvs₁, b₁, he, h => by
    match e₂, he with
    | .forallE ty' bd' m', he =>
      obtain ⟨rfl, hty, hbd⟩ := he
      simp only [ConLeche.openPisAtFvars] at h
      split at h
      · next fvs' b' hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have he' : Expr.ErasedEq (bd.instantiate1 (.fvar d ty)) (bd'.instantiate1 (.fvar d ty')) :=
          Expr.ErasedEq.instantiate1 hbd rfl
        obtain ⟨fvs₂, b₂, hop₂, hlen, hall, hb⟩ := openPisAtFvars_erasedEq n he' hop
        refine ⟨.fvar d ty' :: fvs₂, b₂, ?_, by simp [hlen], ?_, hb⟩
        · simp only [ConLeche.openPisAtFvars, hop₂]
        · intro k x₁ x₂ hx₁ hx₂
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx₁ hx₂
            subst hx₁; subst hx₂
            exact hty
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx₁ hx₂
            exact hall k x₁ x₂ hx₁ hx₂
      · exact nomatch h
  | n + 1, .bvar _, _, _, _, _, _, h | n + 1, .fvar _ _, _, _, _, _, _, h
  | n + 1, .sort _, _, _, _, _, _, h | n + 1, .const _ _, _, _, _, _, _, h
  | n + 1, .app _ _, _, _, _, _, _, h | n + 1, .lam _ _ _, _, _, _, _, _, h
  | n + 1, .letE _ _ _, _, _, _, _, _, h | n + 1, .lit _, _, _, _, _, _, h
  | n + 1, .proj _ _ _, _, _, _, _, _, h => nomatch h

omit [SetTheory V] in
/-- Erasure equality is reflexive on a constant head: an erasure-equal
term has the same constant at its head. -/
theorem ErasedEq.getAppFn_const :
    ∀ {e₁ e₂ : Expr} {c : Name} {us : List Level}, Expr.ErasedEq e₁ e₂ →
      e₁.getAppFn = .const c us → e₂.getAppFn = .const c us
  | .app f a, e₂, c, us, he, h => by
    match e₂, he with
    | .app g b, he => exact ErasedEq.getAppFn_const (e₁ := f) (e₂ := g) he.1 h
  | .const n us', e₂, c, us, he, h => by
    match e₂, he with
    | .const n' us'', he =>
      obtain ⟨rfl, rfl⟩ := he
      exact h
  | .bvar _, _, _, _, _, h | .fvar _ _, _, _, _, _, h | .sort _, _, _, _, _, h
  | .lam _ _ _, _, _, _, _, h | .forallE _ _ _, _, _, _, _, h | .letE _ _ _, _, _, _, _, h
  | .lit _, _, _, _, _, h | .proj _ _ _, _, _, _, _, h => nomatch h

omit [SetTheory V] in
/-- The Π-prefix length is invariant under erasure equality. -/
theorem ErasedEq.piBinders_length :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → (e₁.piBinders).1.length = (e₂.piBinders).1.length
  | .forallE ty bd m, e₂, he => by
    match e₂, he with
    | .forallE ty' bd' m', he =>
      simp only [Expr.piBinders, List.length_cons]
      rw [ErasedEq.piBinders_length he.2.2]
  | .bvar _, e₂, he | .fvar _ _, e₂, he | .sort _, e₂, he | .const _ _, e₂, he | .app _ _, e₂, he
  | .lam _ _ _, e₂, he | .letE _ _ _, e₂, he | .lit _, e₂, he | .proj _ _ _, e₂, he => by
    cases e₂ <;> first | rfl | exact he.elim

/-! ## Kit: a read spine at a deeper depth, and under erasure -/

/-- A `d`-scoped term read at `d + k` is its depth-`d` reading lifted by
`k` (`denoteMeta_weaken_top` iterated). -/
theorem denoteMeta_weaken_by (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) :
    ∀ k : Nat, denoteMeta m.acval env ψ (d + k) e = (denoteMeta m.acval env ψ d e).map (·.liftN k 0)
  | 0 => by
    cases denoteMeta m.acval env ψ d e with
    | none => rfl
    | some v => simp [AnnotTerm.liftN_zero]
  | k + 1 => by
    rw [show d + (k + 1) = d + k + 1 from by omega,
      denoteMeta_weaken_top m.acval_closed (Expr.WScoped.mono (Nat.le_add_right d k) hw),
      denoteMeta_weaken_by m hw k]
    cases denoteMeta m.acval env ψ d e with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      rw [AVExprSubst.liftN_liftN_absorb v (Nat.le_refl 0) (by omega) 1, Nat.add_comm]

/-- A read spine of `d`-scoped terms at `d + k`: the readings lifted. -/
theorem DenoteMetaSpine.weaken_by (m : EnvModel V env) {ψ : Name → Nat} {d : Nat} (k : Nat) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine m.acval env ψ d as vs →
      (∀ a ∈ as, Expr.WScoped d a) →
      DenoteMetaSpine m.acval env ψ (d + k) as (vs.map (·.liftN k 0))
  | _, _, .nil, _ => .nil
  | a :: as, v :: vs, .cons ha hrest, hw => by
    rw [List.map_cons]
    refine .cons ?_ (DenoteMetaSpine.weaken_by m k hrest fun x hx => hw x (List.mem_cons_of_mem _ hx))
    rw [denoteMeta_weaken_by m (hw a List.mem_cons_self) k, ha]
    rfl

/-- Erasure-equal spines read alike. -/
theorem DenoteMetaSpine.erasedEq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as as' : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.length = as'.length →
      (∀ (k : Nat) (e e' : Expr), as[k]? = some e → as'[k]? = some e' → Expr.ErasedEq e e') →
      DenoteMetaSpine acval env φ d as' vs
  | [], [], _, .nil, _, _ => .nil
  | [], _ :: _, _, .nil, hlen, _ => by simp at hlen
  | _ :: _, [], _, .cons _ _, hlen, _ => by simp at hlen
  | a :: as, a' :: as', v :: vs, .cons ha hrest, hlen, hall => by
    refine .cons ?_ (DenoteMetaSpine.erasedEq hrest (by simpa using hlen)
      fun k e e' he he' => hall (k + 1) e e' (by simpa using he) (by simpa using he'))
    rw [← denoteMeta_erasedEq (hall 0 a a' rfl rfl) d]
    exact ha

/-! ## Kit: a constant head resolves -/

omit [SetTheory V] in
/-- A resolving term's constant head is stored. -/
theorem constsResolve_getAppFn {env : Env} :
    ∀ (e : Expr) {c : Name} {us : List Level}, e.constsResolve env = true →
      e.getAppFn = .const c us → (env.find? c).isSome = true
  | .app f a, c, us, h, hh => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsResolve_getAppFn f h.1 hh
  | .const n us', c, us, h, hh => by
    obtain ⟨rfl, -⟩ := Expr.const.inj hh
    simpa [Expr.constsResolve] using h
  | .bvar _, _, _, _, hh | .fvar _ _, _, _, _, hh | .sort _, _, _, _, hh | .lam _ _ _, _, _, _, hh
  | .forallE _ _ _, _, _, _, hh | .letE _ _ _, _, _, _, hh | .lit _, _, _, _, hh
  | .proj _ _ _, _, _, _, hh => nomatch hh

omit [SetTheory V] in
/-- A resolving telescope's opened body resolves (the openers'
annotations are its own instantiated domains). -/
theorem constsResolve_openPis {env : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {b : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, b) → e.constsResolve env = true →
      b.constsResolve env = true
  | 0, e, d, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact he
  | n + 1, .forallE ty bd m, d, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars] at h
    split at h
    · next fvs' b' hop =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.constsResolve, Bool.and_eq_true] at he
      exact constsResolve_openPis n hop (Expr.constsResolve_instantiate1 he.1 0 he.2)
    · exact nomatch h
  | n + 1, .bvar _, _, _, _, h, _ | n + 1, .fvar _ _, _, _, _, h, _
  | n + 1, .sort _, _, _, _, h, _ | n + 1, .const _ _, _, _, _, h, _
  | n + 1, .app _ _, _, _, _, h, _ | n + 1, .lam _ _ _, _, _, _, h, _
  | n + 1, .letE _ _ _, _, _, _, h, _ | n + 1, .lit _, _, _, _, h, _
  | n + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

/-! ## Kit: the cut of a parameter substitution -/

omit [SetTheory V] in
/-- The two spellings of the cut agree (at `nPJ = 0` the substitution is
empty and the cut is irrelevant). -/
theorem instSeq_cut_congr {DsA : List AnnotTerm} {nPJ : Nat} (hlen : DsA.length = nPJ) (i : Nat)
    (e : AnnotTerm) :
    ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1 + i) e
      = ConLeche.Model.AnnotTerm.instSeq DsA (nPJ + i - 1) e := by
  cases nPJ with
  | zero =>
    obtain rfl : DsA = [] := List.eq_nil_of_length_eq_zero hlen
    rfl
  | succ n => rw [show n + 1 - 1 + i = n + 1 + i - 1 from by omega]

omit [SetTheory V] in
theorem instSeqDoms_nil : ∀ (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)), instSeqDoms [] t Γ = Γ
  | _, [] => rfl
  | t, (u, v, A) :: Γ => by simp only [instSeqDoms, AnnotTerm.instSeq_nil, instSeqDoms_nil (t + 1) Γ]

omit [SetTheory V] in
theorem instSeqDoms_cut_congr {DsA : List AnnotTerm} {nPJ : Nat} (hlen : DsA.length = nPJ) (i : Nat)
    (Γ : List (Nat × Nat × AnnotTerm)) :
    instSeqDoms DsA (nPJ - 1 + i) Γ = instSeqDoms DsA (nPJ + i - 1) Γ := by
  cases nPJ with
  | zero =>
    obtain rfl : DsA = [] := List.eq_nil_of_length_eq_zero hlen
    rw [instSeqDoms_nil, instSeqDoms_nil]
  | succ n => rw [show n + 1 - 1 + i = n + 1 + i - 1 from by omega]

/-- A leaf is untouched by a substitution sequence. -/
theorem instSeq_acval (m : EnvModel V env) (T : Name) (ψ : Name → Nat) :
    ∀ (ws : List AnnotTerm) (t : Nat), ConLeche.Model.AnnotTerm.instSeq ws t (m.acval T ψ) = m.acval T ψ
  | [], _ => rfl
  | w :: ws, t => by rw [AnnotTerm.instSeq_cons, acval_inst_self, instSeq_acval m T ψ ws]

/-! ## The interface: what the walk leaves at a copy's field -/

/-- **A field fired at the top**, as the walk leaves it (DESIGN §M.41):
the copy's stored field `eA` and the container's instantiated field
`eC`, both opened at the copy's depth over the same `n` binders, are a
copy-headed application at the block's parameters and index arguments,
and the container `I` at the pin's components `DsF` and index
arguments erasure-equal to the copy's; the binders' annotations are
erasure-equal and their binder data equal (the walk keeps binder data,
and the readings' codomain bits are read off it); the pin
`⟨aux, I, I lvls' DsF⟩` is in the table and satisfies `P`.  Erasure equality is what the readings are blind to
(`denoteMeta_erasedEq`); the openers' annotations differ between the
two sides exactly there. -/
@[expose] def FiredField (st : ElimState) (blvls : List Level) (params : List Expr)
    (P : NestedPin → Prop) (dpt : Nat) (eA eC : Expr) : Prop :=
  ∃ (n : Nat) (afvs afvsC : List Expr) (aux I : Name) (lvls' : List Level) (DsF idx idxC : List Expr),
    ConLeche.openPisAtFvars n eA dpt = some (afvs, Expr.mkAppN (.const aux blvls) (params ++ idx)) ∧
    ConLeche.openPisAtFvars n eC dpt = some (afvsC, Expr.mkAppN (.const I lvls') (DsF ++ idxC)) ∧
    (eA.piBinders).1.length = n ∧ (eC.piBinders).1.length = n ∧
    (∀ (k : Nat) (a aC : Expr), afvs[k]? = some a → afvsC[k]? = some aC →
      Expr.ErasedEq a.fvarTypeD aC.fvarTypeD) ∧
    (∃ (bsA bsC : List (Expr × ConLeche.BinderMeta)) (rA rC : Expr),
      eA.stripPis n = some (bsA, rA) ∧ eC.stripPis n = some (bsC, rC) ∧
      ∀ (k : Nat) (bA bC : Expr × ConLeche.BinderMeta), bsA[k]? = some bA → bsC[k]? = some bC →
        bA.2 = bC.2) ∧
    idx.length = idxC.length ∧
    (∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC) ∧
    ∃ q ∈ st.pins, q.aux = aux ∧ q.container = I ∧ q.pin = Expr.mkAppN (.const I lvls') DsF ∧ P q

/-- **A field the positivity normalisation `whnf`'d** (K.17's witness
at the field, in the OPENED-CONSTRUCTOR currency — DESIGN §M.44): a
term `dm` erasure-equal to the container's instantiated field `eC` (the
restored PROCESSED constructor's opener, which the walk's inverse makes
the container's field again) reduces, at the environment holding the
block's formers, to a term erasure-equal to the copy's stored field
RESTORED at the instantiated level — `restoreI (R.instAt params) eA`,
exactly what `restoreNested_openPis` says of the restored STORED
constructor's opener — and `dm` carries the reduction's guards.  The
whole-constant `restoreNested R` on a FIELD is the wrong currency
(`stripPisOrLams nP` on a field is not the restore of that field). -/
@[expose] def WhnfField (μ : CheckMode) (F : Nat) (env₁ : Env) (R : ConLeche.RestoreTbl)
    (params : List Expr) (dpt : Nat) (eA eC : Expr) : Prop :=
  ∃ (dm dsR : Expr), Expr.ErasedEq dm eC ∧ ConLeche.whnf μ env₁ F dpt dm = .ok dsR ∧
    Expr.ErasedEq dsR (ConLeche.restoreI (R.instAt params) eA) ∧
    Expr.WScoped dpt dm ∧ dm.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded dm

/-- **What the walk leaves of a copy's constructor** (DESIGN §M.41): the
copy's STORED constructor opened at the block's parameters and its own
field variables (`xFvs`, `xrest` — the auxiliary datum's `xFvsF`/
`xrestF`), against the CONTAINER's constructor instantiated at the pin
and opened at the same variables (`xFvsC`, `xrestC`):

* the residual is the copy at the block's parameters and index
  arguments erasure-equal to the container's at the pin's components;
* at a field the container sees as RECURSIVE (its `ksF`), a fire at the
  top whose pin is the group-mate's (`fieldRec`), the Π-prefix length
  the container's own opened field's;
* at a field the container sees as ORDINARY, one of: unfired and
  copy-free (erasure-equal, no copy name mentioned), a fire at the top
  whose pin is NOT a group pin, or the normalisation's `whnf`
  (`fieldOrd`).

The syntactic half (`Verify`) produces this from `copyCtorFields_of_walk`,
the container's `FixOpened` shapes instantiated at the pin, K.17's
witness and the ledger; the Model half below reads the record off it. -/
structure CopyCtorWalkFacts (μ : CheckMode) (F : Nat) (env₁ : Env) (R : ConLeche.RestoreTbl)
    (st : ElimState) (k₀ nP nF : Nat) (blvls : List Level) (params : List Expr)
    (dJ : IndRepData V) (Jc : Nat) (Jn : Name) (lvls : List Level) (Ds : List Expr)
    (xFvs xFvsC : List Expr) (xrest xrestC : Expr) : Prop where
  lenC : xFvsC.length = nF
  idxC : ∀ (k : Nat) (x : Expr), xFvsC[k]? = some x → ∃ ty, x = .fvar (nP + k) ty
  resid : ∃ (aux : Name) (idx idxC : List Expr),
    xrest = Expr.mkAppN (.const aux blvls) (params ++ idx) ∧
    xrestC = Expr.mkAppN (.const Jn lvls) (Ds ++ idxC) ∧
    idx.length = idxC.length ∧
    ∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC
  fieldRec : ∀ (i : Nat) (x xC : Expr), xFvs[i]? = some x → xFvsC[i]? = some xC →
    i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
    (∀ xJ, (dJ.xFvsF Jc)[i]? = some xJ → (xJ.fvarTypeD.piBinders).1.length = (x.fvarTypeD.piBinders).1.length) ∧
    FiredField st blvls params
      (fun q => q.pin = Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls) Ds)
      (nP + i) x.fvarTypeD xC.fvarTypeD
  fieldOrd : ∀ (i : Nat) (x xC : Expr), xFvs[i]? = some x → xFvsC[i]? = some xC →
    i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
    (Expr.ErasedEq x.fvarTypeD xC.fvarTypeD ∧
      ∀ T ∈ (st.types.map (·.name)).drop k₀, x.fvarTypeD.mentionsConstE T = false) ∨
    FiredField st blvls params
      (fun q => ∀ g, g < dJ.k → q.pin ≠ Expr.mkAppN (.const (dJ.memberName g) lvls) Ds)
      (nP + i) x.fvarTypeD xC.fvarTypeD ∨
    WhnfField μ F env₁ R params (nP + i) x.fvarTypeD xC.fvarTypeD


/-! ## Kit: the reading peel with its binder bits -/

omit [SetTheory V] in
/-- Instantiation keeps a telescope's binder data. -/
theorem stripPis_instantiate1_meta {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Expr × ConLeche.BinderMeta)} {body body' : Expr} (j : Nat),
      e.stripPis k = some (bs, body) → (e.instantiate1 v j).stripPis k = some (bs', body') →
      ∀ (i : Nat) (b b' : Expr × ConLeche.BinderMeta), bs[i]? = some b → bs'[i]? = some b' →
        b'.2 = b.2
  | 0, e, bs, bs', body, body', j, h, h', i, b, b', hb, hb' => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h h'
    rw [← h.1] at hb
    exact nomatch hb
  | k + 1, .forallE ty bd m, bs, bs', body, body', j, h, h', i, b, b', hb, hb' => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨rfl, rfl⟩ := hbs
    simp only [Expr.instantiate1, Expr.stripPis, Option.map_eq_some_iff] at h'
    obtain ⟨⟨bs₁, body₁⟩, h₁, hbs'⟩ := h'
    simp only [Prod.mk.injEq] at hbs'
    obtain ⟨rfl, rfl⟩ := hbs'
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hb'
      subst hb; subst hb'
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb hb'
      exact stripPis_instantiate1_meta k (j + 1) h₀ h₁ i b b' hb hb'
  | k + 1, .bvar _, _, _, _, _, _, h, _, _, _, _, _, _ | k + 1, .fvar _ _, _, _, _, _, _, h, _, _, _, _, _, _
  | k + 1, .sort _, _, _, _, _, _, h, _, _, _, _, _, _ | k + 1, .const _ _, _, _, _, _, _, h, _, _, _, _, _, _
  | k + 1, .app _ _, _, _, _, _, _, h, _, _, _, _, _, _ | k + 1, .lam _ _ _, _, _, _, _, _, h, _, _, _, _, _, _
  | k + 1, .letE _ _ _, _, _, _, _, _, h, _, _, _, _, _, _ | k + 1, .lit _, _, _, _, _, _, h, _, _, _, _, _, _
  | k + 1, .proj _ _ _, _, _, _, _, _, h, _, _, _, _, _, _ => nomatch h

/-- **The reading peel, with the binder bits** (`denoteMeta_openPis`
returning the whole reading as a tower and each binder's codomain bit
as its stored binder datum's): what identifies a copy's telescope
entries with the container's instantiated binders' readings bit for
bit. -/
theorem denoteMeta_openPis' {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {bs : List (Expr × ConLeche.BinderMeta)} {r : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → e.stripPis n = some (bs, r) →
      denoteMeta acval env φ d e = some ea →
      ∃ (pps : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
        ea = mkPisAV pps b ∧ denoteMeta acval env φ (d + n) o = some b ∧ pps.length = n ∧
        (∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          ∃ p, pps[i]? = some p ∧ p.1 = 0 ∧
            (∃ bm, bs[i]? = some bm ∧ p.2.1 = pwBit φ bm.2.pw) ∧
            denoteMeta acval env φ (d + i) x.fvarTypeD = some p.2.2)
  | 0, d, e, fvs, o, ea, bs, r, hop, hst, hden => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨[], ea, rfl, by simpa using hden, rfl, fun i x hx => by simp at hx⟩
  | n + 1, d, .forallE dom body mb, fvs, o, ea, bs, r, hop, hst, hden => by
    simp only [ConLeche.openPisAtFvars] at hop
    split at hop
    · next fvs' o' hop' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₀, r₀⟩, hst₀, hbs⟩ := hst
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hden
      have hsome : ((body.instantiate1 (.fvar d dom)).stripPis n).isSome :=
        Expr.stripPis_instantiate1_isSome n 0 (by rw [hst₀]; rfl)
      obtain ⟨⟨bs₁, r₁⟩, hst₁⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨pps, b, rfl, hb, hlen, hbind⟩ := denoteMeta_openPis' n hop' hst₁ hba
      refine ⟨(0, pwBit φ mb.pw, ta) :: pps, b, rfl, ?_, by simp [hlen], ?_⟩
      · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hb
      · intro i x hx
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨(0, pwBit φ mb.pw, ta), rfl, rfl, ⟨(dom, mb), rfl, rfl⟩, by rw [Nat.add_zero]; exact hta⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨p, hp, hp1, ⟨bm, hbm, hpb⟩, hpd⟩ := hbind i x hx
          have hi : i < bs₀.length := by
            rw [stripPis_length' n hst₀, ← stripPis_length' n hst₁]
            exact (List.getElem?_eq_some_iff.mp hbm).1
          obtain ⟨bm₀, hbm₀⟩ : ∃ bm₀, bs₀[i]? = some bm₀ := ⟨_, List.getElem?_eq_getElem hi⟩
          refine ⟨p, by simpa using hp, hp1, ⟨bm₀, by simpa using hbm₀, ?_⟩,
            by rw [show d + (i + 1) = d + 1 + i from by omega]; exact hpd⟩
          rw [hpb, stripPis_instantiate1_meta n 0 hst₀ hst₁ i bm₀ bm hbm₀ hbm]
    · exact nomatch hop
  | n + 1, _, .bvar _, _, _, _, _, _, hop, _, _ | n + 1, _, .fvar _ _, _, _, _, _, _, hop, _, _
  | n + 1, _, .sort _, _, _, _, _, _, hop, _, _ | n + 1, _, .const _ _, _, _, _, _, _, hop, _, _
  | n + 1, _, .app _ _, _, _, _, _, _, hop, _, _ | n + 1, _, .lam _ _ _, _, _, _, _, _, hop, _, _
  | n + 1, _, .letE _ _ _, _, _, _, _, _, hop, _, _ | n + 1, _, .lit _, _, _, _, _, _, hop, _, _
  | n + 1, _, .proj _ _ _, _, _, _, _, _, hop, _, _ => by simp [ConLeche.openPisAtFvars] at hop

/-! ## Kit: injectivities -/

omit [SetTheory V] in
/-- Distinct positions of a `Nodup` list hold distinct elements. -/
theorem nodup_getElem?_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  refine Classical.byContradiction fun hne => ?_
  have hi' := List.getElem?_eq_some_iff.mp hi
  have hj' := List.getElem?_eq_some_iff.mp hj
  have hp := List.pairwise_iff_getElem.mp h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hp i j hi'.1 hj'.1 hlt (hi'.2.trans hj'.2.symm)
  · exact hp j i hj'.1 hi'.1 hlt (hj'.2.trans hi'.2.symm)

omit [SetTheory V] in
/-- The members' names are injective below the block's size. -/
theorem memberName_inj {d : IndRepData V} (hnd : ((List.range d.k).map d.memberName).Nodup)
    {a b : Nat} (ha : a < d.k) (hb : b < d.k) (h : d.memberName a = d.memberName b) : a = b := by
  refine nodup_getElem?_inj hnd (i := a) (j := b) (a := d.memberName b) ?_ ?_
  · rw [List.getElem?_map, List.getElem?_range ha, Option.map_some, h]
  · rw [List.getElem?_map, List.getElem?_range hb, Option.map_some]

omit [SetTheory V] in
/-- Two pins with one term sit at one index (K.15's `Nodup`). -/
theorem pins_index_inj {st : ElimState} (hnd : (st.pins.map (·.pin)).Nodup) {i j : Nat}
    {q q' : NestedPin} (hi : st.pins[i]? = some q) (hj : st.pins[j]? = some q') (h : q.pin = q'.pin) :
    i = j := by
  refine nodup_getElem?_inj hnd (i := i) (j := j) (a := q'.pin) ?_ ?_
  · rw [List.getElem?_map, hi, Option.map_some, h]
  · rw [List.getElem?_map, hj, Option.map_some]

omit [SetTheory V] in
/-- Two constant-headed spines are one: head name, levels and
arguments. -/
theorem mkAppN_const_inj {n n' : Name} {us us' : List Level} {as bs : List Expr}
    (h : Expr.mkAppN (.const n us) as = Expr.mkAppN (.const n' us') bs) :
    n = n' ∧ us = us' ∧ as = bs := by
  have h1 := congrArg Expr.getAppFn h
  rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
  have h2 := congrArg Expr.getAppArgs h
  rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
  simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.const.injEq] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

omit [SetTheory V] in
/-- A constant-headed term has no Π-prefix. -/
theorem piBinders_nil_of_getAppFn_const :
    ∀ (e : Expr) {c : Name} {us : List Level}, e.getAppFn = .const c us → (e.piBinders).1 = []
  | .app _ _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .bvar _, _, _, h | .fvar _ _, _, _, h | .sort _, _, _, h | .lam _ _ _, _, _, h
  | .forallE _ _ _, _, _, h | .letE _ _ _, _, _, h | .lit _, _, _, h | .proj _ _ _, _, _, h => nomatch h

omit [SetTheory V] in
/-- The arguments of a constant-headed spine after its parameters. -/
theorem getAppArgs_mkAppN_const_drop {n : Name} {us : List Level} {params idx : List Expr} {nP : Nat}
    (hlen : params.length = nP) :
    (Expr.mkAppN (.const n us) (params ++ idx)).getAppArgs.drop nP = idx := by
  rw [Expr.getAppArgs_mkAppN]
  simp only [Expr.getAppArgs, List.nil_append]
  rw [List.drop_left' hlen]


omit [SetTheory V] in
/-- Two bits with the same zeroness are equal. -/
theorem bit_eq_of_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (h : a = 0 ↔ b = 0) : a = b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp_all

/-! ## The whnf arm's content, and the copy-side kind at a fire -/

namespace IndRepData

/-- **The restored reading of a copy's field** (what K.17's witness
reduces the container's instantiated field TO, read at the block):
at a copy field recursive into a COPY, the target pin's container at
the pin's readings (lifted over the field's telescope) at the copy's
index readings, under the copy's telescope — the transport clause's
target; otherwise the copy's own stored domain. -/
@[expose] def restoreAV (m : EnvModel V env) (d : IndRepData V) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm) (i : Nat) :
    AnnotTerm :=
  if i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i then
    mkPisAV ((d.tssR Ja ψ).getD i [])
      (AnnotTerm.mkAppN (m.acval (tgtCont (d.tgtsR Ja i - k₀)) (tgtLps (d.tgtsR Ja i - k₀)))
        ((tgtDsA (d.tgtsR Ja i - k₀)).map (·.liftN (i + ((d.tssR Ja ψ).getD i []).length) 0) ++
          (d.eissR Ja ψ).getD i []))
  else ((d.dsF Ja ψ).getD (d.nP + i) default).2.2

end IndRepData

/-- **A fired field's copy-side kind and target** (DESIGN §M.41): a
copy field the walk fired at the top is not ordinary (an ordinary
field resolves before the block, but the fire's head is a copy name,
fresh there), its target member is the fire's copy, and it is
recursive exactly when the fire has no binders. -/
theorem copyKind_of_fire {μ : CheckMode} {envAux env : Env} (mp : EnvModelM V μ envAux)
    {d : IndRepData V} {Ja : Nat} {cA : ConstantVal × Nat} {lpsT : List Name} {st : ElimState}
    {k₀ : Nat} {blvls : List Level} {params : List Expr}
    (hdk : d.k = k₀ + st.pins.length)
    (hD : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems Ja)) lpsT cA.1 d.nP cA.2
      (d.nIdxAt (d.mems Ja)) d.resSort d.isProp d.large (d.idxF Ja) (d.dsF Ja) (d.esF Ja)
      (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja) (d.eissF Ja) (d.tssF Ja)
      (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hordRes : ∀ (i : Nat) (x : Expr), (d.xFvsF Ja)[i]? = some x →
      (d.ksF Ja).getD i .ordinary = .ordinary → x.fvarTypeD.constsResolve env = true)
    (hfresh : ∀ t, k₀ ≤ t → t < d.k → env.find? (d.memberName t) = none)
    (hpinName : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q → d.memberName (k₀ + jq) = q.aux)
    {i : Nat} {x : Expr} (hx : (d.xFvsF Ja)[i]? = some x) {n : Nat} {afvs : List Expr} {aux : Name}
    {idx : List Expr}
    (hopA : ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i)
      = some (afvs, Expr.mkAppN (.const aux blvls) (params ++ idx)))
    (hnA : (x.fvarTypeD.piBinders).1.length = n)
    {jq : Nat} {q : NestedPin} (hjq : st.pins[jq]? = some q) (hqa : q.aux = aux) :
    (d.ksF Ja).getD i .ordinary ≠ .ordinary ∧ d.memberName (d.tgts Ja i) = aux ∧
      ((d.ksF Ja).getD i .ordinary = .recursive ↔ n = 0) := by
  have hi : i < cA.2 := by rw [← hD.xLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hjqLt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
  have hfreshA : env.find? aux = none := by
    rw [← hqa, ← hpinName jq q hjq]; exact hfresh _ (Nat.le_add_right _ _) (by omega)
  have hnotOrd : (d.ksF Ja).getD i .ordinary ≠ .ordinary := by
    intro hord
    have hres := constsResolve_openPis n hopA (hordRes i x hx hord)
    have hsome := constsResolve_getAppFn _ hres (Expr.getAppFn_mkAppN _ _)
    rw [hfreshA] at hsome
    exact nomatch hsome
  rcases hD.opened.kinds i hi with hord | hrec | hrefl
  · exact absurd hord hnotOrd
  · obtain ⟨hhead, -⟩ := hD.opened.recF i x hx hrec
    have hn0 : n = 0 := by rw [← hnA, piBinders_nil_of_getAppFn_const _ hhead]; rfl
    subst hn0
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopA
    obtain ⟨-, hxE⟩ := hopA
    rw [hxE, Expr.getAppFn_mkAppN] at hhead
    simp only [Expr.getAppFn, Expr.const.injEq] at hhead
    exact ⟨hnotOrd, hhead.1.symm, ⟨fun _ => rfl, fun _ => hrec⟩⟩
  · obtain ⟨afvs', body', hopen, hne, -, hhead, -⟩ := hD.opened.reflF i x hx hrefl
    rw [hnA, hopA] at hopen
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopen)
    rw [Expr.getAppFn_mkAppN] at hhead
    simp only [Expr.getAppFn, Expr.const.injEq] at hhead
    have hlen := openPisAtFvars_length n hopA
    refine ⟨hnotOrd, hhead.1.symm, ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [hrefl] at h; exact nomatch h
    · exact absurd (by rw [hlen, h]) hne

/-! ## The record, read off the walk -/

set_option maxHeartbeats 6400000 in
/-- **`CopyCtorAsRead` from the walk's facts** (DESIGN §M.41, the
record's Model half): with the copy's constructor at the auxiliary
datum, the container's at its datum, the pin's readings, the group's
pins and the targets' pins, the container's instantiated constructor
read (`ctor_peel`/`ctorInst_fields`), what the walk leaves
(`CopyCtorWalkFacts`), the `whnf` arm's content (`hwhnf`) and the
container field's grading at the pin (`hgradeC`), every clause of the
record holds:

* `kindR` — at a container-recursive field the fire's pin is the
  group-mate's, so the copy's target is the group-mate's copy
  (`pins_index_inj`, `memberName_inj`); the kinds agree through the
  Π-prefix lengths; the telescopes' readings agree binder by binder
  (`denoteMeta_erasedEq`) with their bits by `tssBits`; the index
  readings by the residual's spine (`mkAppN_inj_args`);
* `es` — the residual's spine likewise;
* `ord` — unfired: the readings are one term; `whnf`: `hwhnf`; a fire
  is impossible (the copy's target would be a copy);
* `kindT` — unfired: impossible (the copy mentions its target);
  a fire: the target is the fire's pin, outside the group, and the
  container's instantiated reading IS the transport's target term
  (`denoteMeta_openPis'`, the bits by the walk's kept binder data);
  `whnf`: `hwhnf`. -/
theorem copyCtorAsRead_of_walkFacts {μ : CheckMode} {envAux env env₁ : Env} {F : Nat}
    (mp : EnvModelM V μ envAux) {R : ConLeche.RestoreTbl} {st : ElimState}
    {d dJ : IndRepData V} {ψ ψ' : Name → Nat} {DsA : List AnnotTerm} {Ds : List Expr}
    {k₀ j₀ Jc Ja : Nat} {cA cAJ : ConstantVal × Nat}
    {lpsT lpsJ : List Name} {lvls blvls : List Level} {params : List Expr}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    -- sizes
    (hdk : d.k = k₀ + st.pins.length) (hparams : params.length = d.nP)
    -- the copy's constructor at the auxiliary datum
    (hD : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems Ja)) lpsT cA.1 d.nP cA.2
      (d.nIdxAt (d.mems Ja)) d.resSort d.isProp d.large (d.idxF Ja) (d.dsF Ja) (d.esF Ja)
      (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja) (d.eissF Ja) (d.tssF Ja)
      (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hview : d.ksR Ja = d.ksF Ja ∧ d.tgtsR Ja = d.tgts Ja ∧ d.eissR Ja = d.eissF Ja ∧
      d.tssR Ja = d.tssF Ja)
    (hmem : d.mems Ja = k₀ + j₀ + dJ.mems Jc) (hnF : cA.2 = cAJ.2)
    (htgtLt : ∀ i, d.tgts Ja i < d.k)
    (hordRes : ∀ (i : Nat) (x : Expr), (d.xFvsF Ja)[i]? = some x →
      (d.ksF Ja).getD i .ordinary = .ordinary → x.fvarTypeD.constsResolve env = true)
    (hfresh : ∀ t, k₀ ≤ t → t < d.k → env.find? (d.memberName t) = none)
    (hnodupM : ((List.range d.k).map d.memberName).Nodup)
    (hcopyNames : ∀ t, k₀ ≤ t → t < d.k → d.memberName t ∈ (st.types.map (·.name)).drop k₀)
    -- the container's constructor at its datum
    (hDJ : FixCtorDataI mp.base2 dJ.env₀ (dJ.memberName (dJ.mems Jc)) lpsJ cAJ.1 dJ.nP cAJ.2
      (dJ.nIdxAt (dJ.mems Jc)) dJ.resSort dJ.isProp dJ.large (dJ.idxF Jc) (dJ.dsF Jc) (dJ.esF Jc)
      (dJ.srcsF Jc) (dJ.ksF Jc) (dJ.fvsPF Jc) (dJ.xFvsF Jc) (dJ.xrestF Jc) (dJ.eissF Jc) (dJ.tssF Jc)
      (fun i => dJ.memberName (dJ.tgts Jc i)) (fun i => dJ.nIdxAt (dJ.tgts Jc i)))
    (hmemsJ : dJ.mems Jc < dJ.k) (htgtJLt : ∀ i, dJ.tgts Jc i < dJ.k)
    (hkA : ∀ g, g < dJ.k → k₀ + j₀ + g < d.k)
    (hnIdxG : ∀ g, g < dJ.k → d.nIdxAt (k₀ + j₀ + g) = dJ.nIdxAt g)
    (hsort : dJ.w ψ' = d.w ψ)
    -- the pin's readings and the group's pins
    (hDsLen : DsA.length = dJ.nP)
    (hsp : DenoteMetaSpine mp.base2.acval envAux ψ d.nP Ds DsA)
    (hgroup : ∀ g, g < dJ.k → ∃ q, st.pins[j₀ + g]? = some q ∧
      q.pin = Expr.mkAppN (.const (dJ.memberName g) lvls) Ds)
    (hnodupP : (st.pins.map (·.pin)).Nodup)
    (hpinName : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q → d.memberName (k₀ + jq) = q.aux)
    -- the targets' pins: container, levels, components, readings
    (hpin : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q →
      ∃ (lvls' : List Level) (Ds' : List Expr) (cv : ConstantVal) (caps : IndCaps),
        q.container = tgtCont jq ∧ q.pin = Expr.mkAppN (.const (tgtCont jq) lvls') Ds' ∧
        envAux.find? (tgtCont jq) = some (.indInfo cv caps) ∧ lvls'.length = cv.levelParams.length ∧
        (∀ a ∈ Ds', Expr.WScoped d.nP a) ∧
        DenoteMetaSpine mp.base2.acval envAux ψ d.nP Ds' (tgtDsA jq) ∧
        mp.base2.acval (tgtCont jq) (tgtLps jq)
          = mp.base2.acval (tgtCont jq) (Level.substFn ψ cv.levelParams lvls'))
    -- the container's instantiated constructor, read
    {xFvsC : List Expr} {xrestC : Expr}
    (hreadC : ∀ (i : Nat) (xC : Expr), xFvsC[i]? = some xC →
      denoteMeta mp.base2.acval envAux ψ (d.nP + i) xC.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + i)
            ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2))
    (hreadRC : denoteMeta mp.base2.acval envAux ψ (d.nP + cAJ.2) xrestC
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + cAJ.2)
          (ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ' (dJ.esF Jc ψ'))))
    -- the walk
    (hw : CopyCtorWalkFacts μ F env₁ R st k₀ d.nP cAJ.2 blvls params dJ Jc
      (dJ.memberName (dJ.mems Jc)) lvls Ds (d.xFvsF Ja) xFvsC (d.xrestF Ja) xrestC)
    -- the `whnf` arm's content
    (hwhnf : ∀ (i : Nat) (x xC : Expr), (d.xFvsF Ja)[i]? = some x → xFvsC[i]? = some xC →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      WhnfField μ F env₁ R params (d.nP + i) x.fvarTypeD xC.fvarTypeD →
      (i ∈ ConLeche.recIdxOf (d.ksR Ja) → k₀ ≤ d.tgtsR Ja i →
        ¬ (j₀ ≤ d.tgtsR Ja i - k₀ ∧ d.tgtsR Ja i - k₀ < j₀ + dJ.k)) ∧
      ∀ (σ : Nat → V) (ws : List V), ws.length = i → Sat V (d.params ψ).reverse σ →
        SpineFit (consList (DsA.map (interp V σ)) σ)
          ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
        interp V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
            ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2)
          = interp V (consList ws σ) (d.restoreAV mp.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) ∧
        WellDenotedV V (consList ws σ) (d.restoreAV mp.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i))
    -- the container's field at the pin is graded at the record's frames
    (hgradeC : ∀ (i : Nat), i < cAJ.2 → ∀ (σ : Nat → V) (ws : List V), ws.length = i →
      Sat V (d.params ψ).reverse σ →
      SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
      WellDenotedV V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
        ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2)) :
    d.CopyCtorAsRead mp.base2 dJ ψ ψ' DsA k₀ j₀ tgtCont tgtLps tgtDsA Jc Ja cAJ.2 := by
  have hxLen : (d.xFvsF Ja).length = cAJ.2 := by rw [hD.xLen, hnF]
  have hksLenJ : (dJ.ksF Jc).length = cAJ.2 := hDJ.ksLen
  have hxJLen : (dJ.xFvsF Jc).length = cAJ.2 := hDJ.xLen
  have hDsLenE : Ds.length = dJ.nP := by rw [DenoteMetaSpine.length hsp, hDsLen]
  have hw' : dJ.resSort.eval ψ' = d.resSort.eval ψ := hsort
  -- the readings of a fired residual: the target spine, decomposed
  have hresid : ∀ (dp : Nat) (I : Name) (lvls' : List Level) (DsF idxC : List Expr)
      (fa₀ : AnnotTerm) (P E : List AnnotTerm),
      denoteMeta mp.base2.acval envAux ψ dp (Expr.mkAppN (.const I lvls') (DsF ++ idxC))
        = some (AnnotTerm.mkAppN fa₀ (P ++ E)) →
      DsF.length = P.length → idxC.length = E.length →
      ∃ (fa : AnnotTerm) (vs₁ : List AnnotTerm),
        denoteMeta mp.base2.acval envAux ψ dp (.const I lvls') = some fa ∧ fa₀ = fa ∧
        DenoteMetaSpine mp.base2.acval envAux ψ dp DsF vs₁ ∧ P = vs₁ ∧
        DenoteMetaSpine mp.base2.acval envAux ψ dp idxC E := by
    intro dp I lvls' DsF idxC fa₀ P E hb hl1 hl2
    obtain ⟨fa, vs, hfa, hvs, hB⟩ := denoteMeta_mkAppN_inv hb
    obtain ⟨vs₁, vs₂, rfl, hvs₁, hvs₂⟩ := DenoteMetaSpine.append_inv hvs
    have hlen1 : vs₁.length = P.length := by rw [← DenoteMetaSpine.length hvs₁, hl1]
    have hlen2 : vs₂.length = E.length := by rw [← DenoteMetaSpine.length hvs₂, hl2]
    obtain ⟨hfaE, hvsE⟩ := mkAppN_inj_args hB
      (by rw [List.length_append, List.length_append, hlen1, hlen2])
    obtain ⟨hP, hEv⟩ := List.append_inj hvsE hlen1.symm
    exact ⟨fa, vs₁, hfa, hfaE, hvs₁, hP, hEv ▸ hvs₂⟩
  refine ⟨hmem, ?_, ?_, ?_, ?_⟩
  -- ## kindR
  · intro i hi
    obtain ⟨hiLt, hkJ⟩ := mem_recIdxOf.mp hi
    have hi' : i < cAJ.2 := by rw [← hksLenJ]; exact hiLt
    have hiA : i < cA.2 := by rw [hnF]; exact hi'
    obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF Ja)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hxLen]; exact hi')⟩
    obtain ⟨xC, hxC⟩ : ∃ xC, xFvsC[i]? = some xC :=
      ⟨_, List.getElem?_eq_getElem (by rw [hw.lenC]; exact hi')⟩
    obtain ⟨xJ, hxJ⟩ : ∃ xJ, (dJ.xFvsF Jc)[i]? = some xJ :=
      ⟨_, List.getElem?_eq_getElem (by rw [hxJLen]; exact hi')⟩
    obtain ⟨hpb, n, afvs, afvsC, aux, I, lvls', DsF, idx, idxC, hopA, hopC, hnA, hnC, hafvs, -,
      hidxLen, hidxEE, q, hq, hqa, hqc, hqp, hqg⟩ := hw.fieldRec i x xC hx hxC hi
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hq
    obtain ⟨hnotOrd, hname, hrecIff⟩ :=
      copyKind_of_fire mp hdk hD hordRes hfresh hpinName hx hopA hnA hjq hqa
    -- the fire's pin is the group-mate's
    obtain ⟨hI, hlv, hDsF⟩ := mkAppN_const_inj (hqp.symm.trans hqg)
    subst hI; subst hlv; subst hDsF
    have htgtJ : dJ.tgts Jc i < dJ.k := htgtJLt i
    obtain ⟨q', hq', hq'p⟩ := hgroup _ htgtJ
    have hjqE : jq = j₀ + dJ.tgts Jc i := pins_index_inj hnodupP hjq hq' (hqg.trans hq'p.symm)
    have htgtA : d.tgts Ja i = k₀ + j₀ + dJ.tgts Jc i := by
      refine memberName_inj hnodupM (htgtLt i) (hkA _ htgtJ) ?_
      rw [hname, ← hqa, ← hpinName jq q hjq, hjqE, Nat.add_assoc]
    -- the kinds agree
    have hkinds : (d.ksF Ja).getD i .ordinary = (dJ.ksF Jc).getD i .ordinary := by
      rcases hkJ with hkJr | hkJf
      · obtain ⟨hheadJ, -⟩ := hDJ.opened.recF i xJ hxJ hkJr
        have hn0 : n = 0 := by
          rw [← hnA, ← hpb xJ hxJ, piBinders_nil_of_getAppFn_const _ hheadJ]; rfl
        rw [hkJr]; exact hrecIff.mpr hn0
      · obtain ⟨afvsJ, bodyJ, hopenJ, hneJ, -⟩ := hDJ.opened.reflF i xJ hxJ hkJf
        have hn0 : n ≠ 0 := by
          intro h0
          apply hneJ
          rw [openPisAtFvars_length _ hopenJ, hpb xJ hxJ, hnA, h0]
        rcases hD.opened.kinds i hiA with hord | hrec | hrefl
        · exact absurd hord hnotOrd
        · exact absurd (hrecIff.mp hrec) hn0
        · rw [hrefl, hkJf]
    have hreadX := hreadC i xC hxC
    have hnIdxT : d.nIdxAt (d.tgts Ja i) = dJ.nIdxAt (dJ.tgts Jc i) := by
      rw [htgtA]; exact hnIdxG _ htgtJ
    refine ⟨by rw [hview.1, hkinds], by rw [hview.2.1, htgtA], ?_⟩
    rcases hkJ with hkJr | hkJf
    · -- the container's field is recursive: no telescope
      obtain ⟨hheadJ, -⟩ := hDJ.opened.recF i xJ hxJ hkJr
      have hn0 : n = 0 := by
        rw [← hnA, ← hpb xJ hxJ, piBinders_nil_of_getAppFn_const _ hheadJ]; rfl
      subst hn0
      have hkAr : (d.ksF Ja).getD i .ordinary = .recursive := by rw [hkinds, hkJr]
      have htssA : (d.tssF Ja ψ).getD i [] = [] :=
        hD.tssNone ψ i (by rw [hkAr]; intro h; exact nomatch h)
      have htssJ : (dJ.tssF Jc ψ').getD i [] = [] :=
        hDJ.tssNone ψ' i (by rw [hkJr]; intro h; exact nomatch h)
      refine ⟨by rw [hview.2.2.2, htssA, htssJ]; rfl, ?_⟩
      simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopA hopC
      obtain ⟨-, hxE⟩ := hopA
      obtain ⟨-, hxCE⟩ := hopC
      have hspA : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + i) idx ((d.eissF Ja ψ).getD i []) := by
        have := hD.eisRead ψ i x hx hkAr
        rw [hxE, getAppArgs_mkAppN_const_drop hparams] at this
        exact this
      rw [hDJ.recEntry ψ' i hkJr hi', instSeq_mkAppN_annot, instSeq_acval, List.map_append, hxCE]
        at hreadX
      obtain ⟨-, -, -, -, -, -, hE⟩ := hresid _ _ _ _ _ _ _ _ hreadX
        (by rw [List.length_map, hDsLenE]; simp [paramBvarsAt])
        (by rw [← hidxLen, DenoteMetaSpine.length hspA, hD.eisLen ψ i hkAr hiA, hnIdxT,
              List.length_map, hDJ.eisLen ψ' i hkJr hi'])
      have hspC : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + i) idx
          (((dJ.eissF Jc ψ').getD i []).map (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + i))) :=
        DenoteMetaSpine.erasedEq hE hidxLen.symm
          fun k e eC he heC => (hidxEE k eC e heC he).symm
      rw [hview.2.2.1, DenoteMetaSpine.unique hspA hspC, htssJ]
      simp only [List.length_nil, Nat.add_zero]
      exact List.map_congr_left fun e _ => instSeq_cut_congr hDsLen i e
    · -- the container's field is reflexive: the telescope, binder by binder
      have hkAf : (d.ksF Ja).getD i .ordinary = .reflexive := by rw [hkinds, hkJf]
      obtain ⟨afvs', body', hopen', hlenT, hbind, hspA'⟩ := hD.reflOpen ψ i x hx hkAf
      have htssLen : ((d.tssF Ja ψ).getD i []).length = n := by rw [hlenT, hnA]
      rw [htssLen, hopA] at hopen'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopen')
      have hspA : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + i + n) idx
          ((d.eissF Ja ψ).getD i []) := by
        rw [htssLen, getAppArgs_mkAppN_const_drop hparams] at hspA'
        exact hspA'
      obtain ⟨afvsJ, bodyJ, hopenJ, hlenTJ, -, -⟩ := hDJ.reflOpen ψ' i xJ hxJ hkJf
      have htssLenJ : ((dJ.tssF Jc ψ').getD i []).length = n := by rw [hlenTJ, hpb xJ hxJ, hnA]
      rw [hDJ.reflEntry ψ' i hkJf hi', instSeq_mkPisAV DsA _ _ _ (by omega)] at hreadX
      obtain ⟨pps, b, hst, hb, hlenP, hbindC⟩ := denoteMeta_openPis n hopC hreadX
      have hlenI : n ≤ (instSeqDoms DsA (dJ.nP - 1 + i) ((dJ.tssF Jc ψ').getD i [])).length := by
        rw [instSeqDoms_length, htssLenJ]; exact Nat.le_refl _
      rw [stripPisAV_mkPisAV_take n _ _ hlenI] at hst
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨hpps, hbE⟩ := hst
      have hdropN : (instSeqDoms DsA (dJ.nP - 1 + i) ((dJ.tssF Jc ψ').getD i [])).drop n = [] := by
        rw [List.drop_eq_nil_iff, instSeqDoms_length, htssLenJ]; exact Nat.le_refl _
      have htakeN : (instSeqDoms DsA (dJ.nP - 1 + i) ((dJ.tssF Jc ψ').getD i [])).take n
          = instSeqDoms DsA (dJ.nP - 1 + i) ((dJ.tssF Jc ψ').getD i []) :=
        List.take_of_length_le (by rw [instSeqDoms_length, htssLenJ]; exact Nat.le_refl _)
      rw [hdropN] at hbE
      simp only [mkPisAV] at hbE
      rw [htakeN] at hpps
      -- the telescopes agree
      have htss : (d.tssF Ja ψ).getD i []
          = instSeqDoms DsA (dJ.nP - 1 + i) ((dJ.tssF Jc ψ').getD i []) := by
        refine List.ext_getElem? fun k => ?_
        by_cases hk : k < n
        · obtain ⟨a, ha⟩ : ∃ a, afvs[k]? = some a :=
            ⟨_, List.getElem?_eq_getElem (by rw [openPisAtFvars_length n hopA]; exact hk)⟩
          obtain ⟨aC, haC⟩ : ∃ aC, afvsC[k]? = some aC :=
            ⟨_, List.getElem?_eq_getElem (by rw [openPisAtFvars_length n hopC]; exact hk)⟩
          have hrA := hbind k a ha
          obtain ⟨p, hp, -, hpd⟩ := hbindC k aC haC
          rw [← hpps] at hp
          obtain ⟨tA, htA⟩ : ∃ tA, ((d.tssF Ja ψ).getD i [])[k]? = some tA :=
            ⟨_, List.getElem?_eq_getElem (by rw [htssLen]; exact hk)⟩
          have hgetD : ((d.tssF Ja ψ).getD i []).getD k default = tA := by
            rw [List.getD_eq_getElem?_getD, htA]; rfl
          rw [hgetD] at hrA
          have heq : tA.2.2 = p.2.2 := by
            rw [denoteMeta_erasedEq (hafvs k a aC ha haC)] at hrA
            exact Option.some.inj (hrA.symm.trans hpd)
          have hpJ := hp
          rw [instSeqDoms_getElem?] at hpJ
          obtain ⟨tJ, htJ, hptJ⟩ := Option.map_eq_some_iff.mp hpJ
          obtain ⟨h1A, h2A⟩ := hD.tssPiBits ψ i tA (List.mem_of_getElem? htA)
          obtain ⟨h1J, h2J⟩ := hDJ.tssPiBits ψ' i tJ (List.mem_of_getElem? htJ)
          have hbA := hD.tssBits ψ i tA (List.mem_of_getElem? htA)
          have hbJ := hDJ.tssBits ψ' i tJ (List.mem_of_getElem? htJ)
          rw [htA, hp, ← hptJ]
          congr 1
          refine Prod.ext (by rw [h1A, h1J]) (Prod.ext ?_ (by rw [← hptJ] at heq; exact heq))
          exact bit_eq_of_le_one h2A h2J (by rw [hbA, hbJ, hw'])
        · rw [List.getElem?_eq_none (by rw [htssLen]; omega),
            List.getElem?_eq_none (by rw [instSeqDoms_length, htssLenJ]; omega)]
      refine ⟨by rw [hview.2.2.2, htss, instSeqDoms_cut_congr hDsLen], ?_⟩
      -- the index readings, from the residual
      rw [← hbE, htssLenJ, instSeq_mkAppN_annot, instSeq_acval, List.map_append] at hb
      obtain ⟨-, -, -, -, -, -, hE⟩ := hresid _ _ _ _ _ _ _ _ hb
        (by rw [List.length_map, hDsLenE]; simp [paramBvarsAt])
        (by rw [← hidxLen, DenoteMetaSpine.length hspA, hD.eisLenRefl ψ i hkAf hiA, hnIdxT,
              List.length_map, hDJ.eisLenRefl ψ' i hkJf hi'])
      have hspC : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + i + n) idx
          (((dJ.eissF Jc ψ').getD i []).map
            (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + i + n))) :=
        DenoteMetaSpine.erasedEq hE hidxLen.symm
          fun k e eC he heC => (hidxEE k eC e heC he).symm
      rw [hview.2.2.1, DenoteMetaSpine.unique hspA hspC, htssLenJ]
      refine List.map_congr_left fun e _ => ?_
      rw [Nat.add_assoc (dJ.nP - 1) i n, instSeq_cut_congr hDsLen (i + n), Nat.add_assoc dJ.nP i n]
  -- ## kindT
  · intro i hi hT hA hk
    obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF Ja)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hxLen]; exact hi)⟩
    obtain ⟨xC, hxC⟩ : ∃ xC, xFvsC[i]? = some xC :=
      ⟨_, List.getElem?_eq_getElem (by rw [hw.lenC]; exact hi)⟩
    have hiA : i < cA.2 := by rw [hnF]; exact hi
    rw [hview.1] at hA
    obtain ⟨-, hkA⟩ := mem_recIdxOf.mp hA
    rw [hview.2.1] at hk
    rcases hw.fieldOrd i x xC hx hxC hT with ⟨-, hnoCopy⟩ | hF | hW
    · -- unfired: the copy mentions its target, a copy
      exfalso
      have hmention : x.fvarTypeD.mentionsConstE (d.memberName (d.tgts Ja i)) = true := by
        rcases hkA with hk' | hk'
        · obtain ⟨hhead, -⟩ := hD.opened.recF i x hx hk'
          exact ConLeche.Expr.mentionsConstE_of_getAppFn _ _ hhead
        · obtain ⟨afvs, body, hopen, -, -, hhead, -⟩ := hD.opened.reflF i x hx hk'
          exact ConLeche.openPisAtFvars_mentionsConstE _ _ _ hopen
            (Or.inl (ConLeche.Expr.mentionsConstE_of_getAppFn _ _ hhead))
      have := hnoCopy _ (hcopyNames (d.tgts Ja i) hk (htgtLt i))
      rw [this] at hmention
      exact nomatch hmention
    · -- a fire: the target is the fire's pin, outside the group
      obtain ⟨n, afvs, afvsC, aux, I, lvls', DsF, idx, idxC, hopA, hopC, hnA, hnC, hafvs, hmeta,
        hidxLen, hidxEE, q, hq, hqa, hqc, hqp, hqg⟩ := hF
      obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hq
      obtain ⟨hnotOrd, hname, hrecIff⟩ :=
        copyKind_of_fire mp hdk hD hordRes hfresh hpinName hx hopA hnA hjq hqa
      have hjqLt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
      have htgtA : d.tgts Ja i = k₀ + jq := by
        refine memberName_inj hnodupM (htgtLt i) (by omega) ?_
        rw [hname, ← hqa, ← hpinName jq q hjq]
      -- the target pin's data
      obtain ⟨lvls'', Ds'', cv, caps, hqc', hqp', hfind, hlenL, hDs''w, hsp'', hacv⟩ := hpin jq q hjq
      obtain ⟨hI, hlv, hDsF⟩ := mkAppN_const_inj (hqp.symm.trans hqp')
      subst hI; subst hlv; subst hDsF
      -- the copy's spine at the field's depth, and its telescope
      have hspA : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + i + n) idx
          ((d.eissF Ja ψ).getD i []) ∧
          ((d.tssF Ja ψ).getD i []).length = n ∧
          ((d.dsF Ja ψ).getD (d.nP + i) default).2.2
            = mkPisAV ((d.tssF Ja ψ).getD i [])
                (AnnotTerm.mkAppN (mp.base2.acval (d.memberName (d.tgts Ja i)) ψ)
                  (paramBvarsAt d.nP (d.nP + i + ((d.tssF Ja ψ).getD i []).length) ++
                    (d.eissF Ja ψ).getD i [])) := by
        rcases hkA with hk' | hk'
        · have hn0 : n = 0 := hrecIff.mp hk'
          subst hn0
          simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopA
          obtain ⟨-, hxE⟩ := hopA
          have htssA : (d.tssF Ja ψ).getD i [] = [] :=
            hD.tssNone ψ i (by rw [hk']; intro h; exact nomatch h)
          refine ⟨?_, by rw [htssA]; rfl, ?_⟩
          · have := hD.eisRead ψ i x hx hk'
            rw [hxE, getAppArgs_mkAppN_const_drop hparams] at this
            simpa using this
          · rw [hD.recEntry ψ i hk' hiA, htssA]
            rfl
        · obtain ⟨afvs', body', hopen', hlenT, -, hspA'⟩ := hD.reflOpen ψ i x hx hk'
          have htssLen : ((d.tssF Ja ψ).getD i []).length = n := by rw [hlenT, hnA]
          rw [htssLen, hopA] at hopen'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopen')
          rw [htssLen, getAppArgs_mkAppN_const_drop hparams] at hspA'
          exact ⟨hspA', htssLen, hD.reflEntry ψ i hk' hiA⟩
      obtain ⟨hspA, htssLen, hentryA⟩ := hspA
      -- the copy's own reading, peeled: its telescope with the bits of its binders
      obtain ⟨bsA, bsC, rA, rC, hstA, hstC, hmetaEq⟩ := hmeta
      have hreadA := hD.domRead ψ i x hx
      obtain ⟨ppsA, bA, hYA, -, hlenPA, hbindA⟩ := denoteMeta_openPis' n hopA hstA hreadA
      rw [hentryA] at hYA
      obtain ⟨hppsA, -⟩ := mkPisAV_inj (by rw [htssLen, hlenPA]) hYA
      -- the container's instantiated reading, peeled
      have hreadX := hreadC i xC hxC
      obtain ⟨pps, b, hY, hb, hlenP, hbindC⟩ := denoteMeta_openPis' n hopC hstC hreadX
      -- the residual: the target's leaf at its readings lifted, and the copy's index readings
      obtain ⟨fa, vs, hfa, hvs, hB⟩ := denoteMeta_mkAppN_inv hb
      obtain ⟨vs₁, vs₂, rfl, hvs₁, hvs₂⟩ := DenoteMetaSpine.append_inv hvs
      have hvs₁E : vs₁ = (tgtDsA jq).map (·.liftN (i + n) 0) := by
        have hlift := DenoteMetaSpine.weaken_by mp.base2 (i + n) hsp'' hDs''w
        rw [← Nat.add_assoc] at hlift
        exact DenoteMetaSpine.unique hvs₁ hlift
      have hvs₂E : vs₂ = (d.eissF Ja ψ).getD i [] := by
        refine DenoteMetaSpine.unique hvs₂ ?_
        exact DenoteMetaSpine.erasedEq hspA hidxLen fun k e eC he heC => hidxEE k e eC he heC
      have hfaE : fa = mp.base2.acval (tgtCont jq) (tgtLps jq) := by
        rw [denoteMeta_const hfind hlenL] at hfa
        rw [hacv]
        exact (Option.some.inj hfa).symm
      -- the telescopes agree, bit for bit
      have hpps : pps = (d.tssF Ja ψ).getD i [] := by
        rw [hppsA]
        refine List.ext_getElem? fun k => ?_
        by_cases hk : k < n
        · obtain ⟨a, ha⟩ : ∃ a, afvs[k]? = some a :=
            ⟨_, List.getElem?_eq_getElem (by rw [openPisAtFvars_length n hopA]; exact hk)⟩
          obtain ⟨aC, haC⟩ : ∃ aC, afvsC[k]? = some aC :=
            ⟨_, List.getElem?_eq_getElem (by rw [openPisAtFvars_length n hopC]; exact hk)⟩
          obtain ⟨pA, hpA, h1A, ⟨bmA, hbmA, hbitA⟩, hpdA⟩ := hbindA k a ha
          obtain ⟨pC, hpC, h1C, ⟨bmC, hbmC, hbitC⟩, hpdC⟩ := hbindC k aC haC
          have heq : pA.2.2 = pC.2.2 := by
            rw [denoteMeta_erasedEq (hafvs k a aC ha haC)] at hpdA
            exact Option.some.inj (hpdA.symm.trans hpdC)
          have hpe : pA = pC :=
            Prod.ext (by rw [h1A, h1C])
              (Prod.ext (by rw [hbitA, hbitC, hmetaEq k bmA bmC hbmA hbmC]) heq)
          rw [hpA, hpC, hpe]
        · rw [List.getElem?_eq_none (by rw [hlenP]; omega),
            List.getElem?_eq_none (by rw [hlenPA]; omega)]
      -- the container's instantiated reading IS the transport's target term
      have htarget : ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
          ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2
          = mkPisAV ((d.tssR Ja ψ).getD i [])
              (AnnotTerm.mkAppN (mp.base2.acval (tgtCont jq) (tgtLps jq))
                ((tgtDsA jq).map (·.liftN (i + ((d.tssR Ja ψ).getD i []).length) 0) ++
                  (d.eissR Ja ψ).getD i [])) := by
        rw [← instSeq_cut_congr hDsLen, hY, hB, hpps, hfaE, hvs₁E, hvs₂E, hview.2.2.1, hview.2.2.2,
          htssLen]
      refine ⟨jq, by rw [hview.2.1, htgtA], ?_, ?_, ?_⟩
      · rintro ⟨hle, hlt⟩
        obtain ⟨q', hq', hq'p⟩ := hgroup (jq - j₀) (by omega)
        rw [show j₀ + (jq - j₀) = jq by omega] at hq'
        obtain rfl := Option.some.inj (hjq.symm.trans hq')
        exact hqg (jq - j₀) (by omega) hq'p
      · intro σ ws hws hsat hfit
        rw [htarget]
      · intro σ ws hws hsat hfit
        rw [← htarget]
        exact hgradeC i hi σ ws hws hsat hfit
    · -- the `whnf` arm
      obtain ⟨hnotG, hW'⟩ := hwhnf i x xC hx hxC hT hW
      have hcond : i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i := by
        rw [hview.1, hview.2.1]; exact ⟨hA, hk⟩
      have hres : d.restoreAV mp.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i
          = mkPisAV ((d.tssR Ja ψ).getD i [])
              (AnnotTerm.mkAppN (mp.base2.acval (tgtCont (d.tgtsR Ja i - k₀))
                  (tgtLps (d.tgtsR Ja i - k₀)))
                ((tgtDsA (d.tgtsR Ja i - k₀)).map
                    (·.liftN (i + ((d.tssR Ja ψ).getD i []).length) 0) ++
                  (d.eissR Ja ψ).getD i [])) := by
        unfold IndRepData.restoreAV
        rw [if_pos hcond]
      refine ⟨d.tgtsR Ja i - k₀, by rw [hview.2.1]; omega, hnotG hcond.1 hcond.2, ?_, ?_⟩
      · intro σ ws hws hsat hfit
        rw [← hres]
        exact (hW' σ ws hws hsat hfit).1
      · intro σ ws hws hsat hfit
        rw [← hres]
        exact (hW' σ ws hws hsat hfit).2
  -- ## ord
  · intro i hi hT hcopy
    obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF Ja)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hxLen]; exact hi)⟩
    obtain ⟨xC, hxC⟩ : ∃ xC, xFvsC[i]? = some xC :=
      ⟨_, List.getElem?_eq_getElem (by rw [hw.lenC]; exact hi)⟩
    have hiA : i < cA.2 := by rw [hnF]; exact hi
    rcases hw.fieldOrd i x xC hx hxC hT with ⟨hEE, -⟩ | hF | hW
    · -- unfired: one reading
      have h1 := hD.domRead ψ i x hx
      have h2 := hreadC i xC hxC
      rw [denoteMeta_erasedEq hEE] at h1
      have heq := Option.some.inj (h1.symm.trans h2)
      intro σ ws hws hsat hfit
      rw [heq, instSeq_cut_congr hDsLen]
    · -- a fire: the copy's target would be a copy
      exfalso
      obtain ⟨n, afvs, afvsC, aux, I, lvls', DsF, idx, idxC, hopA, hopC, hnA, hnC, hafvs, -,
        hidxLen, hidxEE, q, hq, hqa, hqc, hqp, hqg⟩ := hF
      obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hq
      obtain ⟨hnotOrd, hname, hrecIff⟩ :=
        copyKind_of_fire mp hdk hD hordRes hfresh hpinName hx hopA hnA hjq hqa
      have hjqLt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
      have htgtA : d.tgts Ja i = k₀ + jq := by
        refine memberName_inj hnodupM (htgtLt i) (by omega) ?_
        rw [hname, ← hqa, ← hpinName jq q hjq]
      rcases hcopy with hcopy | hcopy
      · apply hcopy
        rw [hview.1]
        refine mem_recIdxOf.mpr ⟨by rw [hD.ksLen]; exact hiA, ?_⟩
        rcases hD.opened.kinds i hiA with hord | hrec | hrefl
        · exact absurd hord hnotOrd
        · exact Or.inl hrec
        · exact Or.inr hrefl
      · rw [hview.2.1, htgtA] at hcopy
        omega
    · -- the `whnf` arm
      obtain ⟨-, hW'⟩ := hwhnf i x xC hx hxC hT hW
      have hcond : ¬ (i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i) := by
        rintro ⟨hA, hk⟩
        rcases hcopy with hcopy | hcopy
        · exact hcopy hA
        · omega
      have hres : d.restoreAV mp.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i
          = ((d.dsF Ja ψ).getD (d.nP + i) default).2.2 := by
        unfold IndRepData.restoreAV
        rw [if_neg hcond]
      intro σ ws hws hsat hfit
      rw [← hres]
      exact ((hW' σ ws hws hsat hfit).1).symm
  -- ## es
  · obtain ⟨aux, idx, idxC, hxr, hxrC, hidxLen, hidxEE⟩ := hw.resid
    have hspA : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + cAJ.2) idx (d.esF Ja ψ) := by
      have := hD.idxRead ψ
      rw [hD.idxEq, hxr, getAppArgs_mkAppN_const_drop hparams, hnF] at this
      exact this
    have hread := hreadRC
    rw [hxrC] at hread
    unfold ctorBodyAVI at hread
    rw [instSeq_mkAppN_annot, instSeq_acval, List.map_append] at hread
    have hlenP : (paramBvars dJ.nP cAJ.2).length = dJ.nP := by simp [paramBvars]
    obtain ⟨-, -, -, -, -, -, hE⟩ := hresid _ _ _ _ _ _ _ _ hread
      (by rw [List.length_map, hlenP, hDsLenE])
      (by rw [← hidxLen, DenoteMetaSpine.length hspA, hD.lenE ψ, hmem, hnIdxG _ hmemsJ,
            List.length_map, hDJ.lenE ψ'])
    have hspC : DenoteMetaSpine mp.base2.acval envAux ψ (d.nP + cAJ.2) idx
        ((dJ.esF Jc ψ').map (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + cAJ.2))) :=
      DenoteMetaSpine.erasedEq hE hidxLen.symm fun k e eC he heC => (hidxEE k eC e heC he).symm
    rw [DenoteMetaSpine.unique hspA hspC]
    exact List.map_congr_left fun e _ => instSeq_cut_congr hDsLen cAJ.2 e


/-! ## The container's field at the pin is graded (`hgradeC`) -/

/-- A fit transfers along a `Sat`-implication of the telescopes (the
values are re-read off the satisfying frame). -/
theorem spineFit_of_satIff {Γ₁ Γ₂ : List AnnotTerm} {σ : Nat → V} {vals : List V}
    (hlen : Γ₂.length = Γ₁.length)
    (hiff : ∀ ρ : Nat → V, Sat V Γ₁.reverse ρ → Sat V Γ₂.reverse ρ)
    (hfit : SpineFit σ Γ₁ vals) : SpineFit σ Γ₂ vals := by
  have h1 := sat_of_spineFit (Δ₀ := []) (Sat_nil V σ) hfit
  rw [List.append_nil] at h1
  have h2 := hiff _ h1
  have h3 := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact h2)
  have hv : vals.length = Γ₂.length := by rw [hlen, ← hfit.length_eq]
  rw [range_reverse_map_consList' hv] at h3
  have hσ : (fun j => consList vals σ (j + Γ₂.length)) = σ := by
    funext j; rw [← hv, consList_apply_add]
  rw [hσ] at h3
  exact h3

/-- **The container's instantiated field is graded at the record's
frames** (`copyCtorAsRead_of_walkFacts`'s `hgradeC`): the container's
constructor tower is graded everywhere (`CtorDataI.okTy`); the pin's
readings fit its parameter binders (`pinFit_of_leafShape` against the
member's former, moved to the constructor's own parameter telescope by
`paramsIffM`/`paramsIff`); with `i` earlier values fitting the field
domains at the pin the `nPJ + i`-th binder is graded there
(`wellDenoted_mkPisAV_dom`/`annotValid_mkPisAV_dom`), and the
substitution moves the frame to the block's (`wellDenotedV_instSeq_under`). -/
theorem gradeC_of_okTy {μ : CheckMode} {envAux : Env} (mp : EnvModelM V μ envAux)
    {d dJ : IndRepData V} {ψ ψ' : Name → Nat} {DsA : List AnnotTerm} {Jc mmJ : Nat}
    {cAJ : ConstantVal × Nat} {T : Name} {lpsJ : List Name} {nIdx : Nat} {isProp large : Bool}
    {idxArgs : List Expr} {srcs : List (Option Nat)}
    (hDJ : CtorDataI mp.base2 T lpsJ cAJ.1 dJ.nP cAJ.2 nIdx dJ.resSort isProp large idxArgs
      (dJ.dsF Jc) (dJ.esF Jc) srcs)
    (hFFJ : dJ.FormerFacts mp.base2 ψ' mmJ) (hLSJ : dJ.LeafShape mp.base2 ψ' mmJ)
    (hpin : d.PinRead ψ (mp.base2.acval (dJ.memberName mmJ) ψ') DsA dJ.nP)
    (hpIffM : ∀ ρ : Nat → V, Sat V (dJ.params ψ').reverse ρ ↔
      Sat V (((dJ.ppsM mmJ ψ').take dJ.nP).map (·.2.2)).reverse ρ)
    (hpIffC : ∀ ρ : Nat → V, Sat V (dJ.params ψ').reverse ρ ↔
      Sat V (((dJ.dsF Jc ψ').take dJ.nP).map (·.2.2)).reverse ρ) :
    ∀ (i : Nat), i < cAJ.2 → ∀ (σ : Nat → V) (ws : List V), ws.length = i →
      Sat V (d.params ψ).reverse σ →
      SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
      WellDenotedV V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
        ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2) := by
  intro i hi σ ws hws hσ hfit
  have hlenD : DsA.length = dJ.nP := hpin.len
  have hDsWD : ∀ w ∈ DsA, WellDenotedV V σ w := WellDenotedV_mkAppN_args DsA (hpin.wd σ hσ)
  have hfitP := IndRepData.pinFit_of_leafShape d rfl hFFJ hLSJ hpin hσ
  obtain ⟨hlenPP, -, -, -⟩ := hFFJ
  have hlenDs := hDJ.len ψ'
  have hfitC : SpineFit σ (((dJ.dsF Jc ψ').take dJ.nP).map (·.2.2)) (DsA.map (interp V σ)) :=
    spineFit_of_satIff
      (by rw [List.length_map, List.length_map, List.length_take, List.length_take, hlenDs, hlenPP]
          simp)
      (fun ρ h => (hpIffC ρ).mp ((hpIffM ρ).mpr h)) hfitP
  have hfitAll : SpineFit σ (((dJ.dsF Jc ψ').take (dJ.nP + i)).map (·.2.2))
      (DsA.map (interp V σ) ++ ws) := by
    have := SpineFit.append hfitC hfit
    rw [← List.map_append, ← List.take_add] at this
    exact this
  obtain ⟨dd, hdd⟩ : ∃ dd, (dJ.dsF Jc ψ')[dJ.nP + i]? = some dd :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenDs]; omega)⟩
  have hgetD : (dJ.dsF Jc ψ').getD (dJ.nP + i) default = dd := by
    rw [List.getD_eq_getElem?_getD, hdd]; rfl
  have hok := hDJ.okTy ψ' σ
  have h1 := wellDenoted_mkPisAV_dom hok.1 _ _ dd hdd hfitAll
  have h2 := annotValid_mkPisAV_dom hok.2 _ _ dd hdd hfitAll
  rw [consList_append] at h1 h2
  rw [hgetD]
  refine wellDenotedV_instSeq_under σ DsA ws (dJ.nP + i - 1) dd.2.2 (fun hne => ?_) hDsWD ⟨h1, h2⟩
  have : DsA.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
  rw [hlenD, hws]
  omega

end ConLeche.Model
