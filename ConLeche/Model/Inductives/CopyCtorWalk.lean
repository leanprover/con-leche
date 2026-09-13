module

public import ConLeche.Model.Inductives.CopyCtorRun
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
erasure-equal; the pin `⟨aux, I, I lvls' DsF⟩` is in the table and
satisfies `P`.  Erasure equality is what the readings are blind to
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
    idx.length = idxC.length ∧
    (∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC) ∧
    ∃ q ∈ st.pins, q.aux = aux ∧ q.container = I ∧ q.pin = Expr.mkAppN (.const I lvls') DsF ∧ P q

/-- **A field the positivity normalisation `whnf`'d** (K.17's witness
at the field): the container's instantiated field `eC` reduces, at the
environment holding the block's formers, to the RESTORED copy field
(the copy's stored field with every copy application put back to its
container at the pin), and `eC` carries the reduction's guards. -/
@[expose] def WhnfField (μ : CheckMode) (F : Nat) (env₁ : Env) (R : ConLeche.RestoreTbl) (dpt : Nat)
    (eA eC : Expr) : Prop :=
  ∃ (dsR eR : Expr), ConLeche.whnf μ env₁ F dpt eC = .ok dsR ∧
    ConLeche.restoreNested R eA = .ok eR ∧ Expr.ErasedEq dsR eR ∧
    Expr.WScoped dpt eC ∧ eC.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded eC

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
      ∀ T ∈ (st.types.map (·.name)).drop k₀, x.fvarTypeD.mentionsConst T = false) ∨
    FiredField st blvls params
      (fun q => ∀ g, g < dJ.k → q.pin ≠ Expr.mkAppN (.const (dJ.memberName g) lvls) Ds)
      (nP + i) x.fvarTypeD xC.fvarTypeD ∨
    WhnfField μ F env₁ R (nP + i) x.fvarTypeD xC.fvarTypeD

end ConLeche.Model
