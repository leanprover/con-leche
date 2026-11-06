module

public import ConLeche.Model.Modular.RestrictBase
import ConLeche.Verify.Inductives.ReplaceApps

public section

/-!
# A context's recorded blocks, read from their sources

The fifth part of `ctxModel` (`Model/Modular/Restrict.lean`): the context records, for every
type former it stores, the blocks its source records that list it (`CtxSrc.lfpList`).  A block's
members are its former's group (`IndCaps.all`) and their constructors (`CtxRead.ctors`), all read
alike from that source and stored identically, and what the block's clauses read of their types
is read alike (`CtxRead.deep`), so each clause is the source's (`CtxSrc.lfp_ok`), and so is the
constructor ownership (`CtxSrc.lfpOwn`).  A member whose stored type does not show its telescope
is read at the telescope its block read, which the bundle's `defh` supplies.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term SetTheory

universe w

/-! ## Resolution through the canonical crest -/

theorem constsResolve_instantiate1_any {E : Env} {a : Expr} (ha : a.constsResolve E = true) :
    ∀ (e : Expr) (k : Nat), e.constsResolve E = true →
      (e.instantiate1 a k).constsResolve E = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [Expr.constsResolve]

theorem constsResolve_instPisWith {E : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, a.constsResolve E = true) →
      e.constsResolve E = true → instPisWith as e = some r → r.constsResolve E = true
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [Expr.constsResolve, Bool.and_eq_true] at he
      exact constsResolve_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (constsResolve_instantiate1_any (has a List.mem_cons_self) b 0 he.2) h'

theorem constsResolve_replaceApps {E : Env} {f : Name → List Level → Option Expr} {b n : Nat}
    (hf : ∀ c us e, f c us = some e → e.constsResolve E = true) :
    ∀ (e : Expr), e.constsResolve E = true → (e.replaceApps f b n).constsResolve E = true := by
  intro e
  induction e with
  | bvar i => intro _; simp [Expr.replaceApps, Expr.constsResolve]
  | fvar i ty ih => intro h; simpa [Expr.replaceApps, Expr.constsResolve] using h
  | sort u => intro _; simp [Expr.replaceApps, Expr.constsResolve]
  | const c us =>
    intro h
    rw [Expr.replaceApps_const]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := Expr.appHole?_some hr
      exact hf _ _ _ hc
    · exact h
  | lit l => intro h; simpa [Expr.replaceApps] using h
  | app a x iha ihx =>
    intro h
    rw [Expr.replaceApps_app]
    split
    · rename_i r hr
      obtain ⟨c', us', hc⟩ := Expr.appHole?_some hr
      exact hf _ _ _ hc
    · simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨iha h.1, ihx h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [Expr.replaceApps, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [Expr.replaceApps, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.replaceApps, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.replaceApps, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

theorem canonParams_constsResolve {E : Env} (n : Nat) :
    ∀ x ∈ canonParams n, x.constsResolve E = true := fun x hx => by
  obtain ⟨i, -, rfl⟩ := mem_canonParams hx
  simp [Expr.constsResolve]

theorem canonOf_constsResolve {E : Env} {ty A : Expr} (he : ty.constsResolve E = true)
    (hA : CanonOf ty A) : A.constsResolve E = true := by
  rcases hA with ⟨names, us, n, hA⟩ | ⟨n, hA⟩
  · unfold nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    refine constsResolve_replaceApps (fun c us' r hr => ?_) _
      (constsResolve_instPisWith (canonParams_constsResolve _) he ht)
    obtain ⟨m, -, -, -, rfl⟩ := nestCanonSub_some hr
    simp [Expr.constsResolve]
  · exact constsResolve_instPisWith (canonParams_constsResolve _) he hA

/-! ## A container's constructors -/

theorem ctorEntry_some {T : Name} {ci : ConstantInfo} {t : ConstantVal × Nat × Nat}
    (h : ctorEntry T ci = some t) : ci = .ctorInfo t.1 t.2.1 t.2.2 := by
  unfold ctorEntry at h
  split at h
  · split at h
    · split at h
      · split at h
        · obtain rfl := Option.some.inj h; rfl
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **A container's constructor list comes from its member's record.** -/
theorem nestContainer_some {E : Env} {T : Name} {nP' : Nat} {L : List (ConstantVal × Nat)}
    (h : nestContainer (envCtx E) T = some (nP', L)) :
    ∃ cv caps, E.find? T = some (.indInfo cv caps) ∧
      ∀ e ∈ L, ∃ x ∈ caps.ctors, ∃ nPc, E.find? x = some (.ctorInfo e.1 nPc e.2) := by
  rw [nestContainer_eq] at h
  change (match E.find? T with
    | some (.indInfo _ caps) => nestPick caps (caps.ctors.filterMap (ctorLook E.find? T))
    | _ => none) = _ at h
  split at h
  · rename_i cv caps hf
    refine ⟨cv, caps, hf, fun e he => ?_⟩
    have key : ∀ c ∈ caps.ctors.filterMap (ctorLook E.find? T), ∃ x ∈ caps.ctors,
        E.find? x = some (.ctorInfo c.1 c.2.1 c.2.2) := by
      intro c hc
      obtain ⟨x, hx, hl⟩ := List.mem_filterMap.mp hc
      unfold ctorLook at hl
      cases hfx : E.find? x with
      | none => rw [hfx] at hl; exact nomatch hl
      | some ci =>
        rw [hfx] at hl
        exact ⟨x, hx, by rw [hfx, ctorEntry_some hl]⟩
    revert h
    generalize caps.ctors.filterMap (ctorLook E.find? T) = cs at key
    intro h
    cases cs with
    | nil =>
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2] at he; exact absurd he List.not_mem_nil
    | cons c cs' =>
      simp only [nestPick, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2] at he
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp he
      obtain ⟨x, hx, hfx⟩ := key c' hc'
      exact ⟨x, hx, c'.2.1, hfx⟩
  · exact nomatch h

theorem ctorLook_alike {f g : Option ConstantInfo} (h : LookAlike f g) (T : Name) :
    f.bind (ctorEntry T) = g.bind (ctorEntry T) := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := h
  rcases hab with rfl | ⟨-, h1, h2⟩
  · rfl
  · cases a <;> cases b <;> simp_all [ConstantInfo.isStmtKind, ctorEntry]

/-- An inductive type former. -/
@[expose] def _root_.ConLeche.ConstantInfo.isFormer : ConstantInfo → Bool
  | .indInfo .. => true
  | _ => false

/-- A name of a recorded block, read alike and stored identically. -/
@[expose] def BlockName (C : Env) (E R : Name → Env) (n d : Name) : Prop :=
  ((R n).find? d).isSome = true ∧ C.find? d = (E n).find? d

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-! ## The recorded blocks -/

/-- **The context's recorded blocks**: each stored type former's source's blocks that list it. -/
noncomputable def lfpList : List (LfpDatum V) :=
  C.consts.flatMap fun c =>
    (S.m c.name).lfpBlocks.filter fun D => c.isFormer && D.names.contains c.name

theorem mem_lfpList {D : LfpDatum V} (h : D ∈ S.lfpList) :
    ∃ n cv caps, C.find? n = some (.indInfo cv caps) ∧ D ∈ (S.m n).lfpBlocks ∧ n ∈ D.names := by
  obtain ⟨c, hc, hD⟩ := List.mem_flatMap.mp h
  obtain ⟨hD, hn⟩ := List.mem_filter.mp hD
  simp only [Bool.and_eq_true] at hn
  have hf := S.find_of_mem hc
  have hk := hn.1
  cases c with
  | indInfo cv caps => exact ⟨_, cv, caps, hf, hD, List.contains_iff_mem.mp hn.2⟩
  | _ => simp [ConstantInfo.isFormer] at hk

theorem lfpList_of {D : LfpDatum V} {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hn : C.find? n = some (.indInfo cv caps)) (hD : D ∈ (S.m n).lfpBlocks)
    (hmem : n ∈ D.names) : D ∈ S.lfpList := by
  have hname : (ConstantInfo.indInfo cv caps).name = n := Env.find?_name hn
  refine List.mem_flatMap.mpr ⟨_, Env.find?_mem hn, List.mem_filter.mpr ⟨?_, ?_⟩⟩
  · rw [hname]; exact hD
  · simp only [Bool.and_eq_true]
    exact ⟨rfl, by rw [hname]; exact List.contains_iff_mem.mpr hmem⟩


theorem member_getD {D : LfpDatum V} {n : Name} (hD : D ∈ (S.m n).lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) : D.member mm ∈ D.names := by
  have hl : mm < D.names.length := by rw [(S.cover n).len D hD]; exact hmm
  simp only [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
    Option.getD_some]
  exact List.getElem_mem _

/-- **A recorded block's members and constructors are block names.** -/
theorem blockNames {n : Name} {cvn : ConstantVal} {capsn : IndCaps}
    (hfn : C.find? n = some (.indInfo cvn capsn)) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) (hmem : n ∈ D.names) :
    (∀ mm, mm < D.k → BlockName C E R n (D.member mm)) ∧
      ∀ c, c < D.k → ∀ j, j < D.nctors c → BlockName C E R n (D.ctorName c j) := by
  have hn := isSome_of hfn
  have hcov := S.cover n
  have hEn := S.src_ind hfn rfl
  obtain ⟨mm₀, hmm₀, hn₀⟩ := List.getElem_of_mem hmem
  have hk : mm₀ < D.k := by rw [← hcov.len D hD]; exact hmm₀
  have hmem₀ : D.member mm₀ = n := by
    simp [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm₀, hn₀]
  have hall := hcov.all D hD mm₀ hk cvn capsn (by rw [hmem₀]; exact hEn)
  have hallR := ((S.scopeR hfn).2.2.2.1 cvn capsn rfl).1
  have hmR : ∀ mm, mm < D.k → ((R n).find? (D.member mm)).isSome = true := fun mm hmm =>
    hallR _ (by rw [hall]; exact S.member_getD hD hmm)
  have hm : ∀ mm, mm < D.k → BlockName C E R n (D.member mm) := by
    intro mm hmm
    obtain ⟨cv, caps, hf⟩ := LfpCover.member_find hD hmm
    exact ⟨hmR mm hmm, by rw [hf, S.findC hn (hmR mm hmm) hf rfl]⟩
  refine ⟨hm, fun c hc j hj => ?_⟩
  obtain ⟨nP', L, hL, hlen, hfj⟩ := (hcov.own D hD).ctors c hc
  have hjL : j < L.length := by rw [hlen]; exact hj
  have hfx := hfj j hjL
  obtain ⟨cvm, capsm, hfm, hents⟩ := nestContainer_some hL
  obtain ⟨x, hx, nPc, hfxE⟩ := hents L[j] (List.getElem_mem _)
  have hxn : x = D.ctorName c j := by
    rw [← Env.find?_name hfxE, ← Env.find?_name hfx]; rfl
  subst hxn
  have hfmC := S.findC hn (hmR c hc) hfm rfl
  have hxR := S.read.ctors n _ cvm capsm hn (hmR c hc) hfmC _ hx
  exact ⟨hxR, by rw [hfxE, S.findC hn hxR hfxE rfl]⟩

omit [SetTheory V] S in
theorem bfwd {n d : Name} (h : BlockName C E R n d) {ci : ConstantInfo}
    (hf : (E n).find? d = some ci) : C.find? d = some ci := by rw [h.2]; exact hf

/-- A block name's type is read alike. -/
theorem btypeR {n d : Name} (hn : (C.find? n).isSome = true) (h : BlockName C E R n d)
    {ci : ConstantInfo} (hf : (E n).find? d = some ci) (hk : ci.isIndKind = true) :
    ci.toConstantVal.type.constsResolve (R n) = true :=
  S.deepType hn h.1 (bfwd h hf) hk

/-- **A recorded member whose stored type does not show its telescope**: the source reduced it at
a part of itself (`FamilyRan`), so at itself (`reducedFormer_ext`), so the context reduces it alike
and the reduct is read alike (the bundle's `defh`). -/
theorem defhRun {n : Name} (hn : (C.find? n).isSome = true) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) {mm : Nat} (hmm : mm < D.k) (hb : BlockName C E R n (D.member mm))
    {f : ConstantVal} (ht : D.telescope mm = some f)
    {cv : ConstantVal} {caps : IndCaps} (hf : (E n).find? (D.member mm) = some (.indInfo cv caps))
    (hfl : ConLeche.formerDefHeaded cv = true) :
    f.type.constsResolve (R n) = true ∧
      ∃ F', reducedFormer (fueledOps .verified F') C cv (caps.nparams + caps.nIdx) = .ok f := by
  obtain ⟨envB, F, hx, hr, hrun⟩ := S.ran n D hD mm f hmm ht cv caps hf hfl
  exact S.defh n _ cv caps hn hb.1 (bfwd hb hf) hfl F f (reducedFormer_ext hx hr hrun)

/-- **A recorded member's telescope is read alike**: its stored type where that shows its
telescope, `defhRun` where it does not. -/
theorem telR {n : Name} (hn : (C.find? n).isSome = true) {D : LfpDatum V}
    (hD : D ∈ (S.m n).lfpBlocks) {mm : Nat} (hmm : mm < D.k) (hb : BlockName C E R n (D.member mm))
    {cv : ConstantVal} {caps : IndCaps} (hf : (E n).find? (D.member mm) = some (.indInfo cv caps))
    (hflat : ConLeche.formerDefHeaded cv = false → D.formerAt mm cv = cv) :
    (D.formerAt mm cv).type.constsResolve (R n) = true := by
  have hty := S.btypeR hn hb hf rfl
  cases hfl : ConLeche.formerDefHeaded cv with
  | false => rw [hflat hfl]; exact hty
  | true =>
    cases ht : D.telescope mm with
    | none => simp only [LfpDatum.formerAt, ht, Option.getD_none]; exact hty
    | some f =>
      simp only [LfpDatum.formerAt, ht, Option.getD_some]
      exact (S.defhRun hn hD hmm hb ht hf hfl).1

/-- **A recorded block's clauses hold at the context.** -/
theorem lfp_ok : ∀ D ∈ S.lfpList, LfpClause aC D ∧ LfpStored C D ∧ LfpReads aC C D ∧
    LfpCtorReads aC C D ∧ LfpCaps C D := by
  intro D hDl
  obtain ⟨n, cvn, capsn, hfn, hD, hmem⟩ := S.mem_lfpList hDl
  have hn := isSome_of hfn
  obtain ⟨hbm, hbc⟩ := S.blockNames hfn hD hmem
  have hwid := (S.cover n).wid D hD
  obtain ⟨hL, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := (S.m n).lfp_ok D hD
  have hck : ∀ c, c < D.N → c < D.k := fun c hc => hwid ▸ hc
  -- the formers as read, read alike
  have hfat : ∀ mm, mm < D.k → ∀ cv caps, (E n).find? (D.member mm) = some (.indInfo cv caps) →
      (D.formerAt mm cv).type.constsResolve (R n) = true := by
    intro mm hmm cv caps hf
    obtain ⟨cv', caps', hf', ⟨hfa, -⟩, -⟩ := hrd mm hmm
    rw [hf] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact S.telR hn hD hmm (hbm mm hmm) hf hfa
  refine ⟨hL.congr (fun mm hmm => S.leaf n hn _ (hbm mm hmm).1)
      (fun c hc j hj => S.leaf n hn _ (hbc c (hck c hc) j hj).1),
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc j hj => ?_⟩,
    ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact ⟨cv, caps, bfwd (hbm mm hmm) hf⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc j hj
    exact ⟨cv, a, b, bfwd (hbc c (hck c hc) j hj) hf⟩
  · obtain ⟨cv, caps, hf, ⟨hfl, hsh⟩, hab⟩ := hrd mm hmm
    have hty : cv.type.constsResolve (R n) = true := S.btypeR hn (hbm mm hmm) hf rfl
    have hfa := hfat mm hmm cv caps hf
    refine ⟨cv, caps, bfwd (hbm mm hmm) hf, ⟨hfl, ?_⟩, fun ψ => ?_⟩
    · refine hsh.imp id fun ⟨f, hs, h1, h2, h3, h4, _, hdl, hm⟩ => ?_
      have hfR : f.type.constsResolve (R n) = true := by
        have : D.formerAt mm cv = f := by simp [LfpDatum.formerAt, hs]
        rw [← this]; exact hfa
      refine ⟨f, hs, h1, h2, h3, h4, constsBound_of_constsResolve _ (S.resC hfR), hdl,
        fun ψ => ?_⟩
      obtain ⟨ta, ta₀, hta, hta₀, hmm'⟩ := hm ψ
      refine ⟨ta, ta₀, (S.denote_eq hn ψ 0 _ hfR).trans hta, (S.denote_eq hn ψ 0 _ hty).trans hta₀,
        fun ρ => ?_⟩
      rw [S.leaf n hn _ (hbm mm hmm).1]
      exact hmm' ρ
    · obtain ⟨ab, hta, h1⟩ := hab ψ
      exact ⟨ab, (S.denote_eq hn ψ 0 _ hfa).trans hta, h1⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc j hj
    have hbcj := hbc c hc j hj
    have hty : cv.type.constsResolve (R n) = true := S.btypeR hn hbcj hf rfl
    have hAR := canonOf_constsResolve hty (.inl ⟨_, _, _, hA⟩)
    refine ⟨cv, nPc, nF, bfwd hbcj hf, hcf, fun mm hmm => ?_,
      fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc, fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      exact ⟨cvm, caps, bfwd (hbm mm hmm) hfm, hl⟩
    · rw [S.denote_eq hn ψ 0 _ hty] at hrd'
      exact hpars ψ dsC bodyC hrd' hle
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, (S.denote_eq hn ψ _ _ hAR).trans hta, hlab, hlT,
        fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, ty, hfm, hty', hr⟩ := hTys mm hmm
      have htyR := constsResolve_instPisWith (canonParams_constsResolve _)
        (hfat mm hmm cvm caps hfm) hty'
      exact ⟨cvm, caps, ty, bfwd (hbm mm hmm) hfm, hty',
        (S.denote_eq hn ψ _ _ htyR).trans hr⟩
  · obtain ⟨cv, caps, hf, hz⟩ := hcK mm hmm
    exact ⟨cv, caps, bfwd (hbm mm hmm) hf, hz⟩
  · obtain ⟨cv, nPc, nF, hf, hsh⟩ := hcC c hc j hj
    exact ⟨cv, nPc, nF, bfwd (hbc c hc j hj) hf, hsh⟩

/-- **The context owns its recorded blocks' constructors**, as the source does. -/
theorem lfpOwn {D : LfpDatum V} (hDl : D ∈ S.lfpList) : LfpOwn C D := by
  obtain ⟨n, cvn, capsn, hfn, hD, hmem⟩ := S.mem_lfpList hDl
  have hn := isSome_of hfn
  obtain ⟨hbm, hbc⟩ := S.blockNames hfn hD hmem
  refine (S.cover n).own D hD |>.monoOn (fun c hc => (hbm c hc).2) (fun c hc j hj => (hbc c hc j hj).2)
    (fun c hc => ?_)
  obtain ⟨cvm, capsm, hfm⟩ := LfpCover.member_find hD hc
  have hfmC := bfwd (hbm c hc) hfm
  rw [nestContainer_eq, nestContainer_eq]
  show (match C.find? (D.member c) with
      | some (.indInfo _ caps) => nestPick caps (caps.ctors.filterMap (ctorLook C.find? (D.member c)))
      | _ => none) = (match (E n).find? (D.member c) with
      | some (.indInfo _ caps) =>
        nestPick caps (caps.ctors.filterMap (ctorLook (E n).find? (D.member c)))
      | _ => none)
  rw [hfmC, hfm]
  dsimp only
  have hpt : ∀ x ∈ capsm.ctors,
      ctorLook C.find? (D.member c) x = ctorLook (E n).find? (D.member c) x := fun x hx =>
    ctorLook_alike (S.look hn (S.read.ctors n _ cvm capsm hn (hbm c hc).1 hfmC x hx)) _
  congr 1
  clear hfmC hfm
  revert hpt
  generalize capsm.ctors = l
  intro hpt
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons, hpt x List.mem_cons_self,
      ih fun y hy => hpt y (List.mem_cons_of_mem _ hy)]

end CtxSrc

end ConLeche.Model.Modular
