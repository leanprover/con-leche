module

public import ConLeche.Verify.Inductives.PosCompleteElim
public import ConLeche.Verify.Inductives.PosCompleteKeys
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The elimination link (lane COMPLETE-5, (A))

`EInv.elimNested` (`PosCompleteElim.lean`) reads official's elimination to
its end: every type — the members, then one per auxiliary entry — is
replaced against the FINAL map.  This module turns that into the facts
the assembly consumes (`nestedBlockPositivity_of_map`): `OffMap` of the
final map (`offMap_of_elim`), `SigmaOk`/`AuxEnvOk` of its σ-world, and
the member constructors' replacement and official verdict.

The environment facts official's elimination reads beyond `EnvFacts`
are named in `ElimEnv`.
-/

namespace ConLeche

open Expr

section Link

/-- **The environment facts the elimination link reads** (beyond
`EnvFacts`): a stored inductive's recorded block lists stored inductives
with its parameter count whose own blocks lie in it, never `Quot`
(unless it is `Quot`'s); its former is a syntactic telescope ending in a
sort; it is no auxiliary name. -/
structure ElimEnv (c : Official.ElimCtx) (G : Name → Bool) : Prop where
  block : ∀ I cv caps J, c.find? I = some (.indInfo cv caps) → J ∈ caps.all →
    ∃ cv' caps', c.find? J = some (.indInfo cv' caps') ∧ caps'.nparams = caps.nparams ∧
      ∀ n ∈ caps'.all, n ∈ caps.all
  quot : ∀ I cv caps, c.find? I = some (.indInfo cv caps) → I ≠ quotName → quotName ∉ caps.all
  sortEnd : ∀ J cv caps, c.find? J = some (.indInfo cv caps) → ∃ u, cv.type.resultSort = some u
  notAux : ∀ J cv caps, c.find? J = some (.indInfo cv caps) → G J = false

/-- The final map's auxiliary names. -/
@[expose] def finalAux (st : Official.ElimSt) (n : Name) : Bool := (st.aux.map (·.2)).contains n

theorem lookup_mem_lawful {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {b : β}, l.lookup k = some b → (k, b) ∈ l := by
  intro l k b h
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem lookup_isSome_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {b : β}, (k, b) ∈ l → ∃ b', l.lookup k = some b'
  | [], _, _, h => nomatch h
  | (k', b') :: l, k, b, h => by
    simp only [List.lookup]
    by_cases hk : (k == k') = true
    · simp [hk]
    · simp only [Bool.not_eq_true] at hk
      simp only [hk]
      rcases List.mem_cons.mp h with h | h
      · cases h; simp at hk
      · exact lookup_isSome_of_mem h

theorem mkAppN_const_inj {J J' : Name} {us us' : List Level} {ds ds' : List Expr}
    (h : Expr.mkAppN (.const J us) ds = Expr.mkAppN (.const J' us') ds') :
    J = J' ∧ us = us' ∧ ds = ds' := by
  have h1 := congrArg Expr.getAppFn h
  have h2 := congrArg Expr.getAppArgs h
  rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
  rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
  simp only [Expr.getAppFn, Expr.const.injEq] at h1
  simp only [Expr.getAppArgs, List.nil_append] at h2
  exact ⟨h1.1, h1.2, h2⟩

theorem piBinders_length : ∀ (e : Expr), e.piBinders.1.length = e.piArity
  | .forallE t b m => by simp [Expr.piBinders, Expr.piArity, piBinders_length b]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ | .lit _
  | .proj _ _ _ => rfl

theorem resultSort_instantiate1 {v : Expr} : ∀ (e : Expr) (k : Nat), e.resultSort.isSome = true →
    (e.instantiate1 v k).resultSort.isSome = true ∧ (e.instantiate1 v k).piArity = e.piArity
  | .forallE t b m, k, h => by
    simp only [Expr.resultSort] at h
    obtain ⟨h1, h2⟩ := resultSort_instantiate1 (v := v) b (k + 1) h
    simp only [Expr.instantiate1, Expr.resultSort, Expr.piArity, h1, h2, and_self]
  | .sort u, k, _ => by simp [Expr.instantiate1, Expr.resultSort, Expr.piArity]
  | .bvar _, _, h | .fvar _ _, _, h | .const _ _, _, h | .app _ _, _, h | .lam _ _ _, _, h
  | .letE _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => by simp [Expr.resultSort] at h

theorem resultSort_instantiateLevelParams {ks : List Name} {us : List Level} : ∀ (e : Expr),
    e.resultSort.isSome = true → (e.instantiateLevelParams ks us).resultSort.isSome = true ∧
      (e.instantiateLevelParams ks us).piArity = e.piArity
  | .forallE t b m, h => by
    simp only [Expr.resultSort] at h
    obtain ⟨h1, h2⟩ := resultSort_instantiateLevelParams (ks := ks) (us := us) b h
    simp only [Expr.instantiateLevelParams, Expr.resultSort, Expr.piArity, h1, h2, and_self]
  | .sort u, _ => by simp [Expr.instantiateLevelParams, Expr.resultSort, Expr.piArity]
  | .bvar _, h | .fvar _ _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => by simp [Expr.resultSort] at h

/-- A former ending in a sort loses exactly the instantiated binders. -/
theorem piArity_instPisWith : ∀ (ds : List Expr) (t r : Expr), t.resultSort.isSome = true →
    instPisWith ds t = some r → r.piArity + ds.length = t.piArity
  | [], t, r, _, h => by simp only [instPisWith, Option.some.injEq] at h; subst h; rfl
  | d :: ds, .forallE a b m, r, hs, h => by
    simp only [instPisWith] at h
    simp only [Expr.resultSort] at hs
    obtain ⟨h1, h2⟩ := resultSort_instantiate1 (v := d) b 0 hs
    have := piArity_instPisWith ds _ r h1 h
    simp only [Expr.piArity, List.length_cons]; omega
  | _ :: _, .bvar _, _, _, h | _ :: _, .fvar _ _, _, _, h | _ :: _, .sort _, _, _, h
  | _ :: _, .const _ _, _, _, h | _ :: _, .app _ _, _, _, h | _ :: _, .lam _ _ _, _, _, h
  | _ :: _, .letE _ _ _, _, _, h | _ :: _, .lit _, _, _, h | _ :: _, .proj _ _ _, _, _, h => by
    simp [instPisWith] at h

theorem noAux_mono {G H : Name → Bool} (hGH : ∀ n, G n = false → H n = false) :
    ∀ {e : Expr}, NoAux G e → NoAux H e := by
  intro e
  induction e with
  | const n us => intro h; exact hGH n h
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb => intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih => intro h; exact ih h
  | _ => intro _; trivial

variable {ctx : NestCtx} {c : Official.ElimCtx} {G : Name → Bool} {decl : List Official.MemberDecl}
  {st : Official.ElimSt} {q : Nat}

/-- Every final auxiliary name is fresh. -/
theorem finalAux_G (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st) :
    ∀ n, finalAux st n = true → G n = true := by
  intro n hn
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hn)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [hE.names j hj]; exact hH.auxG _

/-- **An entry of the final map**: its type — the first of that name —
replaced against the final map. -/
theorem EInv.entry (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st)
    (hq : st.types.size ≤ q) (hinj : ∀ k k', c.auxName k = c.auxName k' → k = k')
    {k : Expr} {a : Name} (hka : (k, a) ∈ st.aux) :
    ∃ t, st.types.toList.find? (·.name == a) = some t ∧ t ∈ st.types.toList ∧
      AuxTy c ctx.names G True st.aux (k, a) t := by
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hka
  obtain ⟨t, ht, hax⟩ := hE.auxs j hj
  have hlt : decl.length + j < q := by have := hE.size; omega
  have hp : (decl.length + j < q) = True := propext ⟨fun _ => trivial, fun _ => hlt⟩
  rw [hp, hjeq] at hax
  have htm : t ∈ st.types.toList := List.mem_of_getElem? ht
  refine ⟨t, ?_, htm, hax⟩
  have hna : st.aux[j].2 = c.auxName (j + 1) := hE.names j hj
  rw [hjeq] at hna
  simp only at hna
  rw [List.find?_eq_some_iff_getElem]
  have hil : decl.length + j < st.types.toList.length := by
    rcases Nat.lt_or_ge (decl.length + j) st.types.toList.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at ht; cases ht
  refine ⟨by simp [hax.1], decl.length + j, hil, getElem_of_getElem?_some ht, fun i hi => ?_⟩
  have hnm := hE.names_eq hH
  have hmem : ctx.names.length = decl.length := by rw [← hH.declNames]; simp
  have hsz : st.types.toList.length = st.types.size := by simp
  have hname : st.types.toList[i].name = st.names[i]'(by simp [Official.ElimSt.names]; omega) := by
    simp [Official.ElimSt.names]
  rw [hname]
  simp only [hnm]
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  intro heq
  rcases Nat.lt_or_ge i ctx.names.length with hi' | hi'
  · rw [List.getElem_append_left hi'] at heq
    have h1 := hH.memG _ (List.contains_iff_mem.mpr (List.getElem_mem hi'))
    rw [heq, hna, hH.auxG] at h1
    exact Bool.noConfusion h1
  · rw [List.getElem_append_right hi'] at heq
    simp only [List.getElem_map] at heq
    rw [hE.names _ (by have := hE.size; omega), hna] at heq
    have := hinj _ _ heq
    omega

theorem blockOf_of_find {I : Name} {cv : ConstantVal} {caps : IndCaps}
    (h : c.find? I = some (.indInfo cv caps)) : Official.blockOf c I = caps.all := by
  simp [Official.blockOf, h]

/-- **THE ELIMINATION LINK**: official's elimination, run to its end (the
invariant at every type), and its positivity loop accepting every
constructor of the eliminated declaration at every fresh-local base above
the walk's give `OffMap` of the final map. -/
theorem offMap_of_elim {whnf : Nat → Expr → Except CheckError Expr}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st)
    (hq : st.types.size ≤ q) (hinj : ∀ k k', c.auxName k = c.auxName k' → k = k')
    (henv : EnvFacts ctx c (finalAux st)) (hee : ElimEnv c G)
    (hacc : ∀ t ∈ st.types.toList, ∀ ct ∈ t.ctors, ∀ base, ctx.hiAt 0 ≤ base → ∃ fuel nb,
      Official.checkCtorPos (st.oracle c whnf) t.name fuel nb base ct = .ok ()) :
    OffMap ctx c (st.oracle c whnf) (finalAux st) st.aux := by
  have hfG := finalAux_G hH hE
  -- an entry of the final map at a container key
  have hent : ∀ J us Ds a, st.aux.lookup (Expr.mkAppN (.const J us) Ds) = some a →
      ∃ t, st.types.toList.find? (·.name == a) = some t ∧ t ∈ st.types.toList ∧ t.name = a ∧
        ∃ I cvI capsI, c.find? I = some (.indInfo cvI capsI) ∧ capsI.nparams = Ds.length ∧
        I ≠ quotName ∧ (∀ x ∈ Ds, x.bvarB = 0 ∧ NoAux G x) ∧ Ds.any (·.nestOcc ctx.names 0 0) = true ∧
        J ∈ capsI.all ∧ (∀ J' ∈ capsI.all, ∃ a', (Expr.mkAppN (.const J' us) Ds, a') ∈ st.aux) ∧
        ∃ raws, Official.CopyOk c us Ds J ⟨t.name, t.type, raws⟩ ∧
          CtorsOk c ctx.names G True st.aux raws t.ctors := by
    intro J us Ds a hl
    obtain ⟨t, hf, htm, hn, I, J', us', ds', hk, ⟨⟨cvI, capsI, hfI, hnp⟩, hqI, hds, hocc⟩, hJ, hblk,
      raws, hcp, hco⟩ := hE.entry hH hq hinj (lookup_mem_lawful hl)
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hk
    rw [blockOf_of_find hfI] at hJ hblk
    exact ⟨t, hf, htm, hn, I, cvI, capsI, hfI, hnp, hqI, hds, hocc, hJ, hblk, raws, hcp, hco⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- keyOk
    intro k a hl
    obtain ⟨t, -, -, hn, I, J, us, ds, rfl, ⟨-, -, hds, hocc⟩, -⟩ :=
      hE.entry hH hq hinj (lookup_mem_lawful hl)
    refine ⟨looseBVarsBounded_mkAppN rfl fun x hx => lbb_of_bvarB_zero (hds x hx).1, ?_, ?_⟩
    · rw [nestOcc_mkAppN, hocc, Bool.or_true]
    · exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨(_, a), lookup_mem_lawful hl, rfl⟩)
  · -- head
    intro J us Ds a hl
    obtain ⟨t, hf, -, -, I, cvI, capsI, hfI, hnp, hqI, -, -, hJ, -, raws, hcp, -⟩ := hent J us Ds a hl
    obtain ⟨cvJ, capsJ, hfJ, hty, -⟩ := hcp
    obtain ⟨cv', caps', hf', hnp', -⟩ := hee.block I cvI capsI J hfI hJ
    rw [hfJ] at hf'; cases hf'
    have hnm := henv.ind J cvJ capsJ hfJ
    refine ⟨fun h => hee.quot I cvI capsI hfI hqI (h ▸ hJ), hnm, ?_, ⟨cvJ, capsJ, hfJ, by omega⟩, ?_⟩
    · rw [Bool.eq_false_iff]
      intro h
      have := hfG J h
      rw [hee.notAux J cvJ capsJ hfJ] at this
      exact Bool.noConfusion this
    · have hctx : ctx.find? J = some (.indInfo cvJ capsJ) := by rw [← henv.find J hnm]; exact hfJ
      have hnI : (st.oracle c whnf).nIdx a = t.type.piArity := by
        simp only [Official.ElimSt.oracle, hf, piBinders_length]
      obtain ⟨u, hu⟩ := hee.sortEnd J cvJ capsJ hfJ
      obtain ⟨hs, hpa⟩ := resultSort_instantiateLevelParams (ks := cvJ.levelParams) (us := us) cvJ.type
        (by rw [hu]; rfl)
      have := piArity_instPisWith Ds _ _ hs (Official.instPiParams_ok.mp hty)
      simp only at this
      simp only [nestArity, hctx, piBinders_length, hnI]
      omega
  · -- block
    intro C us Ds a hl J hJ
    obtain ⟨t, -, -, -, I, cvI, capsI, hfI, -, -, -, -, hC, hblk, raws, hcp, -⟩ := hent C us Ds a hl
    have hJI : J ∈ capsI.all := by
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact hC
      · obtain ⟨cvC, capsC, hfC, -⟩ := hcp
        obtain ⟨cv', caps', hf', -, hsub⟩ := hee.block I cvI capsI C hfI hC
        rw [hfC] at hf'; cases hf'
        have hnm := henv.ind C cvC capsC hfC
        have hctx : ctx.find? C = some (.indInfo cvC capsC) := by rw [← henv.find C hnm]; exact hfC
        simp only [nestFrameMates, nestBlockOf, hctx, List.mem_filter, List.mem_eraseDups] at hJ
        exact hsub J hJ.1
    obtain ⟨a', ha'⟩ := hblk J hJI
    exact lookup_isSome_of_mem ha'
  · -- ctors
    intro J us Ds a hl cv nF hmem
    obtain ⟨t, -, htm, -, -, -, -, -, -, -, -, -, -, -, raws, hcp, hco⟩ := hent J us Ds a hl
    obtain ⟨-, -, -, -, hcs⟩ := hcp
    obtain ⟨u, hu, hxu⟩ := Official.mapM_except_mem hcs (cv, nF) hmem
    obtain ⟨hna, hpr, -⟩ := hco
    obtain ⟨hsig, hcts⟩ := hpr trivial
    refine ⟨u, Official.instPiParams_ok.mp hxu, hsig u hu,
      noAux_mono (fun n hn => by
        rw [Bool.eq_false_iff]; intro h; rw [hfG n h] at hn; exact Bool.noConfusion hn) (hna u hu), ?_⟩
    intro base hb
    obtain ⟨fuel, nb, hc⟩ := hacc t htm (sigmaAll c ctx.names st.aux u)
      (by rw [hcts]; exact List.mem_map_of_mem hu) base hb
    exact ⟨t.name, fuel, nb, List.contains_iff_mem.mpr (List.mem_map_of_mem htm), hc⟩

/-- **Official's typing of its final map, from the elimination** (`OffTyped`
from `OfficialTypesAt`). -/
theorem offTyped_of_elim {T : Official.TypingOracle}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st)
    (hq : st.types.size ≤ q) (hinj : ∀ k k', c.auxName k = c.auxName k' → k = k')
    (hty : Official.OfficialTypesAt st T (ctx.hiAt 0)) : OffTyped ctx c T st.aux where
  ctors J us Ds a hl cv nF hmem u hu base hb := by
    obtain ⟨t, -, htm, -, I, J', us', ds', hk, -, -, -, raws, hcp, hco⟩ :=
      hE.entry hH hq hinj (lookup_mem_lawful hl)
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hk
    obtain ⟨-, -, -, -, hcs⟩ := hcp
    obtain ⟨u', hu', hxu⟩ := Official.mapM_except_mem hcs (cv, nF) hmem
    have hxu' := Official.instPiParams_ok.mp hxu
    rw [hu, Option.some.injEq] at hxu'
    subst hxu'
    obtain ⟨-, hpr, -⟩ := hco
    obtain ⟨-, hcts⟩ := hpr trivial
    exact hty.1 t htm _ (by rw [hcts]; exact List.mem_map_of_mem hu') base hb
  nested k a hl := hty.2.1 (k, a) (lookup_mem_lawful hl)

theorem deepOcc_mono {p p' : Name → Bool} (hp : ∀ n, p n = true → p' n = true) :
    ∀ (e : Expr), e.deepOcc p' = false → e.deepOcc p = false := by
  intro e
  induction e with
  | fvar i ty ih => intro h; simp only [Expr.deepOcc] at h ⊢; exact ih h
  | const n us =>
    intro h; simp only [Expr.deepOcc] at h ⊢
    rw [Bool.eq_false_iff]; intro hn; rw [hp n hn] at h; exact Bool.noConfusion h
  | app f a ihf iha =>
    intro h; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro h; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i x ih => intro h; simp only [Expr.deepOcc] at h ⊢; exact ih h
  | _ => intro _; rfl

theorem deepOcc_or {p q : Name → Bool} :
    ∀ {e : Expr}, e.deepOcc p = false → e.deepOcc q = false → e.deepOcc (fun n => p n || q n) = false
  | .fvar _ ty, h1, h2 => by simp only [Expr.deepOcc] at h1 h2 ⊢; exact deepOcc_or h1 h2
  | .const n _, h1, h2 => by simp only [Expr.deepOcc] at h1 h2 ⊢; simp [h1, h2]
  | .app f a, h1, h2 => by
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨deepOcc_or h1.1 h2.1, deepOcc_or h1.2 h2.2⟩
  | .lam t b _, h1, h2 | .forallE t b _, h1, h2 => by
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨deepOcc_or h1.1 h2.1, deepOcc_or h1.2 h2.2⟩
  | .letE t v b, h1, h2 => by
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h1 h2 ⊢
    exact ⟨⟨deepOcc_or h1.1.1 h2.1.1, deepOcc_or h1.1.2 h2.1.2⟩, deepOcc_or h1.2 h2.2⟩
  | .proj _ _ x, h1, h2 => by simp only [Expr.deepOcc] at h1 h2 ⊢; exact deepOcc_or h1 h2
  | .bvar _, _, _ | .sort _, _, _ | .lit _, _, _ => rfl

variable (ctx c G) in
/-- **The declaration official receives is the block's**: its parameters,
levels and index counts are the walk's; the members' names are distinct;
the parameters are the canonical closed variables whose annotations
mention no declared type and no auxiliary name. -/
structure DeclOk (decl : List Official.MemberDecl) : Prop where
  ps : c.ps = ctx.params
  lvls : c.lvls = ctx.lps.map .param
  psLen : ctx.params.length = ctx.nP
  psFvar : ∀ i (h : i < ctx.params.length), ∃ ty, ctx.params[i] = .fvar i ty ∧
    ty.deepOcc (fun n => ctx.names.contains n || G n) = false
  psClosed : ∀ p ∈ ctx.params, p.looseBVarsBounded 0 = true
  nodup : ctx.names.Nodup
  nIdx : ∀ i (h : i < decl.length) ty, Official.instPiParams decl[i].type c.ps = .ok ty →
    ty.piArity = ctx.nIdxs.getD i 0

theorem EHyp.name_getElem (hH : EHyp c ctx.names G decl) :
    ∀ t (h1 : t < ctx.names.length) (h2 : t < decl.length), ctx.names[t] = decl[t].name := by
  have e := hH.declNames
  generalize ctx.names = N at e ⊢
  subst e; simp

/-- **The σ-world of the final map is official's**: `SigmaOk`. -/
theorem sigmaOk_of_elim {whnf : Nat → Expr → Except CheckError Expr}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st) (hd : DeclOk ctx c G decl) :
    SigmaOk ctx (sigmaOfMap ctx c (finalAux st) st.aux) (st.oracle c whnf) := by
  have hfG := finalAux_G hH hE
  have hnm := hE.names_eq hH
  have hdisj : ∀ n, finalAux st n = true → ctx.names.contains n = false := by
    intro n hn
    rw [Bool.eq_false_iff]; intro hm
    have := hH.memG n hm
    rw [hfG n hn] at this; exact Bool.noConfusion this
  have hlk : ∀ k a, st.aux.lookup k = some a → finalAux st a = true := fun k a hl =>
    List.contains_iff_mem.mpr (List.mem_map.mpr ⟨(k, a), lookup_mem_lawful hl, rfl⟩)
  refine ⟨?_, hdisj, rfl, rfl, hd.ps, hd.psLen, ?_, ?_, ?_, fun _ _ a h => hlk _ a h,
    fun _ _ a h => hlk _ a h⟩
  · intro n
    show (st.names).contains n = _
    rw [hnm, List.contains_append]; rfl
  · intro i hi
    obtain ⟨ty, hp, hty⟩ := hd.psFvar i hi
    refine ⟨ty, hp, deepOcc_mono (fun n hn => ?_) ty hty⟩
    change (st.names).contains n = true at hn
    rw [hnm, List.contains_append, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · simp only [hn, Bool.true_or]
    · simp only [hfG n hn, Bool.or_true]
  · intro p hp; change p ∈ c.ps at hp; rw [hd.ps] at hp; exact hd.psClosed p hp
  · intro t ht
    have hdl : ctx.names.length = decl.length := by rw [← hH.declNames]; simp
    obtain ⟨tt, htt, hn, hty, -⟩ := hE.mems t (by omega)
    have hname : ctx.names.getD t .anonymous = decl[t].name := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact hH.name_getElem t ht (by omega)
    have hfind : st.types.toList.find? (·.name == ctx.names.getD t .anonymous) = some tt := by
      rw [List.find?_eq_some_iff_getElem]
      have hil : t < st.types.toList.length := by
        rcases Nat.lt_or_ge t st.types.toList.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at htt; cases htt
      refine ⟨by rw [hn, hname]; exact beq_self_eq_true _, t, hil, getElem_of_getElem?_some htt, fun j hj => ?_⟩
      obtain ⟨tj, htj, hnj, -⟩ := hE.mems j (by omega)
      rw [getElem_of_getElem?_some htj, hnj, hname]
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro heq
      have h1 := hH.name_getElem j (by omega) (by omega)
      have h2 := hH.name_getElem t ht (by omega)
      have := (List.getElem_inj hd.nodup).mp (h1.trans (heq.trans h2.symm))
      omega
    simp only [Official.ElimSt.oracle, hfind, piBinders_length]
    exact hd.nIdx t (by omega) tt.type hty

/-- **The auxiliary maps name stored inductives at their parameter
count**: `AuxEnvOk` of the final map's σ-world. -/
theorem auxEnvOk_of_elim {o : Official.PosOracle}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st)
    (henv : EnvFacts ctx c (finalAux st)) (hee : ElimEnv c G)
    (hoff : OffMap ctx c o (finalAux st) st.aux) :
    AuxEnvOk ctx (sigmaOfMap ctx c (finalAux st) st.aux) := by
  have hfG := finalAux_G hH hE
  refine ⟨fun a ha cv caps hf => ?_, fun prog K a h => ?_⟩
  · have hnm : ctx.names.contains a = false := by
      rw [Bool.eq_false_iff]; intro hm
      have := hH.memG a hm
      rw [hfG a ha] at this; exact Bool.noConfusion this
    rw [← henv.find a hnm] at hf
    have := hee.notAux a cv caps hf
    rw [hfG a ha] at this; exact Bool.noConfusion this
  · obtain ⟨-, hnm, -, ⟨cv, caps, hf, hnp⟩, -⟩ := hoff.head _ _ _ _ h
    rw [henv.find _ hnm] at hf
    exact ⟨cv, caps, hf, by simpa using hnp⟩

/-- **The member constructors, from the elimination**: each one's
replacement against the final map, and official's verdict on it. -/
theorem member_of_elim {whnf : Nat → Expr → Except CheckError Expr}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st) (hq : st.types.size ≤ q)
    (hd : DeclOk ctx c G decl)
    (hacc : ∀ t ∈ st.types.toList, ∀ ct ∈ t.ctors, ∀ base, ctx.hiAt 0 ≤ base → ∃ fuel nb,
      Official.checkCtorPos (st.oracle c whnf) t.name fuel nb base ct = .ok ())
    {i : Nat} (hi : i < decl.length) {x : Expr} (hx : x ∈ decl[i].ctors) :
    ∃ u, instPisWith ctx.params x = some u ∧ SigOk c ctx.names st.aux u ∧
      ∃ self fuelO nb, ctx.names.contains self = true ∧
        Official.checkCtorPos (st.oracle c whnf) self fuelO nb (ctx.hiAt 0)
          (sigmaAll c ctx.names st.aux u) = .ok () := by
  obtain ⟨t, ht, hn, -, raws, hr, hco⟩ := hE.mems i hi
  have hlt : i < q := by have := hE.size; omega
  obtain ⟨-, hpr, -⟩ := hco
  obtain ⟨hsig, hcts⟩ := hpr hlt
  obtain ⟨u, hu, hxu⟩ := Official.mapM_except_mem hr x hx
  rw [hd.ps] at hxu
  obtain ⟨fuel, nb, hc⟩ := hacc t (List.mem_of_getElem? ht) (sigmaAll c ctx.names st.aux u)
    (by rw [hcts]; exact List.mem_map_of_mem hu) (ctx.hiAt 0) (Nat.le_refl _)
  refine ⟨u, Official.instPiParams_ok.mp hxu, hsig u hu, t.name, fuel, nb, ?_, hc⟩
  rw [hn, ← hH.declNames]
  exact List.contains_iff_mem.mpr (List.mem_map_of_mem (List.getElem_mem hi))

/-- **Official typed the member constructors' replacements.** -/
theorem memberTyped_of_elim {T : Official.TypingOracle}
    (hE : EInv c ctx.names G decl q st) (hq : st.types.size ≤ q) (hd : DeclOk ctx c G decl)
    (hty : Official.OfficialTypesAt st T (ctx.hiAt 0))
    {i : Nat} (hi : i < decl.length) {x u : Expr} (hx : x ∈ decl[i].ctors)
    (hu : instPisWith ctx.params x = some u) :
    T.ctorOk (ctx.hiAt 0) (sigmaAll c ctx.names st.aux u) := by
  obtain ⟨t, ht, -, -, raws, hr, hco⟩ := hE.mems i hi
  have hlt : i < q := by have := hE.size; omega
  obtain ⟨-, hpr, -⟩ := hco
  obtain ⟨-, hcts⟩ := hpr hlt
  obtain ⟨u', hu', hxu⟩ := Official.mapM_except_mem hr x hx
  rw [hd.ps] at hxu
  have hxu' := Official.instPiParams_ok.mp hxu
  rw [hu, Option.some.injEq] at hxu'
  subst hxu'
  exact hty.1 t (List.mem_of_getElem? ht) _ (by rw [hcts]; exact List.mem_map_of_mem hu')
    (ctx.hiAt 0) (Nat.le_refl _)

/-- **(A) FROM OFFICIAL'S ELIMINATION.**  Let official accept the block's
positivity, its elimination ending with `st`
(`OfficialPosAcceptsAt`, fresh locals above the walk's).  Then, with the σ-world of the final
map, under `WhnfSim`, the per-frame obligations (`FrameObl`), the
member constructors' side conditions, and the environment's and the
declaration's facts (`EnvFacts`, `ElimEnv`, `EHyp`, `DeclOk`), the walk's
`nestedBlockPositivity` succeeds or declines — it never rejects. -/
theorem nestedBlockPositivity_of_elim {ops : CheckerOps CheckM} {env : Env}
    {whnf : Nat → Expr → Except CheckError Expr}
    (hoffc : Official.OfficialPosAcceptsAt c decl whnf (ctx.hiAt 0) st)
    (hH : EHyp c ctx.names G decl) (hinj : ∀ k k', c.auxName k = c.auxName k' → k = k')
    (hd : DeclOk ctx c G decl) (henv : EnvFacts ctx c (finalAux st)) (hee : ElimEnv c G)
    (hsim : WhnfSim ops env ctx (sigmaOfMap ctx c (finalAux st) st.aux) whnf)
    {T : Official.TypingOracle} (htyA : Official.OfficialTypesAt st T (ctx.hiAt 0))
    (hinf : InferSim ops env ctx (sigmaOfMap ctx c (finalAux st) st.aux) T)
    (hu4 : U4Typed ops env ctx (sigmaOfMap ctx c (finalAux st) st.aux) T)
    (hobl : FrameObl ctx c (st.oracle c whnf) (finalAux st) st.aux)
    (hkeys : KeysApplied ctx (sigmaOfMap ctx c (finalAux st) st.aux))
    {holes : List Expr} (hholes : nestHoles ctx = some holes) (hh : HolesOk ctx holes)
    (hps : ParamsOk ctx (finalAux st))
    {ctorss : List (List (ConstantVal × Nat))}
    (hdc : decl.map (·.ctors) = ctorss.map (·.map (·.1.type)))
    (hmem : ∀ cs ∈ ctorss, ∀ cc ∈ cs,
      cc.1.type.hasFvar = false ∧ Good ctx (finalAux st) cc.1.type ∧
      (∀ crest, instPisWith ctx.params (nestAbstract ctx holes cc.1.type) = some crest →
        crest.piArity = cc.2) ∧
      (nestAbstract ctx holes cc.1.type).nestOcc ctx.names 0 0 = false) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) := by
  obtain ⟨⟨fuelE, helim⟩, hacc⟩ := hoffc
  obtain ⟨q, hq, hE⟩ := EInv.elimNested hH helim
  have hoff := offMap_of_elim hH hE hq hinj henv hee hacc
  refine nestedBlockPositivity_of_map (sigmaOk_of_elim hH hE hd) (auxEnvOk_of_elim hH hE henv hee hoff)
    hsim hd.lvls hoff henv hobl hinf hu4 (offTyped_of_elim hH hE hq hinj htyA) hkeys hholes hh hps ?_
  intro cs hcs cc hcc
  obtain ⟨hcl, hgood, hpi, hocc⟩ := hmem cs hcs cc hcc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
  have hil : i < decl.length := by
    have := congrArg List.length hdc; simp at this; omega
  have hx : cc.1.type ∈ decl[i].ctors := by
    have := congrArg (·[i]?) hdc
    simp only [List.getElem?_map, List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hi,
      Option.map_some, Option.some.injEq] at this
    rw [this]; exact List.mem_map_of_mem hcc
  obtain ⟨u, hu, hsig, hchk⟩ := member_of_elim hH hE hq hd hacc hil hx
  exact ⟨u, hcl, hgood, hu, hsig, hchk, memberTyped_of_elim hE hq hd htyA hil hx hu, hpi, hocc⟩

/-! ## The formers' index count -/

/-- **The per-frame side checks**: `FrameObl` without the index count of
the instantiation's former (derived: `frameObl_of_side`). -/
@[expose] def FrameSide (ctx : NestCtx) (c : Official.ElimCtx)
    (o : Official.PosOracle) (isAux : Name → Bool) (M : List (Expr × Name)) : Prop :=
  ∀ prog act C us ds a, StepInv ctx (sigmaOfMap ctx c isAux M) c o prog →
    (sigmaOfMap ctx c isAux M).contAux prog ⟨C, us, ds⟩ = some a → ContKeyOk ctx isAux prog act C us ds →
    OkOr (fun _ => True) (nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨C, us, ds⟩) ∧
    FrameRest ctx prog act C us ds

/-- **The instantiation's index count is official's**: the walk's former
check counts the indices of the container's instantiated former, official
the binders of its auxiliary type's (the same telescope, a stored former
ending in a sort). -/
theorem frameObl_of_side {o : Official.PosOracle}
    {isAux : Name → Bool} {M : List (Expr × Name)} (hoff : OffMap ctx c o isAux M)
    (hsort : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ∃ u, cv.type.resultSort = some u)
    (hside : FrameSide ctx c o isAux M) : FrameObl ctx c o isAux M := by
  intro prog act C us ds a hI ha hk
  obtain ⟨h1, hrest⟩ := hside prog act C us ds a hI ha hk
  refine ⟨?_, hrest⟩
  rcases hr : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨C, us, ds⟩ with e | ⟨nI, cty⟩
  · rw [hr] at h1; exact h1
  show nI = o.nIdx a
  obtain ⟨cvC, caps, hf, -, -, ty, s, hty, -, -, rfl, -⟩ := nestInstType_inv hr
  have hM : M.lookup (Expr.mkAppN (.const C us) (ds.map (rbE ctx prog))) = some a := ha
  obtain ⟨-, -, -, -, har⟩ := hoff.head _ _ _ _ hM
  simp only [nestArity, hf, List.length_map] at har
  obtain ⟨u, hu⟩ := hsort C cvC caps hf
  obtain ⟨hs, -⟩ := resultSort_instantiateLevelParams (ks := cvC.levelParams) (us := us) cvC.type
    (by rw [hu]; rfl)
  have := piArity_instPisWith ds _ _ hs hty
  rw [piBinders_length] at har ⊢
  have hpa := (resultSort_instantiateLevelParams (ks := cvC.levelParams) (us := us) cvC.type
    (by rw [hu]; rfl)).2
  omega

/-! ## The canonical elimination context -/

/-- **Official's elimination context for the block `ctx`**: official's
environment is the one BEFORE the declaration (the members are not in
it); its constructor lists are the walk's reading (`nestContainer`); the
declaration's levels and parameters are the walk's; `auxName` is the
fresh-name supply (`mk_unique_name`). -/
@[expose] def elimCtxOf (ctx : NestCtx) (auxName : Nat → Name) : Official.ElimCtx where
  find? n := if ctx.names.contains n then none else ctx.find? n
  ctorsOf J := ((nestContainer ctx J).map (·.2)).getD []
  lvls := ctx.lps.map .param
  ps := ctx.params
  auxName := auxName

theorem elimCtxOf_ind {auxName : Nat → Name} :
    ∀ I cv caps, (elimCtxOf ctx auxName).find? I = some (.indInfo cv caps) →
      ctx.names.contains I = false := by
  intro I cv caps h
  simp only [elimCtxOf] at h
  split at h
  · cases h
  · rename_i hn; simpa using hn

theorem elimCtxOf_find {auxName : Nat → Name} :
    ∀ n, ctx.names.contains n = false → (elimCtxOf ctx auxName).find? n = ctx.find? n := by
  intro n h
  simp only [elimCtxOf, h, Bool.false_eq_true, if_false]

variable (ctx G) in
/-- **Official's fresh-name supply is fresh** (`mk_unique_name`, the
spec's `auxName`): its names are `G`-names, pairwise distinct, and no
member, no member constructor type and no parameter annotation mentions
one.  A property of the SPEC's instantiation (official's choice of names
is arbitrary), not of the checker. -/
structure FreshSupply (ctorss : List (List (ConstantVal × Nat))) (auxName : Nat → Name) : Prop where
  auxG : ∀ k, G (auxName k) = true
  inj : ∀ k k', auxName k = auxName k' → k = k'
  memG : ∀ n, ctx.names.contains n = true → G n = false
  ctorsG : ∀ cs ∈ ctorss, ∀ cc ∈ cs, NoAux G cc.1.type
  /-- no stored inductive bears an auxiliary name -/
  notAux : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → G J = false
  /-- no stored constructor type mentions an auxiliary name -/
  ctorsFresh : ∀ J n L, nestContainer ctx J = some (n, L) → ∀ x ∈ L, x.1.type.deepOcc G = false
  /-- no stored inductive's former mentions an auxiliary name -/
  formersFresh : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → cv.type.deepOcc G = false
  /-- the auxiliary names are fresh in the environment (`mk_unique_name`) -/
  envFresh : ∀ n, G n = true → ctx.find? n = none

variable (ctx) in
/-- **The stored environment's facts** the completeness proof reads, over
the walk's own context (task 2's catalogue: which invariant each comes
from is recorded in DESIGN, COMPLETE-5).  Every one is about constants
stored BEFORE the block (the containers), off the block's members. -/
structure StoredEnv : Prop where
  /-- a stored inductive's constructors carry its recorded parameter count
  (not `Quot`'s: its pin records none, `Quot.mk` carries 2) -/
  nparams : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → J ≠ quotName →
    ∃ L, nestContainer ctx J = some (caps.nparams, L)
  /-- a stored constructor binds its parameters and fields -/
  ctorArity : ∀ J n L, J ≠ quotName → nestContainer ctx J = some (n, L) → ∀ x ∈ L,
    n + x.2 ≤ x.1.type.piArity
  /-- stored types are closed -/
  closed : NestCtxOk ctx
  /-- a stored constructor's level parameters are distinct -/
  nodup : ∀ J n L, J ≠ quotName → nestContainer ctx J = some (n, L) → ∀ x ∈ L,
    Name.nodup x.1.levelParams = true
  /-- a container's frame group lies in each member's recorded block (at a
  stored inductive other than a member or `Quot`: at any other name the
  group is the name alone and its "block" is empty) -/
  blockClosed : ∀ C cv caps, ctx.find? C = some (.indInfo cv caps) → ctx.names.contains C = false →
    C ≠ quotName → ∀ J, J ∈ C :: nestFrameMates ctx C → ∀ n ∈ C :: nestFrameMates ctx C,
    (nestBlockOf ctx J).contains n = true
  /-- a stored constructor type mentions no member of the block (the
  members are declared by the block itself) -/
  fresh : ∀ J n L, nestContainer ctx J = some (n, L) → ∀ x ∈ L,
    x.1.type.deepOcc (fun n => ctx.names.contains n) = false
  /-- a recorded block lists stored inductives, none a member, at the
  block's parameter count, whose own blocks lie in it -/
  block : ∀ I cv caps J, ctx.find? I = some (.indInfo cv caps) → ctx.names.contains I = false →
    J ∈ caps.all → ctx.names.contains J = false ∧ ∃ cv' caps',
      ctx.find? J = some (.indInfo cv' caps') ∧ caps'.nparams = caps.nparams ∧ ∀ n ∈ caps'.all, n ∈ caps.all
  /-- `Quot` is in no other stored inductive's recorded block -/
  quot : ∀ I cv caps, ctx.find? I = some (.indInfo cv caps) → ctx.names.contains I = false →
    I ≠ quotName → quotName ∉ caps.all
  /-- a stored inductive's former is a syntactic telescope ending in a sort -/
  sortEnd : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ∃ u, cv.type.resultSort = some u
  /-- a stored inductive's former (other than a member's) mentions no member
  (the members are declared by the block itself) -/
  formerFresh : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ctx.names.contains J = false →
    cv.type.deepOcc (fun n => ctx.names.contains n) = false
  /-- a stored constructor's type concludes, past its parameters and
  fields, in its own inductive at the constructor's level parameters, as
  many as the inductive's (the install's `checkSumCtor_shape`; official's
  `is_valid_ind_app`; `LfpOwn.ctorConcl`) -/
  ctorConcl : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → J ≠ quotName → ∀ n L,
    nestContainer ctx J = some (n, L) → ∀ x ∈ L,
      x.1.levelParams.length = cv.levelParams.length ∧ ∃ bs r,
        x.1.type.stripPis (n + x.2) = some (bs, r) ∧
        r.getAppFn = .const J (x.1.levelParams.map .param)

variable (ctx) in
/-- **THE STREAM PREMISE** (beside `OfficialPosAcceptsAt`): official
accepted every declaration stored before the block, so every stored
inductive's constructors passed official's `check_uniform_ind_occs`
(`inductive.cpp` v4.34.0 :134, run by `add_inductive` :1257 on each of
them).  NOT an invariant of our environment: our install checks M2′
(member levels, syntactic) and M3 (`holesApplied`, on the walk's
normal form), so a member applied non-uniformly inside a redex that
whnf drops passes ours and fails official's.  Completeness compares
the two checkers on a stream official accepts, so this is a premise
about the STREAM. -/
structure OfficialStream : Prop where
  /-- every stored inductive passed official's `check_uniform_ind_occs` -/
  uniform : ∀ J cv caps, ctx.find? J = some (.indInfo cv caps) → ∀ L,
    nestContainer ctx J = some (caps.nparams, L) → ∀ x ∈ L,
      Official.uniformOcc caps.all (x.1.levelParams.map .param) caps.nparams 0 x.1.type = true

/-- `EnvFacts` of the canonical context, from the stored environment's. -/
theorem envFacts_of_stored {auxName : Nat → Name} {isAux : Name → Bool}
    {ctorss : List (List (ConstantVal × Nat))}
    (hGa : ∀ n, isAux n = true → G n = true) (hs : StoredEnv ctx) (hos : OfficialStream ctx)
    (hfs : FreshSupply ctx G ctorss auxName) :
    EnvFacts ctx (elimCtxOf ctx auxName) isAux where
  ind := elimCtxOf_ind
  find := elimCtxOf_find
  ctorsOf _ := rfl
  nparams := hs.nparams
  ctorArity := hs.ctorArity
  closed := hs.closed
  nodup := hs.nodup
  uniform := hos.uniform
  blockClosed := hs.blockClosed
  ctorConcl := hs.ctorConcl
  fresh J n L h x hx := deepOcc_mono (fun m hm => by
    rw [Bool.or_eq_true] at hm ⊢
    exact hm.imp id (hGa m)) _ (deepOcc_or (hs.fresh J n L h x hx) (hfs.ctorsFresh J n L h x hx))

/-- `ElimEnv` of the canonical context, from the stored environment's. -/
theorem elimEnv_of_stored {auxName : Nat → Name} {ctorss : List (List (ConstantVal × Nat))}
    (hs : StoredEnv ctx) (hfs : FreshSupply ctx G ctorss auxName) :
    ElimEnv (elimCtxOf ctx auxName) G := by
  have hf : ∀ I cv caps, (elimCtxOf ctx auxName).find? I = some (.indInfo cv caps) →
      ctx.names.contains I = false ∧ ctx.find? I = some (.indInfo cv caps) := by
    intro I cv caps h
    have hn := elimCtxOf_ind I cv caps h
    exact ⟨hn, by rw [← elimCtxOf_find (auxName := auxName) I hn]; exact h⟩
  refine ⟨fun I cv caps J h hJ => ?_, fun I cv caps h hq => ?_, fun J cv caps h => ?_,
    fun J cv caps h => ?_⟩
  · obtain ⟨hn, h'⟩ := hf I cv caps h
    obtain ⟨hJn, cv', caps', hJ', hnp, hsub⟩ := hs.block I cv caps J h' hn hJ
    exact ⟨cv', caps', by rw [elimCtxOf_find J hJn]; exact hJ', hnp, hsub⟩
  · obtain ⟨hn, h'⟩ := hf I cv caps h
    exact hs.quot I cv caps h' hn hq
  · exact hs.sortEnd J cv caps (hf J cv caps h).2
  · exact hfs.notAux J cv caps (hf J cv caps h).2

/-! ## (A) at the canonical declaration -/

/-- A member's former type as stored (official's `inductive_type.get_type`). -/
@[expose] def formerOf (ctx : NestCtx) (n : Name) : Expr :=
  match ctx.find? n with
  | some (.indInfo cv _) => cv.type
  | _ => .sort .zero

/-- **The declaration official receives for the block**: every member
with its stored former and its constructors' types. -/
@[expose] def declOf (ctx : NestCtx) (ctorss : List (List (ConstantVal × Nat))) :
    List Official.MemberDecl :=
  (ctx.names.zip ctorss).map fun p => ⟨p.1, formerOf ctx p.1, p.2.map (·.1.type)⟩

theorem declOf_length {ctorss : List (List (ConstantVal × Nat))} (hl : ctorss.length = ctx.names.length) :
    (declOf ctx ctorss).length = ctx.names.length := by
  simp [declOf, hl]

theorem declOf_names {ctorss : List (List (ConstantVal × Nat))} (hl : ctorss.length = ctx.names.length) :
    (declOf ctx ctorss).map (·.name) = ctx.names := by
  refine List.ext_getElem (by simp [declOf, hl]) fun i h1 h2 => ?_
  simp [declOf]

theorem declOf_ctors {ctorss : List (List (ConstantVal × Nat))} (hl : ctorss.length = ctx.names.length) :
    (declOf ctx ctorss).map (·.ctors) = ctorss.map (·.map (·.1.type)) := by
  refine List.ext_getElem (by simp [declOf, hl]) fun i h1 h2 => ?_
  simp [declOf]

variable (ctx G) in
/-- **The walk's context is the block's** (facts of the install, which
builds `ctx`): the parameters are the canonical variables, closed and
free of the declared types, the members distinct, each member's index
count the syntactic one of its stored former. -/
structure CtxOk (ctorss : List (List (ConstantVal × Nat))) : Prop where
  len : ctorss.length = ctx.names.length
  psLen : ctx.params.length = ctx.nP
  psFvar : ∀ i (h : i < ctx.params.length), ∃ ty, ctx.params[i] = .fvar i ty ∧
    ty.deepOcc (fun n => ctx.names.contains n || G n) = false
  psClosed : ∀ p ∈ ctx.params, p.looseBVarsBounded 0 = true
  nodup : ctx.names.Nodup
  nIdx : ∀ i (h : i < ctx.names.length) ty,
    Official.instPiParams (formerOf ctx ctx.names[i]) ctx.params = .ok ty → ty.piArity = ctx.nIdxs.getD i 0
  /-- the parameters are scoped below themselves -/
  psScoped : ∀ p ∈ ctx.params, Expr.WScoped ctx.nP p
  /-- a member constructor binds exactly its parameters and fields: past
  them its type is its member applied (the install's `checkSumCtor`
  shape; official's `is_valid_ind_app` on the result) -/
  ctorPi : ∀ holes, nestHoles ctx = some holes → ∀ cs ∈ ctorss, ∀ cc ∈ cs, ∀ crest,
    instPisWith ctx.params (nestAbstract ctx holes cc.1.type) = some crest → crest.piArity = cc.2
  /-- a block has a member -/
  ne : ctx.names ≠ []
  /-- the first member's former, past the parameters, ends in the block's
  sort (`p₁.resSort`, the install's `checkBlockInds`) -/
  sort0 : ∀ n ty, ctx.names.head? = some n →
    Official.instPiParams (formerOf ctx n) ctx.params = .ok ty → ty.piBinders.2 = .sort ctx.sort
  /-- the members' stored formers are closed -/
  formerLbb : ∀ m (h : m < ctx.names.length) cv caps,
    ctx.find? ctx.names[m] = some (.indInfo cv caps) → cv.type.looseBVarsBounded 0 = true

theorem ehyp_of {ctorss : List (List (ConstantVal × Nat))} {auxName : Nat → Name}
    (hfs : FreshSupply ctx G ctorss auxName) (hc : CtxOk ctx G ctorss) :
    EHyp (elimCtxOf ctx auxName) ctx.names G (declOf ctx ctorss) where
  auxG := hfs.auxG
  memG := hfs.memG
  declNames := declOf_names hc.len
  ps p hp := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨ty, he, -⟩ := hc.psFvar i hi
    change NoAux G ctx.params[i]
    rw [he]; trivial
  declAux d hd x hx := by
    obtain ⟨⟨n, cs⟩, hp, rfl⟩ := List.mem_map.mp hd
    obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp hx
    exact hfs.ctorsG cs (List.of_mem_zip hp).2 cc hcc
  ctorAux J x hx := by
    change x ∈ ((nestContainer ctx J).map (·.2)).getD [] at hx
    rcases hJ : nestContainer ctx J with _ | ⟨n, L⟩
    · rw [hJ] at hx; exact nomatch hx
    rw [hJ] at hx
    exact noAux_of_deepFree (hfs.ctorsFresh J n L hJ x hx)
where
  noAux_of_deepFree {e : Expr} (h : e.deepOcc G = false) : NoAux G e := by
    induction e with
    | const n us =>
      simp only [Expr.deepOcc] at h; exact h
    | app f a ihf iha =>
      simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h; exact ⟨ihf h.1, iha h.2⟩
    | lam t b m iht ihb | forallE t b m iht ihb =>
      simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h; exact ⟨iht h.1, ihb h.2⟩
    | letE t v b iht ihv ihb =>
      simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
    | proj s i x ih => simp only [Expr.deepOcc] at h; exact ih h
    | _ => trivial

theorem declOk_of {ctorss : List (List (ConstantVal × Nat))} {auxName : Nat → Name}
    (hc : CtxOk ctx G ctorss) : DeclOk ctx (elimCtxOf ctx auxName) G (declOf ctx ctorss) where
  ps := rfl
  lvls := rfl
  psLen := hc.psLen
  psFvar := hc.psFvar
  psClosed := hc.psClosed
  nodup := hc.nodup
  nIdx i h ty hty := by
    have hi : i < ctx.names.length := by rwa [declOf_length hc.len] at h
    have : (declOf ctx ctorss)[i].type = formerOf ctx ctx.names[i] := by simp [declOf]
    rw [this] at hty
    exact hc.nIdx i hi ty hty

theorem option_mapM_getElem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs →
      ∀ i (h : i < l.length), ∃ r, rs[i]? = some r ∧ f l[i] = some r
  | [], rs, _, i, h => absurd h (Nat.not_lt_zero _)
  | a :: l, rs, h, i, hi => by
    rw [List.mapM_cons] at h
    rcases ha : f a with _ | r
    · simp [ha] at h
    rcases hl : l.mapM f with _ | rs'
    · simp [ha, hl] at h
    simp only [ha, hl, Option.bind_some, Option.some.injEq,
      bind, pure] at h
    subst h
    cases i with
    | zero => exact ⟨r, rfl, ha⟩
    | succ i =>
      obtain ⟨r', h1, h2⟩ := option_mapM_getElem hl i (by simpa using hi)
      exact ⟨r', by simpa using h1, by simpa using h2⟩

/-- **The member holes** (`HolesOk`), from the holes' construction: each
member's hole is typed by its stored former, closed. -/
theorem holesOk_of {holes : List Expr} (hcl : NestCtxOk ctx)
    (hlbb : ∀ m (h : m < ctx.names.length) cv caps, ctx.find? ctx.names[m] = some (.indInfo cv caps) →
      cv.type.looseBVarsBounded 0 = true)
    (h : nestHoles ctx = some holes) : HolesOk ctx holes := by
  intro m hm
  obtain ⟨r, hr, hf⟩ := option_mapM_getElem h m (by simpa using hm)
  simp only [List.getElem_range] at hf
  have hgd : ctx.names.getD m .anonymous = ctx.names[m] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  rw [hgd] at hf
  split at hf
  · rename_i cv caps hfind
    cases hf
    exact ⟨cv.type, hr, hcl.2 _ _ hfind, hlbb m hm cv caps hfind⟩
  · cases hf

/-- A scoped term free of the declared types has the walk's shape. -/
theorem good_of_scoped {isAux : Name → Bool} : ∀ (e : Expr) (d : Nat), d ≤ ctx.nP →
    Expr.WScoped d e → e.deepOcc (fun n => ctx.names.contains n || isAux n) = false →
    Good ctx isAux e := by
  intro e
  induction e with
  | fvar j ty ih =>
    intro d hd hw ho
    simp only [Expr.WScoped] at hw
    simp only [Expr.deepOcc] at ho
    exact ⟨by omega, ho, ih j (by omega) hw.2 ho⟩
  | const n us =>
    intro d _ _ ho
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at ho
    exact ⟨ho.2, fun h => by rw [ho.1] at h; exact Bool.noConfusion h⟩
  | app f a ihf iha =>
    intro d hd hw ho
    simp only [Expr.WScoped] at hw; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at ho
    exact ⟨ihf d hd hw.1 ho.1, iha d hd hw.2 ho.2⟩
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro d hd hw ho
    simp only [Expr.WScoped] at hw; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at ho
    exact ⟨iht d hd hw.1 ho.1, ihb d hd hw.2 ho.2⟩
  | letE t v b iht ihv ihb =>
    intro d hd hw ho
    simp only [Expr.WScoped] at hw; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at ho
    exact ⟨iht d hd hw.1 ho.1.1, ihv d hd hw.2.1 ho.1.2, ihb d hd hw.2.2 ho.2⟩
  | proj s i x ih =>
    intro d hd hw ho
    simp only [Expr.WScoped] at hw; simp only [Expr.deepOcc] at ho
    exact ih d hd hw ho
  | _ => intro _ _ _ _; trivial

/-- **The parameters have the walk's shape** (`ParamsOk`), from the
install's context facts. -/
theorem paramsOk_of {ctorss : List (List (ConstantVal × Nat))} {isAux : Name → Bool}
    (hGa : ∀ n, isAux n = true → G n = true) (hc : CtxOk ctx G ctorss) : ParamsOk ctx isAux := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨ty, he, hty⟩ := hc.psFvar i hi
  have hw := hc.psScoped _ hp
  have ho : ctx.params[i].deepOcc (fun n => ctx.names.contains n || isAux n) = false := by
    rw [he]
    simp only [Expr.deepOcc]
    exact deepOcc_mono (fun m hm => by
      rw [Bool.or_eq_true] at hm ⊢; exact hm.imp id (hGa m)) ty hty
  exact ⟨good_of_scoped _ ctx.nP (Nat.le_refl _) hw ho, ho, hw⟩

theorem good_mkAppN_of {isAux : Name → Bool} : ∀ (args : List Expr) (f : Expr), Good ctx isAux f →
    (∀ x ∈ args, Good ctx isAux x) → Good ctx isAux (Expr.mkAppN f args)
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha => good_mkAppN_of as (.app f a) ⟨hf, ha a List.mem_cons_self⟩
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- **M2′ from official's `check_uniform_ind_occs`**: a closed member
constructor type official's uniformity check passes, free of auxiliary
names, has the walk's shape — every member occurrence at the block's own
levels. -/
theorem good_of_uniform {isAux : Name → Bool} {np : Nat} : ∀ (e : Expr) (off : Nat),
    Official.uniformOcc ctx.names (ctx.lps.map .param) np off e = true → e.hasFvar = false →
    NoAux isAux e → Good ctx isAux e := by
  intro e
  induction e with
  | const n us =>
    intro off hu _ hna
    simp only [Official.uniformOcc, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      beq_iff_eq] at hu
    refine ⟨hna, fun hc => ?_⟩
    rcases hu with hu | hu
    · rw [hu] at hc; exact nomatch hc
    · exact hu.2
  | app f a ihf iha =>
    intro off hu hfv hna
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    have hcong : Official.uniformOcc ctx.names (ctx.lps.map .param) np off f = true →
        Official.uniformOcc ctx.names (ctx.lps.map .param) np off a = true →
        Good ctx isAux (.app f a) :=
      fun h1 h2 => ⟨ihf off h1 hfv.1 hna.1, iha off h2 hfv.2 hna.2⟩
    simp only [Official.uniformOcc] at hu
    split at hu
    · rename_i c us' hfn
      split at hu
      · split at hu
        · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
          obtain ⟨⟨⟨-, -⟩, hus⟩, hargs⟩ := hu
          have hE : Expr.app f a = Expr.mkAppN (.const c us') (Expr.app f a).getAppArgs := by
            conv => lhs; rw [← Expr.mkAppN_getApp (.app f a)]
            rw [hfn]
          rw [hE]
          have hnc : NoAux isAux (.const c us') := by
            have := noAux_getAppFn _ hna; rwa [hfn] at this
          refine good_mkAppN_of _ _ ⟨hnc, fun _ => hus⟩ fun x hx => ?_
          rw [hargs] at hx
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          trivial
      · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
    · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
  | lam t b m iht ihb | forallE t b m iht ihb =>
    intro off hu hfv hna
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    exact ⟨iht off hu.1 hfv.1 hna.1, ihb (off + 1) hu.2 hfv.2 hna.2⟩
  | letE t v b iht ihv ihb =>
    intro off hu hfv hna
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    exact ⟨iht off hu.1.1 hfv.1.1 hna.1, ihv off hu.1.2 hfv.1.2 hna.2.1, ihb (off + 1) hu.2 hfv.2 hna.2.2⟩
  | proj s i x ih =>
    intro off hu hfv hna
    simp only [Official.uniformOcc] at hu
    simp only [Expr.hasFvar] at hfv
    exact ih off hu hfv hna
  | fvar i ty => intro _ _ hfv _; simp [Expr.hasFvar] at hfv
  | bvar _ | sort _ | lit _ => intro _ _ _ _; trivial

/-- After the member abstraction a well-shaped term mentions no member. -/
theorem nestOcc_abs_false {isAux : Name → Bool} {holes : List Expr} (hh : HolesOk ctx holes) :
    ∀ (x : Expr), Good ctx isAux x → (nestAbstract ctx holes x).nestOcc ctx.names 0 0 = false := by
  intro x
  induction x with
  | const n us =>
    intro hg
    rcases nestAbstract_const hh n us with ⟨m, ty, -, -, -, -, -, -, h⟩ | ⟨hno, h⟩
    · rw [h]; simp [Expr.nestOcc]
    · rw [h]; simp only [Expr.nestOcc]
      rcases hno with hno | hno
      · exact hno
      · rw [Bool.eq_false_iff]; intro hc; exact hno (hg.2 hc)
  | fvar i ty => intro _; rw [abs_fvar]; simp [Expr.nestOcc]
  | app f a ihf iha =>
    intro hg; rw [abs_app]; simp only [Expr.nestOcc, ihf hg.1, iha hg.2, Bool.or_self]
  | lam t b m iht ihb =>
    intro hg; rw [abs_lam]; simp only [Expr.nestOcc, iht hg.1, ihb hg.2, Bool.or_self]
  | forallE t b m iht ihb =>
    intro hg; rw [abs_forallE]; simp only [Expr.nestOcc, iht hg.1, ihb hg.2, Bool.or_self]
  | letE t v b iht ihv ihb =>
    intro hg; rw [abs_letE]; simp only [Expr.nestOcc, iht hg.1, ihv hg.2.1, ihb hg.2.2, Bool.or_self]
  | proj s i x ih => intro hg; rw [abs_proj]; simp only [Expr.nestOcc, ih hg]
  | bvar _ | sort _ | lit _ => intro _; rfl

/-- **(A): OFFICIAL ACCEPTS ⇒ THE WALK NEVER REJECTS** (at the block's
canonical declaration and elimination context).  Let official accept the
block's positivity (`OfficialPosAcceptsAt`: its elimination, run with a
fresh name supply, ends with `st`; its positivity loop accepts every
constructor of the eliminated declaration at every fresh-local base).
Then `nestedBlockPositivity` succeeds or declines, at every fuel, given
the sanctioned `WhnfSim` and the hypotheses still open (COMPLETE-5,
DESIGN): the per-frame obligations `FrameObl` (freshness and the side
checks), the stored environment's facts `StoredEnv`, the install's
`CtxOk`/`HolesOk`/`ParamsOk`, and — for the member constructors' M3,
whose uniform half is official's (`keys_unif_of_elimNested`) — the
residual `KeysLetProjFree` (a restriction: `PosCompleteKeys.lean`). -/
theorem nestedBlockPositivity_of_frameSide {ops : CheckerOps CheckM} {env : Env}
    {ctorss : List (List (ConstantVal × Nat))} {auxName : Nat → Name}
    {whnf : Nat → Expr → Except CheckError Expr}
    (hacc : Official.OfficialPosAcceptsAt (elimCtxOf ctx auxName) (declOf ctx ctorss) whnf
      (ctx.hiAt 0) st)
    (hos : OfficialStream ctx)
    (hfs : FreshSupply ctx G ctorss auxName) (hc : CtxOk ctx G ctorss) (hs : StoredEnv ctx)
    (hsim : WhnfSim ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) whnf)
    {T : Official.TypingOracle} (htyA : Official.OfficialTypesAt st T (ctx.hiAt 0))
    (hinf : InferSim ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) T)
    (hu4 : U4Typed ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) T)
    (hobl : FrameSide ctx (elimCtxOf ctx auxName) (st.oracle (elimCtxOf ctx auxName) whnf)
      (finalAux st) st.aux)
    {holes : List Expr} (hholes : nestHoles ctx = some holes)
    (hdecl : ∀ cs ∈ ctorss, Official.DeclChecks ctx.names (ctx.lps.map .param) ctx.nP
      (cs.map (·.1.type)))
    (hlp : KeysLetProjFree ctx st.aux) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) := by
  have hh := holesOk_of hs.closed hc.formerLbb hholes
  have hH := ehyp_of hfs hc
  have ⟨⟨fuelE, helim⟩, hacc'⟩ := hacc
  obtain ⟨q, hq, hE⟩ := EInv.elimNested hH helim
  have hfG := finalAux_G hH hE
  have hoff := offMap_of_elim hH hE hq hfs.inj (envFacts_of_stored hfG hs hos hfs) (elimEnv_of_stored hs hfs) hacc'
  -- M3: official's keys are uniform (the elimination link), and free of
  -- members under `let`/projections (the residual `hlp`)
  have hP : ∀ j (h : j < ctx.params.length), ∃ ty, ctx.params[j] = .fvar j ty := fun j h => by
    obtain ⟨ty, h1, -⟩ := hc.psFvar j h
    exact ⟨ty, h1⟩
  have hU : UHyp (elimCtxOf ctx auxName) ctx.names := by
    refine ⟨fun p hp => ?_, fun J x hx => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨ty, h1⟩ := hP i hi
      exact ⟨i, ty, h1⟩
    · change x ∈ ((nestContainer ctx J).map (·.2)).getD [] at hx
      rcases hJ : nestContainer ctx J with _ | ⟨n, L⟩
      · rw [hJ] at hx; exact nomatch hx
      rw [hJ] at hx
      have hf := hs.fresh J n L hJ x hx
      cases ho : x.1.type.nestOcc ctx.names 0 0
      · rfl
      · rw [deepOcc_of_nestOcc (fun m hm => hm) _ ho] at hf
        exact nomatch hf
  have hdecl' : ∀ d ∈ declOf ctx ctorss, ∀ x ∈ d.ctors, x.hasFvar = false ∧
      Official.uniformOcc ctx.names (ctx.lps.map .param) (elimCtxOf ctx auxName).ps.length 0 x
        = true := by
    intro d hd x hx
    obtain ⟨⟨n, cs⟩, hp, rfl⟩ := List.mem_map.mp hd
    have := hdecl cs (List.of_mem_zip hp).2 x hx
    simpa [elimCtxOf, hc.psLen] using this
  have hkeys : KeysApplied ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) :=
    keysApplied_of_map hP hc.psLen (keys_unif_of_elimNested hU hdecl' helim) hlp
  refine nestedBlockPositivity_of_elim hacc hH hfs.inj (declOk_of hc) (envFacts_of_stored hfG hs hos hfs)
    (elimEnv_of_stored hs hfs) hsim htyA hinf hu4 (frameObl_of_side hoff hs.sortEnd hobl) hkeys
    hholes hh (paramsOk_of hfG hc) (declOf_ctors hc.len) ?_
  intro cs hcs cc hcc
  obtain ⟨hcl, hu⟩ := hdecl cs hcs cc.1.type (List.mem_map_of_mem hcc)
  have hna : NoAux (finalAux st) cc.1.type :=
    noAux_mono (fun n hn => by
      rw [Bool.eq_false_iff]; intro h; rw [hfG n h] at hn; exact Bool.noConfusion hn)
      (hfs.ctorsG cs hcs cc hcc)
  have hg := good_of_uniform cc.1.type 0 hu hcl hna
  exact ⟨hcl, hg, fun crest hcr => hc.ctorPi holes hholes cs hcs cc hcc crest hcr,
    nestOcc_abs_false hh _ hg⟩

end Link

end ConLeche
