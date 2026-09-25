module

public import ConLeche.Verify.Inductives.PosCompleteSteps
public import ConLeche.Verify.Inductives.PosCompleteElim
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves

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
    exact ⟨t.name, fuel, nb, hc⟩

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
    (hobl : FrameObl ops env ctx c (st.oracle c whnf) (finalAux st) st.aux)
    {holes : List Expr} (hholes : nestHoles ctx = some holes) (hh : HolesOk ctx holes)
    (hps : ParamsOk ctx (finalAux st))
    {ctorss : List (List (ConstantVal × Nat))}
    (hdc : decl.map (·.ctors) = ctorss.map (·.map (·.1.type)))
    (hmem : ∀ cs ∈ ctorss, ∀ cc ∈ cs,
      cc.1.type.hasFvar = false ∧ Good ctx (finalAux st) cc.1.type ∧
      (∀ crest, instPisWith ctx.params (nestAbstract ctx holes cc.1.type) = some crest →
        cc.2 ≤ crest.piArity ∧ MemberSide ops env ctx cc.2 crest) ∧
      (nestAbstract ctx holes cc.1.type).nestOcc ctx.names 0 0 = false) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) := by
  obtain ⟨⟨fuelE, helim⟩, hacc⟩ := hoffc
  obtain ⟨q, hq, hE⟩ := EInv.elimNested hH helim
  have hoff := offMap_of_elim hH hE hq hinj henv hee hacc
  refine nestedBlockPositivity_of_map (sigmaOk_of_elim hH hE hd) (auxEnvOk_of_elim hH hE henv hee hoff)
    hsim hd.lvls hoff henv hobl hholes hh hps ?_
  intro cs hcs cc hcc
  obtain ⟨hcl, hgood, hside, hocc⟩ := hmem cs hcs cc hcc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
  have hil : i < decl.length := by
    have := congrArg List.length hdc; simp at this; omega
  have hx : cc.1.type ∈ decl[i].ctors := by
    have := congrArg (·[i]?) hdc
    simp only [List.getElem?_map, List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hi,
      Option.map_some, Option.some.injEq] at this
    rw [this]; exact List.mem_map_of_mem hcc
  obtain ⟨u, hu, hsig, hchk⟩ := member_of_elim hH hE hq hd hacc hil hx
  exact ⟨u, hcl, hgood, hu, hsig, hchk, hside, hocc⟩

end Link

end ConLeche
