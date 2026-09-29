module

public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.StreamConsts
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Leaves
import ConLeche.Verify.Knot
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Level
import ConLeche.Semantics.DeclRun

public section

/-!
# The recursor stage's record, from the GENERATED stage's run

`recStage_of_gen`: the generated recursor stage's run (`GenRecRun`,
`Verify/Inductives/GenRecRun.lean`) supplies the kind-free stage record
`RecStageG` (`Verify/Inductives/RecStage.lean`) at the stored family
`tgtRs out`, with no member-shaped fact (`mem := fun _ => False`): the
generic recursor-stage proof (`blockRecStaged_runR`) reads it.

Per recursor the checked constant is the GENERATED type
`{ rc.cvR with type := (classGenRecTy g c).resetMeta }` (`RecTyGen.cv0`),
annotated by `checkConstantVal`.  What the record asks of it:

* it opens `mI + 1` binders and its conclusion `motive_c ı⃗ t` infers to
  `Sort elim` (`genConclSort_core`: the conclusion's head is the motive's
  variable, whose annotated domain is still `∀ ı⃗ t, Sort elim`) — the
  generated type is annotated AFTER `resetMeta`, so the ported
  `classGenRecTy_conclSort` (stated at the raw type) is re-derived here
  over the reset telescope;
* the elimination level is `structElimLevel p.elim p.large` at every
  recursor, syntactically, so the pin is `isEquiv` reflexivity and the
  counting half is the run's guard (or, at a small eliminator, the level
  `0` itself);
* the family's rule prefix is SHARED SYNTACTICALLY (`RecPrefixSame`): every
  generated type is a telescope over the same reset prefix `g.pre`, and
  annotating a domain reads only the domains before it (`SameDoms`);
* every stored rule is the annotated generated rule (`ClassRuleRun`).
-/

namespace ConLeche

/-! ## `resetMeta` through the generator's syntax -/

theorem resetMeta_closeTelescope :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (B : Expr),
      (closeTelescope nds i B).resetMeta
        = closeTelescope (nds.map fun q => (q.1.resetMeta, (⟨.never⟩ : BinderMeta))) i
            B.resetMeta
  | [], _, _ => rfl
  | (dom, bm) :: nds, i, B => by
    simp only [closeTelescope, List.map_cons, Expr.resetMeta, resetMeta_abstract1,
      resetMeta_closeTelescope nds (i + 1) B]

theorem resetMeta_mkAppN : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).resetMeta = Expr.mkAppN f.resetMeta (as.map Expr.resetMeta)
  | [], _ => rfl
  | a :: as, f => by
    simp only [Expr.mkAppN, List.map_cons]
    rw [resetMeta_mkAppN as (.app f a)]
    rfl

theorem Expr.Plain.resetMeta : ∀ {e : Expr}, Expr.Plain e → Expr.Plain e.resetMeta
  | .bvar _, _ => trivial
  | .fvar _ _, _ => trivial
  | .sort _, _ => trivial
  | .const _ _, _ => trivial
  | .app _ _, h => ⟨Expr.Plain.resetMeta h.1, Expr.Plain.resetMeta h.2⟩

theorem EndsInSort.resetMeta {u : Level} :
    ∀ (m : Nat) {e : Expr}, EndsInSort m u e → EndsInSort m u e.resetMeta
  | 0, e, h => by
    simp only [EndsInSort] at h ⊢
    subst h; rfl
  | m + 1, .forallE _ b _, h => EndsInSort.resetMeta m (e := b) h

theorem SameDoms.resetMeta :
    ∀ (n : Nat) {e₁ e₂ : Expr}, SameDoms n e₁ e₂ → SameDoms n e₁.resetMeta e₂.resetMeta
  | 0, _, _, _ => trivial
  | n + 1, .forallE A b _, .forallE A' b' _, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, SameDoms.resetMeta n h⟩

/-! ## The pre-pass's classes have motives -/

/-- **Every recursor's class, as the pre-pass reads it, has a motive**:
`classRead` reads a recursor's class as the motive ordinal of its
conclusion's head (`classOfMotiveVar`), an index into the very list of
motive slots `ClassRead.motiveSlot` indexes.  (A fact about the
pre-pass's OUTPUT shape, not about the stream.) -/
theorem classRead_recCls_motive {nP : Nat} {nPc : Name → Nat} {recs : List RecShape}
    {rd : ClassRead} (h : classRead nP nPc recs = some rd) :
    ∀ c ∈ rd.recCls, ∃ s, ClassRead.motiveSlot ⟨rd.slots, []⟩ c = some s := by
  unfold classRead at h
  obtain ⟨rc0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, body⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨slots, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨recCls, hrc, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  intro c hc
  obtain ⟨rc, -, hf⟩ := option_mapM_mem hrc c hc
  obtain ⟨⟨_, concl⟩, -, hf⟩ := Option.bind_eq_some_iff.mp hf
  simp only at hf
  split at hf
  · rename_i q _ _
    unfold classOfMotiveVar at hf
    split at hf
    · obtain ⟨hlt, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      exact ⟨_, List.getElem?_eq_getElem hlt⟩
    · exact nomatch hf
  · exact nomatch hf

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (CheckMode Env Expr Name Level ConstantVal openPisAtFvars closeTelescope
  ClassGen ClassGenScoped SameDoms EndsInSort classGenRecTy classBinder BinderMeta)

variable {μ : CheckMode}

set_option maxHeartbeats 800000 in
/-- **A telescope over a variable applied, its conclusion sorted**: the
annotated `closeTelescope nds 0 (x_k a⃗)` — the head `x_k` one of the
telescope's own binders, its domain `∀ …, Sort u` with one binder per
argument — opens at its binder count, and its conclusion infers to
`Sort u`.  (`classGenRecTy_conclSort`'s argument, over any telescope: the
annotation of the head's domain keeps its shape, and the head's
annotated variable is what the inference types.) -/
theorem genConclSort_core (hμ : μ.verifiedChecks = true) {envK : Env}
    {nds : List (Expr × BinderMeta)} {k : Nat} {T0 Tm : Expr} {bm : BinderMeta}
    {as : List Expr} {u : Level} {F : Nat} {gtyA S : Expr}
    (hcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true)
    (hbb : (Expr.mkAppN (.fvar k T0) as).looseBVarsBounded 0 = true)
    (hPlain : ConLeche.Expr.Plain (Expr.mkAppN (.fvar k T0) as))
    (hk : nds[k]? = some (Tm, bm)) (hTm : EndsInSort as.length u Tm)
    (hfv : (closeTelescope nds 0 (Expr.mkAppN (.fvar k T0) as)).hasFvar = false)
    (hann : ConLeche.annotateCore μ envK F 0 (closeTelescope nds 0 (Expr.mkAppN (.fvar k T0) as))
      = .ok gtyA)
    (hinf : ConLeche.inferTypeCore μ envK F 0 gtyA = .ok S) :
    ∃ fvs o, openPisAtFvars nds.length gtyA 0 = some (fvs, o) ∧
      ConLeche.inferTypeCore μ envK F nds.length o = .ok (.sort u) ∧
      ConLeche.ensureSortCore μ envK F nds.length (.sort u) = .ok u := by
  have hklt : k < nds.length := (List.getElem?_eq_some_iff.mp hk).1
  generalize hbody : Expr.mkAppN (.fvar k T0) as = body at hbb hPlain hfv hann
  -- the annotated type opens
  have hsd : SameDoms nds.length (closeTelescope nds 0 body) (closeTelescope nds 0 body) := by
    have := ConLeche.SameDoms.closeTelescope_append nds [] [] 0 body body
    simpa using this
  have hsdA := ConLeche.SameDoms.annotate nds.length hsd hann hann
  obtain ⟨fvs, o, hop⟩ := ConLeche.SameDoms.open_isSome nds.length (d := 0) hsdA
  obtain ⟨n', hn'⟩ : ∃ n', nds.length = n' + 1 := ⟨nds.length - 1, by omega⟩
  rw [hn'] at hop
  obtain ⟨bt, u', hbt, hu⟩ := inferTypeCore_openPis_body hμ n' hop hinf
  rw [← hn', Nat.zero_add] at hbt hu
  rw [← hn'] at hop
  -- the annotated telescope, piece by piece
  obtain ⟨nds', B', hl', he', hB', hdoms⟩ := ConLeche.annotateCore_closeTelescope nds
    hcl hbb hPlain (Expr.ErasedEq.rfl _) hann
  have hcl' : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms j _ (List.getElem?_eq_getElem hj)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hcl nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hB' hbb
  obtain ⟨xs, rest, hop', hrest, hxs⟩ :=
    open_of_erasedEq_closeTelescope nds' 0 B' gtyA hcl' hB'b he'
  rw [hl'] at hop'
  obtain ⟨hxf, hro⟩ : fvs = xs ∧ o = rest := by
    have := Option.some.inj (hop.symm.trans hop')
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  subst hxf hro
  -- the conclusion: the head variable, applied
  have hoE : Expr.ErasedEq o body := hrest.trans hB'
  rw [← hbody] at hoE
  obtain ⟨f', as', rfl, hf', has'⟩ := erasedEq_mkAppN_inv _ hoE
  obtain ⟨T, rfl⟩ : ∃ T, f' = .fvar k T := by
    match f', hf' with
    | .fvar j T, hf' => exact ⟨T, by rw [show j = k from hf']⟩
  have hgA := annotate_syntax hann hfv (ConLeche.closeTelescope_bounded nds 0 body hcl hbb)
  have hleaf : (k, T) ∈ (Expr.mkAppN (.fvar k T) as').fvarLeaves :=
    fvarLeaves_mkAppN_head as' (by simp [Expr.fvarLeaves])
  rcases ConLeche.Verify.openPisAtFvars_leaves _ hop _ (Or.inl hleaf) with hl | hl
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hgA.1] at hl; exact nomatch hl
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hl
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hop j _ hj
  simp only [Expr.fvar.injEq, Nat.zero_add] at hty
  obtain ⟨rfl, rfl⟩ := hty
  -- the head's domain keeps its shape
  have hk' : k < nds'.length := by rw [hl']; exact hklt
  obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms k _ (List.getElem?_eq_getElem hk')
  rw [hk] at hnd
  obtain rfl := Option.some.inj hnd
  have hTA := EndsInSort.annotate _ (EndsInSort.of_erasedEq _ hX hTm) hann'
  have hTx := hxs k _ nds'[k].1 hj (by simp [List.getElem?_eq_getElem hk'])
  have hTT : EndsInSort as.length u T := EndsInSort.of_erasedEq _ hTx hTA
  obtain ⟨bsT, hbsT⟩ := EndsInSort.stripPis _ hTT
  -- the inference of the conclusion
  have hF : 1 ≤ F := inferTypeCore_pos hbt
  obtain ⟨F₀, rfl⟩ : ∃ F₀, F = F₀ + 1 := ⟨F - 1, by omega⟩
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv as' hbt
  obtain ⟨-, rfl⟩ := ConLeche.Rules.inferTypeCore_fvar_inv htf
  rw [← has'] at hbsT
  obtain rfl := inferTypeCore_mkAppN_sort as' htf hbsT hbt
  obtain rfl := ensureSortCore_sort_eq hu
  exact ⟨_, _, hop, hbt, hu⟩

/-- The reset binder of the generated telescopes. -/
@[expose] def genRm (q : Expr × BinderMeta) : Expr × BinderMeta := (q.1.resetMeta, ⟨.never⟩)

/-- **The reset generated type is a telescope over the reset prefix.** -/
theorem classGenRecTy_reset_prefix {g : ClassGen} (hg : ClassGenScoped g) {c : Nat}
    {gty : Expr} (hgty : classGenRecTy g c = some gty) :
    ∃ Y B, gty.resetMeta = closeTelescope (g.pre.map genRm ++ Y) 0 B := by
  obtain ⟨ifs, maj, -, -, rfl, -, -⟩ := ConLeche.classGenRecTy_spec hg hgty
  refine ⟨(ifs.map classBinder ++ [(maj, default)]).map genRm,
    ((g.motVar c).mkAppN (ifs ++ [Expr.fvar (g.pre.length + ifs.length) maj])).resetMeta, ?_⟩
  rw [ConLeche.resetMeta_closeTelescope, List.append_assoc, List.map_append]
  rfl

set_option maxHeartbeats 800000 in
/-- **The generated type, reset and annotated, opens and its conclusion is
sorted at `Sort elim`** — `classGenRecTy_conclSort` at the type
`checkConstantVal` annotates (the RESET one, `classRecTyOk`). -/
theorem classGenRecTy_conclSort_reset (hμ : μ.verifiedChecks = true)
    {envK : Env} {g : ClassGen} (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {F : Nat}
    {gty gtyA S : Expr}
    (hgty : classGenRecTy g c = some gty) (hfv : gty.resetMeta.hasFvar = false)
    (hann : ConLeche.annotateCore μ envK F 0 gty.resetMeta = .ok gtyA)
    (hinf : ConLeche.inferTypeCore μ envK F 0 gtyA = .ok S) :
    ∃ fvs o, openPisAtFvars (g.pre.length + (g.cls.getD c default).nIdx + 1) gtyA 0
        = some (fvs, o) ∧
      ConLeche.inferTypeCore μ envK F (g.pre.length + (g.cls.getD c default).nIdx + 1) o
        = .ok (.sort g.elim) ∧
      ConLeche.ensureSortCore μ envK F (g.pre.length + (g.cls.getD c default).nIdx + 1)
        (.sort g.elim) = .ok g.elim := by
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  have hmv := ConLeche.ClassGen.motVar_eq hm
  rw [hmv] at hbb hann hfv
  have hPlain : ConLeche.Expr.Plain
      (Expr.mkAppN (.fvar (g.nP + s) (.sort .zero))
        (ifs ++ [.fvar (g.pre.length + ifs.length) maj])) := by
    refine ConLeche.Expr.Plain.mkAppN (by simp [ConLeche.Expr.Plain]) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, -⟩ := (ConLeche.ClassGen.major_scoped hg (by
        have := (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1; omega) hmaj).1 k _
        (List.getElem?_eq_getElem hk)
      rw [hxe]; trivial
    · simp only [List.mem_singleton] at ha
      subst ha; trivial
  -- the motive's domain
  obtain ⟨hcount, key, hkey⟩ := motiveSlot_count hm
  have hslen : s < g.slots.length := ConLeche.ClassRead.motiveSlot_lt hm
  have hpl := (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  obtain ⟨Tm, hTm, hpreT⟩ := ConLeche.ClassGen.prefixBinders_motive hg hkey
  rw [hcount] at hTm
  have hTmS := ClassGen.motiveTy_endsInSort hTm
  generalize hnds : g.pre ++ ifs.map classBinder ++ [(maj, (default : BinderMeta))] = nds
    at hann hcl hfv
  have hkP : g.nP + s < g.pre.length := by omega
  have hndk : (nds.map genRm)[g.nP + s]? = some (Tm.resetMeta, ⟨.never⟩) := by
    rw [List.getElem?_map, ← hnds, List.append_assoc, List.getElem?_append_left hkP, hpreT]
    rfl
  have hn : (nds.map genRm).length = g.pre.length + (g.cls.getD c default).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_map, List.length_append, List.length_singleton, hifl]
  rw [ConLeche.resetMeta_closeTelescope, ConLeche.resetMeta_mkAppN] at hann hfv
  have hTmR : EndsInSort ((ifs ++ [Expr.fvar (g.pre.length + ifs.length) maj]).map
      Expr.resetMeta).length g.elim Tm.resetMeta := by
    rw [List.length_map, List.length_append, List.length_singleton, hifl]
    exact ConLeche.EndsInSort.resetMeta _ hTmS
  have hclR : ∀ p ∈ nds.map genRm, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact looseBVarsBounded_resetMeta _ 0 (hcl q hq)
  have hbbR := looseBVarsBounded_resetMeta _ 0 hbb
  rw [ConLeche.resetMeta_mkAppN] at hbbR
  have hPlainR := ConLeche.Expr.Plain.resetMeta hPlain
  rw [ConLeche.resetMeta_mkAppN] at hPlainR
  obtain ⟨fvs, o, hop, hbt, hu⟩ := genConclSort_core hμ (nds := nds.map genRm)
    (k := g.nP + s) (T0 := .sort .zero) hclR hbbR hPlainR hndk hTmR hfv hann hinf
  rw [hn] at hop hbt hu
  exact ⟨fvs, o, hop, hbt, hu⟩

end ConLeche.Model
