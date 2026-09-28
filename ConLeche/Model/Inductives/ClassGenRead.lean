module

public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Kernel.Inductives.ClassCheck
public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Mono
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Leaves
import ConLeche.Semantics.DeclRun

public section

/-!
# The generated recursor TYPE, read (G1-syn, the type side)

Check 6 of the class check generates, per class `c`, the recursor type

    classGenRecTy g c = Π (prefix) (ı⃗ : index domains) (t : I D⃗ ı⃗), motive_c ı⃗ t

(`Kernel/Inductives/ClassCheck.lean`), annotates it and infers it at the
empty context (`classRecTyOk`).  What the graph route's producer at the
generated family (`graphRecPre_gen`, `ClassRecKit.lean`) asks of the
type's binder data, read off the generator's syntax and the two runs:

* **every binder numeral is the elimination level's zero bit**
  (`classGenRecTy_bits`) — the ∀ clause validated each binder's datum
  against its codomain's sort (the bits law, `stripPisAV_denoteMeta_pw`),
  and the conclusion `motive_c ı⃗ t` is sorted at `Sort elim`: its head
  is the motive's variable, whose annotation is the annotated motive
  type, still `∀ ı⃗ t, Sort elim`.  So `OneElimLevel` holds at
  `Level.eval φ elim` (`hbits`);
* **the prefix is SHARED** (`classGenRecTy_prefix_eq`): the first
  `nP + #slots` binders of two classes' types read to the same binder
  data — the annotation of a domain reads only the domains before it
  (`SameDoms.annotate`), and every numeral is the one bit.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal openPisAtFvars closeTelescope
  ClassGen ClassGenScoped ScB SameDoms EndsInSort classGenRecTy classBinder)

universe w

variable {μ : CheckMode}

/-! ## Syntax helpers -/

theorem looseBVarsBounded_of_erasedEq :
    ∀ {e e' : Expr} {k : Nat}, Expr.ErasedEq e e' → e'.looseBVarsBounded k = true →
      e.looseBVarsBounded k = true
  | .bvar i, .bvar j, k, he, h => by
    obtain rfl : i = j := he
    exact h
  | .fvar _ _, .fvar _ _, _, _, _ => rfl
  | .sort _, .sort _, _, _, _ => rfl
  | .const _ _, .const _ _, _, _, _ => rfl
  | .lit _, .lit _, _, _, _ => rfl
  | .app f a, .app g b, k, he, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_of_erasedEq he.1 h.1, looseBVarsBounded_of_erasedEq he.2 h.2⟩
  | .lam t b _, .lam t' b' _, k, he, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_of_erasedEq he.2.1 h.1, looseBVarsBounded_of_erasedEq he.2.2 h.2⟩
  | .forallE t b _, .forallE t' b' _, k, he, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_of_erasedEq he.2.1 h.1, looseBVarsBounded_of_erasedEq he.2.2 h.2⟩
  | .letE t v b, .letE t' v' b', k, he, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨looseBVarsBounded_of_erasedEq he.1 h.1.1, looseBVarsBounded_of_erasedEq he.2.1 h.1.2⟩,
      looseBVarsBounded_of_erasedEq he.2.2 h.2⟩
  | .proj _ _ e, .proj _ _ e', k, he, h => by
    simp only [Expr.looseBVarsBounded] at h ⊢
    exact looseBVarsBounded_of_erasedEq he.2.2 h

/-- An expression erasure-equal to an application spine is one. -/
theorem erasedEq_mkAppN_inv :
    ∀ (as : List Expr) {e f : Expr}, Expr.ErasedEq e (Expr.mkAppN f as) →
      ∃ f' as', e = Expr.mkAppN f' as' ∧ Expr.ErasedEq f' f ∧ as'.length = as.length
  | [], e, f, he => ⟨e, [], rfl, he, rfl⟩
  | a :: as, e, f, he => by
    obtain ⟨g, as', rfl, hg, hl⟩ := erasedEq_mkAppN_inv as (f := .app f a) he
    match g, hg with
    | .app f' a', hg => exact ⟨f', a' :: as', rfl, hg.1, by simp [hl]⟩

theorem EndsInSort.closeTelescope {u : Level} {m : Nat} {B : Expr} (hB : EndsInSort m u B) :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat),
      EndsInSort (nds.length + m) u (closeTelescope nds i B)
  | [], _ => by simpa [ConLeche.closeTelescope] using hB
  | (dom, bm) :: nds, i => by
    rw [show (List.length ((dom, bm) :: nds)) + m = (nds.length + m) + 1 by simp; omega]
    exact EndsInSort.abstract1 _ 0 (EndsInSort.closeTelescope hB nds (i + 1))

/-! ## The inference, peeled to the conclusion -/

/-- **A successful inference of a telescope infers its opened body**, at
a fuel no larger, and sorts it. -/
theorem inferTypeCore_openPis_body (hμ : μ.verifiedChecks = true) {envK : Env} :
    ∀ (n : Nat) {d F : Nat} {e s : Expr} {fvs : List Expr} {o : Expr},
      openPisAtFvars (n + 1) e d = some (fvs, o) →
      ConLeche.inferTypeCore μ envK F d e = .ok s →
      ∃ bt u, ConLeche.inferTypeCore μ envK F (d + (n + 1)) o = .ok bt ∧
        ConLeche.ensureSortCore μ envK F (d + (n + 1)) bt = .ok u
  | n, d, F, e, s, fvs, o, hop, hinf => by
    match e, hop with
    | .forallE ty bd mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨-, rfl⟩ := hop
        obtain ⟨F₀, udom, v, bt₁, rfl, -, hbt₁, hv, -, -⟩ := inferTypeCore_forallE_peel hμ hinf
        cases n with
        | zero =>
          simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop'
          obtain ⟨-, rfl⟩ := hop'
          exact ⟨bt₁, v, ConLeche.inferTypeCore_mono (Nat.le_succ _) hbt₁,
            ConLeche.ensureSortCore_mono (Nat.le_succ _) hv⟩
        | succ n =>
          obtain ⟨bt, u, hbt, hu⟩ := inferTypeCore_openPis_body hμ n hop' hbt₁
          refine ⟨bt, u, ?_, ?_⟩
          · rw [show d + (n + 1 + 1) = d + 1 + (n + 1) by omega]
            exact ConLeche.inferTypeCore_mono (Nat.le_succ _) hbt
          · rw [show d + (n + 1 + 1) = d + 1 + (n + 1) by omega]
            exact ConLeche.ensureSortCore_mono (Nat.le_succ _) hu
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _, hop | .sort _, hop | .const _ _, hop | .app _ _, hop
    | .lam _ _ _, hop | .letE _ _ _, hop | .lit _, hop | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-! ## The motive's slot -/

/-- The `c`-th element of a filtered range is preceded by exactly `c`
hits. -/
theorem filter_range_getElem_count {p : Nat → Bool} {n c s : Nat}
    (h : ((List.range n).filter p)[c]? = some s) :
    ((List.range s).filter p).length = c ∧ s < n ∧ p s = true := by
  have hm := List.mem_of_getElem? h
  simp only [List.mem_filter, List.mem_range] at hm
  obtain ⟨hs, hps⟩ := hm
  refine ⟨?_, hs, hps⟩
  have hsplit : List.range n = List.range s ++ (List.range (n - s)).map (s + ·) := by
    rw [← List.range_add]; congr 1; omega
  have hfilt : (List.range n).filter p
      = (List.range s).filter p ++ s :: ((List.range (n - s - 1)).map
          (fun x => s + (x + 1))).filter p := by
    rw [hsplit, List.filter_append]
    congr 1
    rw [show n - s = (n - s - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.filter_cons]
    simp only [Nat.add_zero, hps, if_true]
    rfl
  have hnd : ((List.range n).filter p).Nodup := List.nodup_range.filter _
  rw [hfilt] at h hnd
  have h2 : ((List.range s).filter p ++ s :: ((List.range (n - s - 1)).map
      (fun x => s + (x + 1))).filter p)[((List.range s).filter p).length]? = some s := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hlt : c < ((List.range s).filter p ++ s :: ((List.range (n - s - 1)).map
      (fun x => s + (x + 1))).filter p).length := (List.getElem?_eq_some_iff.mp h).1
  exact ((List.getElem?_inj hlt hnd).mp (by rw [h, h2])).symm

/-- The motive slots before a class's motive are the classes before it. -/
theorem motiveSlot_count {slots : List ConLeche.ClassSlot} {c s : Nat}
    (h : ConLeche.ClassRead.motiveSlot ⟨slots, []⟩ c = some s) :
    ConLeche.ClassGen.motiveCount slots s = c ∧
    ∃ key, slots[s]? = some (.motive key) := by
  unfold ConLeche.ClassRead.motiveSlot at h
  simp only at h
  obtain ⟨hc, hs, hps⟩ := filter_range_getElem_count h
  refine ⟨?_, ?_⟩
  · rw [← hc, ConLeche.ClassGen.motiveCount]
    congr 1
    refine List.filter_congr fun x hx => ?_
    rw [List.mem_range] at hx
    have hxl : x < slots.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxl, Option.getD_some]
    cases slots[x] <;> rfl
  · cases hsl : slots[s]? with
    | none => rw [hsl] at hps; exact nomatch hps
    | some sl =>
      rw [hsl] at hps
      cases sl with
      | motive key => exact ⟨key, rfl⟩
      | minor _ _ _ => exact nomatch hps

/-- A motive's type is `∀ ı⃗ (t : I D⃗ ı⃗), Sort elim`. -/
theorem ClassGen.motiveTy_endsInSort {g : ClassGen} {c d : Nat} {T : Expr}
    (h : g.motiveTy c d = some T) :
    EndsInSort ((g.cls.getD c default).nIdx + 1) g.elim T := by
  unfold ClassGen.motiveTy at h
  obtain ⟨⟨ifs, maj⟩, hmaj, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  obtain ⟨ty0, body0, hty0, hop, hmj⟩ := ConLeche.ClassGen.major_inv hmaj
  have hl := ConLeche.Verify.openPisAtFvars_length _ hop
  have := EndsInSort.closeTelescope (m := 1) (u := g.elim) (B := .forallE maj (.sort g.elim) default)
    rfl (ifs.map classBinder) d
  rwa [List.length_map, hl] at this

/-- An application spine's head is one of its leaves' owners. -/
theorem fvarLeaves_mkAppN_head {i : Nat} {T : Expr} :
    ∀ (as : List Expr) {f : Expr}, (i, T) ∈ f.fvarLeaves →
      (i, T) ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, h => h
  | a :: as, f, h => fvarLeaves_mkAppN_head as (f := .app f a)
      (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h)

/-! ## The bits -/

set_option maxHeartbeats 800000 in
/-- **Every binder numeral of the generated type's reading is the
elimination level's zero bit.** -/
theorem classGenRecTy_bits (hμ : μ.verifiedChecks = true) {acval : Name → (Name → Nat) → AnnotTerm}
    {env envK : Env} {φ : Name → Nat} {g : ClassGen} (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {F : Nat}
    {gty gtyA S : Expr} {ea : AnnotTerm}
    (hgty : classGenRecTy g c = some gty)
    (hann : ConLeche.annotateCore μ envK F 0 gty = .ok gtyA)
    (hinf : ConLeche.inferTypeCore μ envK F 0 gtyA = .ok S)
    (hread : denoteMeta acval env φ 0 gtyA = some ea) :
    ∃ pps b, stripPisAV (g.pre.length + (g.cls.getD c default).nIdx + 1) ea = some (pps, b) ∧
      pps.length = g.pre.length + (g.cls.getD c default).nIdx + 1 ∧
      ∀ p ∈ pps, p.1 = 0 ∧ p.2.1 = pwBit φ (Level.zeronessOf g.elim) := by
  obtain ⟨hpl, hpreS⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  have hPlain : ConLeche.Expr.Plain
      (Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])) := by
    refine ConLeche.Expr.Plain.mkAppN (by simp [ClassGen.motVar, ClassGen.slotVar,
      ConLeche.Expr.Plain]) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, -⟩ := (ConLeche.ClassGen.major_scoped hg (by omega) hmaj).1 k _
        (List.getElem?_eq_getElem hk)
      rw [hxe]; trivial
    · simp only [List.mem_singleton] at ha
      subst ha; trivial
  generalize hnds : g.pre ++ ifs.map classBinder ++ [(maj, (default : ConLeche.BinderMeta))]
    = nds at hann hcl
  generalize hbody : Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])
    = body at hann hbb hPlain
  have hn : nds.length = g.pre.length + (g.cls.getD c default).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_append, List.length_map, List.length_singleton, hifl]
  -- the annotated type opens
  have hsd : SameDoms nds.length (closeTelescope nds 0 body) (closeTelescope nds 0 body) := by
    have := ConLeche.SameDoms.closeTelescope_append nds [] [] 0 body body
    simpa using this
  have hsdA := ConLeche.SameDoms.annotate nds.length hsd hann hann
  obtain ⟨fvs, o, hop⟩ := ConLeche.SameDoms.open_isSome nds.length (d := 0) hsdA
  obtain ⟨pps, b, hst, -, hlen, hpp⟩ := denoteMeta_openPis nds.length hop hread
  -- the conclusion's inference
  obtain ⟨n', hn'⟩ : ∃ n', nds.length = n' + 1 := ⟨nds.length - 1, by omega⟩
  rw [hn'] at hop
  obtain ⟨bt, u, hbt, hu⟩ := inferTypeCore_openPis_body hμ n' hop hinf
  rw [← hn'] at hop hbt hu
  have hbits := stripPisAV_denoteMeta_pw (acval := acval) (env := env) (envK := envK) (φ := φ) hμ
    nds.length (Nat.le_refl F) hop hread hst hinf hbt hu
  refine ⟨pps, b, by rw [← hn]; exact hst, by rw [hlen, hn], fun p hp => ?_⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨x, hx⟩ : ∃ x, fvs[i]? = some x := by
      have hfl := ConLeche.Verify.openPisAtFvars_length _ hop
      exact ⟨fvs[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p', hp', hp1, -⟩ := hpp i x hx
    rw [List.getElem?_eq_getElem hi] at hp'
    rw [← (Option.some.inj hp')] at hp1
    exact hp1
  rw [hbits p hp]
  congr 1
  -- the conclusion is sorted at `Sort elim`
  obtain ⟨nds', B', hl', he', hB', hdoms⟩ := ConLeche.annotateCore_closeTelescope nds
    hcl hbb hPlain (Expr.ErasedEq.rfl _) hann
  have hcl' : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hcl nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hB' hbb
  obtain ⟨xs, rest, hop', hrest, hxs⟩ := open_of_erasedEq_closeTelescope nds' 0 B' gtyA hcl' hB'b he'
  rw [hl'] at hop'
  obtain ⟨hxf, hro⟩ : fvs = xs ∧ o = rest := by
    have := Option.some.inj (hop.symm.trans hop')
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  subst hxf hro
  -- the conclusion: the motive's variable, applied
  have hoE : Expr.ErasedEq o body := hrest.trans hB'
  rw [← hbody] at hoE
  obtain ⟨f', as', rfl, hf', has'⟩ := erasedEq_mkAppN_inv _ hoE
  have hmv := ConLeche.ClassGen.motVar_eq hm
  rw [hmv] at hf'
  obtain ⟨T, rfl⟩ : ∃ T, f' = .fvar (g.nP + s) T := by
    match f', hf' with
    | .fvar j T, hf' => exact ⟨T, by rw [show j = g.nP + s from hf']⟩
  -- its annotation is the opened motive domain
  have hgA := annotate_syntax hann (by rw [← hnds, ← hbody]; exact
    (ConLeche.classGenRecTy_closed hg hm hgty).1) (by rw [← hnds, ← hbody]; exact
    (ConLeche.classGenRecTy_closed hg hm hgty).2)
  have hleaf : (g.nP + s, T) ∈ (Expr.mkAppN (.fvar (g.nP + s) T) as').fvarLeaves :=
    fvarLeaves_mkAppN_head as' (by simp [Expr.fvarLeaves])
  rcases ConLeche.Verify.openPisAtFvars_leaves _ hop _ (Or.inl hleaf) with hl | hl
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hgA.1] at hl; exact nomatch hl
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hl
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hop k _ hk
  simp only [Expr.fvar.injEq, Nat.zero_add] at hty
  obtain ⟨rfl, rfl⟩ := hty
  -- the motive domain's shape
  have hslen : s < g.slots.length := ConLeche.ClassRead.motiveSlot_lt hm
  obtain ⟨hcount, key, hkey⟩ := motiveSlot_count hm
  obtain ⟨Tm, hTm, hpreT⟩ := ConLeche.ClassGen.prefixBinders_motive hg hkey
  rw [hcount] at hTm
  have hTmS := ClassGen.motiveTy_endsInSort hTm
  have hkP : g.nP + s < g.pre.length := by omega
  have hndk : nds[g.nP + s]? = some (Tm, default) := by
    rw [← hnds, List.append_assoc, List.getElem?_append_left hkP]; exact hpreT
  have hk' : g.nP + s < nds'.length := by rw [hl', hn]; omega
  obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms (g.nP + s) _ (List.getElem?_eq_getElem hk')
  rw [hndk] at hnd
  obtain rfl := Option.some.inj hnd
  have hTA := EndsInSort.annotate _ (EndsInSort.of_erasedEq _ hX hTmS) hann'
  have hTx := hxs (g.nP + s) _ nds'[g.nP + s].1 hk (by simp [List.getElem?_eq_getElem hk'])
  have hTT : EndsInSort ((g.cls.getD c default).nIdx + 1) g.elim T :=
    EndsInSort.of_erasedEq _ hTx hTA
  obtain ⟨bsT, hbsT⟩ := EndsInSort.stripPis _ hTT
  -- the inference of the conclusion
  have hF : 1 ≤ F := inferTypeCore_pos hbt
  obtain ⟨F₀, rfl⟩ : ∃ F₀, F = F₀ + 1 := ⟨F - 1, by omega⟩
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv as' hbt
  obtain ⟨-, rfl⟩ := ConLeche.Rules.inferTypeCore_fvar_inv htf
  have hasl : as'.length = (g.cls.getD c default).nIdx + 1 := by
    rw [has']; simp [hifl]
  rw [← hasl] at hbsT
  obtain rfl := inferTypeCore_mkAppN_sort as' htf hbsT hbt
  rw [ensureSortCore_sort_eq hu]

end ConLeche.Model
