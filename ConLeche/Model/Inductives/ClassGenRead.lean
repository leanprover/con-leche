module

public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Mono
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Leaves
import ConLeche.Semantics.DeclRun
public import ConLeche.Model.Inductives.ClassRecKit
import ConLeche.Verify.Denote.Shift
import ConLeche.Model.Annot.BitRename

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

/-! ## The conclusion -/

/-- The index of a variable (`0` off variables). -/
@[expose] def fvIdx : Expr → Nat
  | .fvar i _ => i
  | _ => 0

section Concl

variable {V : Type w} [SetTheory V]

/-- A prefix value at a frame extended by `bs`. -/
theorem consList_prefix_getD' {xs bs : List V} {ρ : Nat → V} {k : Nat} (hk : k < xs.length) :
    consList (xs ++ bs) ρ (bs.length + xs.length - 1 - k) = xs.getD k (SetTheory.pt : V) := by
  have hlen : (xs ++ bs).length = bs.length + xs.length := by simp; omega
  rw [consList_getD_of_lt _ _ _ (by omega), hlen,
    show bs.length + xs.length - 1 - (bs.length + xs.length - 1 - k) = k by omega,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]

/-- **A variable applied to variables, read and interpreted** at a frame
of the reading's depth: the head's value applied to the arguments'. -/
theorem interp_denoteMeta_fvarSpine {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {ρ : Nat → V} {vs : List V} {d : Nat} (hvl : vs.length = d) :
    ∀ (as : List Expr) (f : Expr) (fa : AnnotTerm),
      denoteMeta acval env φ d f = some fa →
      (∀ a ∈ as, ∃ i T, a = .fvar i T ∧ i < d) →
      ∃ ra, denoteMeta acval env φ d (Expr.mkAppN f as) = some ra ∧
        interp V (consList vs ρ) ra
          = (as.map fun a => vs.getD (fvIdx a) (SetTheory.pt : V)).foldl SetTheory.app
              (interp V (consList vs ρ) fa)
  | [], f, fa, hf, _ => ⟨fa, hf, rfl⟩
  | a :: as, f, fa, hf, has => by
    obtain ⟨i, T, rfl, hi⟩ := has a List.mem_cons_self
    have hfa : denoteMeta acval env φ d (.app f (.fvar i T))
        = some (.app fa (.bvar (d - 1 - i))) := by
      rw [denoteMeta_app, hf, denoteMeta_fvar]; rfl
    obtain ⟨ra, hra, hint⟩ := interp_denoteMeta_fvarSpine hvl as _ _ hfa
      (fun b hb => has b (List.mem_cons_of_mem _ hb))
    refine ⟨ra, hra, ?_⟩
    rw [hint]
    simp only [List.map_cons, List.foldl_cons, interp_app, interp_bvar, fvIdx]
    congr 2
    rw [consList_getD_of_lt _ _ _ (by omega), hvl, show d - 1 - (d - 1 - i) = i by omega]

set_option maxHeartbeats 800000 in
/-- **The generated type's conclusion, read**: at a frame of the
prefix, an index spine and a major, the motive's value applied to the
index spine and the major. -/
theorem classGenRecTy_concl
    {acval : Name → (Name → Nat) → AnnotTerm} {env envK : Env} {φ : Name → Nat} {g : ClassGen}
    (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {F : Nat}
    {gty gtyA : Expr} {ea : AnnotTerm}
    (hgty : classGenRecTy g c = some gty)
    (hann : ConLeche.annotateCore μ envK F 0 gty = .ok gtyA)
    (hread : denoteMeta acval env φ 0 gtyA = some ea) {pps : List (Nat × Nat × AnnotTerm)}
    {b : AnnotTerm}
    (hst : stripPisAV (g.pre.length + (g.cls.getD c default).nIdx + 1) ea = some (pps, b)) :
    ∀ (ρ : Nat → V) (xs zs : List V) (x : V), xs.length = g.pre.length →
      zs.length = (g.cls.getD c default).nIdx →
      interp V (consList (xs ++ (zs ++ [x])) ρ) b
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (g.nP + s) (SetTheory.pt : V)) := by
  intro ρ xs zs x hxl hzl
  obtain ⟨hpl, -⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  obtain ⟨hifs, -⟩ := ConLeche.ClassGen.major_scoped hg (by omega) hmaj
  have hPlain : ConLeche.Expr.Plain
      (Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])) := by
    refine ConLeche.Expr.Plain.mkAppN (by simp [ClassGen.motVar, ClassGen.slotVar,
      ConLeche.Expr.Plain]) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, -⟩ := hifs k _ (List.getElem?_eq_getElem hk)
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
  obtain ⟨nds', B', hl', he', hB', hdoms⟩ := ConLeche.annotateCore_closeTelescope nds
    hcl hbb hPlain (Expr.ErasedEq.rfl _) hann
  have hcl' : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hcl nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hB' hbb
  obtain ⟨fvs, o, hop, hrest, -⟩ := open_of_erasedEq_closeTelescope nds' 0 B' gtyA hcl' hB'b he'
  rw [hl', hn] at hop
  obtain ⟨pps', b', hst', hbo, -, -⟩ := denoteMeta_openPis _ hop hread
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hst'))
  have hoE : Expr.ErasedEq o body := hrest.trans hB'
  rw [Nat.zero_add, denoteMeta_erasedEq hoE, ← hbody, ConLeche.ClassGen.motVar_eq hm] at hbo
  have hvl : (xs ++ (zs ++ [x])).length = g.pre.length + (g.cls.getD c default).nIdx + 1 := by
    simp only [List.length_append, List.length_singleton, hxl, hzl]; omega
  have hsl : s < g.slots.length := ConLeche.ClassRead.motiveSlot_lt hm
  obtain ⟨ra, hra, hint⟩ := interp_denoteMeta_fvarSpine (acval := acval) (env := env) (φ := φ)
    (ρ := ρ) hvl (ifs ++ [.fvar (g.pre.length + ifs.length) maj]) (.fvar (g.nP + s) (.sort .zero))
    _ (denoteMeta_fvar _ _ _ _) (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, -⟩ := hifs k _ (List.getElem?_eq_getElem hk)
        exact ⟨_, ty, hxe, by omega⟩
      · simp only [List.mem_singleton] at ha
        exact ⟨_, maj, ha, by omega⟩)
  obtain rfl := Option.some.inj (hbo.symm.trans hra)
  rw [hint]
  have hhd : interp V (consList (xs ++ (zs ++ [x])) ρ)
      (.bvar (g.pre.length + (g.cls.getD c default).nIdx + 1 - 1 - (g.nP + s)))
      = xs.getD (g.nP + s) (SetTheory.pt : V) := by
    show consList (xs ++ (zs ++ [x])) ρ _ = _
    rw [show g.pre.length + (g.cls.getD c default).nIdx + 1 - 1 - (g.nP + s)
      = (zs ++ [x]).length + xs.length - 1 - (g.nP + s) by simp [hxl, hzl]; omega]
    exact consList_prefix_getD' (by omega)
  rw [hhd]
  congr 1
  refine List.ext_getElem (by simp [hifl, hzl]) fun k hk₁ hk₂ => ?_
  simp only [List.getElem_map]
  rcases Nat.lt_or_ge k ifs.length with hk | hk
  · rw [List.getElem_append_left hk, List.getElem_append_left (by omega)]
    obtain ⟨ty, hxe, -⟩ := hifs k _ (List.getElem?_eq_getElem hk)
    rw [hxe, fvIdx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by omega)]
    simp [hxl, List.getElem?_eq_getElem (show k < zs.length by omega)]
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have hk' : k - ifs.length = 0 := by simp at hk₁; omega
    simp only [hk', List.getElem_cons_zero, fvIdx]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by simp [hxl, hzl, hifl])]
    simp [hxl, hzl, hifl]

end Concl

/-! ## The shared prefix -/

set_option maxHeartbeats 800000 in
/-- **The prefix is shared**: two classes' generated types, annotated and
inferred by the same runs, read to the same first `nP + #slots` binder
data — the same domains (a domain's annotation reads only the domains
before it) and the same numeral (the one bit). -/
theorem classGenRecTy_prefix_eq (hμ : μ.verifiedChecks = true)
    {acval : Name → (Name → Nat) → AnnotTerm} {env envK : Env} {φ : Name → Nat} {g : ClassGen}
    (hg : ClassGenScoped g) {F : Nat} {c₁ c₂ s₁ s₂ : Nat}
    (hm₁ : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c₁ = some s₁)
    (hm₂ : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c₂ = some s₂)
    {gty₁ gty₂ gtyA₁ gtyA₂ S₁ S₂ : Expr} {ea₁ ea₂ : AnnotTerm}
    (hgty₁ : classGenRecTy g c₁ = some gty₁) (hgty₂ : classGenRecTy g c₂ = some gty₂)
    (hann₁ : ConLeche.annotateCore μ envK F 0 gty₁ = .ok gtyA₁)
    (hann₂ : ConLeche.annotateCore μ envK F 0 gty₂ = .ok gtyA₂)
    (hinf₁ : ConLeche.inferTypeCore μ envK F 0 gtyA₁ = .ok S₁)
    (hinf₂ : ConLeche.inferTypeCore μ envK F 0 gtyA₂ = .ok S₂)
    (hread₁ : denoteMeta acval env φ 0 gtyA₁ = some ea₁)
    (hread₂ : denoteMeta acval env φ 0 gtyA₂ = some ea₂)
    {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm}
    (hst₁ : stripPisAV (g.pre.length + (g.cls.getD c₁ default).nIdx + 1) ea₁ = some (pps₁, b₁))
    (hst₂ : stripPisAV (g.pre.length + (g.cls.getD c₂ default).nIdx + 1) ea₂ = some (pps₂, b₂)) :
    pps₁.take g.pre.length = pps₂.take g.pre.length := by
  obtain ⟨q₁, b₁', hq₁, hql₁, hbits₁⟩ := classGenRecTy_bits hμ (acval := acval) (env := env)
    (φ := φ) hg hm₁ hgty₁ hann₁ hinf₁ hread₁
  obtain ⟨q₂, b₂', hq₂, hql₂, hbits₂⟩ := classGenRecTy_bits hμ (acval := acval) (env := env)
    (φ := φ) hg hm₂ hgty₂ hann₂ hinf₂ hread₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst₁.symm.trans hq₁))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst₂.symm.trans hq₂))
  obtain ⟨ifs₁, maj₁, -, hifl₁, rfl, -, -⟩ := ConLeche.classGenRecTy_spec hg hgty₁
  obtain ⟨ifs₂, maj₂, -, hifl₂, rfl, -, -⟩ := ConLeche.classGenRecTy_spec hg hgty₂
  -- the same first domains, annotated
  have hsd : SameDoms g.pre.length
      (closeTelescope (g.pre ++ ifs₁.map classBinder ++ [(maj₁, default)]) 0
        (Expr.mkAppN (g.motVar c₁) (ifs₁ ++ [.fvar (g.pre.length + ifs₁.length) maj₁])))
      (closeTelescope (g.pre ++ ifs₂.map classBinder ++ [(maj₂, default)]) 0
        (Expr.mkAppN (g.motVar c₂) (ifs₂ ++ [.fvar (g.pre.length + ifs₂.length) maj₂]))) := by
    simp only [List.append_assoc]
    exact ConLeche.SameDoms.closeTelescope_append _ _ _ 0 _ _
  have hsdA := ConLeche.SameDoms.annotate _ hsd hann₁ hann₂
  -- both open along the full telescope, hence along the prefix
  have hsdF₁ : SameDoms (g.pre.length + (g.cls.getD c₁ default).nIdx + 1) gtyA₁ gtyA₁ := by
    refine ConLeche.SameDoms.annotate _ ?_ hann₁ hann₁
    have := ConLeche.SameDoms.closeTelescope_append
      (g.pre ++ ifs₁.map classBinder ++ [(maj₁, default)]) [] [] 0
      (Expr.mkAppN (g.motVar c₁) (ifs₁ ++ [.fvar (g.pre.length + ifs₁.length) maj₁]))
      (Expr.mkAppN (g.motVar c₁) (ifs₁ ++ [.fvar (g.pre.length + ifs₁.length) maj₁]))
    have hlen : (g.pre ++ ifs₁.map classBinder ++ [(maj₁, (default : ConLeche.BinderMeta))]).length
        = g.pre.length + (g.cls.getD c₁ default).nIdx + 1 := by
      simp only [List.length_append, List.length_map, List.length_singleton, hifl₁]
    rw [hlen] at this
    simpa only [List.append_nil] using this
  have hsdF₂ : SameDoms (g.pre.length + (g.cls.getD c₂ default).nIdx + 1) gtyA₂ gtyA₂ := by
    refine ConLeche.SameDoms.annotate _ ?_ hann₂ hann₂
    have := ConLeche.SameDoms.closeTelescope_append
      (g.pre ++ ifs₂.map classBinder ++ [(maj₂, default)]) [] [] 0
      (Expr.mkAppN (g.motVar c₂) (ifs₂ ++ [.fvar (g.pre.length + ifs₂.length) maj₂]))
      (Expr.mkAppN (g.motVar c₂) (ifs₂ ++ [.fvar (g.pre.length + ifs₂.length) maj₂]))
    have hlen : (g.pre ++ ifs₂.map classBinder ++ [(maj₂, (default : ConLeche.BinderMeta))]).length
        = g.pre.length + (g.cls.getD c₂ default).nIdx + 1 := by
      simp only [List.length_append, List.length_map, List.length_singleton, hifl₂]
    rw [hlen] at this
    simpa only [List.append_nil] using this
  obtain ⟨fvs₁, o₁, hop₁⟩ := ConLeche.SameDoms.open_isSome _ (d := 0) hsdF₁
  obtain ⟨fvs₂, o₂, hop₂⟩ := ConLeche.SameDoms.open_isSome _ (d := 0) hsdF₂
  rw [Nat.add_assoc] at hop₁ hop₂
  obtain ⟨pf₁, rf₁, po₁, hpo₁, -, hF₁⟩ := openPisAtFvars_split g.pre.length hop₁
  obtain ⟨pf₂, rf₂, po₂, hpo₂, -, hF₂⟩ := openPisAtFvars_split g.pre.length hop₂
  have hpf : pf₁ = pf₂ := ConLeche.SameDoms.open _ hsdA hpo₁ hpo₂
  rw [← Nat.add_assoc] at hop₁ hop₂
  obtain ⟨pp₁, bb₁, hs₁, -, -, hpp₁⟩ := denoteMeta_openPis _ hop₁ hread₁
  obtain ⟨pp₂, bb₂, hs₂, -, -, hpp₂⟩ := denoteMeta_openPis _ hop₂ hread₂
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hs₁.symm.trans hq₁))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hs₂.symm.trans hq₂))
  have hpfl : pf₁.length = g.pre.length := ConLeche.Verify.openPisAtFvars_length _ hpo₁
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_take, List.getElem?_take]
  split
  · next hi =>
    have hx₁ : fvs₁[i]? = pf₁[i]? := by
      rw [hF₁, List.getElem?_append_left (by omega)]
    have hx₂ : fvs₂[i]? = pf₁[i]? := by
      rw [hF₂, ← hpf, List.getElem?_append_left (by omega)]
    obtain ⟨x, hx⟩ : ∃ x, pf₁[i]? = some x := ⟨pf₁[i]'(by omega), List.getElem?_eq_getElem _⟩
    rw [hx] at hx₁ hx₂
    obtain ⟨p₁, hp₁, hp₁1, hp₁3⟩ := hpp₁ i x hx₁
    obtain ⟨p₂, hp₂, hp₂1, hp₂3⟩ := hpp₂ i x hx₂
    rw [hp₁, hp₂]
    congr 1
    have hb₁ := (hbits₁ p₁ (List.mem_of_getElem? hp₁)).2
    have hb₂ := (hbits₂ p₂ (List.mem_of_getElem? hp₂)).2
    have hr := Option.some.inj (hp₁3.symm.trans hp₂3)
    obtain ⟨a₁, b₁, c₁'⟩ := p₁
    obtain ⟨a₂, b₂, c₂'⟩ := p₂
    simp only at hp₁1 hp₂1 hb₁ hb₂ hr
    rw [hp₁1, hp₂1, hb₁, hb₂, hr]
  · rfl

/-- **`hbits`**: binder data whose every numeral is the elimination
level's zero bit have ONE elimination level, `Level.eval φ elim`. -/
theorem oneElimLevel_of_bits {φ : Name → Nat} {elim : Level} {K : Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)}
    (h : ∀ c, c < K → ∀ p ∈ rds c, p.2.1 = pwBit φ (Level.zeronessOf elim)) :
    OneElimLevel (Level.eval φ elim) K rds := by
  intro c hc p hp
  rw [h c hc p hp, pwBit_zeronessOf]

/-! ## Chain independence and the `ih` data's bounds, from readings

The graph route's rows at the generated family read the prefix and
field domains, the index expressions, the fired spine and the `ih` data
at frames that carry the recursors' CHAIN below the base (`chainFrame`).
They are the model's readings of SCOPED terms — every generated piece
is (`ClassGenScope.lean`) — so they read no chain variable. -/

section Rows

variable {V : Type w} [SetTheory V] {env : Env}

/-- `a` is the model's reading, at depth `D`, of a term scoped at `D`. -/
@[expose] def IsReadingAt (m : EnvModel V env) (φ : Name → Nat) (D : Nat) (a : AnnotTerm) :
    Prop :=
  ∃ e : Expr, ScB D e ∧ denoteMeta m.acval env φ D e = some a

/-- A reading of a scoped term names no variable at or above its depth. -/
theorem IsReadingAt.below {m : EnvModel V env} {φ : Name → Nat} {D : Nat} {a : AnnotTerm}
    (h : IsReadingAt m φ D a) : Term.bvarsBelow D a.erase := by
  obtain ⟨e, ⟨hw, hb⟩, hd⟩ := h
  exact ConLeche.Verify.denote_bvarsBelow m.cval_closedL D e hw hb
    (denoteMeta_erase (cval := fun n ψ => (m.acval n ψ).erase) (fun _ _ => rfl) D e hd)

theorem fieldsBelow_of_readings {m : EnvModel V env} {φ : Name → Nat} :
    ∀ {b : Nat} {Ds : List AnnotTerm},
      (∀ (k : Nat) (D : AnnotTerm), Ds[k]? = some D → IsReadingAt m φ (b + k) D) →
      FieldsBelow b Ds
  | _, [], _ => trivial
  | b, D :: Ds, h => by
    refine ⟨by simpa using (h 0 D rfl).below,
      fieldsBelow_of_readings (m := m) (φ := φ) fun k D' hk => ?_⟩
    have := h (k + 1) D' (by simpa using hk)
    rwa [show b + (k + 1) = b + 1 + k by omega] at this

/-- Two frames sharing a spine agree below its length. -/
theorem consList_agree_below {σ σ' : Nat → V} (zs : List V) :
    ∀ i, i < zs.length → consList zs σ i = consList zs σ' i := by
  intro i hi
  rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]

/-- **`hchI`, from readings.**  The prefix and field domains, the index
expressions and the fired spine of the generated family are readings of
scoped terms, so they read alike at the chain frame and at its base. -/
theorem genHchI_of_readings {m : EnvModel V env} {φ : Name → Nat} {K : Nat} {ρ : Nat → V}
    {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
    {mk : Nat → Nat → AnnotTerm}
    (hP : ∀ c, c < K → ∀ (k : Nat) (D : AnnotTerm), (pdoms c)[k]? = some D →
      IsReadingAt m φ k D)
    (hF : ∀ c, c < K → ∀ j, j < nCt c → ∀ (k : Nat) (D : AnnotTerm), (fdoms c j)[k]? = some D →
      IsReadingAt m φ ((pdoms c).length + k) D)
    (hE : ∀ c, c < K → ∀ j, j < nCt c → ∀ e ∈ es c j,
      IsReadingAt m φ ((pdoms c).length + (fdoms c j).length) e)
    (hM : ∀ c, c < K → ∀ j, j < nCt c →
      IsReadingAt m φ ((pdoms c).length + (fdoms c j).length) (mk c j)) :
    ∀ (a : Nat → V), ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs) ∧
      (es c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = (es c j).map (interp V (consList (xs ++ fs) ρ)) ∧
      interp V (consList (xs ++ fs) (chainFrame K a ρ)) (mk c j)
        = interp V (consList (xs ++ fs) ρ) (mk c j) := by
  intro a c hc j hj xs fs hxl hsp
  have hbelow : FieldsBelow 0 (pdoms c ++ fdoms c j) := by
    refine fieldsBelow_append (fieldsBelow_of_readings (m := m) (φ := φ) fun k D hk => ?_)
      (fieldsBelow_of_readings (m := m) (φ := φ) fun k D hk => ?_)
    · simpa using hP c hc k D hk
    · simpa using hF c hc j hj k D hk
  have hlen : (xs ++ fs).length = (pdoms c).length + (fdoms c j).length := by
    have := hsp.length_eq
    simpa using this
  refine ⟨spineFit_congr_fieldsBelow (k := 0) hbelow (fun i hi => absurd hi (Nat.not_lt_zero _))
    hsp, List.map_congr_left fun e he => ?_, ?_⟩
  · exact interp_congr_below V e _ _ _ (hlen ▸ (hE c hc j hj e he).below)
      (consList_agree_below _)
  · exact interp_congr_below V _ _ _ _ (hlen ▸ (hM c hc j hj).below) (consList_agree_below _)

/-- **`IhDatumBelow`, from readings**: a generated `ih`'s telescope
domains and its index and major arguments are readings of scoped terms
at the rule's depth `D`. -/
theorem ihDatumBelow_of_readings {m : EnvModel V env} {φ : Name → Nat} {D : Nat} {q : IhDatum}
    (hT : ∀ (k : Nat) (p : Nat × AnnotTerm), q.2.1[k]? = some p → IsReadingAt m φ (D + k) p.2)
    (hA : ∀ e ∈ q.2.2.1 ++ [q.2.2.2], IsReadingAt m φ (D + q.2.1.length) e) :
    IhDatumBelow D q := by
  refine ⟨fieldsBelow_of_readings (m := m) (φ := φ) fun k T hk => ?_, fun e he => (hA e he).below⟩
  rw [List.getElem?_map] at hk
  cases hp : q.2.1[k]? with
  | none => rw [hp] at hk; exact nomatch hk
  | some p =>
    rw [hp] at hk
    obtain rfl := (Option.some.inj hk).symm
    exact hT k p hp

end Rows

end ConLeche.Model
