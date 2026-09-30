module

public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Mono
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Denote.Shift
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Rules.InferBridge
public import ConLeche.Model.Inductives.ClassRecKit
import ConLeche.Verify.Leaves

public section

/-!
# The generated recursor TYPE, read (G1-syn, the type side)

The generated recursor stage generates, per class `c`, the recursor type

    classGenRecTy g c = Π (prefix) (ı⃗ : index domains) (t : I D⃗ ı⃗), motive_c ı⃗ t

(`Kernel/Inductives/GenRec.lean`), checks it as a constant — stored as
generated (every binder datum written, `ClassGen.bm`), inferred at the
empty context (`classRecTyOk`, `classConstOk`).  What the graph route's producer at the
generated family (`graphRecPre_gen`, `ClassRecKit.lean`) asks of the
type's binder data, read off the generator's syntax and the two runs:

* **every binder numeral is the elimination level's zero bit**
  (`classGenRecTy_bits`) — the ∀ clause validated each binder's datum
  against its codomain's sort (the bits law, `stripPisAV_denoteMeta_pw`),
  and the conclusion `motive_c ı⃗ t` is sorted at `Sort elim`: its head
  is the motive's variable, whose domain is the motive type
  `∀ ı⃗ t, Sort elim`.  So `OneElimLevel` holds at
  `Level.eval φ elim` (`hbits`);
* **the prefix is SHARED** (`classGenRecTy_prefix_eq`): the first
  `nP + #slots` binders of two classes' types read to the same binder
  data — both types are telescopes over the one prefix (`SameDoms`), and
  every numeral is the one bit.
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
    {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat} {g : ClassGen}
    (hg : ClassGenScoped g) {c s : Nat}
    (hm : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s)
    {gty : Expr} {ea : AnnotTerm}
    (hgty : classGenRecTy g c = some gty)
    (hread : denoteMeta acval env φ 0 gty = some ea) {pps : List (Nat × Nat × AnnotTerm)}
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
  generalize hnds : g.pre ++ ifs.map g.binder ++ [(maj, g.bm)] = nds at hread hcl
  generalize hbody : Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])
    = body at hread hbb
  have hn : nds.length = g.pre.length + (g.cls.getD c default).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_append, List.length_map, List.length_singleton, hifl]
  obtain ⟨fvs, o, hop, hrest, -⟩ := open_of_erasedEq_closeTelescope nds 0 body
    (closeTelescope nds 0 body) hcl hbb (Expr.ErasedEq.rfl _)
  rw [hn] at hop
  obtain ⟨pps', b', hst', hbo, -, -⟩ := denoteMeta_openPis _ hop hread
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hst'))
  have hoE : Expr.ErasedEq o body := hrest
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

end Rows

end ConLeche.Model
