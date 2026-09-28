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
    ((List.range s).filter fun s' =>
      match slots.getD s' default with | .motive _ => true | _ => false).length = c ∧
    ∃ key, slots[s]? = some (.motive key) := by
  unfold ConLeche.ClassRead.motiveSlot at h
  simp only at h
  obtain ⟨hc, hs, hps⟩ := filter_range_getElem_count h
  refine ⟨?_, ?_⟩
  · rw [← hc]
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

end ConLeche.Model
