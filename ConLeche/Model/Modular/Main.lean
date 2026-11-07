module

public import ConLeche.Model.Modular.Instance
public import ConLeche.Model.Modular.Valid

public section

/-!
# The modular theorem at con-leche's models

A development of modules (`ConLeche.Modular.Module`) is a development over the instance
(`toDev`): a module's context and own environment expose every name, its sources are every
earlier module's own environment exposing what the module reads alike from it (the names whose
copies agree, `ConLeche.Modular.readsAlike`), a context name is read from the module `src` says,
and the part below a name is the context's records before the name's.  A module passing the local
checks (`LocalOk`) is a valid one (`toDev_valid`): its context and every part are assembled from
the sources (`reading`, `reading_part`, `Valid.lean`), every source storing a name agrees by the
views' exposure, translated route by route (`Agree.same` is the read module, `Agree.via` one
record through two paths, `Agree.proof` two proofs: an inference over the part, or theorems), and
its records are accepted from the context.  The generic theorem (`Development.modular`) then gives
the compatible family of models (`modularModels`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Cached
open ConLeche.Term (Term)

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet}

/-- The view module `i` reads of module `b`: `b`'s own environment, exposing what `i` reads alike
from it. -/
@[expose] def viewOf (dev : Nat → Module) (i b : Nat) : XEnv :=
  ((dev b).own, fun n => ((dev i).context.find? n).isSome = true ∧ Agree dev i b n)

variable (V pins) in
/-- **A development of modules over the instance.** -/
@[expose] noncomputable def toDev (dev : Nat → Module) : Development (conlecheSemantics V pins) where
  ctx j := ((dev j).context, fun _ => True)
  decls j := (dev j).decls
  own j := ((dev j).own, fun _ => True)
  sources j := (List.range j).map fun b => (b, viewOf dev j b)
  src j := (dev j).src
  rank j := (dev j).rank
  part j n := ((dev j).part n, fun _ => True)

theorem findIdx_le {α : Type} {p : α → Bool} :
    ∀ {L : List α} {j : Nat} (h : j < L.length), p L[j] = true → L.findIdx p ≤ j
  | [], _, h, _ => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, _, hp => by simp [List.findIdx_cons, show p a = true from hp]
  | a :: L, j + 1, h, hp => by
    rw [List.findIdx_cons]
    split
    · omega
    · have := findIdx_le (L := L) (j := j) (by simp at h; omega) hp
      omega

/-- **A part of the context read from the sources is assembled from them**: a part `C` of the
context, read from the sources' own environments at parts of what is read alike. -/
theorem assembled_reads {dev : Nat → Module} {i : Nat} (hK : ImportOk .verified pins dev i)
    {C : Env} {R : Name → Env}
    (hC : ∀ n, (C.find? n).isSome = true → ((dev i).context.find? n).isSome = true)
    (hR : ∀ n d, ((dev i).context.find? n).isSome = true → ((R n).find? d).isSome = true →
      ((srcReads dev i n).find? d).isSome = true)
    (hread : CtxRead C (srcOwn dev i) R) :
    AssembledX (C, fun _ => True) (fun x : (toDev V pins dev).Src i => x.1.2) := by
  classical
  let srcOf : Name → Option ((toDev V pins dev).Src i) := fun n =>
    if h : ((dev i).context.find? n).isSome = true then
      some ⟨((dev i).src n, viewOf dev i ((dev i).src n)),
        List.mem_map.mpr ⟨(dev i).src n, List.mem_range.mpr (hK.src_lt n h), rfl⟩⟩
    else none
  have hsE : srcEnv (fun x : (toDev V pins dev).Src i => x.1.2) srcOf = srcOwn dev i := by
    funext n
    by_cases h : ((dev i).context.find? n).isSome = true
    · simp [srcEnv, srcOf, srcOwn, h, viewOf]
    · simp [srcEnv, srcOf, srcOwn, h]
  refine AssembledX.reads srcOf R (fun _ => trivial)
    (fun n h => by
      simp only [srcOf, dite_eq_left (hC n h)]; rfl)
    (fun n x hx d hd => ?_) (hsE ▸ hread)
  -- what a source exposes is what is read alike from it
  by_cases h : ((dev i).context.find? n).isSome = true
  · simp only [srcOf, dite_eq_left h] at hx
    obtain rfl := Option.some.inj hx
    show ((dev i).context.find? d).isSome = true ∧ Agree dev i ((dev i).src n) d
    have hd' := hR n d h hd
    simp only [srcReads, h, ↓reduceIte] at hd'
    rw [readsAlike_find?] at hd'
    split at hd'
    · next hc => exact hc
    · exact nomatch hd'
  · simp [srcOf, h] at hx

/-- **A module passing the local checks is valid.** -/
theorem toDev_valid {dev : Nat → Module} {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) :
    (toDev V pins dev).Valid i := by
  classical
  have hK := (hok i (Nat.le_refl i)).importOk
  have hnd : NodupNames (streamEnv (dev i).ctx) := hK.nodup
  obtain ⟨q, hq⟩ := hK.accepted
  -- the sources
  have hsrcs : ∀ x ∈ (toDev V pins dev).sources i, ∃ b < i, x = (b, viewOf dev i b) := fun x hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact ⟨b, List.mem_range.mp hb, rfl⟩
  have hmem : ∀ {j b}, b < j → (b, viewOf dev j b) ∈ (toDev V pins dev).sources j := fun h =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr h, rfl⟩
  -- an agreeing copy is stored
  have hstored : ∀ {j b x}, Agree dev j b x → j ≤ i → b ≤ i →
      ((dev j).context.find? x).isSome = true → ((dev b).own.find? x).isSome = true := by
    intro j b x h hj hb hx
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨cb, hcb, -⟩ := agree_alike hok h hj hb hc
    rw [hcb]; rfl
  refine ⟨fun x hx => ?_, ?_, fun n hn => ?_, .inl ⟨rfl, fun _ => trivial, _, q, hq⟩⟩
  · -- a source is an earlier module's own environment, exposing fewer names
    obtain ⟨b, hb, rfl⟩ := hsrcs x hx
    exact ⟨hb, AssembledX.self PUnit.unit rfl fun _ _ _ => trivial⟩
  · -- the context, assembled from the sources
    exact assembled_reads (C := (dev i).context) (R := srcReads dev i) hK (fun _ h => h)
      (fun _ _ _ h => h) (reading hok)
  · have hnC : ((dev i).context.find? n).isSome = true := hn.1
    have hsn : (dev i).src n < i := hK.src_lt n hnC
    obtain ⟨ciC, hciC⟩ := Option.isSome_iff_exists.mp hnC
    -- the side of a proof, translated
    have side : ∀ b, b < i → ∀ {ci' : ConstantInfo}, (dev b).own.find? n = some ci' →
        ci'.toConstantVal = ciC.toConstantVal → ci'.isStmtKind = true → pinnedLeafName n = false →
        (∀ c ∈ ciC.toConstantVal.type.readNames, Agree dev i b c) →
        ProofSide dev i b n ciC.toConstantVal.type →
        (toDev V pins dev).ProofSide i n (b, viewOf dev i b) := by
      intro b hb ci' hB hcv hk' hpin hnames hps
      rcases hps with ⟨hres, hprop⟩ | hthm
      · refine .inl ⟨ci', hB, hk', hpin, by rw [hcv]; exact hprop, fun c hc => ?_⟩
        have hc' : c ∈ ciC.toConstantVal.type.readNames := by rw [hcv] at hc; exact hc
        have hcP : (((dev i).part n).find? c).isSome = true :=
          Expr.readNames_of_constsResolve hres c hc'
        have hcC : ((dev i).context.find? c).isSome = true := take_isSome hnd hcP
        have hag := hnames c hc'
        obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hcP
        obtain ⟨cb, hcb, hal, htab⟩ := agree_alike hok hag (Nat.le_refl i) (Nat.le_of_lt hb)
          (take_find? hnd hcc)
        refine ⟨⟨hcP, trivial⟩, ⟨hcC, hag⟩, ⟨cc, cb, hcc, hcb, hal⟩, ?_⟩
        show (streamEnv ((dev i).ctx.take ((dev i).rank n))).findTable? c = _
        rw [take_findTable? hnd hcP]
        exact htab
      · refine .inr ?_
        rcases hthm with ⟨cv, h⟩ | ⟨hctx, cv, h⟩
        · exact .inl ⟨⟨cv, h⟩, hpin⟩
        · exact .inr ⟨⟨hctx, trivial⟩, ⟨cv, h⟩, hpin⟩
    refine ⟨⟨_, hmem hsn, rfl, hstored (.same rfl) (Nat.le_refl i) (Nat.le_of_lt hsn) hnC,
        hnC, .same rfl⟩, ?_, fun c hc => ?_, fun x hx hs => ?_⟩
    · -- the part below the name, assembled
      exact assembled_reads (C := streamEnv ((dev i).ctx.take ((dev i).rank n)))
        (R := srcReadsTake dev i ((dev i).rank n)) hK (fun _ h => take_isSome hnd h)
        (fun _ _ _ h => (srcReadsTake_isSome.mp h).2) (reading_part hok _)
    · -- the part holds context names of smaller rank
      refine ⟨⟨take_isSome hnd hc.1, trivial⟩, ?_⟩
      obtain ⟨e, he, cc, hcc, hnm, -⟩ := streamEnv_isSome hc.1
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      have hjr : j < (dev i).rank n := by simp at hj; omega
      show (dev i).ctx.findIdx _ < _
      refine Nat.lt_of_le_of_lt (findIdx_le (by simp at hj; omega) ?_) hjr
      rw [List.getElem_take] at hcc
      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨cc, hcc, hnm⟩)
    · -- every source storing the name agrees
      obtain ⟨b, hb, rfl⟩ := hsrcs x hx
      obtain ⟨-, -, hag⟩ := hs
      cases hag with
      | same h => exact .inl h
      | @via _ _ t _ hctx hlt hbt hit =>
        refine .inr (.inl ⟨⟨hctx, trivial⟩, (t, viewOf dev b t), hmem hlt,
          ⟨hstored hbt (Nat.le_of_lt hb) (by omega) hctx, hctx, hbt⟩, (t, viewOf dev i t),
          hmem (by omega), rfl, ⟨hstored hit (Nat.le_refl i) (by omega) hnC, hnC, hit⟩, hlt⟩)
      | @proof _ _ _ ci ci' hC hB hcv hk hk' hpin hnames hps hps' =>
        rw [hciC] at hC
        obtain rfl := Option.some.inj hC
        refine .inr (.inr ⟨side b hb hB hcv hk' hpin hnames hps, fun y hy hy1 hys => ?_⟩)
        obtain ⟨b', hb', rfl⟩ := hsrcs y hy
        obtain rfl : b' = (dev i).src n := hy1
        -- the read module's copy: its names agree by the record's reads
        obtain ⟨ciO, hO, hal, -⟩ := agree_alike hok (.same rfl) (Nat.le_refl i)
          (Nat.le_of_lt hsn) hciC
        obtain ⟨e, he, hce, hnm⟩ := streamEnv_find?_some hciC
        have hrd := (hK.reads e he n (List.mem_map.mpr ⟨ciC, hce, hnm⟩)).1 ciC hce
        refine side _ hsn hO hal.cv.symm ?_ hpin (fun c hc => ?_) hps'
        · rcases hal with rfl | ⟨-, -, h⟩
          · exact hk
          · exact h
        · have hcR := Expr.readNames_of_constsResolve hrd.1 c hc
          rw [readsAlike_find?] at hcR
          split at hcR
          · next h => exact h.2
          · exact nomatch hcR

/-- A context name is stored in the module's own environment. -/
theorem own_stored_of_context {dev : Nat → Module} {i j : Nat}
    (hok : ∀ j ≤ i, LocalOk .verified pins dev j) (hj : j ≤ i) {n : Name}
    (hn : ((dev j).context.find? n).isSome = true) : ((dev j).own.find? n).isSome = true := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
  rw [own_find?_of_context (ImportOk.chain (hok j hj).importOk).1 hc]; rfl

/-- A context name is stored by the module it is read from. -/
theorem src_stored {dev : Nat → Module} {i j : Nat}
    (hok : ∀ j ≤ i, LocalOk .verified pins dev j) (hj : j ≤ i) {n : Name}
    (hn : ((dev j).context.find? n).isSome = true) :
    ((dev ((dev j).src n)).own.find? n).isSome = true := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
  have hlt := (hok j hj).importOk.src_lt n hn
  obtain ⟨cb, hcb, -⟩ := agree_alike hok (Agree.same rfl) hj (by omega) hc
  rw [hcb]; rfl

/-- **The compatible family of models**, over the instance. -/
theorem modularModels {dev : Nat → Module} {i : Nat}
    (hok : ∀ j ≤ i, LocalOk .verified pins dev j) :
    ∃ m : (j : Nat) → j < i + 1 → MMod V ((dev j).own, fun _ => True),
      (toDev V pins dev).Compatible (i + 1) m :=
  (toDev V pins dev).modular (i + 1) fun j hj =>
    toDev_valid fun k hk => hok k (by omega)

end ConLeche.Model.Modular
