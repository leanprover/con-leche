module

public import ConLeche.SetModel.NestRecB
@[expose] public section

/-!
# The nested kit's induction at the RECURSOR's classes (lane NESTIND)

`NestKit` (`SetModel/NestRec.lean`) proves the induction principle of
its majors — the tagged elements `nenc b m t x` of every CLAUSE class
`b` (a member block, or a container at an instantiation), component
`m`.  The recursor model's graph kit (`graphKitG`,
`Model/Inductives/BlockRecGraph.lean`) is stated over the RECURSOR's
classes: recursor `c` eliminates component `mOf c` of clause class
`bOf c`, its majors are `tagged c t x`, its decodings are the rule
data's, and its predecessors are the rule's call targets (`predR`).

`NestKit.ind_recClasses` transports the one to the other.  The
property is read back along the class map: `P'` holds at the clause
major `nenc b m t x` when `P` holds at `tagged c t x` for EVERY
recursor `c` of that class — several recursors may share a class (a
stream may carry two recursors at one container instance); the kit's
predecessors must then contain every such recursor's call targets
(`hpredR`), which is how the instance defines them.

Nothing else is asked: the recursor classes' index sets, carriers and
injections ARE the clause classes' (`hIs`, `hCr`, `hinj`), a
constructor fitting at the true frame is a rule of the recursor
(`hnCt`), and the recursor's decoding fit is the clause's fit at the
true frame and carrier (`hfit`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

namespace NestKit

variable {F : Type u} (K : NestKit V F)

/-- **`NestKit.ind` at the recursor's classes.**  Recursor `c < Kr`
eliminates component `mOf c` of clause class `bOf c`; `Is`/`Cr`/`inj`
are the clause's there; a decoding of `tagged c t x` is a constructor
`j < nCt c` whose fields fit at the TRUE frame and carrier
(`fitR`); `predR e` are the rule `e`'s call targets, each of which
appears — as the clause major of its own recursor's class — among the
kit's predecessors of the corresponding clause decoding. -/
theorem ind_recClasses (Kr : Nat) (bOf mOf nCt : Nat → Nat)
    (Is Cr : Nat → V) (inj : Nat → Nat → List V → V)
    (fitR : Nat → V → Nat → List V → Prop) (predR : Nat × Nat × List V → V)
    (hb : ∀ c, c < Kr → bOf c < K.nC)
    (hm : ∀ c, c < Kr → mOf c < (K.cl (bOf c)).N)
    (hIs : ∀ c, c < Kr → Is c = (K.cl (bOf c)).Is (mOf c))
    (hCr : ∀ c, c < Kr → Cr c = K.KT (bOf c) (mOf c))
    (hinj : ∀ c, c < Kr → ∀ j fs, inj c j fs = (K.cl (bOf c)).inj (mOf c) j fs)
    (hnCt : ∀ c, c < Kr → ∀ t j fs,
      (K.cl (bOf c)).Fits (K.fr (bOf c)) (K.KT (bOf c)) t (mOf c) j fs → j < nCt c)
    (hfit : ∀ c, c < Kr → ∀ t j fs,
      (K.cl (bOf c)).Fits (K.fr (bOf c)) (K.KT (bOf c)) t (mOf c) j fs → fitR c t j fs)
    (hpredR : ∀ c, c < Kr → ∀ t j fs, ∀ v, v ∈ˢ predR (c, j, fs) →
      ∃ c' t' y, c' < Kr ∧ v = tagged c' t' y ∧
        nenc (bOf c') (mOf c') t' y ∈ˢ K.pred ⟨bOf c, mOf c, t, j, fs⟩) :
    ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet Kr Is Cr →
        (∃ e : Nat × Nat × List V, (e.1 < Kr ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ Is e.1 ∧
            fitR e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (inj e.1 e.2.1 e.2.2)) ∧
          ∀ v, v ∈ˢ predR e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet Kr Is Cr → P u := by
  intro P hP
  -- the property, read back along the class map
  let P' : V → Prop := fun v => ∀ c, c < Kr → ∀ t x, v = nenc (bOf c) (mOf c) t x →
    P (tagged c t x)
  have hP' : ∀ v, v ∈ˢ K.U → P' v := by
    refine K.ind P' fun v _ ⟨d, hd, hpd⟩ => ?_
    intro c hc t x hv
    obtain ⟨b0, m0, t0, j0, fs0⟩ := d
    obtain ⟨hdb, hdc, hdt, hdf, hdv⟩ := hd
    rw [hdv] at hv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj hv
    -- the clause decoding is recursor `c`'s at constructor `j0`
    refine hP _ ?_ ⟨(c, j0, fs0), ⟨hc, hnCt c hc _ _ _ hdf, t0, ?_, hfit c hc _ _ _ hdf,
      by rw [hinj c hc]⟩, fun w hw => ?_⟩
    · refine tagged_mem_unionSet hc ?_ ?_
      · rw [hIs c hc]; exact hdt
      · rw [hCr c hc]; exact (K.okT hdb).inj_mem hdc hdt hdf
    · rw [hIs c hc]; exact hdt
    · obtain ⟨c', t', y, hc', rfl, hmem⟩ := hpredR c hc t0 j0 fs0 w hw
      exact hpd _ hmem c' hc' t' y rfl
  intro u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  refine hP' _ ?_ c hc t x rfl
  refine K.nenc_mem_U (hb c hc) (hm c hc) ?_ ?_
  · rw [← hIs c hc]; exact ht
  · show x ∈ˢ app (K.KT (bOf c) (mOf c)) t
    rw [← hCr c hc]; exact hx

end NestKit

namespace NestKitB

variable {F : Type u} (K : NestKitB V F)
  (hpredT : ∀ u, u ∈ˢ K.U → ∀ d, K.Dec u d → K.pred d ⊆ˢ K.U)
include hpredT

/-- **`NestKitB.ind` at the recursor's classes** (Route B, `hpredT` given).  Recursor `c < Kr`
eliminates component `mOf c` of clause class `bOf c`; `Is`/`Cr`/`inj`
are the clause's there; a decoding of `tagged c t x` is a constructor
`j < nCt c` whose fields fit at the TRUE frame and carrier
(`fitR`); `predR e` are the rule `e`'s call targets, each of which
appears — as the clause major of its own recursor's class — among the
kit's predecessors of the corresponding clause decoding. -/
theorem ind_recClasses (Kr : Nat) (bOf mOf nCt : Nat → Nat)
    (Is Cr : Nat → V) (inj : Nat → Nat → List V → V)
    (fitR : Nat → V → Nat → List V → Prop) (predR : Nat × Nat × List V → V)
    (hb : ∀ c, c < Kr → bOf c < K.nC)
    (hm : ∀ c, c < Kr → mOf c < (K.cl (bOf c)).N)
    (hIs : ∀ c, c < Kr → Is c = (K.cl (bOf c)).Is (mOf c))
    (hCr : ∀ c, c < Kr → Cr c = K.KT (bOf c) (mOf c))
    (hinj : ∀ c, c < Kr → ∀ j fs, inj c j fs = (K.cl (bOf c)).inj (mOf c) j fs)
    (hnCt : ∀ c, c < Kr → ∀ t j fs,
      (K.cl (bOf c)).Fits (K.fr (bOf c)) (K.KT (bOf c)) t (mOf c) j fs → j < nCt c)
    (hfit : ∀ c, c < Kr → ∀ t j fs,
      (K.cl (bOf c)).Fits (K.fr (bOf c)) (K.KT (bOf c)) t (mOf c) j fs → fitR c t j fs)
    (hpredR : ∀ c, c < Kr → ∀ t j fs, ∀ v, v ∈ˢ predR (c, j, fs) →
      ∃ c' t' y, c' < Kr ∧ v = tagged c' t' y ∧
        nenc (bOf c') (mOf c') t' y ∈ˢ K.pred ⟨bOf c, mOf c, t, j, fs⟩) :
    ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet Kr Is Cr →
        (∃ e : Nat × Nat × List V, (e.1 < Kr ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ Is e.1 ∧
            fitR e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (inj e.1 e.2.1 e.2.2)) ∧
          ∀ v, v ∈ˢ predR e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet Kr Is Cr → P u := by
  intro P hP
  -- the property, read back along the class map
  let P' : V → Prop := fun v => ∀ c, c < Kr → ∀ t x, v = nenc (bOf c) (mOf c) t x →
    P (tagged c t x)
  have hP' : ∀ v, v ∈ˢ K.U → P' v := by
    refine K.ind hpredT P' fun v _ ⟨d, hd, hpd⟩ => ?_
    intro c hc t x hv
    obtain ⟨b0, m0, t0, j0, fs0⟩ := d
    obtain ⟨hdb, hdc, hdt, hdf, hdv⟩ := hd
    rw [hdv] at hv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj hv
    -- the clause decoding is recursor `c`'s at constructor `j0`
    refine hP _ ?_ ⟨(c, j0, fs0), ⟨hc, hnCt c hc _ _ _ hdf, t0, ?_, hfit c hc _ _ _ hdf,
      by rw [hinj c hc]⟩, fun w hw => ?_⟩
    · refine tagged_mem_unionSet hc ?_ ?_
      · rw [hIs c hc]; exact hdt
      · rw [hCr c hc]; exact (K.okT hdb).inj_mem hdc hdt hdf
    · rw [hIs c hc]; exact hdt
    · obtain ⟨c', t', y, hc', rfl, hmem⟩ := hpredR c hc t0 j0 fs0 w hw
      exact hpd _ hmem c' hc' t' y rfl
  intro u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  refine hP' _ ?_ c hc t x rfl
  refine K.nenc_mem_U (hb c hc) (hm c hc) ?_ ?_
  · rw [← hIs c hc]; exact ht
  · show x ∈ˢ app (K.KT (bOf c) (mOf c)) t
    rw [← hCr c hc]; exact hx

end NestKitB

end ConLeche.SetTheory
