module

public import ConLeche.SetModel.NestRec
@[expose] public section

/-!
# The nested kit's induction at the RECURSOR's classes

The nested kit `NestKit` (`SetModel/NestRec.lean`: `trans` at every
admissible frame) proves the induction principle of its majors,
the tagged elements `nenc b m t x` of every CLAUSE class `b` (a member
block, or a container at an instantiation — a positivity NODE),
component `m`.  `NestNodeInd` is that principle, DECODED (a major's
predecessors are the kit's `pred` at a decoding at the true frame and
carrier), and the one interface the recursor side reads; `NestKit.toNodeInd`
is its instance.

The recursor model's graph kit (`graphKitG`,
`Model/Inductives/BlockRecGraph.lean`) is stated over the RECURSOR's
classes: recursor `c`'s majors are `tagged c t x`, its decodings are the
rule data's, and its predecessors are the rule's call targets (`predR`).
`NestNodeInd.ind_recNodesOn` transports the one to the other, with
SEVERAL nodes per class (`Rel c b`: node `b` visits recursor `c`'s class
at component `mOf c b`; one instantiation may be visited at several
nodes), on a set `S` of classes that have nodes.
The property is read back along every node of a class: `P'` holds at the
node major `nenc b (mOf c b) t x` when `P` holds at `tagged c t x`
for every related recursor `c` (discharged via `HasSep` on
`unionSet Kr Is Cr` and `DefRel.finForall_lt` over `c < Kr`, `b < K.nC`);
the kit's predecessors must contain every related recursor's call
targets (`hpredR`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- **The majors' induction principle, decoded** — what `NestKit`
proves, over clause classes (nodes) `b < nC` with their
true frames `fr b : Fin (frLen b) → V`: a major's decodings are the spines
fitting at the TRUE frame and carrier, and its predecessors are `pred` at
the decoding.  `ind` is guarded by `HasSep (nestU nC cl fr) P`. -/
structure NestNodeInd (V : Type u) [SetTheory V] where
  nC : Nat
  frLen : Nat → Nat
  cl : (b : Nat) → SClause V (frLen b)
  fr : (b : Nat) → Fin (frLen b) → V
  pred : NDec V → V
  /-- a decoding's injection is a true major -/
  inj_mem : ∀ b c t j fs, b < nC → c < (cl b).N → t ∈ˢ (cl b).Is c →
    (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs →
    (cl b).inj c j fs ∈ˢ app ((cl b).carrier (fr b) c) t
  /-- the induction over the true majors, by their decodings (guarded by `HasSep`) -/
  ind : ∀ P : V → Prop, HasSep (nestU nC cl fr) P →
    (∀ b c t j fs, b < nC → c < (cl b).N → t ∈ˢ (cl b).Is c →
      (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs →
      (∀ v, v ∈ˢ pred ⟨b, c, t, j, fs⟩ → P v) → P (nenc b c t ((cl b).inj c j fs))) →
    ∀ b c t x, b < nC → c < (cl b).N → t ∈ˢ (cl b).Is c →
      x ∈ˢ app ((cl b).carrier (fr b) c) t → P (nenc b c t x)

/-- `NestKit`'s induction, decoded. -/
noncomputable def NestKit.toNodeInd (K : NestKit V) : NestNodeInd V where
  nC := K.nC
  frLen := K.frLen
  cl := K.cl
  fr := K.fr
  pred := K.pred
  inj_mem := fun _ c t _ _ hb hc ht hf => (K.okT hb ⟨c, hc, t, ht⟩).inj_mem hc ht hf
  ind := fun P hSep hstep b c t x hb hc ht hx => by
    refine K.ind P hSep (fun u _ ⟨d, hd, hpd⟩ => ?_) _ (K.nenc_mem_U hb hc ht hx)
    obtain ⟨hdb, hdc, hdt, hdf, rfl⟩ := hd
    exact hstep _ _ _ _ _ hdb hdc hdt hdf hpd

namespace NestNodeInd

variable (K : NestNodeInd V)

/-- The true class `b`. -/
noncomputable def KT (b : Nat) : Nat → V := (K.cl b).carrier (K.fr b)

/-- **The induction at the recursor's classes, several NODES per class,
on a set `S` of classes that have nodes** (guarded by `HasSep (unionSet Kr Is Cr) P`).
`Rel c b`: node `b` is a visit of recursor `c`'s class, at component
`mOf c b` of the node's clause; every class of `S` has a node (`hex`).
The data agree at EVERY related pair: `Is`/`Cr`/`inj` are the node
clause's, a constructor fitting at the node's true frame is a rule of the
recursor (`hnCt`) whose decoding fit is the recursor's (`hfit`), and
each call target of the rule appears, as the major of SOME node of its
callee's class, among the kit's predecessors at that node (`hpredR` —
which node depends on the caller's node: the caller itself, an enclosing
node, or a kid; so the related classes are closed under calls).  At
`Rel c b ↔ b = bOf c` it is the one-node-per-class transport. -/
theorem ind_recNodesOn (Kr : Nat) (S : Nat → Prop) (Rel : Nat → Nat → Prop)
    (mOf : Nat → Nat → Nat)
    (nCt : Nat → Nat) (Is Cr : Nat → V) (inj : Nat → Nat → List V → V)
    (fitR : Nat → V → Nat → List V → Prop) (predR : Nat × Nat × List V → V)
    (hex : ∀ c, c < Kr → S c → ∃ b, Rel c b)
    (hb : ∀ c b, c < Kr → Rel c b → b < K.nC)
    (hm : ∀ c b, c < Kr → Rel c b → mOf c b < (K.cl b).N)
    (hIs : ∀ c b, c < Kr → Rel c b → Is c = (K.cl b).Is (mOf c b))
    (hCr : ∀ c b, c < Kr → Rel c b → Cr c = K.KT b (mOf c b))
    (hinj : ∀ c b, c < Kr → Rel c b → ∀ j fs, inj c j fs = (K.cl b).inj (mOf c b) j fs)
    (hnCt : ∀ c b, c < Kr → Rel c b → ∀ t j fs,
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → j < nCt c)
    (hfit : ∀ c b, c < Kr → Rel c b → ∀ t j fs,
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → fitR c t j fs)
    (hpredR : ∀ c b, c < Kr → Rel c b → ∀ t j fs, t ∈ˢ (K.cl b).Is (mOf c b) →
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → ∀ v, v ∈ˢ predR (c, j, fs) →
      ∃ c' t' y, c' < Kr ∧ v = tagged c' t' y ∧ ∃ b', Rel c' b' ∧
        nenc b' (mOf c' b') t' y ∈ˢ K.pred ⟨b, mOf c b, t, j, fs⟩) :
    ∀ P : V → Prop, HasSep (unionSet Kr Is Cr) P →
      (∀ u, u ∈ˢ unionSet Kr Is Cr →
        (∃ e : Nat × Nat × List V, (e.1 < Kr ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ Is e.1 ∧
            fitR e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (inj e.1 e.2.1 e.2.2)) ∧
          ∀ v, v ∈ˢ predR e → P v) → P u) →
      ∀ c, c < Kr → S c → ∀ t, t ∈ˢ Is c → ∀ x, x ∈ˢ app (Cr c) t → P (tagged c t x) := by
  intro P hSepP hP
  let Pset := sep (unionSet Kr Is Cr) P hSepP
  -- the property, read back along EVERY node of a class (purely first-order via Pset)
  let P' : V → Prop := fun v =>
    ∀ c, c < Kr → ∀ b, b < K.nC → Rel c b → ∀ t x,
      v = nenc b (mOf c b) t x → tagged c t x ∈ˢ Pset
  have hP'def : DefPred P' := by
    refine DefRel.finForall_lt fun c _ => DefRel.finForall_lt fun b _ => ?_
    refine (DefRel.constProp (Rel c b)).imp ?_
    refine DefRel.forall_curry (DefRel.forall_curry ?_)
    exact DefRel.imp
      (DefRel.eq_apply (DefFun.proj 2) (DefFun.nenc_apply b (mOf c b) (DefFun.proj 1) (DefFun.proj 0)))
      (DefRel.mem_apply (DefFun.tagged_apply c (DefFun.proj 1) (DefFun.proj 0)) (DefFun.const Pset))
  have hP' := K.ind P' (hasSep_of_defPred hP'def) fun b0 m0 t0 j0 fs0 hdb hdc hdt hdf hpd => by
    intro c hc b hb0 hR t x hv
    obtain ⟨hbb, hmm, rfl, rfl⟩ := nenc_inj hv
    subst hbb
    subst hmm
    have huU : tagged c t0 ((K.cl b0).inj (mOf c b0) j0 fs0) ∈ˢ unionSet Kr Is Cr := by
      refine tagged_mem_unionSet hc ?_ ?_
      · rw [hIs c b0 hc hR]; exact hdt
      · rw [hCr c b0 hc hR]
        exact K.inj_mem _ _ _ _ _ hdb hdc hdt hdf
    refine mem_sep.mpr ⟨huU, hP _ huU ⟨(c, j0, fs0), ⟨hc, hnCt c b0 hc hR _ _ _ hdf, t0, ?_,
      hfit c b0 hc hR _ _ _ hdf, by rw [hinj c b0 hc hR]⟩, fun w hw => ?_⟩⟩
    · rw [hIs c b0 hc hR]; exact hdt
    · obtain ⟨c', t', y, hc', rfl, b', hR', hmem⟩ := hpredR c b0 hc hR t0 j0 fs0 hdt hdf w hw
      exact (mem_sep.mp (hpd _ hmem c' hc' b' (hb c' b' hc' hR') hR' t' y rfl)).2
  intro c hc hS t ht x hx
  obtain ⟨b, hR⟩ := hex c hc hS
  have hp := hP' b (mOf c b) t x (hb c b hc hR) (hm c b hc hR)
    (by rw [← hIs c b hc hR]; exact ht)
    (by show x ∈ˢ app (K.KT b (mOf c b)) t; rw [← hCr c b hc hR]; exact hx)
    c hc b (hb c b hc hR) hR t x rfl
  exact (mem_sep.mp hp).2

/-- Convenience form of `ind_recNodesOn` when `P` is `DefPredOn (unionSet Kr Is Cr) P`. -/
theorem ind_recNodesOn_of_def (Kr : Nat) (S : Nat → Prop) (Rel : Nat → Nat → Prop)
    (mOf : Nat → Nat → Nat)
    (nCt : Nat → Nat) (Is Cr : Nat → V) (inj : Nat → Nat → List V → V)
    (fitR : Nat → V → Nat → List V → Prop) (predR : Nat × Nat × List V → V)
    (hex : ∀ c, c < Kr → S c → ∃ b, Rel c b)
    (hb : ∀ c b, c < Kr → Rel c b → b < K.nC)
    (hm : ∀ c b, c < Kr → Rel c b → mOf c b < (K.cl b).N)
    (hIs : ∀ c b, c < Kr → Rel c b → Is c = (K.cl b).Is (mOf c b))
    (hCr : ∀ c b, c < Kr → Rel c b → Cr c = K.KT b (mOf c b))
    (hinj : ∀ c b, c < Kr → Rel c b → ∀ j fs, inj c j fs = (K.cl b).inj (mOf c b) j fs)
    (hnCt : ∀ c b, c < Kr → Rel c b → ∀ t j fs,
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → j < nCt c)
    (hfit : ∀ c b, c < Kr → Rel c b → ∀ t j fs,
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → fitR c t j fs)
    (hpredR : ∀ c b, c < Kr → Rel c b → ∀ t j fs, t ∈ˢ (K.cl b).Is (mOf c b) →
      (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → ∀ v, v ∈ˢ predR (c, j, fs) →
      ∃ c' t' y, c' < Kr ∧ v = tagged c' t' y ∧ ∃ b', Rel c' b' ∧
        nenc b' (mOf c' b') t' y ∈ˢ K.pred ⟨b, mOf c b, t, j, fs⟩) :
    ∀ P : V → Prop, DefPredOn (unionSet Kr Is Cr) P →
      (∀ u, u ∈ˢ unionSet Kr Is Cr →
        (∃ e : Nat × Nat × List V, (e.1 < Kr ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ Is e.1 ∧
            fitR e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (inj e.1 e.2.1 e.2.2)) ∧
          ∀ v, v ∈ˢ predR e → P v) → P u) →
      ∀ c, c < Kr → S c → ∀ t, t ∈ˢ Is c → ∀ x, x ∈ˢ app (Cr c) t → P (tagged c t x) :=
  fun P hPdef => K.ind_recNodesOn Kr S Rel mOf nCt Is Cr inj fitR predR
    hex hb hm hIs hCr hinj hnCt hfit hpredR P (hasSep_of_def hPdef)

end NestNodeInd

end ConLeche.SetTheory
