module

public import ConLeche.Verify.Inductives.NestedRestoreTbl
public import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Subst
import ConLeche.Verify.InferLeaves

public section

/-!
# The restore table's CONSTRUCTOR pins, inverted and opened (task #315, M7-2)

`restoreTbl`'s `ctorPins` is one entry per constructor of every minted
copy: the constructor's auxiliary name, the copy's pin abstracted at
the block's parameters, and the container's own constructor name
(`replacePrefix aux container`).  Two facts about it, for the walk's
constructor-pin leaf agreement (`RestoreAgree.ctor`):

* `restoreTbl_ctorPins_find?` — a `find?` hit comes from a pin `q`, the
  copy `st.types[p.k + q]` and one of its constructors, with the pin
  and the restored name exactly as the table writes them (the
  inversion the agreement's universally quantified clause consumes);
* `restoreTbl_ctorPins_mem` — the converse: every copy constructor IS
  an entry;
* `instSeq_ctorPin_open` — the restored head at the LIFTED pin's
  arguments, opened at the parameter and depth openers, is the pin's
  own opening with the head swapped: the depth openers never reach the
  abstracted pin, which lives in the parameter context alone
  (`instSeq_liftLooseBVars_prefix`).
-/

namespace ConLeche

/-! ## The constructor pins, inverted -/

/-- **A `ctorPins` HIT IS A COPY'S CONSTRUCTOR** (task #315): the
table lists, for every pin `j` whose copy is `st.types[p.k + j]`, one
entry per constructor of that copy — the constructor's own name, the
copy's pin abstracted at the block's parameters, and the container's
constructor name.  A `find?` hit is therefore exactly such a triple. -/
theorem restoreTbl_ctorPins_find? {p : NestedParts} {st : ElimState} {n : Name} {pin : Expr}
    {newName : Name}
    (h : (restoreTbl p st).ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName)) :
    ∃ (j : Nat) (qn : NestedPin) (t : AuxType) (jc : Nat) (c : Name × Expr × Nat),
      st.pins[j]? = some qn ∧ st.types[p.k + j]? = some t ∧ t.ctors[jc]? = some c ∧ c.1 = n ∧
      pin = Expr.abstractRange qn.pin 0 p.nP 0 ∧
      newName = Name.replacePrefix qn.aux qn.container n := by
  have hmem := List.mem_of_find?_eq_some h
  simp only [restoreTbl] at hmem
  obtain ⟨l, hl, hin⟩ := List.mem_flatten.mp hmem
  obtain ⟨tj, htj, hleq⟩ := List.mem_map.mp hl
  obtain ⟨t, j⟩ := tj
  subst hleq
  simp only at hin
  split at hin
  · rename_i qn hqn
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hin
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hn, hp, hnn⟩ := heq
    obtain ⟨jc, hjc⟩ := List.getElem?_of_mem hc
    have ht : st.types[p.k + j]? = some t := by
      have h1 : (st.types.drop p.k)[j]? = some t := by
        simpa using List.mk_mem_zipIdx_iff_getElem?.mp htj
      rwa [List.getElem?_drop] at h1
    exact ⟨j, qn, t, jc, c, hqn, ht, hjc, hn, hp.symm, by rw [← hnn, hn]⟩
  · simp only [List.not_mem_nil] at hin

/-- **EVERY COPY CONSTRUCTOR IS A `ctorPins` KEY** (task #315): the
converse of the inversion — the table's entry at pin `j`'s copy's
`jc`-th constructor. -/
theorem restoreTbl_ctorPins_mem {p : NestedParts} {st : ElimState} {j : Nat} {qn : NestedPin}
    {t : AuxType} {jc : Nat} {c : Name × Expr × Nat} (hq : st.pins[j]? = some qn)
    (ht : st.types[p.k + j]? = some t) (hc : t.ctors[jc]? = some c) :
    (c.1, Expr.abstractRange qn.pin 0 p.nP 0, Name.replacePrefix qn.aux qn.container c.1)
      ∈ (restoreTbl p st).ctorPins := by
  simp only [restoreTbl]
  refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨(t, j), ?_, rfl⟩, ?_⟩
  · refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
    rw [List.getElem?_drop]
    simpa using ht
  · simp only [hq]
    exact List.mem_map.mpr ⟨c, List.mem_of_getElem? hc, rfl⟩

/-! ## The opened constructor pin -/

/-- Lifting distributes over an application spine. -/
theorem liftLooseBVars_mkAppN (d c : Nat) : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).liftLooseBVars d c
      = Expr.mkAppN (f.liftLooseBVars d c) (args.map (·.liftLooseBVars d c))
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      liftLooseBVars_mkAppN d c as (.app f a)]
    rfl

/-- **A BULK ABSTRACTION IS BOUNDED AT THE RANGE'S WIDTH**: closing `k`
free-variable levels into bound variables at the cursor `c` raises the
loose-bvar bound by exactly `k`. -/
theorem looseBVarsBounded_abstractRange : ∀ (e : Expr) (d k c : Nat),
    e.looseBVarsBounded c = true → (e.abstractRange d k c).looseBVarsBounded (c + k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    omega
  | fvar idx ty =>
    intro d k c _
    simp only [Expr.abstractRange]
    split
    · rename_i hr
      simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
      omega
    · rfl
  | sort _ => intro d k c _; rfl
  | const _ _ => intro d k c _; rfl
  | lit _ => intro d k c _; rfl
  | app f a ihf iha =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf d k c hb.1, iha d k c hb.2⟩
  | lam ty body m ihty ihb =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty d k c hb.1, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 from by omega] at this
  | forallE ty body m ihty ihb =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty d k c hb.1, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 from by omega] at this
  | letE ty val body ihty ihv ihb =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨⟨ihty d k c hb.1.1, ihv d k c hb.1.2⟩, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 from by omega] at this
  | proj _ _ e ih =>
    intro d k c hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded] at hb ⊢
    exact ih d k c hb

/-- **THE OPENED CONSTRUCTOR PIN** (task #315, M7-2): the restore
writes a copy's constructor as the container's constructor applied to
the LIFTED pin's arguments (`restoreNode`); opened at the block's
parameter openers `fvsP` and `d` depth openers `fvs` below them, that
is the pin's own abstraction with the head constant swapped, opened at
`fvsP` alone — the abstracted pin lives in the parameter context, so
the depth openers never reach it (`instSeq_liftLooseBVars_prefix`). -/
theorem instSeq_ctorPin_open {nP d : Nat} {fvsP fvs : List Expr} {J N : Name}
    {lvls ilvls : List Level} {DsE : List Expr}
    (hlenP : fvsP.length = nP) (hlenF : fvs.length = d)
    (hP : ∀ a ∈ fvsP, a.looseBVarsBounded 0 = true)
    (hb : (Expr.mkAppN (.const J lvls) DsE).looseBVarsBounded 0 = true) :
    Expr.instSeq (fvsP ++ fvs) (nP + d - 1)
        (Expr.mkAppN (.const N ilvls)
          ((Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0).liftLooseBVars d 0).getAppArgs)
      = Expr.instSeq fvsP (nP - 1) (Expr.abstractRange (Expr.mkAppN (.const N ilvls) DsE) 0 nP 0) := by
  have hAJ : Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0
      = Expr.mkAppN (.const J lvls) (DsE.map (·.abstractRange 0 nP 0)) := by
    rw [abstractRange_mkAppN]; rfl
  have hAN : Expr.abstractRange (Expr.mkAppN (.const N ilvls) DsE) 0 nP 0
      = Expr.mkAppN (.const N ilvls) (DsE.map (·.abstractRange 0 nP 0)) := by
    rw [abstractRange_mkAppN]; rfl
  have hargs :
      ((Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0).liftLooseBVars d 0).getAppArgs
        = (DsE.map (·.abstractRange 0 nP 0)).map (·.liftLooseBVars d 0) := by
    rw [hAJ, liftLooseBVars_mkAppN, Expr.getAppArgs_mkAppN]
    rfl
  have hq : (Expr.mkAppN (.const N ilvls) (DsE.map (·.abstractRange 0 nP 0))).looseBVarsBounded
      fvsP.length = true := by
    rw [hlenP]
    refine looseBVarsBounded_mkAppN rfl (fun x hx => ?_)
    have hbJ : (Expr.mkAppN (.const J lvls) (DsE.map (·.abstractRange 0 nP 0))).looseBVarsBounded
        (0 + nP) = true := by
      rw [← hAJ]
      exact looseBVarsBounded_abstractRange _ 0 nP 0 hb
    rw [Nat.zero_add] at hbJ
    refine looseBVarsBounded_getAppArgs hbJ x ?_
    rw [Expr.getAppArgs_mkAppN]
    exact hx
  have hlift : Expr.mkAppN (.const N ilvls) ((DsE.map (·.abstractRange 0 nP 0)).map
        (·.liftLooseBVars d 0))
      = (Expr.mkAppN (.const N ilvls) (DsE.map (·.abstractRange 0 nP 0))).liftLooseBVars d 0 := by
    rw [liftLooseBVars_mkAppN]; rfl
  have hkey := Expr.instSeq_liftLooseBVars_prefix fvsP fvs hP hq
  rw [hlenP, hlenF] at hkey
  rw [hargs, hAN, hlift]
  exact hkey

end ConLeche
