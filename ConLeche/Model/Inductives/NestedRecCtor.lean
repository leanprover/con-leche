module

public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecWalk
public import ConLeche.Verify.Inductives.NestedRecCtorPin
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.NestedTransfer
public section

/-!
# The copy constructor's agreement at the tail (task #315, M7-2, PLAN-M7 §1c)

`RestoreAgree.ctor` (`Model/Inductives/NestedRecWalk.lean`) is the
walk's leaf agreement at a `ctorPins` key: the restore rewrites a
copy's constructor `aux_q.c` applied to the block's parameters into the
CONTAINER's constructor `J.c` applied to the pin's components, and the
two readings must interpret alike wherever the restored one is graded.

This file states the two definitions the walk's shape and its leaf
agreements are phrased with at the tail's data (`nestedArity`, the key
arities; `NestedCtorPinNames`, the restore's name round-trip — K.35,
the kernel record's model face) and proves the agreement itself
(`NestedTailIn.ctorArm`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  AuxType ContainerInfo ContainerMember ContainerCtor fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## B0 — the two definitions the walk is stated with -/

/-- The key arities the walk's shape `AuxAppsOk` and its leaf
agreements use: a pin key's copy index count, a constructor pin key's
field count. -/
@[expose] def nestedArity (p : NestedParts) (st : ElimState) (pinsS : List PinSyn) :
    Name → Option Nat :=
  fun n =>
    match (st.pins.zipIdx.find? fun (q, _) => q.aux == n) with
    | some (_, j) => some (pinsS.getD j default).nIdx
    | none =>
      match ((st.types.drop p.k).flatMap (·.ctors)).find? fun c => c.1 == n with
      | some c => some c.2.2
      | none => none

/-- **K.35 (requested)**: the restore's constructor names round-trip —
the copy's constructor `replacePrefix J aux cc.name` restored by
`replacePrefix aux J` is the container's `cc.name` again.  True
whenever the auxiliary name is not a prefix of a stored constructor's
name, which nothing checks; stated as the kernel record's model face
until it lands. -/
@[expose] def NestedCtorPinNames (env : Env) (_p : NestedParts) (st : ElimState) : Prop :=
  ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
    ∀ (ci : ContainerInfo) (J : ContainerMember), ConLeche.containerInfo? env qn.container = some ci →
      J ∈ ci.members → J.name = qn.container →
      ∀ cc ∈ J.ctors, Name.replacePrefix qn.aux qn.container (Name.replacePrefix J.name qn.aux cc.name) = cc.name

/-! ### The arity, read at a copy constructor -/

/-- With the keys pairwise distinct, a member with the sought key IS
the `find?`. -/
private theorem find?_key_of_nodup {α : Type} (f : α → Name) {n : Name} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ a ∈ l, f a = n →
      l.find? (fun x => f x == n) = some a
  | [], _, a, ha, _ => absurd ha (by simp)
  | x :: l, hnd, a, ha, hfa => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    split
    · rename_i hx
      rcases List.mem_cons.mp ha with rfl | ha'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨a, ha', hfa.trans (beq_iff_eq.mp hx).symm⟩) hnd.1
    · rename_i hx
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd (beq_iff_eq.mpr hfa) (by simp [hx])
      · exact find?_key_of_nodup f hnd.2 a ha' hfa

/-- **THE ARITY AT A COPY'S CONSTRUCTOR** is its field count: the pin
keys miss (a copy's constructor name is no copy's TYPE name) and the
copies' constructors, listed once each, answer at their own name. -/
theorem nestedArity_ctor {p : NestedParts} {st : ElimState} {pinsS : List PinSyn}
    {j : Nat} {t : AuxType} {jc : Nat} {c : Name × Expr × Nat}
    (hnotpin : ∀ q' ∈ st.pins, q'.aux ≠ c.1)
    (ht : st.types[p.k + j]? = some t) (hc : t.ctors[jc]? = some c)
    (hnd : (((st.types.drop p.k).flatMap (·.ctors)).map (·.1)).Nodup) :
    nestedArity p st pinsS c.1 = some c.2.2 := by
  have hnone : (st.pins.zipIdx.find? fun (q, _) => q.aux == c.1) = none := by
    refine List.find?_eq_none.mpr fun x hx => ?_
    obtain ⟨q, i⟩ := x
    show ¬ ((q.aux == c.1) = true)
    exact fun hh => hnotpin q (List.fst_mem_of_mem_zipIdx hx) (beq_iff_eq.mp hh)
  have htm : t ∈ st.types.drop p.k := by
    refine List.mem_of_getElem? (i := j) ?_
    rw [List.getElem?_drop]
    exact ht
  have hcm : c ∈ (st.types.drop p.k).flatMap (·.ctors) :=
    List.mem_flatMap.mpr ⟨t, htm, List.mem_of_getElem? hc⟩
  have hfind := find?_key_of_nodup (·.1) hnd c hcm rfl
  simp only [nestedArity, hnone, hfind]

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))
local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I


/-- The syntactic inversion at a constructor-pin key. -/
theorem NestedTailIn.ctorPinInv (hnames : NestedCtorPinNames env p st)
    {n : Name} {pin : Expr} {newName : Name}
    (hfind : (ConLeche.restoreTbl p st).ctorPins.find? (fun q => q.1 == n)
      = some (n, pin, newName)) :
    ∃ (q : Nat) (qn : NestedPin) (t : AuxType) (jc : Nat) (c : Name × Expr × Nat)
      (ci : ContainerInfo) (J : ContainerMember) (cc : ContainerCtor),
      st.pins[q]? = some qn ∧ st.types[p.k + q]? = some t ∧ t.ctors[jc]? = some c ∧
      t.name = qn.aux ∧ c.1 = n ∧ pin = Expr.abstractRange qn.pin 0 p.nP 0 ∧
      q < pinsS.length ∧
      ConLeche.containerInfo? env qn.container = some ci ∧ J ∈ ci.members ∧
      J.name = qn.container ∧ J.ctors[jc]? = some cc ∧ cc.name = newName ∧
      cc.nFields = c.2.2 := by
  obtain ⟨q, qn, t, jc, c, hqn, ht, hc, hn, hpin, hnn⟩ :=
    ConLeche.restoreTbl_ctorPins_find? hfind
  -- the pins and the types are aligned
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length I.hfA]
    rfl
  have hal := ConLeche.elimNested_aligned hlen0 I.helim
  have htn : t.name = qn.aux := by
    obtain ⟨t₁, ht₁, h₁⟩ := hal.2 q qn hqn
    rwa [Option.some.inj (ht₁.symm.trans ht)] at h₁
  have hq : q < pinsS.length := by
    rw [I.out.stage.pinsLen]
    exact (List.getElem?_eq_some_iff.mp hqn).1
  -- the copy's source
  obtain ⟨t₀, pbs, body, -, -, hsrc⟩ := ConLeche.nestedCopySrcOk_inv I.hsrc
  obtain ⟨t₂, Jn, lvls, Ds, ci, J, cpy, ht₂, -, hJn, -, hci, hJf, hJname, hmk, -, -, hmap⟩ :=
    hsrc q qn hqn
  have ht2 : t₂ = t := Option.some.inj (ht₂.symm.trans ht)
  rw [ht2] at hmk hmap
  obtain ⟨-, -, -, -, hclen, hcc⟩ := ConLeche.mkCopy_inv hmk
  have hJmem : J ∈ ci.members := List.mem_of_find?_eq_some hJf
  -- the constructor at `jc`, on the container's side
  have hjlt : jc < t.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hlen2 : cpy.ctors.length = t.ctors.length := by
    have := congrArg List.length hmap
    simpa using this
  have hjJ : jc < J.ctors.length := by omega
  obtain ⟨cc, hccj⟩ : ∃ cc, J.ctors[jc]? = some cc := ⟨_, List.getElem?_eq_getElem hjJ⟩
  obtain ⟨cI, -, hcpyj⟩ := hcc jc cc hccj
  have hpos : (Name.replacePrefix J.name t.name cc.name, cc.nFields) = (c.1, c.2.2) := by
    have h1 : (cpy.ctors.map (fun x => (x.1, x.2.2)))[jc]?
        = some (Name.replacePrefix J.name t.name cc.name, cc.nFields) := by
      rw [List.getElem?_map, hcpyj]; rfl
    have h2 : (t.ctors.map (fun x => (x.1, x.2.2)))[jc]? = some (c.1, c.2.2) := by
      rw [List.getElem?_map, hc]; rfl
    rw [hmap] at h1
    exact Option.some.inj (h1.symm.trans h2)
  simp only [Prod.mk.injEq] at hpos
  rw [hJn] at hci hJname
  refine ⟨q, qn, t, jc, c, ci, J, cc, hqn, ht, hc, htn, hn, hpin, hq, hci, hJmem, hJname,
    hccj, ?_, hpos.2⟩
  rw [hnn, ← hn, ← hpos.1, htn]
  exact (hnames q qn hqn ci J hci hJmem hJname cc (List.mem_of_getElem? hccj)).symm


omit I in
private theorem auxCtorNames_flat (lps : List Name) : ∀ (ts : List AuxType) (s : Nat),
    (((ts.zipIdx s).map fun (tm : AuxType × Nat) =>
        tm.1.ctors.map fun cc =>
          (⟨⟨cc.1, lps, cc.2.1⟩, cc.2.2, tm.2⟩ : ConLeche.MutualCtor)).flatten).map (·.cv.name)
      = (ts.flatMap (·.ctors)).map (·.1)
  | [], _ => rfl
  | t :: ts, s => by
    rw [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.map_append,
      auxCtorNames_flat lps ts (s + 1), List.flatMap_cons, List.map_append, List.map_map]
    rfl


omit I in
private theorem hasFvar_mkAppN_inv : ∀ (args : List Expr) (g : Expr),
    (Expr.mkAppN g args).hasFvar = false → g.hasFvar = false ∧ ∀ x ∈ args, x.hasFvar = false
  | [], g, h => ⟨h, fun x hx => absurd hx (by simp)⟩
  | a :: as, g, h => by
    obtain ⟨hg, has⟩ := hasFvar_mkAppN_inv as _ h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hg
    exact ⟨hg.1, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hg.2
      · exact has x hx'⟩

/-- The pin's level parameters are the container's constructor's
(step (iii)): both are the stored container member's. -/
theorem NestedTailIn.ctorPinLps
    {q : Nat} {qn : NestedPin} {jc : Nat} {ci : ContainerInfo} {J : ContainerMember}
    {cc : ContainerCtor} {cvc : ConstantVal}
    (hqn : st.pins[q]? = some qn)
    (hci : ConLeche.containerInfo? env qn.container = some ci) (hJmem : J ∈ ci.members)
    (hccj : J.ctors[jc]? = some cc)
    (hfindcc : env.find? cc.name = some (.ctorInfo cvc ci.nP cc.nFields)) :
    cvc.levelParams = J.lps := by
  obtain ⟨d₀, CM⟩ := I.hPM qn (List.mem_of_getElem? hqn) ci hci
  obtain ⟨i₀, hi₀⟩ := List.getElem?_of_mem hJmem
  obtain ⟨-, hnm, cvR', mI', rP', rules', hI'⟩ := CM.member i₀ J hi₀
  have hjlt : jc < (d₀.ctorsM i₀).length := by
    have := congrArg List.length hnm
    simp only [List.length_map] at this
    rw [this]
    exact (List.getElem?_eq_some_iff.mp hccj).1
  obtain ⟨cA₀, hcA₀⟩ : ∃ cA₀, (d₀.ctorsM i₀)[jc]? = some cA₀ :=
    ⟨_, List.getElem?_eq_getElem hjlt⟩
  have hname : cA₀.1.name = cc.name := by
    have h1 : ((d₀.ctorsM i₀).map (·.1.name))[jc]? = some cA₀.1.name := by
      rw [List.getElem?_map, hcA₀]; rfl
    have h2 : ((J.ctors).map (·.name))[jc]? = some cc.name := by
      rw [List.getElem?_map, hccj]; rfl
    rw [hnm] at h1
    exact Option.some.inj (h1.symm.trans h2)
  have hi₀k : i₀ < d₀.k := by rw [CM.k]; exact (List.getElem?_eq_some_iff.mp hi₀).1
  obtain ⟨hfind₀, hlps₀, -⟩ := hI'.ctors i₀ jc cA₀ hi₀k hcA₀
  rw [hname] at hfind₀
  rw [hfindcc] at hfind₀
  obtain ⟨hcv, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfind₀)
  rw [← hcv] at hlps₀
  exact hlps₀

theorem NestedTailIn.ctorPinRead
    {q : Nat} {qn : NestedPin} {jc : Nat} {ci : ContainerInfo} {J : ContainerMember}
    {cc : ContainerCtor}
    (hqn : st.pins[q]? = some qn) (hq : q < pinsS.length)
    (hci : ConLeche.containerInfo? env qn.container = some ci) (hJmem : J ∈ ci.members)
    (hccj : J.ctors[jc]? = some cc)
    (ψ : Name → Nat) :
    ∀ (fvsP fvs : List Expr) (d : Nat), OpenersFrom fvsP 0 b.nP → OpenersFrom fvs b.nP d →
      denoteMeta mp₂.base2.acval (ENV₂) ψ (b.nP + d) (Expr.instSeq (fvsP ++ fvs) (b.nP + d - 1)
          (Expr.mkAppN (.const cc.name ((D).pinAt q).lvls)
            (((Expr.abstractRange qn.pin 0 p.nP 0).liftLooseBVars d 0).getAppArgs)))
        = some (AnnotTerm.mkAppN (mp₂.base2.acval cc.name (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map (·.liftN d 0))) := by
  intro fvsP fvs d hfvsP hfvs
  obtain ⟨hnP, -, -, -⟩ := ConLeche.auxBlock_fields I.hb
  obtain ⟨hPJ, hpinEq⟩ := I.out.stage.pinRec q qn hqn
  have hpinDs : DenoteMetaSpine mp₂.base2.acval (ENV₂) ψ b.nP ((D).pinAt q).DsE
      (((D).pinAt q).Ds ψ) := I.out.stage.pinDs q hq ψ
  have hndNames : (fms.map (·.cvTa.name)).Nodup := by
    rw [I.out.facts.names]
    have h0 := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hfv0 := (ConLeche.pinsClosed_inv I.hclosed qn (List.mem_of_getElem? hqn)).1
  rw [hpinEq, ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const] at hfv0
  obtain ⟨-, hfvArgs⟩ := hasFvar_mkAppN_inv _ _ hfv0
  have hfv : (Expr.abstractRange (Expr.mkAppN (.const cc.name ((D).pinAt q).lvls)
      ((D).pinAt q).DsE) 0 b.nP 0).hasFvar = false := by
    rw [hnP, ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const]
    exact ConLeche.hasFvar_mkAppN _ _ rfl hfvArgs
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfindI, -, -, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfindJ, -, hJlps, -, hlpsEq, -, hccs⟩ := hmembers J hJmem
  obtain ⟨r, cvc, -, hccr, hfindcc, -⟩ := hccs jc cc hccj
  rw [← hccr] at hfindcc
  have hcvc : cvc.levelParams = cvT.levelParams := by
    rw [I.ctorPinLps hqn hci hJmem hccj hfindcc, hJlps, hlpsEq]
  have hFE1 : FindPreserved env (ENV₁) :=
    (consMutualFormers_extend (fms := fms.take p.k) (env := env)
      (fun f hf => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf)
        exact I.out.facts.fresh t f ht)
      (by
        have := hndNames
        rw [← List.take_append_drop p.k fms, List.map_append] at this
        exact (List.nodup_append.mp this).1)).1
  have hfindI1 : (ENV₁).find? ((D).pinAt q).J = some (.indInfo cvT caps) := by
    rw [hPJ]; exact hFE1 hfindI
  obtain ⟨hlvlsLen, hψJ₀⟩ := I.out.stage.pinψ q hq cvT caps hfindI1
  have hψJ : ∀ ψ' : Name → Nat, ((D).pinAt q).ψJ ψ'
      = Level.substFn ψ' cvT.levelParams ((D).pinAt q).lvls := hψJ₀
  have hfindcc2 : (ENV₂).find? cc.name = some (.ctorInfo cvc ci.nP cc.nFields) :=
    I.out.stage.find (hFE1 hfindcc)
  have hidx : ∀ k, k < b.nP → ∃ ty, fvsP[k]? = some (.fvar k ty) := by
    intro k hk
    obtain ⟨x, hx⟩ : ∃ x, fvsP[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hfvsP.1]; exact hk)⟩
    obtain ⟨ty, rfl⟩ := hfvsP.2 k x hx
    exact ⟨ty, by simpa using hx⟩
  rw [hpinEq, ← hnP,
    ConLeche.instSeq_ctorPin_open hfvsP.1 hfvs.1 hfvsP.closed (nt_pin_bounded hpinDs)]
  rw [nt_denoteMeta_restoredPin mp₂.base2 hfvsP.1 hidx hfv hfindcc2
    (by show ((D).pinAt q).lvls.length = cvc.levelParams.length; rw [hcvc]; exact hlvlsLen)
    hpinDs]
  rw [show (ConstantInfo.ctorInfo cvc ci.nP cc.nFields).toConstantVal.levelParams
      = cvT.levelParams from hcvc, ← hψJ ψ]


end Run

end ConLeche.Model
