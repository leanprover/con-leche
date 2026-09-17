module

public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecWalk
public import ConLeche.Verify.Inductives.NestedRecCtorPin
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.MutualRecsStage
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
theorem auxCtorNames_flat (lps : List Name) : ∀ (ts : List AuxType) (s : Nat),
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
  obtain ⟨CM, -⟩ := I.hPM qn (List.mem_of_getElem? hqn) ci hci
  generalize blockOf mp.base2 ci = d₀ at CM
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


omit I in
/-- Two frames from spines of one length over one base agree only on
equal spines. -/
private theorem consListInjLen {as bs : List V} {ρ : Nat → V} (hl : as.length = bs.length)
    (h : consList as ρ = consList bs ρ) : as = bs := by
  apply List.ext_getElem hl
  intro i hi₁ hi₂
  have hk : as.length - 1 - i < as.length := by omega
  have := congrFun h (as.length - 1 - i)
  rw [consList_getD_lt as ρ _ hk, consList_getD_lt bs ρ _ (by omega),
    show as.length - 1 - (as.length - 1 - i) = i from by omega,
    show bs.length - 1 - (as.length - 1 - i) = i from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi₂] at this
  exact this

/-- The container member's constructor, at the RESTORED environment. -/
theorem NestedTailIn.ctorPinFind2
    {qn : NestedPin} {jc : Nat} {ci : ContainerInfo} {J : ContainerMember}
    {cc : ContainerCtor}
    (hci : ConLeche.containerInfo? env qn.container = some ci) (hJmem : J ∈ ci.members)
    (hccj : J.ctors[jc]? = some cc) :
    ∃ cvc : ConstantVal, (ENV₂).find? cc.name = some (.ctorInfo cvc ci.nP cc.nFields) := by
  have hndNames : (fms.map (·.cvTa.name)).Nodup := by
    rw [I.out.facts.names]
    have h0 := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, -, -, -, hmembers⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, -, -, -, -, hccs⟩ := hmembers J hJmem
  obtain ⟨r, cvc, -, hccr, hfindcc, -⟩ := hccs jc cc hccj
  rw [← hccr] at hfindcc
  have hFE1 : FindPreserved env (ENV₁) :=
    (consMutualFormers_extend (fms := fms.take p.k) (env := env)
      (fun f hf => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf)
        exact I.out.facts.fresh t f ht)
      (by
        have := hndNames
        rw [← List.take_append_drop p.k fms, List.map_append] at this
        exact (List.nodup_append.mp this).1)).1
  exact ⟨cvc, I.out.stage.find (hFE1 hfindcc)⟩


/-- **THE CRUX**: the container's fitting field spine fits the COPY's
telescope at the scratch block — `CopyCtorInst.fit_iff_at` at the
container's `ChainFit`, its composed slots identified with the scratch
block's own by `NestedTailIn.slotAt_aux` (F5). -/
theorem NestedTailIn.ctorPinFieldsFit {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {q₀ kJ i : Nat} {dJ : BlockModel V} (G : PG mp₂.base2 q₀ kJ dJ) (hi : i < kJ)
    (ψ : Name → Nat) (ρ₀ : Nat → V) (as : List V) (hsp : SpineFit ρ₀ ((D).params ψ) as)
    {jc : Nat} {cA : ConstantVal × Nat}
    (hjA : ((DA).ctorsM (p.k + q₀ + i))[jc]? = some cA)
    {cAJ : ConstantVal × Nat} (hjJ : (dJ.ctorsM i)[jc]? = some cAJ)
    {fs : List V}
    (hfsJ : SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
      (consList as ρ₀)) (((dJ.Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD jc [])) fs) :
    SpineFit (consList as ρ₀) (((DA).Fss (p.k + q₀ + i) ψ).getD jc []) fs := by
  have hρp : Sat V ((D).params ψ).reverse (consList as ρ₀) := (D).satOfSpine hsp
  have hi' : i < dJ.k := by rw [G.kEq]; exact hi
  obtain ⟨cvT', cvR', mI', rP', rules', hIJ⟩ := G.rep i hi
  have hDsFit := G.DsFit i hi ψ ρ₀ as hsp
  have hρJ := dJ.satOfSpine hDsFit
  have hwJ : dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ := G.w i hi ψ
  have hcdJ := hIJ.ctorData hjJ
  have hjJlt : jc < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hjJ).1
  -- (1) the container's own fit at its least tuple
  have hfitsJ : FitsFrom ((dJ.rss i).getD jc [])
      (dJ.slotAt (((D).pinAt (q₀ + i)).ψJ ψ)
        (lfpTuple (f₀.s.eval ψ) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
              (consList as ρ₀)))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
              (consList as ρ₀)))) i jc) 0
      (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀))) (consList as ρ₀))
      ((dJ.Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD jc []) fs := by
    have := G.reps.fitsFrom_of_spineFit_go (G.typed _) (G.pinsTyped _) hi' hjJ hρJ _ 0 [] fs rfl
      trivial (by rw [consList_nil]; exact hfsJ)
    rw [consList_nil, hwJ] at this
    exact this
  -- (2) the index equations at the result's tuple
  have hEs := G.reps.res_es_fit (G.typed _) hi' hjJ hρJ hfsJ
  have hidxeq : ∀ l, l < (dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)).length →
      interp V (consList fs
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
            (consList as ρ₀)))
          (((dJ.Ess i (((D).pinAt (q₀ + i)).ψJ ψ)).getD jc []).getD l default)
        = Tower.projS l (dJ.tup (((D).pinAt (q₀ + i)).ψJ ψ) i
            ((dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)).map (interp V (consList fs
              (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
                (consList as ρ₀)))))) := by
    intro l hl
    rw [hIJ.IdsM_length] at hl
    have hlenE : ((dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)).map (interp V (consList fs
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
          (consList as ρ₀))))).length = dJ.nIdxAt i := by
      rw [List.length_map, hcdJ.lenE]
    have hgetD : interp V (consList fs
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
            (consList as ρ₀)))
          (((dJ.Ess i (((D).pinAt (q₀ + i)).ψJ ψ)).getD jc []).getD l default)
        = ((dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)).map (interp V (consList fs
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
              (consList as ρ₀))))).getD l pt := by
      rw [IsBlockModel.Ess_getD hjJ, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem (by rw [hcdJ.lenE]; exact hl),
        Option.map_some, Option.getD_some, Option.getD_some]
    rw [hgetD]
    show _ = Tower.projS l (tupW (dJ.uM i (((D).pinAt (q₀ + i)).ψJ ψ)) _)
    by_cases hu : dJ.uM i (((D).pinAt (q₀ + i)).ψJ ψ) = 0
    · rw [tupW, if_pos hu, Tower.projS_pt]
      have hrep := spineFit_zero_replicate (hu ▸ (hIJ.idxOk _ _ hρJ i hi').2) hEs
      rw [hrep, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_replicate, hIJ.IdsM_length]; exact hl)]
      simp
    · rw [tupW, if_neg hu, Tower.projS_mkTower l _ (by rw [hlenE]; exact hl),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenE]; exact hl),
        Option.getD_some]
  -- (3) the composed fit at the copy's global tables
  have ht := tupW_mem (u := dJ.uM i (((D).pinAt (q₀ + i)).ψJ ψ)) hEs
  have hcomposed := ((hfit_at_of_inst mp₂.base2.acval G.reps (G.typed _) (G.pinsTyped _) G.kEq hwJ
      (nestedU_pin_group mp₂.base2 G hi ψ) hρJ (G.idx i hi ψ)
      (fun i' hi' j => G.grp I.out.grouped I.out.facts.lenA ψ hi' j)
      (G.shape i hi ψ _ hρp) (G.entry i hi ψ _ hρp) i hi _ ht jc fs).mpr
      ⟨hjJlt, hfitsJ, hidxeq⟩).2.2.1
  -- (4) the scratch block's own fit
  have hck : p.k + q₀ + i < b.k := by rw [I.out.bk]; have := G.seg; omega
  obtain ⟨cvTA, cvRA, mIA, rPA, rulesA, hIA⟩ := S.reps (p.k + q₀ + i) hck
  have hjAlt : jc < ((DA).ctorsM (p.k + q₀ + i)).length := (List.getElem?_eq_some_iff.mp hjA).1
  have hρpA : Sat V ((DA).params ψ).reverse (consList as ρ₀) := hρp
  obtain ⟨hJl, hJ, -⟩ := mutualBlockModel_ctorsM_get I.out.grouped I.out.facts.lenA hjA
  have hnf : mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i) + jc) = cA.2 := mutNFOf_eq hJ
  have hksl : (mutKsOf kinds (b.ownOffset (p.k + q₀ + i) + jc)).length = cA.2 :=
    (I.out.facts.ksJ _ cA hJ).1
  have hlenDs : (dsF (b.ownOffset (p.k + q₀ + i) + jc) ψ).length = b.nP + cA.2 :=
    (I.out.facts.CD _ cA hJ).len ψ
  have hlenFA : (((DA).Fss (p.k + q₀ + i) ψ).getD jc []).length = cA.2 := hIA.Fss_length hjA ψ
  have hrsA : ((DA).rss (p.k + q₀ + i)).getD jc [] = rsOf ((DA).ksF (p.k + q₀ + i) jc) :=
    IsBlockModel.rss_getD hjAlt
  have hfitsA : FitsFrom (((DA).rss (p.k + q₀ + i)).getD jc [])
      ((DA).slotAt ψ
        (lfpTuple ((DA).w ψ) (DA).k ((DA).idx ψ (consList as ρ₀)) ((DA).Φ ψ (consList as ρ₀)))
        (p.k + q₀ + i) jc) 0 (consList as ρ₀) (((DA).Fss (p.k + q₀ + i) ψ).getD jc []) fs := by
    refine (fitsFrom_iff_frames_spine ?_ ?_).mpr hcomposed
    · rw [hlenFA, blkFss0_getD hJl, shadowFs_length, hnf]
    · intro l hl fs₁ hl₁ hsp₁ hfA hfC
      rw [hlenFA] at hl
      have hrEq : (((DA).rss (p.k + q₀ + i)).getD jc []).getD (0 + l) false
          = ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + jc) []).getD (0 + l) false := by
        rw [hrsA, blkRss_getD hJl]
        rfl
      constructor
      · by_cases hr : (((DA).rss (p.k + q₀ + i)).getD jc []).getD (0 + l) false = true
        · rw [if_pos hr, Nat.zero_add]
          rw [← S.reps.real_dom_eq (S.typed ψ).1 (PinsTyped.of_noPins rfl ψ) hck hjA hρpA hl
            (by rw [← hrsA, Nat.zero_add] at *; exact hr) hsp₁]
          exact Subset.refl _
        · rw [if_neg hr]
          exact Subset.refl _
      · by_cases hr : (((DA).rss (p.k + q₀ + i)).getD jc []).getD (0 + l) false = true
        · rw [if_pos hr, if_pos (hrEq ▸ hr), Nat.zero_add]
          have hF5 := I.slotAt_aux S G hi ψ ρ₀ as hsp hjA hl
            (by rw [← hrsA, Nat.zero_add] at *; exact hr) hsp₁
          rw [hwJ] at hF5
          exact hF5
        · have hrf : (((DA).rss (p.k + q₀ + i)).getD jc []).getD (0 + l) false = false := by
            simpa using hr
          have hnrec : ¬ recAt b.nP
              (kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i) + jc))) (b.nP + l) := by
            intro hrec
            have hkind := hrec.2
            rw [Nat.add_sub_cancel_left] at hkind
            have hb := (rsOf_getD_iff
              (ks := kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i) + jc)))
              (by rw [kindsOf_length, hksl]; exact hl)).mpr hkind
            rw [← blkRss_getD hJl, ← Nat.zero_add l, ← hrEq] at hb
            rw [hrf] at hb
            exact Bool.false_ne_true hb
          rw [if_neg hr, if_neg (by rw [← hrEq]; exact hr),
            IsBlockModel.Fss_getD hjA, blkFss0_getD hJl,
            shadowFs_getD (by rw [hnf]; exact hl), if_neg hnrec]
          rfl
  exact S.reps.spineFit_of_fitsFrom (S.typed ψ).1 (PinsTyped.of_noPins rfl ψ) hck hjA hρpA
    (lfpTuple_mem _ _ _ _) (TupleLe.refl _ _ _) hfitsA



/-! ### The copy constructors' names, against the pins' -/

omit I in
/-- A key absent from an association list is not answered. -/
private theorem lookup_eq_none_of {β : Type} {a : Name} :
    ∀ {l : List (Name × β)}, (∀ q ∈ l, q.1 ≠ a) → l.lookup a = none
  | [], _ => rfl
  | (k, v) :: l, h => by
    rw [List.lookup_cons]
    have hk : ¬ (a == k) = true := fun hb => h (k, v) List.mem_cons_self (beq_iff_eq.mp hb).symm
    rw [Bool.not_eq_true] at hk
    rw [hk]
    exact lookup_eq_none_of fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **A COPY'S CONSTRUCTOR NAME IS NO COPY'S TYPE NAME**: the former
is one of the auxiliary block's constructor names, the latter one of
its member names, and `b.blockNames.Nodup` keeps the two lists
apart. -/
theorem NestedTailIn.ctorName_ne_aux {q jc : Nat} {t : AuxType} {c : Name × Expr × Nat}
    (ht : st.types[p.k + q]? = some t) (hc : t.ctors[jc]? = some c) :
    ∀ q' ∈ st.pins, q'.aux ≠ c.1 := by
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length I.hfA]
    rfl
  have hal := ConLeche.elimNested_aligned hlen0 I.helim
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  have hdisj := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  have hcmem : c.1 ∈ b.ctors.map (·.cv.name) :=
    List.mem_map.mpr ⟨_, List.mem_of_getElem?
      (ConLeche.auxBlock_ctors_getElem? I.hb I.out.grouped (p.k + q) jc t c ht hc), rfl⟩
  intro q' hq' hce
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq'
  obtain ⟨t', ht', htn'⟩ := hal.2 j q' hj
  obtain ⟨nIdx', hfo', -⟩ := hform (p.k + j) t' ht'
  have hmem : q'.aux ∈ b.memberNames := by
    refine List.mem_of_getElem? (i := p.k + j) ?_
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hfo', Option.map_some, htn']
  exact hdisj _ hmem _ hcmem hce

/-- **THE COPIES' CONSTRUCTOR NAMES ARE PAIRWISE DISTINCT**: they are
the auxiliary block's constructor names past the block's own members,
and `b.blockNames.Nodup` lists them once each. -/
theorem NestedTailIn.ctorNames_nodup :
    (((st.types.drop p.k).flatMap (·.ctors)).map (·.1)).Nodup := by
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  have hcn : (b.ctors.map (·.cv.name)).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  obtain ⟨-, -, -, hct⟩ := ConLeche.auxBlock_fields I.hb
  rw [hct, auxCtorNames_flat p.lps st.types 0] at hcn
  rw [← List.take_append_drop p.k st.types, List.flatMap_append, List.map_append] at hcn
  exact (List.nodup_append.mp hcn).2.1

/-- **THE PIN MAP DECLINES AT A COPY'S CONSTRUCTOR**: its keys are the
copies' TYPE names. -/
theorem NestedTailIn.ctorPinLookupNone {q jc : Nat} {t : AuxType} {c : Name × Expr × Nat}
    (ht : st.types[p.k + q]? = some t) (hc : t.ctors[jc]? = some c) :
    (ConLeche.restoreTbl p st).pins.lookup c.1 = none := by
  refine lookup_eq_none_of fun x hx => ?_
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
  exact I.ctorName_ne_aux ht hc q' hq'


/-! ### The container's constructor at a `Prop`-valued block -/

omit I in
/-- **AT A `Prop`-VALUED BLOCK THE CONTAINER'S CONSTRUCTOR IS THE
POINT**: its type reads to a Π-tower whose binders all carry bit `0`
(`CtorDataI.bits` at `w = 0`), so the tower is a truth value
(`interp_mkPisAV_mem_univZero`) — and at an EMPTY telescope its body is
the member at the index readings, which the member's own typing
(`FormersTyped` at the sort `0`, along the readings' fit) puts in
`univ 0` all the same. -/
theorem NestedTailIn.ctorPinPt {q₀ kJ i : Nat} {dJ : BlockModel V} (G : PG mp₂.base2 q₀ kJ dJ)
    (hi : i < kJ) (ψ : Name → Nat)
    (hw : dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) = 0)
    {jc : Nat} {cAJ : ConstantVal × Nat} (hjJ : (dJ.ctorsM i)[jc]? = some cAJ) (ρ : Nat → V) :
    interp V ρ (mp₂.base2.acval cAJ.1.name (((D).pinAt (q₀ + i)).ψJ ψ)) = pt := by
  have hi' : i < dJ.k := by rw [G.kEq]; exact hi
  obtain ⟨cvT', cvR', mI', rP', rules', hIJ⟩ := G.rep i hi
  have hcd := hIJ.ctorData hjJ
  refine eq_pt_of_mem_univZero ?_
    (IsBlockModels.ctorsTyped mp₂ G.reps (((D).pinAt (q₀ + i)).ψJ ψ) i hi' jc cAJ hjJ ρ)
  refine interp_mkPisAV_mem_univZero
    (fun d hd => (hcd.bits (((D).pinAt (q₀ + i)).ψJ ψ) d hd).mp hw) ?_
  intro hnil
  -- the telescope is empty: no parameters, no fields
  have hlen := hcd.len (((D).pinAt (q₀ + i)).ψJ ψ)
  rw [hnil, List.length_nil] at hlen
  have hnP : dJ.nP = 0 := by omega
  have hnF : cAJ.2 = 0 := by omega
  -- the member's telescope is its indices alone, in the Π regime
  have hfd := hIJ.former
  have hppsLen : (dJ.ppsM i (((D).pinAt (q₀ + i)).ψJ ψ)).length = dJ.nIdxAt i := by
    rw [hfd.len, hnP, Nat.zero_add]
  have hEsLen : (dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)).length = dJ.nIdxAt i :=
    hcd.lenE (((D).pinAt (q₀ + i)).ψJ ψ)
  -- the body is the member at the index readings
  have hbody : ctorBodyAVI mp₂.base2 (dJ.memberName i) dJ.nP cAJ.2
      (((D).pinAt (q₀ + i)).ψJ ψ) (dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ))
      = AnnotTerm.mkAppN (mp₂.base2.acval (dJ.memberName i) (((D).pinAt (q₀ + i)).ψJ ψ))
        (dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)) := by
    unfold ctorBodyAVI
    rw [hnP, hnF]
    rfl
  have hok : WellDenoted V ρ (AnnotTerm.mkAppN
      (mp₂.base2.acval (dJ.memberName i) (((D).pinAt (q₀ + i)).ψJ ψ))
      (dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ))) := by
    have := (hcd.okTy (((D).pinAt (q₀ + i)).ψJ ψ) ρ).1
    rw [hnil] at this
    show WellDenoted V ρ _
    rw [← hbody]
    exact this
  have hmemT := G.typed (((D).pinAt (q₀ + i)).ψJ ψ) i hi' ρ
  have hsp := spineFit_of_wellDenoted_mkAppN_pis
    (C := AnnotTerm.sort (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)))
    (hfd.bits (((D).pinAt (q₀ + i)).ψJ ψ)) (Nat.le_of_eq (hEsLen.trans hppsLen.symm)) hok rfl hmemT
  rw [hEsLen, ← hppsLen, List.take_length] at hsp
  have hfold := mkPisAV_fold_mem (m := 1) (C := AnnotTerm.sort
      (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)))
    (fun d hd => ⟨fun h => absurd h (by omega),
      fun h => absurd h (hfd.bits (((D).pinAt (q₀ + i)).ψJ ψ) d hd)⟩)
    (fun h => absurd h (by omega)) hmemT hsp
  rw [hbody, interp_mkAppN_foldl]
  have : interp V (consList ((dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)).map (interp V ρ)) ρ)
      (AnnotTerm.sort (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ))) = (univZero : V) := by
    rw [interp_sort, hw, univ_zero]
  rw [this] at hfold
  exact hfold


/-! ### The fields fit the container's telescope -/

omit I in
/-- **THE RESTORED READING'S FIELDS FIT THE CONTAINER'S CONSTRUCTOR
TELESCOPE** at a `Type`-valued block: the application's grading puts
every argument in its domain (`spineFit_of_wellDenoted_mkAppN_pis` at
the constructor's own typing, F1), and the split at the parameter
count leaves the pin's components on the left and the fields on the
right. -/
theorem NestedTailIn.ctorPinFitJ {q₀ kJ i : Nat} {dJ : BlockModel V} (G : PG mp₂.base2 q₀ kJ dJ)
    (hi : i < kJ) (ψ : Name → Nat) (hw : dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) ≠ 0)
    {jc : Nat} {cAJ : ConstantVal × Nat} (hjJ : (dJ.ctorsM i)[jc]? = some cAJ)
    (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Fs : List AnnotTerm)
    (hxs : xs.length = d) (hFs : Fs.length = cAJ.2)
    (hwd : WellDenoted V (consList xs (consList as ρ₀))
      (AnnotTerm.mkAppN (mp₂.base2.acval cAJ.1.name (((D).pinAt (q₀ + i)).ψJ ψ))
        ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN d 0) ++ Fs))) :
    SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
        (consList as ρ₀)) ((dJ.Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD jc [])
      (Fs.map (interp V (consList xs (consList as ρ₀)))) := by
  have hi' : i < dJ.k := by rw [G.kEq]; exact hi
  obtain ⟨cvT', cvR', mI', rP', rules', hIJ⟩ := G.rep i hi
  have hcd := hIJ.ctorData hjJ
  have hDsLen : ((((D).pinAt (q₀ + i)).Ds ψ)).length = dJ.nP := G.pinDsLen i hi ψ
  have hdsLen := hcd.len (((D).pinAt (q₀ + i)).ψJ ψ)
  -- the arguments read at the shifted frame
  have hlift : ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN d 0)).map
      (interp V (consList xs (consList as ρ₀)))
      = (((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun Dc _ => ?_
    show interp V (consList xs (consList as ρ₀)) (Dc.liftN d 0) = _
    rw [← hxs]
    exact interp_liftN_consList Dc xs (consList as ρ₀)
  -- the whole spine fits the constructor's telescope
  have hall := spineFit_of_wellDenoted_mkAppN_pis
    (C := ctorBodyAVI mp₂.base2 (dJ.memberName i) dJ.nP cAJ.2 (((D).pinAt (q₀ + i)).ψJ ψ)
      (dJ.esF i jc (((D).pinAt (q₀ + i)).ψJ ψ)))
    (σ := consList as ρ₀)
    (fun d' hd' => fun h0 => hw ((hcd.bits (((D).pinAt (q₀ + i)).ψJ ψ) d' hd').mpr h0))
    (by rw [List.length_append, List.length_map, hDsLen, hFs, hdsLen]; exact Nat.le_refl _)
    hwd (interp_closed (V := V) (mp₂.base2.cval_closedL _ _) _ (consList as ρ₀))
    (IsBlockModels.ctorsTyped mp₂ G.reps (((D).pinAt (q₀ + i)).ψJ ψ) i hi' jc cAJ hjJ
      (consList as ρ₀))
  rw [List.length_append, List.length_map, hDsLen, hFs, ← hdsLen, List.take_length,
    List.map_append, hlift] at hall
  -- split it at the parameter count
  rw [← List.take_append_drop dJ.nP (dJ.dsF i jc (((D).pinAt (q₀ + i)).ψJ ψ)),
    List.map_append] at hall
  obtain ⟨as₁, as₂, hcat, h1, h2⟩ := spineFit_append_inv hall
  have hl1 : as₁.length = dJ.nP := by
    rw [h1.length_eq, List.length_map, List.length_take, hdsLen]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj hcat (by rw [hl1, List.length_map, hDsLen])
  rw [IsBlockModel.Fss_getD hjJ]
  exact h2


/-! ### B1 — the constructor pin's agreement -/

/-- **THE COPY CONSTRUCTOR'S AGREEMENT AT THE TAIL** (task #315 M7-2,
PLAN-M7 §1c): `RestoreAgree.ctor` at the restore table of the
elimination, the scratch install's model `mpA` and the restored one
`mp₂`.  A `ctorPins` hit is a copy's constructor (`ctorPinInv`); its
pin is the container's own application, closed at the block's
parameters (bounded, headed by the container, absent from the pin
map); the copy's constructor is stored at the scratch environment with
the block's level parameters and its field count is the key's arity;
the restored head reads as the container's constructor at the pin's
components (`ctorPinRead`); and the two readings interpret alike —
both sides are the SAME tagged tower, the container's constructor
through `IsBlockModel.ctor` at the pin's components (whose fields fit
by `ctorPinFitJ`) and the copy's through the scratch block's, the two
field spines identified by THE CRUX (`ctorPinFieldsFit`); at a
`Prop`-valued block both sides are the point (`ctorPinPt`,
`sumMkAV_zero`).

`hctorsJ` is the second named model face of T2 (with `NestedCtorPinNames`
= K.35): the pin group's constructors are the container member's, by
name and in order. -/
theorem NestedTailIn.ctorArm {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (ψ : Name → Nat) :
    ∀ (n : Name) (pin : Expr) (newName : Name),
      (ConLeche.restoreTbl p st).ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName) →
      pin.looseBVarsBounded b.nP = true ∧ (ConLeche.restoreTbl p st).pins.lookup n = none ∧
      ∃ (ci : ConstantInfo) (J : Name) (ilvls : List Level) (ψJ : Name → Nat)
        (Ds : List AnnotTerm) (nF : Nat),
        (ENVA).find? n = some ci ∧ ci.toConstantVal.levelParams = b.lps ∧
        nestedArity p st pinsS n = some nF ∧
        (∀ d, (pin.liftLooseBVars d 0).getAppFn = .const J ilvls) ∧
        (∀ (fvsP fvs : List Expr) (d : Nat), OpenersFrom fvsP 0 b.nP → OpenersFrom fvs b.nP d →
          denoteMeta mp₂.base2.acval (ENV₂) ψ (b.nP + d) (Expr.instSeq (fvsP ++ fvs) (b.nP + d - 1)
              (Expr.mkAppN (.const newName ilvls) (pin.liftLooseBVars d 0).getAppArgs))
            = some (AnnotTerm.mkAppN (mp₂.base2.acval newName ψJ) (Ds.map (·.liftN d 0)))) ∧
        ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Fs : List AnnotTerm),
          SpineFit ρ₀ ((D).params ψ) as → xs.length = d → Fs.length = nF →
          WellDenoted V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (mp₂.base2.acval newName ψJ) (Ds.map (·.liftN d 0) ++ Fs)) →
          interp V (consList xs (consList as ρ₀))
              (AnnotTerm.mkAppN (mp₂.base2.acval newName ψJ) (Ds.map (·.liftN d 0) ++ Fs))
            = interp V (consList xs (consList as ρ₀))
              (AnnotTerm.mkAppN (mpA.base2.acval n ψ) (paramBvarsAt b.nP (b.nP + d) ++ Fs)) := by
  intro n pin newName hfind
  obtain ⟨q, qn, t, jc, c, ci, J, cc, hqn, ht, hc, htn, rfl, rfl, hq, hci, hJmem, hJname,
    hccj, rfl, hnFc⟩ := I.ctorPinInv hnames hfind
  obtain ⟨q₀, kJ, i, dJ, rfl, hi, G⟩ := I.out.stage.groups q hq
  obtain ⟨hnP, -, -, -⟩ := ConLeche.auxBlock_fields I.hb
  obtain ⟨hPJ, hpinEq⟩ := I.out.stage.pinRec (q₀ + i) qn hqn
  have hpinDs := I.out.stage.pinDs (q₀ + i) hq ψ
  -- the block position of the copy and of its constructor
  have hck : p.k + q₀ + i < b.k := by
    rw [I.out.bk]; have := G.seg; omega
  have hassoc : p.k + (q₀ + i) = p.k + q₀ + i := (Nat.add_assoc _ _ _).symm
  have hown := ConLeche.auxBlock_ownCtors_getElem? I.hb I.out.grouped (p.k + (q₀ + i)) jc t c ht hc
  have hct := ConLeche.auxBlock_ctors_getElem? I.hb I.out.grouped (p.k + (q₀ + i)) jc t c ht hc
  rw [hassoc] at hown hct
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  have hJlt : b.ownOffset (p.k + q₀ + i) + jc < ctorsA.length := by
    rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hct).1
  obtain ⟨cA, hcAget⟩ : ∃ cA, ctorsA[b.ownOffset (p.k + q₀ + i) + jc]? = some cA :=
    ⟨_, List.getElem?_eq_getElem hJlt⟩
  have hcAgetD : ctorsA.getD (b.ownOffset (p.k + q₀ + i) + jc) default = cA := by
    rw [List.getD_eq_getElem?_getD, hcAget]; rfl
  have hcAname : cA.1.name = c.1 := (hnamesA _ _ _ hcAget hct).1
  have hcAlps : cA.1.levelParams = b.lps := (hnamesA _ _ _ hcAget hct).2.2
  have hjA : ((DA).ctorsM (p.k + q₀ + i))[jc]? = some cA := by
    show ((b.ownCtors (p.k + q₀ + i)).map fun z => ctorsA.getD z.1 default)[jc]? = _
    rw [List.getElem?_map, hown]
    show some (ctorsA.getD (b.ownOffset (p.k + q₀ + i) + jc) default) = _
    rw [hcAgetD]
  obtain ⟨hfactsA, -, hleafA⟩ := S.cons _ _ hcAget
  refine ⟨?_, I.ctorPinLookupNone ht hc, .ctorInfo cA.1 b.nP cA.2,
    ((D).pinAt (q₀ + i)).J, ((D).pinAt (q₀ + i)).lvls,
    ((D).pinAt (q₀ + i)).ψJ ψ, ((D).pinAt (q₀ + i)).Ds ψ, c.2.2,
    by rw [← hcAname]; exact hfactsA.1, by show cA.1.levelParams = b.lps; exact hcAlps,
    nestedArity_ctor (I.ctorName_ne_aux ht hc) ht hc I.ctorNames_nodup, ?_,
    I.ctorPinRead hqn hq hci hJmem hccj ψ, ?_⟩
  · -- (1) the abstracted pin is bounded at the block's parameters
    have h := ConLeche.looseBVarsBounded_abstractRange qn.pin 0 p.nP 0
      (by rw [hpinEq]; exact nt_pin_bounded hpinDs)
    rw [Nat.zero_add] at h
    rw [hnP]; exact h
  · -- (4) the pin is headed by the container
    intro d
    rw [hpinEq, ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const,
      ConLeche.liftLooseBVars_mkAppN, Expr.getAppFn_mkAppN, hPJ]
    rfl
  -- (6) the two readings interpret alike
  intro d as xs ρ₀ Fs hsp hxs hFs hwd
  have hi' : i < dJ.k := by rw [G.kEq]; exact hi
  obtain ⟨cvT', cvR', mI', rP', rules', hIJ⟩ := G.rep i hi
  have hwJ : dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ := G.w i hi ψ
  -- the container member's constructor at the group's block model
  have hmapJ := hctorsJ q₀ kJ i dJ G hi ci J (by rw [hPJ]; exact hci) hJmem (by rw [hPJ]; exact hJname)
  have hjcJ : jc < (dJ.ctorsM i).length := by
    have hl := congrArg List.length hmapJ
    simp only [List.length_map] at hl
    rw [hl]
    exact (List.getElem?_eq_some_iff.mp hccj).1
  obtain ⟨cAJ, hjJ⟩ : ∃ cAJ, (dJ.ctorsM i)[jc]? = some cAJ :=
    ⟨_, List.getElem?_eq_getElem hjcJ⟩
  have hnameJ : cAJ.1.name = cc.name := by
    have h1 : ((dJ.ctorsM i).map (·.1.name))[jc]? = some cAJ.1.name := by
      rw [List.getElem?_map, hjJ]; rfl
    have h2 : ((J.ctors).map (·.name))[jc]? = some cc.name := by
      rw [List.getElem?_map, hccj]; rfl
    rw [hmapJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  obtain ⟨cvc, hfind2⟩ := I.ctorPinFind2 hci hJmem hccj
  have hnFJ : cAJ.2 = c.2.2 := by
    obtain ⟨hfindJ, -, -⟩ := hIJ.ctors i jc cAJ hi' hjJ
    rw [hnameJ, hfind2] at hfindJ
    obtain ⟨-, -, hnf2⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfindJ)
    rw [← hnf2]; exact hnFc
  have hwd' : WellDenoted V (consList xs (consList as ρ₀))
      (AnnotTerm.mkAppN (mp₂.base2.acval cAJ.1.name (((D).pinAt (q₀ + i)).ψJ ψ))
        ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN d 0) ++ Fs)) := by rw [hnameJ]; exact hwd
  -- the common rewriting of the two folds
  have hplen : ((D).params ψ).length = b.nP := by
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (I.out.facts.FD 0 f₀ I.out.facts.first).len ψ]
    omega
  have hlenAs : as.length = b.nP := by rw [hsp.length_eq, hplen]
  have hrng : (List.range b.nP).reverse.map (consList as ρ₀) = as := by
    have h1 := consList_range_reverse b.nP (consList as ρ₀)
    have h2 : (fun j' => consList as ρ₀ (j' + b.nP)) = ρ₀ := by
      funext j'; rw [← hlenAs]; exact consList_apply_add as ρ₀ j'
    rw [h2] at h1
    exact consListInjLen (by simp [hlenAs]) h1
  have hlift : ((((D).pinAt (q₀ + i)).Ds ψ).map (·.liftN d 0)).map
      (interp V (consList xs (consList as ρ₀)))
      = (((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun Dc _ => ?_
    show interp V (consList xs (consList as ρ₀)) (Dc.liftN d 0) = _
    rw [← hxs]
    exact interp_liftN_consList Dc xs (consList as ρ₀)
  rw [interp_mkAppN_foldl, interp_mkAppN_foldl, List.map_append, List.map_append, hlift,
    interp_closed (V := V) (mp₂.base2.cval_closedL _ _) _ (consList as ρ₀),
    interp_closed (V := V) (mpA.base2.cval_closedL _ _) _ ρ₀,
    map_paramBvarsAt_interp (ρp := consList as ρ₀)
      (fun j' => by rw [← hxs]; exact consList_apply_add xs _ j'), hrng]
  by_cases hw0 : f₀.s.eval ψ = 0
  · -- the `Prop` regime: both folds are the point
    rw [← hnameJ, NestedTailIn.ctorPinPt G hi ψ (by rw [hwJ]; exact hw0) hjJ (consList as ρ₀),
      ← hcAname, hleafA ψ, hw0, sumMkAV_zero, foldl_app_pt, foldl_app_pt]
  · -- the `Type` regime: both folds are the same tagged tower
    have hwJ' : dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) ≠ 0 := by rw [hwJ]; exact hw0
    have hfsJ := NestedTailIn.ctorPinFitJ G hi ψ hwJ' hjJ d as xs ρ₀ Fs hxs
      (by rw [hFs, hnFJ]) hwd'
    have hfsA := I.ctorPinFieldsFit S G hi ψ ρ₀ as hsp hjA hjJ hfsJ
    have hleft := hIJ.ctor i jc cAJ hi' hjJ (((D).pinAt (q₀ + i)).ψJ ψ) (consList as ρ₀)
      ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ₀)))
      (Fs.map (interp V (consList xs (consList as ρ₀))))
      (G.DsFit i hi ψ ρ₀ as hsp) hfsJ
    rw [G.inj, hwJ] at hleft
    obtain ⟨cvTA, cvRA, mIA, rPA, rulesA, hIA⟩ := S.reps (p.k + q₀ + i) hck
    have hright := hIA.ctor (p.k + q₀ + i) jc cA hck hjA ψ ρ₀ as
      (Fs.map (interp V (consList xs (consList as ρ₀)))) hsp hfsA
    have hrinj : (DA).inj ψ (p.k + q₀ + i) jc (Fs.map (interp V (consList xs (consList as ρ₀))))
        = injW (f₀.s.eval ψ) jc
          (mkTower (Fs.map (interp V (consList xs (consList as ρ₀))) ++ [pt])) := by rfl
    rw [hrinj] at hright
    rw [← hnameJ, hleft, ← hcAname, hright]

end Run

end ConLeche.Model
