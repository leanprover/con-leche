module

public import ConLeche.Model.Inductives.CopyCtorWalkRun
public import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedRestoreWalk
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Inductives.ContainerWalk
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels

public section

/-!
# The walk's facts at a copy's constructor, from the STORED data (task #279 M-D′, step (1), DESIGN §M.45)

`CopyCtorWalkRun.lean` reads the constructor record off `CopyWalkFacts`,
the SYNTACTIC half: per copy constructor, the container's constructor
instantiated at the pin opens, and `CopyCtorWalkFacts` holds of the pair
(the copy's STORED constructor opened at the auxiliary datum's variables
against it).  This module derives that half — NOT by walking forward
through the elimination, but from what the run already compares:

* K.17's witness (`nestedCtorsWhnfOk`) restores the PROCESSED and the
  STORED constructor and compares them field by field, `dm = ds` or
  `whnf dm = ds`;
* the restore undoes the walk (`restoreI_walk`, W1): the restored
  processed field is the container's instantiated field up to erasure;
* `whnf` is the identity on a Π-tower over an inductive-headed
  application (task #305), so at a container-RECURSIVE field K.17's
  `whnf` arm is the `=` arm too;
* the STORED field's shape is the auxiliary datum's (`FixOpened`: an
  ordinary field resolves before the block, a recursive or reflexive one
  is a block member at the parameters), and a copy application restores
  to its pin (`restoreI_copyField`).

So at every field the restored stored field is erasure-equal to the
container's instantiated field, and the record's arms follow: a
container-recursive field is a fire whose pin is the group-mate's; a
container-ordinary field is unfired (copy-ordinary, or recursive into a
REAL member), a fire outside the group (copy-recursive into a copy — the
exclusion is K.23's record, `NestedGroupExclusionOk`, bridged through the
container datum's `OrdNotRec`), or K.17's `whnf` arm verbatim.

Two facts are NAMED here and consumed as hypotheses of the assembly:

* **`NestedGroupExclusionOk`** — K.23's kernel record, in the shape of a
  stored-data conjunct: a copy constructor field that is
  copy-recursive into a group-mate has a container field that is
  recursive-shaped (a group member at the exact parameters);
* the containers' `lps.Nodup` (K.21, `hlpsNodup`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState ContainerCtor)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The two named facts -/

/-- **K.23's record, as a stored-data conjunct** (DESIGN §M.45): for
every pin `j` and every constructor `l` of its copy, a field `i` of the
STORED copy constructor (at the scratch environment) that is
copy-recursive into a GROUP-MATE — its Π-body is headed by the `aux`
name of a pin of the same mint group — has a container constructor
field `i` (the container's stored constructor, `containerInfo?`'s
record) that is RECURSIVE-shaped: its Π-body is headed by a member of
the container's group applied to the exact parameter variables
(`containerFieldOk`'s first arm, K.15).  A syntactic test on stored
data; the decline never fires on a stream official accepts. -/
@[expose] def NestedGroupExclusionOk (env envAux : Env) (p : ConLeche.NestedParts)
    (st : ElimState) : Prop :=
  ∀ (j : Nat) (q : NestedPin), st.pins[j]? = some q →
  ∀ (tyA : AuxType), st.types[p.k + j]? = some tyA →
  ∀ (l : Nat) (cn : Name) (cty : Expr) (nF : Nat), tyA.ctors[l]? = some (cn, cty, nF) →
  ∀ (cvS : ConstantVal) (nPS nFS : Nat), envAux.find? cn = some (.ctorInfo cvS nPS nFS) →
  ∀ (bsS : List (Expr × ConLeche.BinderMeta)) (rS : Expr),
    cvS.type.stripPis (nPS + nFS) = some (bsS, rS) →
  ∀ (i : Nat) (domS : Expr × ConLeche.BinderMeta), bsS[nPS + i]? = some domS →
  ∀ (aux : Name) (args : List Expr) (n : Nat), ConLeche.fieldHeadAt domS.1 = some (aux, args, n) →
  (∃ t, t < q.grpSize ∧ ∃ q', st.pins[q.grpBase + t]? = some q' ∧ q'.aux = aux) →
  ∀ (ci : ContainerInfo) (J : ContainerMember) (c : ContainerCtor),
    ConLeche.containerInfo? env q.container = some ci → J ∈ ci.members → J.name = q.container →
    J.ctors[l]? = some c →
  ∀ (bsJ : List (Expr × ConLeche.BinderMeta)) (rJ : Expr),
    c.type.stripPis (ci.nP + c.nFields) = some (bsJ, rJ) →
  ∀ (domJ : Expr × ConLeche.BinderMeta), bsJ[ci.nP + i]? = some domJ →
  ∃ (C : Name) (argsJ : List Expr) (nJ : Nat), ConLeche.fieldHeadAt domJ.1 = some (C, argsJ, nJ) ∧
    C ∈ ci.members.map (·.name) ∧ ci.nP ≤ argsJ.length ∧
    ∀ k, k < ci.nP → argsJ[k]? = some (.bvar (ci.nP + i - 1 - k + nJ))

/-- **An ordinary field of a container datum is not recursive-shaped**
(the container-side bridge of K.23, DESIGN §M.45): at a constructor's
field the datum classifies ORDINARY, the stored constructor's binder is
not a group member applied to the exact parameter variables under its
Π-prefix — what the kernel's classification gives (`mutualCtorKinds`:
ordinary ⟺ no member mentioned) and no `IndRep` clause records.  A
conjunct of the container-side premise `ContainersRep`. -/
@[expose] def IndRepData.OrdNotRec (dJ : IndRepData V) : Prop :=
  ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), dJ.ctorsA[Jc]? = some cAJ →
  ∀ (bsJ : List (Expr × ConLeche.BinderMeta)) (rJ : Expr),
    cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bsJ, rJ) →
  ∀ (i : Nat), i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
  ∀ (domJ : Expr × ConLeche.BinderMeta), bsJ[dJ.nP + i]? = some domJ →
  ∀ (C : Name) (args : List Expr) (n : Nat), ConLeche.fieldHeadAt domJ.1 = some (C, args, n) →
    (∃ t, t < dJ.k ∧ dJ.memberName t = C) → dJ.nP ≤ args.length →
    (∀ k, k < dJ.nP → args[k]? = some (.bvar (dJ.nP + i - 1 - k + n))) → False

/-! ## Kit -/

omit [SetTheory V] in
/-- A pointwise relation across an append splits at the first list's
length. -/
theorem pointwise_append_split {P : Expr → Expr → Prop} {l₁ l₂ m₁ m₂ : List Expr}
    (h : ∀ (k : Nat) (a b : Expr), (l₁ ++ l₂)[k]? = some a → (m₁ ++ m₂)[k]? = some b → P a b)
    (hlen₁ : l₁.length = m₁.length) (hlen : (l₁ ++ l₂).length = (m₁ ++ m₂).length) :
    (∀ (k : Nat) (a b : Expr), l₁[k]? = some a → m₁[k]? = some b → P a b) ∧
    l₂.length = m₂.length ∧
    (∀ (k : Nat) (a b : Expr), l₂[k]? = some a → m₂[k]? = some b → P a b) := by
  refine ⟨fun k a b ha hb => ?_, ?_, fun k a b ha hb => ?_⟩
  · have hk : k < l₁.length := (List.getElem?_eq_some_iff.mp ha).1
    exact h k a b (by rw [List.getElem?_append_left hk]; exact ha)
      (by rw [List.getElem?_append_left (by rw [← hlen₁]; exact hk)]; exact hb)
  · simp only [List.length_append] at hlen
    omega
  · exact h (l₁.length + k) a b
      (by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact ha)
      (by rw [hlen₁, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hb)

omit [SetTheory V] in
/-- The openers of an opening at depth `d` have indices `≥ d`. -/
theorem opener_index_ge {n : Nat} {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars n e d = some (fvs, o)) {i : Nat} {ty : Expr}
    (hmem : Expr.fvar i ty ∈ fvs) : d ≤ i := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hmem
  obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis n hop
  obtain ⟨ty', hty'⟩ := hsh j (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)
  rw [hj] at hty'
  obtain ⟨h, -⟩ := Expr.fvar.inj (Option.some.inj hty')
  omega

omit [SetTheory V] in
/-- **The leaves below the parameter count of an opened field are the
openers**: a leaf of the container's instantiated constructor's field
(and of that field opened further) at an index below `nP` is a leaf of
the instantiated constructor, whose leaves are the parameters. -/
theorem leaves_below_of_opened {nP nF n i : Nat} {cI : Expr} {xFvsC : List Expr} {xrestC : Expr}
    {params : List Expr} (hcIL : Expr.LeavesIn params cI)
    (hopen : ConLeche.openPisAtFvars nF cI nP = some (xFvsC, xrestC))
    {xC : Expr} (hxC : xFvsC[i]? = some xC) {afvsC : List Expr} {oC : Expr}
    (hopC : ConLeche.openPisAtFvars n xC.fvarTypeD (nP + i) = some (afvsC, oC)) :
    ∀ l ∈ oC.fvarLeaves, l.1 < nP → Expr.fvar l.1 l.2 ∈ params := by
  intro l hl hlt
  have hxCsh : ∃ ty, xC = .fvar (nP + i) ty := by
    obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis nF hopen
    obtain ⟨ty, hty⟩ := hsh i (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hxC).1)
    rw [hxC] at hty
    exact ⟨ty, Option.some.inj hty⟩
  obtain ⟨ty, rfl⟩ := hxCsh
  rcases Verify.openPisAtFvars_leaves n hopC l (Or.inl hl) with h₁ | h₁
  · have hl' : l ∈ (Expr.fvar (nP + i) ty).fvarLeaves := by
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ h₁
    rcases Verify.openPisAtFvars_leaves nF hopen l (Or.inr ⟨_, List.mem_of_getElem? hxC, hl'⟩)
      with h₂ | h₂
    · exact hcIL l h₂
    · have := opener_index_ge hopen h₂
      omega
  · have := opener_index_ge hopC h₁
    omega

/-! ## The stored copy field, by its kind -/

omit [SetTheory V] in
/-- The blind mention-freeness of an opened field from its pieces. -/
theorem mentionsConstE_eq_false_of_opened {T : Name} {n : Nat} {e : Expr} {d : Nat}
    {afvs : List Expr} {body : Expr} (hop : ConLeche.openPisAtFvars n e d = some (afvs, body))
    (hdoms : ∀ a ∈ afvs, a.fvarTypeD.mentionsConstE T = false)
    (hbody : body.mentionsConstE T = false) : e.mentionsConstE T = false := by
  cases hE : e.mentionsConstE T with
  | false => rfl
  | true =>
    rcases ConLeche.mentionsConstE_of_openPis n e d hop hE with h | ⟨x, hx, hxm⟩
    · rw [hbody] at h; exact nomatch h
    · rw [hdoms x hx] at hxm; exact nomatch hxm


/-! ## The record's syntactic half, from the stored data -/

omit [SetTheory V] in
/-- A component of a pin `mkAppN (const J lvls) Ds` has the pin's leaves. -/
theorem leavesIn_component {params : List Expr} {J : Name} {lvls : List Level} {Ds : List Expr}
    (h : Expr.LeavesIn params (Expr.mkAppN (.const J lvls) Ds)) {D : Expr} (hD : D ∈ Ds) :
    Expr.LeavesIn params D :=
  Expr.LeavesIn.getAppArgs h (by rw [Expr.getAppArgs_mkAppN]; simpa [Expr.getAppArgs] using hD)

set_option maxHeartbeats 6400000 in
/-- **`CopyCtorWalkFacts` from the STORED data** (DESIGN §M.45): the
copy's stored constructor at the auxiliary datum (its kinds the
kernel's, `MutualOpened` at the pre-block environment), the container's
at its datum, the container's instantiated constructor opened, and —
per field — K.17's witness composed with the restore and the walk's
inverse: the restored stored field is erasure-equal to the container's
instantiated field, or K.17's `whnf` arm holds verbatim
(`WhnfField`).  The residual clause is the caller's (`hresid`). -/
theorem copyCtorWalkFacts_of_stored {μ : CheckMode} {envAux env env₁ : Env} {F : Nat}
    (mp : EnvModelM V μ envAux) {R : ConLeche.RestoreTbl} {st : ElimState}
    {p : ConLeche.NestedParts} {b : MutualBlock}
    {d dJ : IndRepData V} {k₀ base Jc Ja : Nat} {cA cAJ : ConstantVal × Nat}
    {lpsT lpsJ : List Name} {lvls : List Level} {Ds : List Expr} {cI : Expr}
    {ks : List (ConLeche.RecFieldKind × Nat)} {params : List Expr}
    -- the copy's constructor at the auxiliary datum, and its kernel kinds
    (hD : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems Ja)) lpsT cA.1 d.nP cA.2
      (d.nIdxAt (d.mems Ja)) d.resSort d.isProp d.large (d.idxF Ja) (d.dsF Ja) (d.esF Ja)
      (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja) (d.eissF Ja) (d.tssF Ja)
      (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hlpsT : lpsT = p.lps)
    (hMO : MutualOpened env b.members3 b.lps b.nP cA.2 ks (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja))
    (hbnP : b.nP = d.nP)
    (hks : ∀ i, i < cA.2 → (d.ksF Ja).getD i .ordinary = kindAt ks i)
    (hnF : cA.2 = cAJ.2) (htgtLt : ∀ i, d.tgts Ja i < d.k)
    (hdk : d.k = k₀ + st.pins.length)
    (hrealFresh : ∀ t, t < k₀ → env.find? (d.memberName t) = none)
    (hcopyAux : ∀ T ∈ (st.types.map (·.name)).drop k₀, T ∈ R.auxNames)
    -- the container's constructor at its datum
    (hDJ : FixCtorDataI mp.base2 dJ.env₀ (dJ.memberName (dJ.mems Jc)) lpsJ cAJ.1 dJ.nP cAJ.2
      (dJ.nIdxAt (dJ.mems Jc)) dJ.resSort dJ.isProp dJ.large (dJ.idxF Jc) (dJ.dsF Jc) (dJ.esF Jc)
      (dJ.srcsF Jc) (dJ.ksF Jc) (dJ.fvsPF Jc) (dJ.xFvsF Jc) (dJ.xrestF Jc) (dJ.eissF Jc)
      (dJ.tssF Jc) (fun i => dJ.memberName (dJ.tgts Jc i)) (fun i => dJ.nIdxAt (dJ.tgts Jc i)))
    (htgtJLt : ∀ i, dJ.tgts Jc i < dJ.k)
    (hstoredJ : ∀ g, g < dJ.k →
      (∃ (cv : ConstantVal) (caps : IndCaps), env₁.find? (dJ.memberName g) = some (.indInfo cv caps)) ∧
      (env.find? (dJ.memberName g)).isSome = true)
    -- the container's instantiated constructor, opened; the openers
    {xFvsC : List Expr} {xrestC : Expr}
    (hopen : ConLeche.openPisAtFvars cAJ.2 cI d.nP = some (xFvsC, xrestC))
    (hcIL : Expr.LeavesIn params cI)
    (hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty)
    (hparLen : params.length = d.nP)
    -- the pin's components
    (hDsLen : Ds.length = dJ.nP) (hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
    (hDsL : ∀ D ∈ Ds, Expr.LeavesIn params D)
    (hDsMention : ∃ D ∈ Ds, ∃ t, t < k₀ ∧ D.mentionsConstE (d.memberName t) = true)
    -- the container-recursive fields' shape at the instantiated constructor
    (hCshape : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
      ∀ (xJ xC : Expr), (dJ.xFvsF Jc)[i]? = some xJ → xFvsC[i]? = some xC →
      ∃ (n : Nat) (bsC : List (Expr × ConLeche.BinderMeta)) (idxCb : List Expr),
        xC.fvarTypeD.stripPis n = some (bsC,
          Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls) (Ds ++ idxCb)) ∧
        (xJ.fvarTypeD.piBinders).1.length = n)
    -- the pins
    (hgroup : ∀ g, g < dJ.k → ∃ q, st.pins[base + g]? = some q ∧
      q.pin = Expr.mkAppN (.const (dJ.memberName g) lvls) Ds)
    (hnodupP : (st.pins.map (·.pin)).Nodup)
    (hpinName : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q → d.memberName (k₀ + jq) = q.aux)
    (hpinShape : ∀ q ∈ st.pins, ∃ (J' : Name) (lvls' : List Level) (Ds' : List Expr),
      q.pin = Expr.mkAppN (.const J' lvls') Ds' ∧ q.container = J' ∧ Expr.LeavesIn params q.pin ∧
      q.pin.looseBVarsBounded 0 = true)
    (hpinLen : ∀ q ∈ st.pins, ∀ g, g < dJ.k → q.container = dJ.memberName g →
      q.pin.getAppArgs.length = dJ.nP)
    -- the table at the copy's parameter openers
    (hRS : (R.instAt (d.fvsPF Ja)).Named) (hRnP : R.nP = d.nP)
    (hlookS : ∀ q ∈ st.pins, ∃ pin', (R.instAt (d.fvsPF Ja)).pins.lookup q.aux = some pin' ∧
      Expr.ErasedEq pin' q.pin ∧ pin'.looseBVarsBounded 0 = true)
    (hrecS : ∀ q ∈ st.pins, (R.instAt (d.fvsPF Ja)).recMap.lookup q.aux = none)
    (hauxFresh : ∀ n ∈ R.auxNames, env.find? n = none ∧ ∀ t, t < k₀ → d.memberName t ≠ n)
    -- the exclusion (K.23 through the container datum's `OrdNotRec`), in datum form
    (hexcl : ∀ i, i ∉ ConLeche.recIdxOf (dJ.ksF Jc) → i ∈ ConLeche.recIdxOf (d.ksF Ja) →
      k₀ ≤ d.tgts Ja i → ¬ (base ≤ d.tgts Ja i - k₀ ∧ d.tgts Ja i - k₀ < base + dJ.k))
    -- K.17 composed with the restore and W1, per field
    (hfields : ∀ (i : Nat) (x xC : Expr), (d.xFvsF Ja)[i]? = some x → xFvsC[i]? = some xC →
      Expr.ErasedEq (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD) xC.fvarTypeD ∨
      WhnfField μ F env₁ R (d.fvsPF Ja) (d.nP + i) x.fvarTypeD xC.fvarTypeD)
    -- the residual
    (hresid : ∃ (aux : Name) (idx idxC : List Expr),
      d.xrestF Ja = Expr.mkAppN (.const aux (p.lps.map Level.param)) (d.fvsPF Ja ++ idx) ∧
      xrestC = Expr.mkAppN (.const (dJ.memberName (dJ.mems Jc)) lvls) (Ds ++ idxC) ∧
      idx.length = idxC.length ∧
      ∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC) :
    CopyCtorWalkFacts μ F env₁ R st k₀ d.nP cAJ.2 (p.lps.map Level.param) (d.fvsPF Ja) dJ Jc
      (dJ.memberName (dJ.mems Jc)) lvls Ds (d.xFvsF Ja) xFvsC (d.xrestF Ja) xrestC := by
  have hxLen : (d.xFvsF Ja).length = cA.2 := hD.xLen
  have hxCLen : xFvsC.length = cAJ.2 := openPisAtFvars_length _ hopen
  have hpLen : (d.fvsPF Ja).length = d.nP := hD.pLen
  have hRSnP : (d.fvsPF Ja).length = (R.instAt (d.fvsPF Ja)).nP := by
    show _ = R.nP; rw [hRnP, hpLen]
  have hksLenJ : (dJ.ksF Jc).length = cAJ.2 := hDJ.ksLen
  have hxJLen : (dJ.xFvsF Jc).length = cAJ.2 := hDJ.xLen
  have hfvsPBlind : ∀ (T : Name), ∀ a ∈ d.fvsPF Ja, a.mentionsConstE T = false := by
    intro T a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hD.pIdx k a hk
    rfl
  -- (A) a recursive or reflexive copy field opens to its target member at
  -- the parameters, its pieces resolving before the block
  have hcopyShape : ∀ (i : Nat) (x : Expr), (d.xFvsF Ja)[i]? = some x →
      (d.ksF Ja).getD i .ordinary ≠ .ordinary →
      ∃ (n : Nat) (afvs idx : List Expr),
        ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
          Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param))
            (d.fvsPF Ja ++ idx)) ∧
        (x.fvarTypeD.piBinders).1.length = n ∧
        (∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true) ∧
        (∀ e ∈ idx, e.constsResolve env = true) := by
    intro i x hx hnotOrd
    have hi : i < cA.2 := by rw [← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1
    rcases hD.opened.kinds i hi with hord | hrec | hrefl
    · exact absurd hord hnotOrd
    · obtain ⟨hhead, htake, -, -, -, -⟩ := hD.opened.recF i x hx hrec
      obtain ⟨-, -, -, hres, -, -⟩ := hMO.recF i x hx (by rw [← hks i hi]; exact hrec)
      rw [hbnP] at hres
      rw [hlpsT] at hhead
      refine ⟨0, [], x.fvarTypeD.getAppArgs.drop d.nP, ?_, ?_, ?_, hres⟩
      · show some ([], x.fvarTypeD) = _
        rw [← htake, List.take_append_drop, ← hhead, Expr.mkAppN_getApp]
      · rw [piBinders_eq_of_getAppFn_const hhead]
        rfl
      · intro a ha
        exact absurd ha (by simp)
    · obtain ⟨afvs, body, hop, -, -, hhead, htake, -, -, -, -⟩ := hD.opened.reflF i x hx hrefl
      obtain ⟨afvs', body', hop', -, hres₁, -, -, -, hres₂, -, -⟩ :=
        hMO.reflF i x hx (by rw [← hks i hi]; exact hrefl)
      rw [hbnP, hop] at hop'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop')
      rw [hbnP] at hres₂
      rw [hlpsT] at hhead
      refine ⟨_, afvs, body.getAppArgs.drop d.nP, ?_, rfl, hres₁, hres₂⟩
      rw [hop, ← htake, List.take_append_drop, ← hhead, Expr.mkAppN_getApp]
  -- (B) a field into a REAL member mentions no table name, blindly
  have hblindReal : ∀ (i : Nat) (x : Expr) (n : Nat) (afvs idx : List Expr),
      ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
        Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param))
          (d.fvsPF Ja ++ idx)) →
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true) →
      (∀ e ∈ idx, e.constsResolve env = true) →
      d.tgts Ja i < k₀ →
      ∀ m ∈ R.auxNames, x.fvarTypeD.mentionsConstE m = false := by
    intro i x n afvs idx hop hdoms hidx hlt m hm
    refine mentionsConstE_eq_false_of_opened hop
      (fun a ha => Expr.mentionsConstE_eq_false_of_fresh (hdoms a ha) (hauxFresh m hm).1) ?_
    cases hB : (Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param))
        (d.fvsPF Ja ++ idx)).mentionsConstE m with
    | false => rfl
    | true =>
      exfalso
      rcases (ConLeche.mentionsConstE_mkAppN_const_iff _ _ _).mp hB with h | ⟨a, ha, ham⟩
      · exact (hauxFresh m hm).2 _ hlt h
      · rcases List.mem_append.mp ha with ha | ha
        · rw [hfvsPBlind m a ha] at ham; exact nomatch ham
        · rw [Expr.mentionsConstE_eq_false_of_fresh (hidx a ha) (hauxFresh m hm).1] at ham
          exact nomatch ham
  -- (C) a field into a COPY, restored, opens to the pin at its index
  -- arguments, and the container's field then opens to that pin's
  -- container at the pin's components and the index arguments
  have hfire : ∀ (i : Nat) (x xC : Expr), (d.xFvsF Ja)[i]? = some x → xFvsC[i]? = some xC →
      Expr.ErasedEq (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD) xC.fvarTypeD →
      ∀ (n : Nat) (afvs idx : List Expr),
      ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
        Expr.mkAppN (.const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param))
          (d.fvsPF Ja ++ idx)) →
      (x.fvarTypeD.piBinders).1.length = n →
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true) →
      k₀ ≤ d.tgts Ja i →
      ∃ (q : NestedPin) (J' : Name) (lvls' : List Level) (Ds' idxC afvsC : List Expr),
        st.pins[d.tgts Ja i - k₀]? = some q ∧ q.aux = d.memberName (d.tgts Ja i) ∧
        q.container = J' ∧ q.pin = Expr.mkAppN (.const J' lvls') Ds' ∧
        ConLeche.openPisAtFvars n xC.fvarTypeD (d.nP + i)
          = some (afvsC, Expr.mkAppN (.const J' lvls') (Ds' ++ idxC)) ∧
        (xC.fvarTypeD.piBinders).1.length = n ∧
        (∀ (k : Nat) (a aC : Expr), afvs[k]? = some a → afvsC[k]? = some aC →
          Expr.ErasedEq a.fvarTypeD aC.fvarTypeD) ∧
        (∃ (bsA bsC : List (Expr × ConLeche.BinderMeta)) (rA rC : Expr),
          x.fvarTypeD.stripPis n = some (bsA, rA) ∧ xC.fvarTypeD.stripPis n = some (bsC, rC) ∧
          ∀ (k : Nat) (bA bC : Expr × ConLeche.BinderMeta), bsA[k]? = some bA → bsC[k]? = some bC →
            bA.2 = bC.2) ∧
        idx.length = idxC.length ∧
        (∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC) := by
    intro i x xC hx hxC hE n afvs idx hop hnA hdoms hge
    have hjq : d.tgts Ja i - k₀ < st.pins.length := by have := htgtLt i; omega
    obtain ⟨q, hq⟩ : ∃ q, st.pins[d.tgts Ja i - k₀]? = some q :=
      ⟨_, List.getElem?_eq_getElem hjq⟩
    have hqa : q.aux = d.memberName (d.tgts Ja i) := by
      rw [← hpinName _ q hq, show k₀ + (d.tgts Ja i - k₀) = d.tgts Ja i by omega]
    have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
    obtain ⟨J', lvls', Ds', hqp, hqc, hqL, hqB⟩ := hpinShape q hqmem
    obtain ⟨pin', hlook, hpinE, hpinC⟩ := hlookS q hqmem
    have hrec := hrecS q hqmem
    rw [hqa] at hlook hrec
    obtain ⟨o, hopR, hoE⟩ := ConLeche.restoreI_copyField hRS hop
      (fun a ha m hm => Expr.not_mentionsConst_of_fresh (hdoms a ha) (hauxFresh m hm).1)
      hlook hpinC hRSnP hrec
    have hoE' : Expr.ErasedEq o (Expr.mkAppN (.const J' lvls') (Ds' ++ idx)) := by
      rw [Expr.mkAppN_append, ← hqp]
      exact hoE.trans (Expr.ErasedEq.mkAppN idx idx hpinE rfl (fun k a₁ a₂ h₁ h₂ => by
        rw [h₁] at h₂; obtain rfl := Option.some.inj h₂; exact Expr.ErasedEq.rfl _))
    obtain ⟨afvsC, oC, hopC, hoC, hlenC', hafvs⟩ := ConLeche.openPisAtFvars_erasedEq hE hopR
    have hoCE : Expr.ErasedEq oC (Expr.mkAppN (.const J' lvls') (Ds' ++ idx)) :=
      hoC.symm.trans hoE'
    -- `oC`'s spine: the head, and the arguments against the pin's
    -- components and the index arguments
    have hfnC : oC.getAppFn = .const J' lvls' :=
      (Expr.ErasedEq.getAppFn_const_iff hoCE).mpr (by rw [Expr.getAppFn_mkAppN]; rfl)
    obtain ⟨-, hlenE, hargsE⟩ := hoCE.getApp
    rw [Expr.getAppArgs_mkAppN] at hlenE hargsE
    simp only [Expr.getAppArgs, List.nil_append] at hlenE hargsE
    have hDs'L : Ds'.length ≤ oC.getAppArgs.length := by rw [hlenE]; simp
    obtain ⟨hDsE, hidxLen, hidxE⟩ := pointwise_append_split (P := Expr.ErasedEq)
      (l₁ := oC.getAppArgs.take Ds'.length) (l₂ := oC.getAppArgs.drop Ds'.length)
      (m₁ := Ds') (m₂ := idx)
      (by rw [List.take_append_drop]; exact hargsE)
      (by rw [List.length_take]; omega)
      (by rw [List.take_append_drop]; exact hlenE)
    -- the components agree exactly: the leaves below the parameters are
    -- the openers on both sides
    have hqLeaves : ∀ l ∈ q.pin.fvarLeaves, l.1 < d.nP ∧ Expr.fvar l.1 l.2 ∈ params := by
      intro l hl
      have hm := hqL l hl
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
      obtain ⟨ty, hty⟩ := hshape j _ hj
      obtain ⟨rfl, -⟩ := Expr.fvar.inj hty
      exact ⟨by rw [← hparLen]; exact (List.getElem?_eq_some_iff.mp hj).1, hm⟩
    have hDs'Eq : oC.getAppArgs.take Ds'.length = Ds' := by
      refine List.ext_getElem? fun k => ?_
      cases hk : Ds'[k]? with
      | none =>
        rw [List.getElem?_eq_none_iff] at hk ⊢
        rw [List.length_take]; omega
      | some a =>
        have hkLt : k < Ds'.length := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨b, hb⟩ : ∃ b, (oC.getAppArgs.take Ds'.length)[k]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by rw [List.length_take]; omega)⟩
        rw [hb]
        congr 1
        refine Expr.ErasedEq.eq_of_leaves_below hshape (nP := d.nP) (hDsE k b a hb hk) ?_ ?_
        · intro l hl hlt
          refine leaves_below_of_opened hcIL hopen hxC hopC l ?_ hlt
          exact fvarLeaves_getAppArgs (List.mem_of_mem_take (List.mem_of_getElem? hb)) l hl
        · intro l hl
          refine hqLeaves l ?_
          rw [hqp]
          have hmemArgs : a ∈ (Expr.mkAppN (.const J' lvls') Ds').getAppArgs := by
            rw [Expr.getAppArgs_mkAppN]
            simpa [Expr.getAppArgs] using List.mem_of_getElem? hk
          exact fvarLeaves_getAppArgs hmemArgs l hl
    have hoCspine : oC = Expr.mkAppN (.const J' lvls') (Ds' ++ oC.getAppArgs.drop Ds'.length) := by
      have := Expr.mkAppN_getApp oC
      rw [hfnC, ← List.take_append_drop Ds'.length oC.getAppArgs, hDs'Eq] at this
      exact this.symm
    -- the Π-lengths agree
    have hnC : (xC.fvarTypeD.piBinders).1.length = n := by
      obtain ⟨bsC, rC, hsC, -, -, hrC⟩ := Verify.openPisAtFvars_stripPis n hopC
      rw [piBinders_of_stripPis n hsC, List.length_append, stripPis_length' n hsC]
      have hfnRC : rC.getAppFn = .const J' lvls' := by
        have h1 : (Expr.instSeq (Verify.openFvars (d.nP + i) n) (n - 1) rC).getAppFn
            = .const J' lvls' :=
          (Expr.ErasedEq.getAppFn_const_iff hrC).mp hfnC
        exact (ConLeche.getAppFn_instSeq_const_iff (ConLeche.openFvars_allFvars _ _)
          (by rw [Verify.openFvars_length]; omega)).mp h1
      rw [piBinders_eq_of_getAppFn_const hfnRC]
      rfl
    -- the binder data agree: the restored field keeps the copy's, the
    -- erasure equality carries them to the container's
    have hmeta : ∃ (bsA bsC : List (Expr × ConLeche.BinderMeta)) (rA rC : Expr),
        x.fvarTypeD.stripPis n = some (bsA, rA) ∧ xC.fvarTypeD.stripPis n = some (bsC, rC) ∧
        ∀ (k : Nat) (bA bC : Expr × ConLeche.BinderMeta), bsA[k]? = some bA → bsC[k]? = some bC →
          bA.2 = bC.2 := by
      obtain ⟨bsA, rA, hsA, -, -, -⟩ := Verify.openPisAtFvars_stripPis n hop
      obtain ⟨bsC, rC, hsC, -, -, -⟩ := Verify.openPisAtFvars_stripPis n hopC
      have hsR := ConLeche.restoreI_stripPis hRS n hsA
      obtain ⟨bsR, rR, hsR', hlenR, hbsR, -⟩ := Expr.ErasedEq.stripPis_inv n hE hsC
      rw [hsR] at hsR'
      obtain ⟨hbsEq, -⟩ := Prod.mk.inj (Option.some.inj hsR')
      refine ⟨bsA, bsC, rA, rC, hsA, hsC, fun k bA bC hbA hbC => ?_⟩
      have := hbsR k (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) bA.1, bA.2) bC
        (by rw [← hbsEq, List.getElem?_map, hbA]; rfl) hbC
      exact this.2
    refine ⟨q, J', lvls', Ds', oC.getAppArgs.drop Ds'.length, afvsC, hq, hqa, hqc, hqp,
      by rw [hopC]; exact congrArg (fun z => some (afvsC, z)) hoCspine, hnC, hafvs, hmeta,
      hidxLen.symm, fun k e eC he heC => (hidxE k eC e heC he).symm⟩
  -- ## the record
  refine ⟨hxCLen, ?_, hresid, ?_, ?_⟩
  · intro k x hx
    obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis cAJ.2 hopen
    obtain ⟨ty, hty⟩ := hsh k (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx] at hty
    exact ⟨ty, Option.some.inj hty⟩
  · -- ## fieldRec
    intro i x xC hx hxC hi
    have hiJ : i < cAJ.2 := by rw [← hksLenJ]; exact (mem_recIdxOf.mp hi).1
    have hiA : i < cA.2 := by rw [hnF]; exact hiJ
    obtain ⟨xJ, hxJ⟩ : ∃ xJ, (dJ.xFvsF Jc)[i]? = some xJ :=
      ⟨_, List.getElem?_eq_getElem (by rw [hxJLen]; exact hiJ)⟩
    obtain ⟨n', bsC, idxCb, hsC, hnJ⟩ := hCshape i hi xJ xC hxJ hxC
    have htgtJ := htgtJLt i
    obtain ⟨⟨cvJ, capsJ, hfJ₁⟩, hfJenv⟩ := hstoredJ _ htgtJ
    -- the restored stored field is the container's instantiated field
    have hE : Expr.ErasedEq (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD)
        xC.fvarTypeD := by
      rcases hfields i x xC hx hxC with hE | ⟨dm, dsR, hdm, hwhnf, hdsR, -, -, -⟩
      · exact hE
      · have := ConLeche.whnf_eq_of_erasedEq_pis_indApp hfJ₁ hdm hsC hwhnf
        subst this
        exact hdsR.symm.trans hdm
    -- the container's field is a Π-tower of length `n'` over a member application
    have hCpi : (xC.fvarTypeD.piBinders).1.length = n' := by
      rw [piBinders_of_stripPis n' hsC, List.length_append,
        piBinders_eq_of_getAppFn_const (by rw [Expr.getAppFn_mkAppN]; rfl)]
      simp [stripPis_length' n' hsC]
    by_cases hordA : (d.ksF Ja).getD i .ordinary = .ordinary
    · -- ordinary: the field is its own restoration, so it is the
      -- container's field up to erasure — which carries the pin's
      -- components, one of which mentions a block member: the copy's
      -- field cannot resolve before the block
      exfalso
      have hres := hMO.ord i x hx (by rw [← hks i hiA]; exact hordA)
      have hself : ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD = x.fvarTypeD :=
        ConLeche.restoreI_eq_self hRS _ (fun m hm =>
          Expr.mentionsConstE_eq_false_of_fresh hres (hauxFresh m hm).1)
      rw [hself] at hE
      obtain ⟨bsA, rA, hsA, -, -, hrA⟩ := Expr.ErasedEq.stripPis_inv n' hE hsC
      obtain ⟨Dk, hDk, t, htk, hTm⟩ := hDsMention
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hDk
      obtain ⟨-, hlenArgs, hargs⟩ := hrA.getApp
      rw [Expr.getAppArgs_mkAppN] at hlenArgs hargs
      simp only [Expr.getAppArgs, List.nil_append] at hlenArgs hargs
      have hkLt : k < Ds.length := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨ak, hak⟩ : ∃ ak, rA.getAppArgs[k]? = some ak :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenArgs, List.length_append]; omega)⟩
      have hakE := hargs k ak Dk hak (by rw [List.getElem?_append_left hkLt]; exact hk)
      have hakM : ak.mentionsConstE (d.memberName t) = true := by
        rw [Expr.mentionsConstE_erasedEq hakE]; exact hTm
      have hrAM : rA.mentionsConstE (d.memberName t) = true := by
        rw [← Expr.mkAppN_getApp rA, ConLeche.mentionsConstE_mkAppN_iff]
        exact Or.inr ⟨ak, List.mem_of_getElem? hak, hakM⟩
      have hxM : x.fvarTypeD.mentionsConst (d.memberName t) = true :=
        Expr.mentionsConst_of_mentionsConstE _ (Expr.stripPis_mentionsConstE n' hsA hrAM)
      have := Expr.not_mentionsConst_of_fresh hres (hrealFresh t htk)
      rw [hxM] at this
      exact nomatch this
    · obtain ⟨n, afvs, idx, hop, hnA, hdoms, hidx⟩ := hcopyShape i x hx hordA
      by_cases hlt : d.tgts Ja i < k₀
      · -- into a REAL member: the field is its own restoration, so the
        -- container's field is headed by a fresh name — but it is headed
        -- by a stored container
        exfalso
        have hself : ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD = x.fvarTypeD :=
          ConLeche.restoreI_eq_self hRS _ (hblindReal i x n afvs idx hop hdoms hidx hlt)
        rw [hself] at hE
        have hnn : n = n' := by
          rw [← hnA, ← hCpi]
          exact Expr.ErasedEq.piBinders_length' hE
        subst hnn
        obtain ⟨bsA, rA, hsA, -, -, hrA⟩ := Expr.ErasedEq.stripPis_inv n hE hsC
        obtain ⟨bsA', rA', hsA', -, -, -⟩ := Verify.openPisAtFvars_stripPis n hop
        rw [hsA'] at hsA
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hsA)
        have hbodyE := Verify.openPisAtFvars_instSeq n hop hsA'
        have hF : Expr.AllFvars afvs := by
          intro a ha
          obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
          obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis n hop
          obtain ⟨ty, hty⟩ := hsh j (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)
          rw [hj] at hty
          exact ⟨_, _, Option.some.inj hty⟩
        have hheadA' : rA'.getAppFn
            = .const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param) := by
          have h1 : (Expr.instSeq afvs (n - 1) rA').getAppFn
              = .const (d.memberName (d.tgts Ja i)) (p.lps.map Level.param) := by
            rw [← hbodyE, Expr.getAppFn_mkAppN]; rfl
          exact (ConLeche.getAppFn_instSeq_const_iff hF (by
            rw [openPisAtFvars_length n hop]; omega)).mp h1
        have hheadC : rA'.getAppFn = .const (dJ.memberName (dJ.tgts Jc i)) lvls :=
          (Expr.ErasedEq.getAppFn_const_iff hrA).mpr (by rw [Expr.getAppFn_mkAppN]; rfl)
        rw [hheadA'] at hheadC
        have hnameEq := (Expr.const.inj hheadC).1
        have hfresh := hrealFresh _ hlt
        rw [← hnameEq, hfresh] at hfJenv
        exact nomatch hfJenv
      · -- into a COPY: the restored field opens to the pin at the index
        -- arguments, and that pin is the group-mate's
        have hge : k₀ ≤ d.tgts Ja i := Nat.le_of_not_lt hlt
        obtain ⟨q, J', lvls', Ds', idxC, afvsC, hq, hqa, hqc, hqp, hopC, hnC, hafvs, hmeta,
          hidxLen, hidxE⟩ := hfire i x xC hx hxC hE n afvs idx hop hnA hdoms hge
        -- the container's opened body, from its strip
        have hnn : n = n' := by rw [← hnC, hCpi]
        subst hnn
        have hoCE : Expr.mkAppN (.const J' lvls') (Ds' ++ idxC)
            = Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls)
                (Ds ++ idxCb.map (Expr.instSeq afvsC (n - 1))) := by
          have h1 := Verify.openPisAtFvars_instSeq n hopC hsC
          rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const _ _) rfl,
            List.map_append] at h1
          rw [h1]
          congr 2
          rw [List.map_congr_left (fun D hD => Expr.instSeq_eq_self afvsC (n - 1) (hDsC D hD)),
            List.map_id']
        have hfnE := congrArg Expr.getAppFn hoCE
        rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at hfnE
        simp only [Expr.getAppFn, Expr.const.injEq] at hfnE
        obtain ⟨hJ'E, hlvlsE⟩ := hfnE
        have hargsE := congrArg Expr.getAppArgs hoCE
        rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at hargsE
        simp only [Expr.getAppArgs, List.nil_append] at hargsE
        have hDs'Len : Ds'.length = Ds.length := by
          have := hpinLen q (List.mem_of_getElem? hq) _ htgtJ (by rw [hqc, hJ'E])
          rw [hqp, Expr.getAppArgs_mkAppN] at this
          simp only [Expr.getAppArgs, List.nil_append] at this
          rw [this, hDsLen]
        have hDs'Eq : Ds' = Ds := by
          have := congrArg (List.take Ds'.length) hargsE
          rw [List.take_left, hDs'Len, List.take_left] at this
          exact this
        subst hDs'Eq
        subst hJ'E
        subst hlvlsE
        refine ⟨?_, n, afvs, afvsC, d.memberName (d.tgts Ja i), dJ.memberName (dJ.tgts Jc i),
          lvls', Ds', idx, idxC, hop, hopC, hnA, hnC, hafvs, hmeta, hidxLen, hidxE,
          q, List.mem_of_getElem? hq, hqa, hqc, hqp, hqp⟩
        intro xJ' hxJ'
        rw [hxJ] at hxJ'
        obtain rfl := Option.some.inj hxJ'
        rw [hnJ, hnA]
  · -- ## fieldOrd
    intro i x xC hx hxC hi
    have hiA : i < cA.2 := by rw [← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1
    rcases hfields i x xC hx hxC with hE | hW
    · by_cases hordA : (d.ksF Ja).getD i .ordinary = .ordinary
      · -- copy-ordinary: unfired
        have hres := hMO.ord i x hx (by rw [← hks i hiA]; exact hordA)
        have hblind : ∀ m ∈ R.auxNames, x.fvarTypeD.mentionsConstE m = false := fun m hm =>
          Expr.mentionsConstE_eq_false_of_fresh hres (hauxFresh m hm).1
        rw [ConLeche.restoreI_eq_self hRS _ hblind] at hE
        exact Or.inl ⟨hE, fun T hT => hblind T (hcopyAux T hT)⟩
      · obtain ⟨n, afvs, idx, hop, hnA, hdoms, hidx⟩ := hcopyShape i x hx hordA
        by_cases hlt : d.tgts Ja i < k₀
        · -- into a REAL member: unfired
          have hblind := hblindReal i x n afvs idx hop hdoms hidx hlt
          rw [ConLeche.restoreI_eq_self hRS _ hblind] at hE
          exact Or.inl ⟨hE, fun T hT => hblind T (hcopyAux T hT)⟩
        · -- into a COPY: a fire whose pin is outside the group
          have hge : k₀ ≤ d.tgts Ja i := Nat.le_of_not_lt hlt
          obtain ⟨q, J', lvls', Ds', idxC, afvsC, hq, hqa, hqc, hqp, hopC, hnC, hafvs, hmeta,
            hidxLen, hidxE⟩ := hfire i x xC hx hxC hE n afvs idx hop hnA hdoms hge
          refine Or.inr (Or.inl ⟨n, afvs, afvsC, d.memberName (d.tgts Ja i), J', lvls', Ds', idx,
            idxC, hop, hopC, hnA, hnC, hafvs, hmeta, hidxLen, hidxE, q, List.mem_of_getElem? hq,
            hqa, hqc, hqp, ?_⟩)
          intro g hg hqg
          obtain ⟨qm, hqm, hqmp⟩ := hgroup g hg
          have hjq : d.tgts Ja i - k₀ = base + g :=
            pins_index_inj hnodupP hq hqm (by rw [hqg, hqmp])
          have hrecA : i ∈ ConLeche.recIdxOf (d.ksF Ja) := by
            refine mem_recIdxOf.mpr ⟨by rw [hD.ksLen]; exact hiA, ?_⟩
            rcases hD.opened.kinds i hiA with h | h | h
            · exact absurd h hordA
            · exact Or.inl h
            · exact Or.inr h
          exact hexcl i hi hrecA hge ⟨by omega, by omega⟩
    · exact Or.inr (Or.inr hW)

end ConLeche.Model
