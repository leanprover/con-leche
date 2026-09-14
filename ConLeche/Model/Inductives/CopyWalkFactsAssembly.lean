module

public import ConLeche.Model.Inductives.CopyWalkFactsRun
import ConLeche.Verify.Inductives.NestedRestoreWalk
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Inductives.ContainerWalk
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels

public section

/-!
# The walk's facts from the run: the pieces (task #279 M-D′, step (1), DESIGN §M.45)

The hypotheses of `copyCtorWalkFacts_of_stored` that need their own
derivation from the run's data:

* **`containerRecField_shape`** — at a field the CONTAINER classifies
  recursive or reflexive, the container's constructor instantiated at
  the pin has, at that field, a Π-tower over the target member at the
  pin's components and index arguments: the container's opened field is
  the target at its parameter VARIABLES (`FixOpened.recF`/`reflF`), so
  its binder in the stored constructor carries the parameter BOUND
  variables in the exact positions (`instSeq_bvar`), which the pin's
  instantiation sends to the components (`map_instSeq_structPsAt`); the
  level instantiation sends the container's level parameters to the
  pin's levels because they are DISTINCT (K.21, `map_subst_params_nodup`).
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

/-! ## The parameter positions of a binder -/

omit [SetTheory V] in
/-- `instSeq` at a bound variable above the cut: the variable, lowered
past the arguments. -/
theorem instSeq_bvar_gt :
    ∀ (args : List Expr) (t m : Nat), args.length ≤ t + 1 → t < m →
      Expr.instSeq args t (.bvar m) = .bvar (m - args.length)
  | [], t, m, _, _ => rfl
  | a :: as, t, m, hlen, h => by
    show Expr.instSeq as (t - 1) ((Expr.bvar m).instantiate1 a t) = _
    rw [Expr.instantiate1_bvar, if_neg (by omega), if_pos (by omega)]
    cases t with
    | zero =>
      have : as = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst this
      rfl
    | succ t =>
      rw [instSeq_bvar_gt as (t + 1 - 1) (m - 1) (by simp only [List.length_cons] at hlen; omega)
        (by omega)]
      simp only [List.length_cons]
      congr 1
      omega

omit [SetTheory V] in
/-- **`instSeq` at a bound variable is a variable or an argument**, and
an argument exactly when the variable is within the cut's window. -/
theorem instSeq_bvar_window (args : List Expr) (hC : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (t m : Nat) (hlen : args.length ≤ t + 1) :
    (∃ j, Expr.instSeq args t (.bvar m) = .bvar j) ∨
    (m ≤ t ∧ t - m < args.length ∧ args[t - m]? = some (Expr.instSeq args t (.bvar m))) := by
  by_cases h1 : t < m
  · exact Or.inl ⟨_, instSeq_bvar_gt args t m hlen h1⟩
  · by_cases h2 : m + args.length ≤ t
    · exact Or.inl ⟨m, ConLeche.instSeq_bvar_lt args t m h2⟩
    · exact Or.inr ⟨by omega, by omega, ConLeche.Expr.instSeq_bvar args t m hC (by omega) (by omega)⟩

omit [SetTheory V] in
/-- An fvar-free term that instantiates (at variables) to a variable is
a bound variable of the cut's window. -/
theorem bvar_of_instSeq_fvar {XS : List Expr} (hXS : Expr.AllFvars XS) {t : Nat}
    (hlen : XS.length ≤ t + 1) {a : Expr} (haF : a.hasFvar = false) {j : Nat} {ty : Expr}
    (h : Expr.instSeq XS t a = .fvar j ty) :
    ∃ m, a = .bvar m ∧ m ≤ t ∧ t - m < XS.length ∧ XS[t - m]? = some (.fvar j ty) := by
  have hXSC : ∀ x ∈ XS, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨k, ty', rfl⟩ := hXS x hx
    rfl
  cases a with
  | bvar m =>
    rcases instSeq_bvar_window XS hXSC t m hlen with ⟨j', hj'⟩ | ⟨hm₁, hm₂, hm₃⟩
    · rw [hj'] at h; exact nomatch h
    · exact ⟨m, rfl, hm₁, hm₂, by rw [hm₃, h]⟩
  | fvar _ _ => simp [Expr.hasFvar] at haF
  | sort u => rw [Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
  | const c us => rw [Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
  | lit l => rw [Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
  | app f x => rw [Expr.instSeq_app] at h; exact nomatch h
  | lam d b m => rw [ConLeche.instSeq_lam _ _ _ _ _ hlen] at h; exact nomatch h
  | forallE d b m => rw [Expr.instSeq_forallE _ _ _ _ _ hlen] at h; exact nomatch h
  | letE ty' v b => rw [ConLeche.instSeq_letE _ _ _ _ _ hlen] at h; exact nomatch h
  | proj s i x => rw [ConLeche.instSeq_proj] at h; exact nomatch h

omit [SetTheory V] in
/-- A binder whose opened form is headed by a constant applied first to
the parameter openers carries, in the stored (bvar) form, the parameter
BOUND variables at those positions: `structPsAt` at the binder's own
depth. -/
theorem params_of_opened_spine {XS : List Expr} (hXS : Expr.AllFvars XS)
    (hXSsh : ∀ (j : Nat) (x : Expr), XS[j]? = some x → ∃ ty, x = .fvar j ty)
    {t : Nat} (hlen' : XS.length ≤ t + 1) (hlen : XS ≠ [] → XS.length = t + 1) {B : Expr}
    (hBnf : B.hasFvar = false)
    {c : Name} {us : List Level} (hhead : (Expr.instSeq XS t B).getAppFn = .const c us)
    {nPJ : Nat} (hnPJ : nPJ ≤ XS.length)
    (htake : ∀ j, j < nPJ → ∃ ty, (Expr.instSeq XS t B).getAppArgs[j]? = some (.fvar j ty))
    (hlenArgs : nPJ ≤ (Expr.instSeq XS t B).getAppArgs.length) :
    B.getAppFn = .const c us ∧
    B.getAppArgs.take nPJ = ConLeche.structPsAt (XS.length - nPJ) nPJ ∧
    nPJ ≤ B.getAppArgs.length := by
  have hheadB : B.getAppFn = .const c us :=
    (ConLeche.getAppFn_instSeq_const_iff hXS hlen').mp hhead
  have hspine := Expr.mkAppN_getApp B
  rw [hheadB] at hspine
  have hinst : Expr.instSeq XS t B
      = Expr.mkAppN (.const c us) (B.getAppArgs.map (Expr.instSeq XS t)) := by
    have := congrArg (Expr.instSeq XS t) hspine
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const c us) rfl] at this
    exact this.symm
  rw [hinst, Expr.getAppArgs_mkAppN] at htake hlenArgs
  simp only [Expr.getAppArgs, List.nil_append] at htake hlenArgs
  have hlenB : nPJ ≤ B.getAppArgs.length := by
    rw [List.length_map] at hlenArgs
    exact hlenArgs
  refine ⟨hheadB, ?_, hlenB⟩
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < nPJ
  · rw [List.getElem?_take_of_lt hj]
    obtain ⟨a, ha⟩ : ∃ a, B.getAppArgs[j]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ty, hmap⟩ := htake j hj
    rw [List.getElem?_map, ha] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    have haF : a.hasFvar = false := hasFvar_getAppArgs hBnf a (List.mem_of_getElem? ha)
    obtain ⟨m, rfl, hm₁, hm₂, hm₃⟩ := bvar_of_instSeq_fvar hXS hlen' haF hmap
    obtain ⟨ty', hty'⟩ := hXSsh (t - m) _ hm₃
    obtain ⟨hj', -⟩ := Expr.fvar.inj hty'
    have hXSne : XS ≠ [] := by
      intro h0
      rw [h0] at hm₂
      simp at hm₂
    have hlenE := hlen hXSne
    have hmE : m = XS.length - nPJ + nPJ - 1 - j := by omega
    rw [ha, hmE]
    simp [ConLeche.structPsAt, List.getElem?_map, List.getElem?_range hj]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_take]; omega),
      List.getElem?_eq_none_iff.mpr (by simp [ConLeche.structPsAt]; omega)]


/-! ## The container's recursive fields at the pin -/

omit [SetTheory V] in
/-- `structPsAt` is level-blind. -/
theorem structPsAt_instantiateLevelParams (o nP : Nat) (ks : List Name) (us : List Level) :
    (ConLeche.structPsAt o nP).map (Expr.instantiateLevelParams ks us) = ConLeche.structPsAt o nP := by
  unfold ConLeche.structPsAt
  rw [List.map_map]
  rfl

omit [SetTheory V] in
/-- The parameter positions of a spine, instantiated at the pin's
components: the components. -/
theorem spine_at_components {c : Name} {us : List Level} {args : List Expr} {o nP t : Nat}
    (htake : args.take nP = ConLeche.structPsAt o nP) (hle : nP ≤ args.length)
    {Ds : List Expr} (hDsLen : Ds.length = nP) (hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
    (ht : 0 < nP → t = nP + o - 1) :
    Expr.instSeq Ds t (Expr.mkAppN (.const c us) args)
      = Expr.mkAppN (.const c us) (Ds ++ (args.drop nP).map (Expr.instSeq Ds t)) := by
  rcases Nat.eq_zero_or_pos nP with h0 | hpos
  · subst h0
    have hDsnil : Ds = [] := List.eq_nil_of_length_eq_zero hDsLen
    subst hDsnil
    rw [List.drop_zero, List.nil_append, List.map_id'' (f := Expr.instSeq [] t) (fun _ => rfl)]
    rfl
  rw [ht hpos]
  have hargs : args = ConLeche.structPsAt o nP ++ args.drop nP := by
    rw [← htake, List.take_append_drop]
  have key : ∀ (rest : List Expr),
      Expr.instSeq Ds (nP + o - 1) (Expr.mkAppN (.const c us) (ConLeche.structPsAt o nP ++ rest))
        = Expr.mkAppN (.const c us) (Ds ++ rest.map (Expr.instSeq Ds (nP + o - 1))) := by
    intro rest
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const c us) rfl, List.map_append,
      show nP + o - 1 = o + nP - 1 by omega, ConLeche.map_instSeq_structPsAt Ds o nP hDsC (by omega),
      List.take_of_length_le (by omega)]
  have := key (args.drop nP)
  rwa [← hargs] at this

omit [SetTheory V] in
/-- A level-instantiated spine at a parameter head. -/
theorem instantiateLevelParams_spine {e : Expr} {c : Name} {lps : List Name} {lvls : List Level}
    (hnd : lps.Nodup) (hlen : lvls.length = lps.length)
    (hhead : e.getAppFn = .const c (lps.map Level.param)) :
    (e.instantiateLevelParams lps lvls).getAppFn = .const c lvls ∧
    (e.instantiateLevelParams lps lvls).getAppArgs
      = e.getAppArgs.map (Expr.instantiateLevelParams lps lvls) := by
  have hspine := Expr.mkAppN_getApp e
  rw [hhead] at hspine
  have hconst : (Expr.const c (lps.map Level.param)).instantiateLevelParams lps lvls
      = .const c lvls := by
    simp only [Expr.instantiateLevelParams]
    rw [ConLeche.map_subst_params_nodup hnd hlen.symm]
  refine ⟨?_, ?_⟩
  · rw [Expr.getAppFn_instantiateLevelParams, hhead, hconst]
  · rw [← hspine, ConLeche.instantiateLevelParams_mkAppN, hconst, Expr.getAppArgs_mkAppN,
      Expr.getAppArgs_mkAppN]
    rfl

set_option maxHeartbeats 3200000 in
/-- **The container's constructor instantiated at the pin, at a
container-recursive field**: a Π-tower over the target member at the
pin's components and index arguments, of the container's own Π-length
(DESIGN §M.45).  The container's opened field is the target at its
parameter VARIABLES (`FixOpened.recF`/`reflF`), so the stored binder
carries the parameter BOUND variables in the exact positions
(`params_of_opened_spine`); the level instantiation sends the container's
level parameters to the pin's levels (K.21's `Nodup`), and the pin's
instantiation sends those bound variables to the components. -/
theorem containerRecField_shape {μ : CheckMode} {envAux : Env} (mp : EnvModelM V μ envAux)
    {dJ : IndRepData V} {Jc : Nat} {cAJ : ConstantVal × Nat} {lpsJ : List Name}
    {lvls : List Level} {Ds : List Expr} {cI : Expr} {nP : Nat}
    (hDJ : FixCtorDataI mp.base2 dJ.env₀ (dJ.memberName (dJ.mems Jc)) lpsJ cAJ.1 dJ.nP cAJ.2
      (dJ.nIdxAt (dJ.mems Jc)) dJ.resSort dJ.isProp dJ.large (dJ.idxF Jc) (dJ.dsF Jc) (dJ.esF Jc)
      (dJ.srcsF Jc) (dJ.ksF Jc) (dJ.fvsPF Jc) (dJ.xFvsF Jc) (dJ.xrestF Jc) (dJ.eissF Jc)
      (dJ.tssF Jc) (fun i => dJ.memberName (dJ.tgts Jc i)) (fun i => dJ.nIdxAt (dJ.tgts Jc i)))
    (hlpsNodup : lpsJ.Nodup) (hlvlsLen : lvls.length = lpsJ.length)
    (hDsLen : Ds.length = dJ.nP) (hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
    (hcI : Expr.instPis (cAJ.1.type.instantiateLevelParams lpsJ lvls) Ds = some cI)
    (hJnf : cAJ.1.type.hasFvar = false)
    {xFvsC : List Expr} {xrestC : Expr}
    (hopen : ConLeche.openPisAtFvars cAJ.2 cI nP = some (xFvsC, xrestC)) :
    ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
      ∀ (xJ xC : Expr), (dJ.xFvsF Jc)[i]? = some xJ → xFvsC[i]? = some xC →
      ∃ (n : Nat) (bsC : List (Expr × ConLeche.BinderMeta)) (idxCb : List Expr),
        xC.fvarTypeD.stripPis n = some (bsC,
          Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls) (Ds ++ idxCb)) ∧
        (xJ.fvarTypeD.piBinders).1.length = n := by
  intro i hi xJ xC hxJ hxC
  have hiJ : i < cAJ.2 := by rw [← hDJ.ksLen]; exact (mem_recIdxOf.mp hi).1
  -- the container's stored constructor, opened over parameters and fields
  obtain ⟨crestJ, hopP, hopF⟩ := hDJ.opens
  have hopJ : ConLeche.openPisAtFvars (dJ.nP + cAJ.2) cAJ.1.type 0
      = some (dJ.fvsPF Jc ++ dJ.xFvsF Jc, dJ.xrestF Jc) :=
    ConLeche.openPisAtFvars_add' _ hopP (by rw [Nat.zero_add]; exact hopF)
  obtain ⟨bsJ, rJ, hsJ, hlenJ, hshJ, -⟩ := Verify.openPisAtFvars_stripPis _ hopJ
  have hbsJlen : bsJ.length = dJ.nP + cAJ.2 := stripPis_length' _ hsJ
  obtain ⟨bJ, hbJ⟩ : ∃ bJ, bsJ[dJ.nP + i]? = some bJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hxJ' := openPisAtFvars_binder _ hopJ hsJ (dJ.nP + i) bJ hbJ
  have hxJapp : (dJ.fvsPF Jc ++ dJ.xFvsF Jc)[dJ.nP + i]? = some xJ := by
    rw [List.getElem?_append_right (by rw [hDJ.pLen]; omega), hDJ.pLen, Nat.add_sub_cancel_left]
    exact hxJ
  rw [hxJapp] at hxJ'
  obtain rfl := Option.some.inj hxJ'
  simp only [Expr.fvarTypeD]
  -- the openers up to the field, and their shape
  have hXSlen : ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)).length = dJ.nP + i := by
    rw [List.length_take, List.length_append, hDJ.pLen, hDJ.xLen]; omega
  have hshJ' : ∀ (j : Nat) (x : Expr), (dJ.fvsPF Jc ++ dJ.xFvsF Jc)[j]? = some x →
      ∃ ty, x = .fvar j ty := by
    intro j x hx
    have hj : j < dJ.nP + cAJ.2 := by rw [← hlenJ]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨ty, hty⟩ := hshJ j hj
    rw [hx] at hty
    exact ⟨ty, by rw [Nat.zero_add] at hty; exact Option.some.inj hty⟩
  have hXSsh : ∀ (j : Nat) (x : Expr), ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i))[j]? = some x →
      ∃ ty, x = .fvar j ty := by
    intro j x hx
    have hj : j < dJ.nP + i := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hXSlen] at this
      exact this
    rw [List.getElem?_take_of_lt hj] at hx
    exact hshJ' j x hx
  have hXS : Expr.AllFvars ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hXSsh j a hj
    exact ⟨_, _, rfl⟩
  have hbJnf : bJ.1.hasFvar = false :=
    (stripPis_not_hasFvar _ hsJ hJnf).1 bJ (List.mem_of_getElem? hbJ)
  have hparamsAt : ∀ j, j < dJ.nP → ∀ (l : List Expr), l.take dJ.nP = dJ.fvsPF Jc →
      ∃ ty, l[j]? = some (.fvar j ty) := by
    intro j hj l hl
    have := congrArg (fun l => l[j]?) hl
    simp only [List.getElem?_take_of_lt hj] at this
    obtain ⟨x, hx⟩ : ∃ x, (dJ.fvsPF Jc)[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hDJ.pLen]; exact hj)⟩
    obtain ⟨ty, rfl⟩ := hDJ.pIdx j x hx
    exact ⟨ty, by rw [this, hx]⟩
  -- the level instantiation of the stored constructor: the same telescope
  obtain ⟨⟨bsJ', rJ'⟩, hsJ'⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome lpsJ lvls _ (by rw [hsJ]; rfl))
  obtain ⟨-, hbsJ'⟩ := Expr.stripPis_instantiateLevelParams_eq lpsJ lvls _ hsJ hsJ'
  obtain ⟨bJ', hbJ'⟩ : ∃ bJ', bsJ'[dJ.nP + i]? = some bJ' :=
    ⟨_, List.getElem?_eq_getElem (by rw [stripPis_length' _ hsJ']; omega)⟩
  have hbJ'E : bJ'.1 = bJ.1.instantiateLevelParams lpsJ lvls := hbsJ' _ bJ bJ' hbJ hbJ'
  -- the instantiated constructor's telescope, per field
  have hsJ'' : (cAJ.1.type.instantiateLevelParams lpsJ lvls).stripPis (Ds.length + cAJ.2)
      = some (bsJ', rJ') := by rw [hDsLen]; exact hsJ'
  obtain ⟨bsC₀, hsC₀, hbsC₀⟩ := ConLeche.instPis_stripPis Ds cAJ.2 hcI hsJ''
  have hbC₀ := hbsC₀ i bJ' (by rw [hDsLen]; exact hbJ')
  have hxC' := openPisAtFvars_binder _ hopen hsC₀ i _ hbC₀
  rw [hxC] at hxC'
  obtain rfl := Option.some.inj hxC'
  simp only [hDsLen]
  -- the field's own opener list is variables
  have hxFvsCsh : Expr.AllFvars (xFvsC.take i) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨-, -, -, hlenC, hshC, -⟩ := Verify.openPisAtFvars_stripPis _ hopen
    have hj' : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rw [List.length_take] at this; omega
    rw [List.getElem?_take_of_lt hj'] at hj
    obtain ⟨ty, hty⟩ := hshC j (by omega)
    rw [hj] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  have hxFvsClen : (xFvsC.take i).length ≤ i - 1 + 1 := by
    rw [List.length_take]; omega
  rcases (mem_recIdxOf.mp hi).2 with hrec | hrefl
  · -- ## recursive: the field is the member application itself
    obtain ⟨hhead, htake, hlenArgs, -, -, -⟩ := hDJ.opened.recF i _ hxJ hrec
    simp only [Expr.fvarTypeD] at hhead htake hlenArgs
    obtain ⟨hheadB, htakeB, hleB⟩ := params_of_opened_spine hXS hXSsh (t := dJ.nP + i - 1)
      (by rw [hXSlen]; omega)
      (fun hne => by
        have := List.length_pos_iff.mpr hne
        rw [hXSlen] at this ⊢; omega)
      hbJnf hhead (nPJ := dJ.nP) (by rw [hXSlen]; omega)
      (fun j hj => hparamsAt j hj _ htake)
      (by rw [hlenArgs]; omega)
    rw [hXSlen, Nat.add_sub_cancel_left] at htakeB
    -- the level-instantiated binder
    obtain ⟨hheadB', hargsB'⟩ := instantiateLevelParams_spine hlpsNodup hlvlsLen hheadB
    rw [← hbJ'E] at hheadB' hargsB'
    have htakeB' : bJ'.1.getAppArgs.take dJ.nP = ConLeche.structPsAt i dJ.nP := by
      rw [hargsB', ← List.map_take, htakeB, structPsAt_instantiateLevelParams]
    have hleB' : dJ.nP ≤ bJ'.1.getAppArgs.length := by rw [hargsB', List.length_map]; exact hleB
    -- the field at the pin
    have hspineB' := Expr.mkAppN_getApp bJ'.1
    rw [hheadB'] at hspineB'
    have hinstDs : Expr.instSeq Ds (dJ.nP + i - 1) bJ'.1
        = Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls)
            (Ds ++ (bJ'.1.getAppArgs.drop dJ.nP).map (Expr.instSeq Ds (dJ.nP + i - 1))) := by
      have h := spine_at_components (c := dJ.memberName (dJ.tgts Jc i)) (us := lvls)
        htakeB' hleB' hDsLen hDsC (t := dJ.nP + i - 1) (fun _ => rfl)
      rw [hspineB'] at h
      exact h
    refine ⟨0, [], ((bJ'.1.getAppArgs.drop dJ.nP).map (Expr.instSeq Ds (dJ.nP + i - 1))).map
      (Expr.instSeq (xFvsC.take i) (i - 1)), ?_, ?_⟩
    · show some ([], _) = _
      rw [hinstDs, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const _ _) rfl,
        List.map_append, List.map_congr_left (fun D hD => Expr.instSeq_eq_self _ _ (hDsC D hD)),
        List.map_id']
    · rw [piBinders_eq_of_getAppFn_const hhead]
      rfl
  · -- ## reflexive: the field is a Π-tower over the member application
    obtain ⟨afvs, body, hop, hne, -, hhead, htake, hlenArgs, -, -, -⟩ :=
      hDJ.opened.reflF i _ hxJ hrefl
    simp only [Expr.fvarTypeD] at hop
    have hn : (Expr.instSeq ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)) (dJ.nP + i - 1)
        bJ.1).piBinders.1.length = afvs.length := (openPisAtFvars_length _ hop).symm
    rw [hn] at hop
    obtain ⟨bsA, body₀, hsA, -, -, hbody⟩ := Verify.openPisAtFvars_stripPis _ hop
    -- the strip of the opened field is the strip of the binder, instantiated
    obtain ⟨bsB, rB, hsB⟩ := ConLeche.stripPis_instSeq_inv hXS _ (dJ.nP + i - 1)
      (by rw [hXSlen]; omega) hsA
    obtain ⟨bsB₁, hsB₁, -, -⟩ := ConLeche.stripPis_instSeq _ _ (dJ.nP + i - 1)
      (by rw [hXSlen]; omega) hsB
    rw [hsB₁] at hsA
    obtain ⟨-, hbody₀⟩ := Prod.mk.inj (Option.some.inj hsA)
    have hnpos : 0 < afvs.length := Nat.pos_of_ne_zero hne
    have hbody₀' : Expr.instSeq ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i))
        (dJ.nP + i + afvs.length - 1) rB = body₀ := by
      rcases Nat.eq_zero_or_pos (dJ.nP + i) with h0 | h0
      · have hnil : (dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i) = [] :=
          List.eq_nil_of_length_eq_zero (by rw [hXSlen, h0])
        rw [hnil] at hbody₀ ⊢
        exact hbody₀
      · rw [show dJ.nP + i + afvs.length - 1 = dJ.nP + i - 1 + afvs.length by omega]
        exact hbody₀
    -- the body, as one instantiation at the combined variables
    have hXS' : Expr.AllFvars ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)
        ++ Verify.openFvars (dJ.nP + i) afvs.length) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hXS a ha
      · exact ConLeche.openFvars_allFvars _ _ a ha
    have hXS'sh : ∀ (j : Nat) (x : Expr),
        ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i) ++ Verify.openFvars (dJ.nP + i) afvs.length)[j]?
          = some x → ∃ ty, x = .fvar j ty := by
      intro j x hx
      by_cases hj : j < dJ.nP + i
      · rw [List.getElem?_append_left (by rw [hXSlen]; exact hj)] at hx
        exact hXSsh j x hx
      · rw [List.getElem?_append_right (by rw [hXSlen]; omega), hXSlen] at hx
        have hj' : j - (dJ.nP + i) < afvs.length := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          rw [Verify.openFvars_length] at this
          exact this
        rw [Verify.openFvars_getElem? hj'] at hx
        exact ⟨_, by rw [← Option.some.inj hx]; congr 1; omega⟩
    have hXS'len : ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)
        ++ Verify.openFvars (dJ.nP + i) afvs.length).length = dJ.nP + i + afvs.length := by
      rw [List.length_append, hXSlen, Verify.openFvars_length]
    have hbodyE : Expr.ErasedEq body
        (Expr.instSeq ((dJ.fvsPF Jc ++ dJ.xFvsF Jc).take (dJ.nP + i)
          ++ Verify.openFvars (dJ.nP + i) afvs.length) (dJ.nP + i + afvs.length - 1) rB) := by
      rw [Expr.instSeq_append, hXSlen,
        show dJ.nP + i + afvs.length - 1 - (dJ.nP + i) = afvs.length - 1 by omega, hbody₀']
      exact hbody
    obtain ⟨-, hlenE, hargsE⟩ := hbodyE.getApp
    obtain ⟨hheadB, htakeB, hleB⟩ := params_of_opened_spine hXS' hXS'sh
      (t := dJ.nP + i + afvs.length - 1)
      (by rw [hXS'len]; omega) (fun _ => by rw [hXS'len]; omega)
      (stripPis_not_hasFvar _ hsB hbJnf).2
      ((Expr.ErasedEq.getAppFn_const_iff hbodyE).mp hhead) (nPJ := dJ.nP) (by rw [hXS'len]; omega)
      (fun j hj => by
        obtain ⟨ty, hbj⟩ := hparamsAt j hj _ htake
        obtain ⟨a', ha'⟩ : ∃ a', (Expr.instSeq _ _ rB).getAppArgs[j]? = some a' :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hlenE]; exact (List.getElem?_eq_some_iff.mp hbj).1)⟩
        have hE := hargsE j _ a' hbj ha'
        cases a' with
        | fvar j' ty' =>
          have : j = j' := hE
          subst this
          exact ⟨ty', ha'⟩
        | _ => exact absurd hE (by simp [Expr.ErasedEq]))
      (by rw [← hlenE, hlenArgs]; omega)
    rw [hXS'len, show dJ.nP + i + afvs.length - dJ.nP = i + afvs.length by omega] at htakeB
    -- the level-instantiated binder's strip
    obtain ⟨⟨bsB', rB'⟩, hsB'⟩ := Option.isSome_iff_exists.mp
      (Expr.stripPis_instantiateLevelParams_isSome lpsJ lvls _ (by rw [hsB]; rfl))
    obtain ⟨hrB', -⟩ := Expr.stripPis_instantiateLevelParams_eq lpsJ lvls _ hsB hsB'
    subst hrB'
    obtain ⟨hheadB', hargsB'⟩ := instantiateLevelParams_spine hlpsNodup hlvlsLen hheadB
    have htakeB' : (rB.instantiateLevelParams lpsJ lvls).getAppArgs.take dJ.nP
        = ConLeche.structPsAt (i + afvs.length) dJ.nP := by
      rw [hargsB', ← List.map_take, htakeB, structPsAt_instantiateLevelParams]
    have hleB' : dJ.nP ≤ (rB.instantiateLevelParams lpsJ lvls).getAppArgs.length := by
      rw [hargsB', List.length_map]; exact hleB
    have hspineB' := Expr.mkAppN_getApp (rB.instantiateLevelParams lpsJ lvls)
    rw [hheadB'] at hspineB'
    -- the binder at the pin: strip, then the body at the components
    have hsB'' : bJ'.1.stripPis afvs.length = some (bsB', rB.instantiateLevelParams lpsJ lvls) := by
      rw [hbJ'E]; exact hsB'
    obtain ⟨bsC₁, hsC₁, -, -⟩ := ConLeche.stripPis_instSeq Ds afvs.length (dJ.nP + i - 1)
      (by omega) hsB''
    have hbodyDs : Expr.instSeq Ds (dJ.nP + i - 1 + afvs.length) (rB.instantiateLevelParams lpsJ lvls)
        = Expr.mkAppN (.const (dJ.memberName (dJ.tgts Jc i)) lvls)
            (Ds ++ ((rB.instantiateLevelParams lpsJ lvls).getAppArgs.drop dJ.nP).map
              (Expr.instSeq Ds (dJ.nP + i - 1 + afvs.length))) := by
      have h := spine_at_components (c := dJ.memberName (dJ.tgts Jc i)) (us := lvls)
        htakeB' hleB' hDsLen hDsC (t := dJ.nP + i - 1 + afvs.length) (fun _ => by omega)
      rw [hspineB'] at h
      exact h
    rw [hbodyDs] at hsC₁
    -- the field at the pin, opened at the copy's own variables
    obtain ⟨bsC, hsC, -, -⟩ := ConLeche.stripPis_instSeq (xFvsC.take i) afvs.length (i - 1)
      hxFvsClen hsC₁
    refine ⟨afvs.length, bsC, (((rB.instantiateLevelParams lpsJ lvls).getAppArgs.drop dJ.nP).map
      (Expr.instSeq Ds (dJ.nP + i - 1 + afvs.length))).map
        (Expr.instSeq (xFvsC.take i) (i - 1 + afvs.length)), ?_, hn⟩
    rw [hsC, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const _ _) rfl, List.map_append,
      List.map_congr_left (fun D hD => Expr.instSeq_eq_self _ _ (hDsC D hD)), List.map_id']


/-! ## The fields: K.17's witness through the restore -/

set_option maxHeartbeats 3200000 in
/-- **The copy's fields from K.17's witness** (DESIGN §M.45): at every
field, the STORED copy constructor's opener restored at the copy's own
parameter openers is erasure-equal to the container's constructor at
the pin — or its `whnf` is, at the restored PROCESSED field, which is
the container's constructor at the pin by W1 (`restoreI_walk`).  K.17
compares the two restored constants' openers; `restoreNested_openPis`
reads each opener as the restore of the auxiliary opener; the processed
constructor's body is the pin's constructor walked
(`CopyCtorsStored`), so its restored field is the pin's constructor's
field, up to the openers' annotations. -/
theorem copyFields_of_whnfOk {μ : CheckMode} {F : Nat} {env env₁ : Env}
    {R : ConLeche.RestoreTbl} {nP nF : Nat} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)}
    (hR : R.WF) (hRN : R.Named) (hRnP : R.nP = nP)
    (hpF : ∀ q ∈ R.pins, q.2.hasFvar = false) (hcF : ∀ q ∈ R.ctorPins, q.2.1.hasFvar = false)
    (hpB : ∀ q ∈ R.pins, q.2.looseBVarsBounded R.nP = true)
    (hcB : ∀ q ∈ R.ctorPins, q.2.1.looseBVarsBounded R.nP = true)
    {T₀ body₀ bodyT : Expr} (hst₀ : T₀.stripPis nP = some (pbs, body₀))
    (hop₀ : ConLeche.openPisAtFvars nP T₀ 0 = some (params, bodyT)) (hnf₀ : T₀.hasFvar = false)
    {P : List NestedPin}
    (hP : ∀ q ∈ P, (R.instAt params).pins.lookup q.aux = some q.pin ∧
      (R.instAt params).recMap.lookup q.aux = none ∧
      ∀ x ∈ q.pin.getAppArgs, x.looseBVarsBounded 0 = true)
    {pairs : List (ConLeche.MutualCtor × (ConstantVal × Nat × Nat))}
    (hK17 : ConLeche.nestedCtorsWhnfOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₁ R nP
      pairs = .ok ())
    {c : ConLeche.MutualCtor} {cvS : ConstantVal} {nP' : Nat} (hpr : (c, (cvS, nP', nF)) ∈ pairs)
    {cI cbody body' rest : Expr} {pbs' : List (Expr × ConLeche.BinderMeta)} {sta stb : ElimState}
    (hcv : c.cv.type = ConLeche.closeTelescope pbs' 0 body')
    (hstrip' : (ConLeche.closeTelescope pbs 0 cI).stripPis nP = some (pbs', rest))
    (hinst : Expr.instPis (ConLeche.closeTelescope pbs 0 cI) params = some cbody)
    (hwalk : ConLeche.replaceAllNested env blvls params pbs sta cbody = .ok (body', stb))
    (hstb : ∀ q ∈ stb.pins, q ∈ P)
    (hcvF : c.cv.type.hasFvar = false) (hcvB : c.cv.type.looseBVarsBounded 0 = true)
    (hcIL : Expr.LeavesIn params cI) (hcIB : cI.looseBVarsBounded 0 = true)
    (hcIaux : ∀ n ∈ R.auxNames, cI.mentionsConstE n = false)
    {xFvsC : List Expr} {xrestC : Expr}
    (hopenC : ConLeche.openPisAtFvars nF cI nP = some (xFvsC, xrestC))
    {fvsP xFvs : List Expr} {crest xrest : Expr}
    (hopS₁ : ConLeche.openPisAtFvars nP cvS.type 0 = some (fvsP, crest))
    (hopS₂ : ConLeche.openPisAtFvars nF crest nP = some (xFvs, xrest))
    (hSF : cvS.type.hasFvar = false) :
    ∀ (i : Nat) (x xC : Expr), xFvs[i]? = some x → xFvsC[i]? = some xC →
      Expr.ErasedEq (ConLeche.restoreI (R.instAt fvsP) x.fvarTypeD) xC.fvarTypeD ∨
      WhnfField μ F env₁ R fvsP (nP + i) x.fvarTypeD xC.fvarTypeD := by
  intro i x xC hx hxC
  have hi : i < nF := by
    rw [← openPisAtFvars_length _ hopS₂]; exact (List.getElem?_eq_some_iff.mp hx).1
  -- ## K.17 at this pair
  obtain ⟨mR, sR, fvsM, oM, fvsS, oS, hmR, hsR, hopM, hopS, hfield⟩ :=
    ConLeche.nestedCtorsWhnfOk_inv hK17 _ hpr
  have hmR : ConLeche.restoreNested R c.cv.type = .ok mR := hmR
  have hsR : ConLeche.restoreNested R cvS.type = .ok sR := hsR
  have hopM : ConLeche.openPisAtFvars (nP + nF) mR 0 = some (fvsM, oM) := hopM
  have hopS : ConLeche.openPisAtFvars (nP + nF) sR 0 = some (fvsS, oS) := hopS
  have hwhnf := ConLeche.nestedFieldWhnfOk_inv (nF := nF) hfield i hi
  -- ## the stored constructor, restored and opened
  have hopS' : ConLeche.openPisAtFvars (nP + nF) cvS.type 0 = some (fvsP ++ xFvs, xrest) :=
    ConLeche.openPisAtFvars_add' _ hopS₁ (by rw [Nat.zero_add]; exact hopS₂)
  obtain ⟨fvsS', restS', hopS'', hlenS', -, hfieldS', -⟩ :=
    ConLeche.restoreNested_openPis hR hsR hSF (n := nP + nF) (by omega) hopS'
  rw [hopS''] at hopS
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopS)
  have hfvsPlen : fvsP.length = nP := openPisAtFvars_length _ hopS₁
  have hxapp : (fvsP ++ xFvs)[nP + i]? = some x := by
    rw [List.getElem?_append_right (by omega), hfvsPlen, Nat.add_sub_cancel_left]; exact hx
  obtain ⟨xR, hxR⟩ : ∃ xR, fvsS'[nP + i]? = some xR :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨tyS, rfl, hxRE⟩ := hfieldS' (nP + i) x xR (by omega) hxapp hxR
  have htakeS : (fvsP ++ xFvs).take R.nP = fvsP := by
    rw [hRnP, List.take_left' hfvsPlen]
  rw [htakeS] at hxRE
  simp only [Expr.fvarTypeD] at hxRE
  have hds : (fvsS'.getD (nP + i) default).fvarTypeD = tyS := by
    rw [List.getD_eq_getElem?_getD, hxR]; rfl
  -- ## the processed constructor: the pin's constructor, walked
  have hcbody : cbody = cI :=
    Option.some.inj (hinst.symm.trans (ConLeche.instPis_closeTelescope_leaves hst₀ hop₀ hnf₀ hcIL hcIB))
  subst hcbody
  have hpbsF : ∀ b ∈ pbs, b.1.hasFvar = false := (ConLeche.stripPis_not_hasFvar _ hst₀ hnf₀).1
  have hpbsLen : pbs.length = nP := stripPis_length' _ hst₀
  obtain ⟨r, hr⟩ := ConLeche.stripPis_closeTelescope_of_not_hasFvar pbs 0 cbody hpbsF
  rw [hpbsLen] at hr
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hstrip'.symm.trans hr))
  have hparamsLen : params.length = nP := openPisAtFvars_length _ hop₀
  have hparSh := ConLeche.openers_shape hop₀
  have hparL : ∀ p ∈ params, Expr.LeavesIn params p := ConLeche.openPisAtFvars_leavesIn hop₀ hnf₀
  have hparC : ∀ p ∈ params, p.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    obtain ⟨ty, rfl⟩ := hparSh j p hj
    rfl
  have hbody'L : Expr.LeavesIn params body' :=
    ConLeche.replaceAllNested_leavesIn hparL cbody hwalk hcIL
  have hbody'B : body'.looseBVarsBounded 0 = true :=
    ConLeche.replaceAllNested_looseBVarsBounded hparC cbody hwalk hcIB
  have hopM₁ : ConLeche.openPisAtFvars nP c.cv.type 0 = some (params, body') := by
    rw [hcv]; exact ConLeche.openPisAtFvars_closeTelescope_leaves hst₀ hop₀ hnf₀ hbody'L hbody'B
  obtain ⟨fs, resid, hsI, -, hshC, -⟩ := Verify.openPisAtFvars_stripPis nF hopenC
  obtain ⟨fs', resid', hsW, hlenW, hfsW, -⟩ := ConLeche.replaceAllNested_stripPis nF cbody hwalk hsI
  obtain ⟨fvsW, restW, hopW⟩ := ConLeche.openPisAtFvars_of_stripPis' nF nP hsW
  have hopM' : ConLeche.openPisAtFvars (nP + nF) c.cv.type 0 = some (params ++ fvsW, restW) :=
    ConLeche.openPisAtFvars_add' _ hopM₁ (by rw [Nat.zero_add]; exact hopW)
  obtain ⟨fvsM', restM', hopM'', hlenM', -, hfieldM', -⟩ :=
    ConLeche.restoreNested_openPis hR hmR hcvF (n := nP + nF) (by omega) hopM'
  rw [hopM''] at hopM
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopM)
  have hfsLen : fs.length = nF := stripPis_length' _ hsI
  obtain ⟨bW, hbW⟩ : ∃ bW, fs'[i]? = some bW :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenW, hfsLen]; exact hi)⟩
  obtain ⟨bI, hbI⟩ : ∃ bI, fs[i]? = some bI :=
    ⟨_, List.getElem?_eq_getElem (by rw [hfsLen]; exact hi)⟩
  have hy := openPisAtFvars_binder _ hopW hsW i bW hbW
  have hxC' := openPisAtFvars_binder _ hopenC hsI i bI hbI
  rw [hxC] at hxC'
  obtain rfl := Option.some.inj hxC'
  simp only [Expr.fvarTypeD]
  have hyapp : (params ++ fvsW)[nP + i]? =
      some (.fvar (nP + i) (Expr.instSeq (fvsW.take i) (i - 1) bW.1)) := by
    rw [List.getElem?_append_right (by omega), hparamsLen, Nat.add_sub_cancel_left]; exact hy
  obtain ⟨yR, hyR⟩ : ∃ yR, fvsM'[nP + i]? = some yR :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨tyM, rfl, hyRE⟩ := hfieldM' (nP + i) _ yR (by omega) hyapp hyR
  have htakeM : (params ++ fvsW).take R.nP = params := by
    rw [hRnP, List.take_left' hparamsLen]
  rw [htakeM] at hyRE
  simp only [Expr.fvarTypeD] at hyRE
  have hdm : (fvsM'.getD (nP + i) default).fvarTypeD = tyM := by
    rw [List.getD_eq_getElem?_getD, hyR]; rfl
  -- ## W1 at the field: the restored walked binder is the pin's binder
  obtain ⟨-, s₁, s₂, -, hwalkB, hgrow₂⟩ := hfsW i bI bW hbI hbW
  have hs₂ : ∀ q ∈ s₂.pins, q ∈ P := by
    intro q hq
    obtain ⟨new, hnew, -⟩ := hgrow₂
    exact hstb q (by rw [hnew]; exact List.mem_append_left _ hq)
  obtain ⟨-, -, -, hlenWo, hshW, -⟩ := Verify.openPisAtFvars_stripPis nF hopW
  have hfvsWF : Expr.AllFvars (fvsW.take i) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    have hj' : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rw [List.length_take] at this; omega
    rw [List.getElem?_take_of_lt hj'] at hj
    obtain ⟨ty, hty⟩ := hshW j (by omega)
    rw [hj] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  have hbIaux : ∀ n ∈ R.auxNames, bI.1.mentionsConstE n = false := by
    intro n hn
    have hxCF : Expr.AllFvars (xFvsC.take i) := by
      intro a ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
      have hj' : j < i := by
        have := (List.getElem?_eq_some_iff.mp hj).1; rw [List.length_take] at this; omega
      rw [List.getElem?_take_of_lt hj'] at hj
      obtain ⟨ty, hty⟩ := hshC j (by omega)
      rw [hj] at hty
      exact ⟨_, _, Option.some.inj hty⟩
    rw [← Expr.mentionsConstE_instSeq_fvars (xFvsC.take i) hxCF (i - 1) bI.1]
    cases hm : (Expr.instSeq (xFvsC.take i) (i - 1) bI.1).mentionsConstE n with
    | false => rfl
    | true =>
      exact absurd (ConLeche.openPisAtFvars_mentionsConstE nF cbody nP hopenC
        (Or.inr ⟨_, List.mem_of_getElem? hxC, hm⟩)) (by rw [hcIaux n hn]; decide)
  have hW1 := ConLeche.restoreI_walk (hRN.instAt params)
    (by show R.nP = params.length; rw [hRnP, hparamsLen]) hparC hP bI.1 hwalkB hs₂ hbIaux
    (fvsW.take i) (i - 1) hfvsWF (by rw [List.length_take]; omega)
  have hxCE : Expr.ErasedEq (Expr.instSeq (fvsW.take i) (i - 1) bI.1)
      (Expr.instSeq (xFvsC.take i) (i - 1) bI.1) := by
    refine Expr.instSeq_erasedEq_args _ _ _ (Expr.ErasedEq.rfl _) ?_ ?_
    · intro k a₁ a₂ ha₁ ha₂
      have hk : k < i := by
        have := (List.getElem?_eq_some_iff.mp ha₁).1; rw [List.length_take] at this; omega
      rw [List.getElem?_take_of_lt hk] at ha₁ ha₂
      obtain ⟨ty₁, hty₁⟩ := hshW k (by omega)
      obtain ⟨ty₂, hty₂⟩ := hshC k (by omega)
      rw [ha₁] at hty₁
      rw [ha₂] at hty₂
      obtain rfl := Option.some.inj hty₁
      obtain rfl := Option.some.inj hty₂
      exact rfl
    · rw [List.length_take, List.length_take, hlenWo, openPisAtFvars_length _ hopenC]
  have hdmE : Expr.ErasedEq tyM (Expr.instSeq (xFvsC.take i) (i - 1) bI.1) :=
    hyRE.trans (hW1.trans hxCE)
  -- ## the two arms
  rcases hwhnf with heq | hwh
  · left
    rw [hdm, hds] at heq
    subst heq
    exact hxRE.symm.trans hdmE
  · right
    rw [hdm, hds] at hwh
    -- the restored processed constant is closed: its openers are scoped
    obtain ⟨r', hr'⟩ := ConLeche.stripPis_closeTelescope_of_not_hasFvar pbs' 0 body' hpbsF
    rw [hpbsLen] at hr'
    obtain ⟨hmRF, hmRB⟩ := ConLeche.restoreNested_closed hpF hcF hpB hcB hmR
      (by rw [hcv, hRnP]; exact hr') hcvF hcvB
    have hyMem : Expr.fvar (nP + i) tyM ∈ fvsM' := List.mem_of_getElem? hyR
    have hws := (ConLeche.openPisAtFvars_WScoped (nP + nF) mR 0 hopM''
      (Expr.WScoped.of_not_hasFvar hmRF)).1 _ hyMem
    simp only [Expr.WScoped] at hws
    have hbnd := (Verify.openPisAtFvars_bounded (nP + nF) hopM'' hmRB).2 _ hyMem
    have hlb := (ConLeche.openPisAtFvars_leavesBounded hopM'' hmRF hmRB).1 _ hyMem
    simp only [Expr.fvarTypeD] at hbnd hlb
    exact ⟨tyM, tyS, hdmE, hwh, hxRE, hws.2, hbnd, hlb⟩


/-! ## The residual: W2 through the stored constructor's shape -/

/-- The container's constructor at the pin, stripped at the fields:
the target at the pin's components and the container's index
expressions instantiated at the components. -/
theorem containerResid_at_pin {μ : CheckMode} {envAux : Env} (mp : EnvModelM V μ envAux)
    {dJ : IndRepData V} {Jc : Nat} {cAJ : ConstantVal × Nat} {lpsJ : List Name}
    {lvls : List Level} {Ds : List Expr} {cI : Expr}
    (hDJ : FixCtorDataI mp.base2 dJ.env₀ (dJ.memberName (dJ.mems Jc)) lpsJ cAJ.1 dJ.nP cAJ.2
      (dJ.nIdxAt (dJ.mems Jc)) dJ.resSort dJ.isProp dJ.large (dJ.idxF Jc) (dJ.dsF Jc) (dJ.esF Jc)
      (dJ.srcsF Jc) (dJ.ksF Jc) (dJ.fvsPF Jc) (dJ.xFvsF Jc) (dJ.xrestF Jc) (dJ.eissF Jc)
      (dJ.tssF Jc) (fun i => dJ.memberName (dJ.tgts Jc i)) (fun i => dJ.nIdxAt (dJ.tgts Jc i)))
    (hlpsNodup : lpsJ.Nodup) (hlvlsLen : lvls.length = lpsJ.length)
    (hDsLen : Ds.length = dJ.nP) (hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
    (hcI : Expr.instPis (cAJ.1.type.instantiateLevelParams lpsJ lvls) Ds = some cI) :
    ∃ (fs : List (Expr × ConLeche.BinderMeta)) (idx₀ : List Expr),
      cI.stripPis cAJ.2 = some (fs,
        Expr.mkAppN (.const (dJ.memberName (dJ.mems Jc)) lvls) (Ds ++ idx₀)) := by
  obtain ⟨cbs, es, hsJ, -⟩ := hDJ.resid
  obtain ⟨⟨bsJ', rJ'⟩, hsJ'⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome lpsJ lvls _ (by rw [hsJ]; rfl))
  obtain ⟨hrJ', -⟩ := Expr.stripPis_instantiateLevelParams_eq lpsJ lvls _ hsJ hsJ'
  subst hrJ'
  have hsJ'' : (cAJ.1.type.instantiateLevelParams lpsJ lvls).stripPis (Ds.length + cAJ.2)
      = some (bsJ', (Expr.mkAppN (.const (dJ.memberName (dJ.mems Jc)) (lpsJ.map Level.param))
        (ConLeche.structPsAt cAJ.2 dJ.nP ++ es)).instantiateLevelParams lpsJ lvls) := by
    rw [hDsLen]; exact hsJ'
  obtain ⟨bsC₀, hsC₀, -⟩ := ConLeche.instPis_stripPis Ds cAJ.2 hcI hsJ''
  have hconst : (Expr.const (dJ.memberName (dJ.mems Jc)) (lpsJ.map Level.param)).instantiateLevelParams
      lpsJ lvls = .const (dJ.memberName (dJ.mems Jc)) lvls := by
    simp only [Expr.instantiateLevelParams]
    rw [ConLeche.map_subst_params_nodup hlpsNodup hlvlsLen.symm]
  have hlenSP : (ConLeche.structPsAt cAJ.2 dJ.nP).length = dJ.nP := by simp [ConLeche.structPsAt]
  refine ⟨bsC₀, (es.map (Expr.instantiateLevelParams lpsJ lvls)).map
    (Expr.instSeq Ds (dJ.nP + cAJ.2 - 1)), ?_⟩
  rw [hsC₀, ConLeche.instantiateLevelParams_mkAppN, List.map_append, structPsAt_instantiateLevelParams,
    hconst, hDsLen, spine_at_components (o := cAJ.2) (List.take_left' hlenSP)
      (by rw [List.length_append, hlenSP]; omega) hDsLen hDsC (fun _ => rfl), List.drop_left' hlenSP]

set_option maxHeartbeats 3200000 in
/-- **The residual from the stored constructor's shape and W2**
(DESIGN §M.45): the stored copy constructor's residual is the copy at
its parameter openers and index arguments (`checkMutualCtor_front`),
erasure-equal to the processed constructor's opened residual
(`normCtorValM_residual`); the processed residual is the walk's output
at the pin's constructor's residual, whose head is the copy — so the
walk FIRED at the top (W2), with the index arguments VERBATIM; the
container's residual at the pin opened at the copy's own field openers
carries the same index arguments up to the openers' annotations. -/
theorem copyResid_of_stored {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {k₀ nP nF : Nat} {sta stb : ElimState}
    {cI body' : Expr}
    (hwalk : ConLeche.replaceAllNested env blvls params pbs sta cI = .ok (body', stb))
    (hpi : sta.PinsIndexed k₀)
    (hin : ∀ T ∈ (stb.types.map (·.name)).drop k₀, cI.mentionsConst T = false)
    {fs : List (Expr × ConLeche.BinderMeta)} {Jn : Name} {lvls : List Level} {Ds idx₀ : List Expr}
    (hsI : cI.stripPis nF = some (fs, Expr.mkAppN (.const Jn lvls) (Ds ++ idx₀)))
    (hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
    (hparC : ∀ p ∈ params, p.looseBVarsBounded 0 = true) (hparamsLen : params.length = nP)
    {xFvsC : List Expr} {xrestC : Expr}
    (hopenC : ConLeche.openPisAtFvars nF cI nP = some (xFvsC, xrestC))
    {fvsW : List Expr} {restW : Expr}
    (hopW : ConLeche.openPisAtFvars nF body' nP = some (fvsW, restW))
    {aux : Name} {fvsP idxArgs : List Expr} {xrestS : Expr}
    (hxrestS : xrestS = Expr.mkAppN (.const aux blvls) (fvsP ++ idxArgs))
    (hfvsPlen : fvsP.length = nP) (hE : Expr.ErasedEq xrestS restW)
    (haux : aux ∈ (stb.types.map (·.name)).drop k₀)
    (hpinOf : ∀ q ∈ stb.pins, q.aux = aux → q.pin = Expr.mkAppN (.const Jn lvls) Ds) :
    ∃ (idx idxC : List Expr),
      xrestS = Expr.mkAppN (.const aux blvls) (fvsP ++ idx) ∧
      xrestC = Expr.mkAppN (.const Jn lvls) (Ds ++ idxC) ∧
      idx.length = idxC.length ∧
      ∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC := by
  -- ## the container's residual at the copy's field openers
  obtain ⟨fs₁, resid₁, hsI₁, hlenC, hshC, -⟩ := Verify.openPisAtFvars_stripPis nF hopenC
  rw [hsI] at hsI₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsI₁)
  have hxrestC := Verify.openPisAtFvars_instSeq nF hopenC hsI
  have hxCF : Expr.AllFvars xFvsC := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, hty⟩ := hshC j (by rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hj).1)
    rw [hj] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  -- ## the processed residual: the walk's output at the residual, opened
  obtain ⟨fs', resid', hsW, -, -, -⟩ := ConLeche.replaceAllNested_stripPis nF cI hwalk hsI
  obtain ⟨fs'', resid'', hsW', hlenW, hshW, -⟩ := Verify.openPisAtFvars_stripPis nF hopW
  rw [hsW] at hsW'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsW')
  have hrestW := Verify.openPisAtFvars_instSeq nF hopW hsW
  have hWF : Expr.AllFvars fvsW := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, hty⟩ := hshW j (by rw [← hlenW]; exact (List.getElem?_eq_some_iff.mp hj).1)
    rw [hj] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  -- its head is the copy's: the stored residual's, up to erasure
  have hheadS : xrestS.getAppFn = .const aux blvls := by
    rw [hxrestS, Expr.getAppFn_mkAppN]; rfl
  have hheadW : resid'.getAppFn = .const aux blvls := by
    have := (Expr.ErasedEq.getAppFn_const_iff hE).mp hheadS
    rw [hrestW] at this
    exact (ConLeche.getAppFn_instSeq_const_iff hWF (by rw [hlenW]; omega)).mp this
  have hspineW := Expr.mkAppN_getApp resid'
  rw [hheadW] at hspineW
  -- ## W2: the walk fired at the top, the index arguments verbatim
  obtain ⟨fs₂, resid₂, hsW₂, -, -, -, hW2⟩ := ConLeche.copyCtorFields_of_walk hwalk hpi hsI hin
  rw [hsW] at hsW₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsW₂)
  obtain ⟨I, lvls', ci, -, hciLe, hresidI, -, hargs, q, hq, hqaux, hqpin⟩ :=
    hW2 aux blvls resid'.getAppArgs hspineW.symm haux
  have hheadI : Jn = I ∧ lvls = lvls' := by
    have := congrArg Expr.getAppFn hresidI
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at this
    exact Expr.const.inj this
  obtain ⟨rfl, rfl⟩ := hheadI
  have hargsI : (Expr.mkAppN (.const Jn lvls) (Ds ++ idx₀)).getAppArgs = Ds ++ idx₀ := by
    rw [Expr.getAppArgs_mkAppN]; rfl
  rw [hargsI] at hciLe hargs hqpin
  have hDsCi : Ds.length = ci.nP := by
    have h₁ := hpinOf q hq hqaux
    rw [hqpin] at h₁
    have h₂ := congrArg Expr.getAppArgs h₁
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h₂
    have h₃ : (Ds ++ idx₀).take ci.nP = Ds := List.append_cancel_left h₂
    have h₄ := congrArg List.length h₃
    rw [List.length_take, List.length_append] at h₄
    rw [List.length_append] at hciLe
    omega
  rw [List.drop_left' hDsCi] at hargs
  -- ## the two residuals at the openers
  have hrestW' : restW = Expr.mkAppN (.const aux blvls)
      (params ++ idx₀.map (Expr.instSeq fvsW (nF - 1))) := by
    rw [hrestW, ← hspineW, hargs, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (e := .const aux blvls) rfl, List.map_append,
      List.map_congr_left (fun p hp => Expr.instSeq_eq_self _ _ (hparC p hp)), List.map_id']
  have hxrestC' : xrestC = Expr.mkAppN (.const Jn lvls)
      (Ds ++ idx₀.map (Expr.instSeq xFvsC (nF - 1))) := by
    rw [hxrestC, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := .const Jn lvls) rfl,
      List.map_append, List.map_congr_left (fun D hD => Expr.instSeq_eq_self _ _ (hDsC D hD)),
      List.map_id']
  refine ⟨idxArgs, idx₀.map (Expr.instSeq xFvsC (nF - 1)), hxrestS, hxrestC', ?_, ?_⟩
  · rw [hxrestS, hrestW'] at hE
    obtain ⟨-, hlenE, -⟩ := hE.getApp
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at hlenE
    simp only [List.length_append, List.length_map] at hlenE
    rw [List.length_map]
    have : (Expr.const aux blvls).getAppArgs.length = 0 := rfl
    omega
  · intro k e eC he heC
    rw [hxrestS, hrestW'] at hE
    obtain ⟨-, hlenE, hargsE⟩ := hE.getApp
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at hargsE
    have hnil : (Expr.const aux blvls).getAppArgs = [] := rfl
    rw [hnil, List.nil_append, List.nil_append] at hargsE
    have hk : k < idx₀.length := by
      rw [List.getElem?_map] at heC
      obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.mp heC
      exact (List.getElem?_eq_some_iff.mp ha).1
    obtain ⟨e₀, he₀⟩ : ∃ e₀, idx₀[k]? = some e₀ := ⟨_, List.getElem?_eq_getElem hk⟩
    have hE₁ := hargsE (nP + k) e (Expr.instSeq fvsW (nF - 1) e₀)
      (by rw [List.getElem?_append_right (by omega), hfvsPlen, Nat.add_sub_cancel_left]; exact he)
      (by rw [List.getElem?_append_right (by omega), hparamsLen, Nat.add_sub_cancel_left,
        List.getElem?_map, he₀]; rfl)
    have heC' : eC = Expr.instSeq xFvsC (nF - 1) e₀ := by
      rw [List.getElem?_map, he₀] at heC
      exact (Option.some.inj heC).symm
    rw [heC']
    refine hE₁.trans (Expr.instSeq_erasedEq_args _ _ _ (Expr.ErasedEq.rfl _) ?_ (by rw [hlenW, hlenC]))
    intro j a₁ a₂ ha₁ ha₂
    obtain ⟨ty₁, hty₁⟩ := hshW j (by rw [← hlenW]; exact (List.getElem?_eq_some_iff.mp ha₁).1)
    obtain ⟨ty₂, hty₂⟩ := hshC j (by rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp ha₂).1)
    rw [ha₁] at hty₁
    rw [ha₂] at hty₂
    obtain rfl := Option.some.inj hty₁
    obtain rfl := Option.some.inj hty₂
    exact rfl


/-! ## The group exclusion: K.23 through the datum's field shapes -/

omit [SetTheory V] in
/-- `fieldHeadAt` at a known Π-prefix and constant head. -/
theorem fieldHeadAt_of_piBinders {e res : Expr} {fbs : List (Expr × ConLeche.BinderMeta)}
    (hpb : e.piBinders = (fbs, res)) {C : Name} {us : List Level}
    (hhead : res.getAppFn = .const C us) :
    ConLeche.fieldHeadAt e = some (C, res.getAppArgs, fbs.length) := by
  unfold ConLeche.fieldHeadAt
  rw [hpb]
  simp only [hhead]

omit [SetTheory V] in
/-- A datum's field the copy classifies RECURSIVE or REFLEXIVE has its
target's name at the head of its opened annotation. -/
theorem fieldHeadAt_of_opened {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx nF : Nat}
    {ks : List ConLeche.RecFieldKind} {fvsP xFvs : List Expr} {xrest : Expr}
    {tgtOf : Nat → Name} {nIdxOf : Nat → Nat}
    (hMO : FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest tgtOf nIdxOf)
    {i : Nat} (hi : i ∈ ConLeche.recIdxOf ks) {x : Expr} (hx : xFvs[i]? = some x) :
    ∃ (args : List Expr) (n : Nat),
      ConLeche.fieldHeadAt x.fvarTypeD = some (tgtOf i, args, n) := by
  rcases (mem_recIdxOf.mp hi).2 with hrec | hrefl
  · obtain ⟨hhead, -⟩ := hMO.recF i x hx hrec
    exact ⟨_, _, fieldHeadAt_of_piBinders (piBinders_eq_of_getAppFn_const hhead) hhead⟩
  · obtain ⟨afvs, body, hop, -, -, hhead, -⟩ := hMO.reflF i x hx hrefl
    obtain ⟨bs, body₀, hs, -, -, hbody⟩ := Verify.openPisAtFvars_stripPis _ hop
    have hhead₀ : body₀.getAppFn = .const (tgtOf i) (lps.map Level.param) := by
      have := (Expr.ErasedEq.getAppFn_const_iff hbody).mp hhead
      exact (ConLeche.getAppFn_instSeq_const_iff (ConLeche.openFvars_allFvars _ _)
        (by rw [Verify.openFvars_length]; omega)).mp this
    have hpb := ConLeche.piBinders_of_stripPis _ hs
    rw [piBinders_eq_of_getAppFn_const hhead₀, List.append_nil] at hpb
    exact ⟨_, _, fieldHeadAt_of_piBinders hpb hhead₀⟩

set_option maxHeartbeats 3200000 in
/-- **The group exclusion from K.23 and the container datum's shapes**
(DESIGN §M.45): a field the CONTAINER classifies ordinary and the COPY
classifies recursive does not target a group-mate.  The copy's stored
binder has the target's name at its head (`fieldHeadAt_of_opened`
through the openers, `fieldHeadAt_instSeq`); were the target in the
group, K.23 says the container's stored binder at that field is a
member at the exact parameter variables — which `OrdNotRec` rules out
at an ordinary field of the container's datum. -/
theorem groupExclusion_of_K23 {μ : CheckMode} {envAux : Env} (mp : EnvModelM V μ envAux)
    {env : Env} {p : ConLeche.NestedParts} {st : ElimState}
    (hK23 : NestedGroupExclusionOk env envAux p st)
    {d dJ : IndRepData V} (hONR : dJ.OrdNotRec)
    {Ja Jc : Nat} {cA cAJ : ConstantVal × Nat} {lpsT : List Name}
    (hD : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems Ja)) lpsT cA.1 d.nP cA.2
      (d.nIdxAt (d.mems Ja)) d.resSort d.isProp d.large (d.idxF Ja) (d.dsF Ja) (d.esF Ja)
      (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja) (d.xrestF Ja) (d.eissF Ja)
      (d.tssF Ja) (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hJc : dJ.ctorsA[Jc]? = some cAJ)
    (hfind : envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    {k₀ j' : Nat} (hk₀ : k₀ = p.k) {q : NestedPin} (hq : st.pins[j']? = some q)
    {tyA : AuxType} (htyA : st.types[p.k + j']? = some tyA)
    {l : Nat} {cty : Expr} {nFc : Nat} (hctorA : tyA.ctors[l]? = some (cA.1.name, cty, nFc))
    {base : Nat} (hgb : q.grpBase = base) (hgs : q.grpSize = dJ.k)
    (hpinName : ∀ t, t < dJ.k → ∃ q', st.pins[base + t]? = some q' ∧
      q'.aux = d.memberName (k₀ + (base + t)))
    {ci : ContainerInfo} {J : ContainerMember} {c : ContainerCtor}
    (hci : ConLeche.containerInfo? env q.container = some ci) (hJ : J ∈ ci.members)
    (hJn : J.name = q.container) (hcl : J.ctors[l]? = some c) (htypeC : c.type = cAJ.1.type)
    (hnFC : c.nFields = cAJ.2) (hciNP : ci.nP = dJ.nP)
    (hmemNames : ∀ C, C ∈ ci.members.map (·.name) → ∃ t, t < dJ.k ∧ dJ.memberName t = C)
    {bsJ : List (Expr × ConLeche.BinderMeta)} {rJ : Expr}
    (hsJ : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bsJ, rJ)) (hnF : cA.2 = cAJ.2) :
    ∀ i, i ∉ ConLeche.recIdxOf (dJ.ksF Jc) → i ∈ ConLeche.recIdxOf (d.ksF Ja) →
      k₀ ≤ d.tgts Ja i →
      ¬ (base ≤ d.tgts Ja i - k₀ ∧ d.tgts Ja i - k₀ < base + dJ.k) := by
  intro i hiJ hiA hk0 ⟨hlo, hhi⟩
  have hiA' : i < cA.2 := by rw [← hD.ksLen]; exact (mem_recIdxOf.mp hiA).1
  -- the copy's stored constructor: the field's binder, its head the target
  obtain ⟨crest, hopP, hopF⟩ := hD.opens
  have hopA : ConLeche.openPisAtFvars (d.nP + cA.2) cA.1.type 0
      = some (d.fvsPF Ja ++ d.xFvsF Ja, d.xrestF Ja) :=
    ConLeche.openPisAtFvars_add' _ hopP (by rw [Nat.zero_add]; exact hopF)
  obtain ⟨bsS, rS, hsS, hlenS, hshS, -⟩ := Verify.openPisAtFvars_stripPis _ hopA
  obtain ⟨domS, hdomS⟩ : ∃ domS, bsS[d.nP + i]? = some domS :=
    ⟨_, List.getElem?_eq_getElem (by rw [stripPis_length' _ hsS]; omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF Ja)[i]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hiA')⟩
  have hxA : (d.fvsPF Ja ++ d.xFvsF Ja)[d.nP + i]? = some x := by
    rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
    exact hx
  have hx' := openPisAtFvars_binder _ hopA hsS (d.nP + i) domS hdomS
  rw [hxA] at hx'
  obtain rfl := Option.some.inj hx'
  obtain ⟨args, n, hfh⟩ := fieldHeadAt_of_opened hD.opened hiA hx
  simp only [Expr.fvarTypeD] at hfh
  have hXSlen : ((d.fvsPF Ja ++ d.xFvsF Ja).take (d.nP + i)).length = d.nP + i := by
    rw [List.length_take, List.length_append, hD.pLen, hD.xLen]; omega
  have hXS : Expr.AllFvars ((d.fvsPF Ja ++ d.xFvsF Ja).take (d.nP + i)) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    have hj' : j < d.nP + i := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rw [hXSlen] at this; exact this
    rw [List.getElem?_take_of_lt hj'] at hj
    obtain ⟨ty, hty⟩ := hshS j (by omega)
    rw [hj] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  rw [ConLeche.fieldHeadAt_instSeq hXS domS.1 (d.nP + i - 1) (by rw [hXSlen]; omega)] at hfh
  obtain ⟨⟨T₀, args₀, n₀⟩, hfh₀, hfhE⟩ := Option.map_eq_some_iff.mp hfh
  simp only [Prod.mk.injEq] at hfhE
  obtain ⟨rfl, -, rfl⟩ := hfhE
  -- the target is a group pin
  obtain ⟨q', hq', hq'aux⟩ := hpinName (d.tgts Ja i - k₀ - base) (by omega)
  rw [show k₀ + (base + (d.tgts Ja i - k₀ - base)) = d.tgts Ja i by omega] at hq'aux
  -- K.23: the container's binder at this field is a member at the exact parameters
  have hsJ' : c.type.stripPis (ci.nP + c.nFields) = some (bsJ, rJ) := by
    rw [htypeC, hnFC, hciNP]; exact hsJ
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, bsJ[dJ.nP + i]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by rw [stripPis_length' _ hsJ]; omega)⟩
  obtain ⟨C, argsJ, nJ, hfhJ, hCmem, hlenJ, hexact⟩ :=
    hK23 j' q hq tyA htyA l cA.1.name cty nFc hctorA cA.1 d.nP cA.2 hfind bsS rS hsS i domS hdomS
      _ args₀ n₀ hfh₀ ⟨d.tgts Ja i - k₀ - base, by omega, q', by rw [hgb]; exact hq', hq'aux⟩
      ci J c hci hJ hJn hcl bsJ rJ hsJ' domJ (by rw [hciNP]; exact hdomJ)
  rw [hciNP] at hlenJ hexact
  exact hONR Jc cAJ hJc bsJ rJ hsJ i hiJ domJ hdomJ C argsJ nJ hfhJ (hmemNames C hCmem) hlenJ hexact

end ConLeche.Model
