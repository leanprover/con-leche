module

public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Semantics.Tower.FixTower
public import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.TableInstall
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Model.Reading.Levels
import ConLeche.Kernel.PropWhen
import ConLeche.Verify.Denote.Inst
import ConLeche.Semantics.Frame

public section

/-!
# Block library: recursive families

The indexed-sum library with recursive fields: the former's index
telescope; the recursive constructor data and their crossing of a
cons; the constructors' loop over any former leaf;
the semantic data of a block; and, for a structure-like block, the
projection entry's law, the projection table's cons, the reflexive
telescopes' bounds and the fieldless block's laws.
-/

/-!
## The former's index telescope

The former's index telescope graded and bounded at the parameter frame
(`idxOk_of`): the index binders' sorts the install read
(`checkStructFieldSortsI` at the former's opened telescope), joined
into the tuple universe `idxUniv`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit -/

/-- The tuple universe: the join of the index binders' sorts. -/
def idxUniv (ψ : Name → Nat) (isorts : List Level) : Nat :=
  (isorts.map (Level.eval ψ)).foldl max 0

omit [SetTheory V] in
theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => nomatch h
  | y :: l, a, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge l _)
    · exact le_foldl_max l (max a y) x h
where
  foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
    | [], _ => Nat.le_refl _
    | y :: l, a => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left a y) (foldl_max_ge l _)

omit [SetTheory V] in
theorem eval_le_idxUniv {ψ : Name → Nat} {isorts : List Level} {j : Nat} {s : Level}
    (h : isorts[j]? = some s) : s.eval ψ ≤ idxUniv ψ isorts :=
  le_foldl_max _ 0 _ (List.mem_map.mpr ⟨s, List.mem_of_getElem? h, rfl⟩)

/-! ## The index telescope -/

/-- **The former's index telescope**, graded and bounded by the tuple
universe at every parameter frame. -/
theorem idxOk_of (hμ : μ.isVerified = true) (mp : EnvModelM V μ env)
    {F : Nat} {nP nIdx : Nat} {resSort : Level} {cvTa : ConstantVal} {T : Name}
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvTa caps))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, trest))
    {isorts : List Level}
    (hsorts : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env true false resSort nP
      (tfvs.drop nP) [] nIdx = .ok isorts)
    {ppsAll : (Name → Nat) → List Term}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP)).reverse ρp) :
    IdxOk (idxUniv ψ isorts) ρp (((ppsAll ψ).drop nP)) := by
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hT : Opened mp.base2 ψ (nP + nIdx) cvTa.type tfvs trest
      (((ppsAll ψ)).reverse) (.sort (resSort.eval ψ)) :=
    opened_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
  have hc := claimsAt_of hμ mp ψ F
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hlenT : tfvs.length = nP + nIdx := openPisAtFvars_length _ hopT
  have hΓ : (((ppsAll ψ)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  -- the index binders' universes at their frames
  have hbnd : ∀ j, j < nIdx → ∀ ρ : Nat → V,
      Sat V ((((ppsAll ψ)).reverse).drop (nP + nIdx - (nP + j))) ρ →
      interp V ρ ((((ppsAll ψ)).reverse).getD (nP + nIdx - 1 - (nP + j)) default)
        ∈ˢ (univ (idxUniv ψ isorts) : V) := by
    intro j hj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, -, -⟩ := hrows j hj
    have hfvT : tfvs[nP + j]? = some fv := by
      rw [List.getElem?_drop] at hfv; exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hT.var (nP + j) fv hfvT
    have hCtx := hT.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hT.doms (nP + j) fv hfvT
    have hrow := hc.sortRow hi hens hws hb hL hCtx hread ρ hρ
    exact univ_mono (eval_le_idxUniv (ψ := ψ) hu) _ hrow.2
  have hρp' : Sat V ((((ppsAll ψ)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_fields_eq (hFD.len ψ) nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
    exact hρp
  have hok := fieldsOkB_of_frame rfl hΓ hT.okΓ (fun j hj ρ hρ _ => hbnd j hj ρ hρ) 0 (Nat.zero_le _)
    ρp hρp'
  have hbd := fieldsBound_of_frame rfl hΓ hbnd 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hok hbd
  exact ⟨hok, hbd⟩



universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Recursive constructor data -/

/-- A recursive constructor datum: name, field count, field data,
index readings, recursive positions, per-field index-expression
readings, per-field telescopes (empty at a finitary field). -/
abbrev CtorDatumR :=
  Name × Nat × List Term × List Term × List Nat × List (List Term) ×
    List (List Term)

/-! ## The constructor data, per block -/

/-- The recursive constructor data of a list of constructors, from
constructor `j` on. -/
@[expose] def fixCtorDataList (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List Term))
    (tssF : Nat → (Name → Nat) → List (List Term)) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatumR
  | [], _ => []
  | c :: cs, j =>
    (c.1.name, c.2, dsF j ψ, esF j ψ, ConLeche.recIdxOf (ksF j), eissF j ψ, tssF j ψ) ::
      fixCtorDataList dsF esF ksF eissF tssF ψ cs (j + 1)

omit [SetTheory V] in
theorem fixCtorDataList_length (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List Term))
    (tssF : Nat → (Name → Nat) → List (List Term)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by
    simp [fixCtorDataList, fixCtorDataList_length dsF esF ksF eissF tssF ψ cs (j + 1)]

omit [SetTheory V] in
theorem fixCtorDataList_getElem? (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List Term))
    (tssF : Nat → (Name → Nat) → List (List Term)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j)[i]?
        = (cs[i]?).map fun c =>
            (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ, ConLeche.recIdxOf (ksF (j + i)),
              eissF (j + i) ψ, tssF (j + i) ψ)
  | [], _, _ => rfl
  | c :: cs, j, 0 => by simp [fixCtorDataList]
  | c :: cs, j, i + 1 => by
    simp only [fixCtorDataList, List.getElem?_cons_succ]
    rw [fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ cs (j + 1) i]
    congr 2
    funext c
    rw [show j + 1 + i = j + (i + 1) from by omega]




open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower


variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Boundness through openings -/

omit [SetTheory V] in
/-- An opening's variables (their types) and residual are bounded when
the opened term is. -/
theorem openPisAtFvars_constsBound {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      ConstsBound env₀ e → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, ConstsBound env₀ x) ∧ ConstsBound env₀ o
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE dom bd, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [constsBound_forallE] at he
        have hfv : ConstsBound env₀ (Expr.fvar d dom) := by
          rw [constsBound_fvar]; exact he.1
        obtain ⟨hfvs, ho⟩ := openPisAtFvars_constsBound n
          (ConstsBound.instantiate1 hfv bd 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop


/-!
## The recursive constructor data across a cons

`BlockCtorDataI` (`BlockData.lean`) crosses a cons whose head is not
the member's former: the sum data cross as before (`CtorDataI.cross`),
and the opened variables' types are bounded at the constructor's
environment (`openPisAtFvars_constsBound`), so their readings cross
too.
-/


/-- **The block constructor data cross a cons** whose head is not the
member's former. -/
theorem BlockCtorDataI.cross {m : EnvModel V env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List Term}
    {Es : (Name → Nat) → List Term} {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (h : BlockCtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs
      fvsP xFvs xrest)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    BlockCtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs
      fvsP xFvs xrest := by
  have hbase := h.toCtorDataI.cross hfresh hT hcb hcbI m₂ hac
  -- the opened variables' types are bounded
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hfvs, -⟩ := openPisAtFvars_constsBound (nP + nF) hcb hopAll
  have hxcb : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ConstsBound env x.fvarTypeD := by
    intro i x hx
    have hb := hfvs x (List.mem_append_right _ (List.mem_of_getElem? hx))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hx
    rw [constsBound_fvar] at hb
    exact hb
  exact {
    toCtorDataI := hbase
    opens := h.opens
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => by
      rw [hac]
      exact denote_cons_mono hfresh ψ (nP + i) (hxcb i x hx) (h.domRead ψ i x hx)
    resShape := h.resShape }


/-!
## The constructors' loop, over any former leaf

`ctorsLoopEta`: the sum route's constructor loop with the former's
leaf abstract — any closed reading `leafT` — and, per constructor, the
fibre fold `stageCtorGen` consumes (`hfold`): the leaf at the parameter
variables and the constructor's index readings, under a fitting field
spine, is the indexed sum route's restricted tagged union at the index
values.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  RecRule)


variable {V : Type w} [SetTheory V] {μ : CheckMode}

set_option maxHeartbeats 6400000 in
/-- **The constructors' conses, in order**, over an ABSTRACT η
invariant.  What the cons needs of the environment's η families is
only that the invariant survives a constructor's cons (`hEtaCons`) and
that it refutes the head as another stored family's η constructor
(`hEtaOther`, `capsOk_cons_native`'s `hother`).  At a block it is
`ConLeche.BlockEtaInv` (`BlockCtorsLoop.lean`), since `checkBlockInds`
leaves up to `k` families pending. -/
theorem ctorsLoopEta (hμ : μ.isVerified = true)
    {F : Nat} {p : InductiveShape} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hCtors : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ envI p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa ctors = .ok (ctorsA, sortss))
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List Term}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List Term}
    {esF : Nat → (Name → Nat) → List Term} {srcsF : Nat → List (Option Nat)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0),
      DomsBelow p.nP Fs)
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))
    (hIdx : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF j ψ).take p.nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP)) bs →
        SpineFit ρ (((ppsAll ψ).drop p.nP)) (idxValsAt ρ (esF j ψ) bs))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → Term)
      (mC : EnvModel V ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts, env'.tables⟩),
      cA ∈ ctorsA → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC)
    -- the block's capability record and its laws at every carrier the
    -- invariant reaches

    (caps : IndCaps)
    (leafT : (Name → Nat) → Term)
    (hTlawsOf : ∀ {env' : Env} (m' : EnvModel V env') (k : Nat) (cA : ConstantVal × Nat),
      ctorsA[k]? = some cA → Inv m' →
      (∀ cvC nPc nFc, env'.find? cA.1.name = some (.ctorInfo cvC nPc nFc) → cvC = cA.1) →
      FormerData m' cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m'.acval p.cvT.name ψ = leafT ψ) →
      (∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (p.resSort.eval ψ) k (dsF k ψ) (((dsF k ψ).drop p.nP))
            (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))) →
      CapsLawsAt m' p.cvT.name cvTa caps)
    (EtaInv : Env → Prop)
    (hEtaCons : ∀ (env' : Env) (cA : ConstantVal × Nat), cA ∈ ctorsA →
      env'.find? cA.1.name = none → EtaInv env' →
      EtaInv ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts, env'.tables⟩)
    (hEtaOther : ∀ (env' : Env) (cA : ConstantVal × Nat), cA ∈ ctorsA →
      env'.find? cA.1.name = none → EtaInv env' →
      ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
        env'.find? T' = some (.indInfo cvT' caps') → T' ≠ p.cvT.name →
        ConLeche.reservedBasisNames.contains T' = false → caps'.eta = true →
        ConLeche.EtaFamilyStored ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts, env'.tables⟩ T' caps' →
        caps'.etaCtor ≠ cA.1.name)
    (hfold : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP)) bs →
        interp V (consList bs ρ)
            (Term.mkAppN (leafT ψ) (paramBvars p.nP cA.2 ++ esF j ψ))
          = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
              (consList (idxValsAt ρ (esF j ψ) bs) ρ)
              (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                (essOf (ctorDataList dsF esF ψ ctorsA 0))))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      EtaInv env →
      env.find? p.cvT.name = some (.indInfo cvTa caps) →
      FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, mp.base2.acval p.cvT.name ψ = leafT ψ) →
      ConsedAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      PendingAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V μ (ConLeche.consSumCtors p.nP rest env),
        EtaInv (ConLeche.consSumCtors p.nP rest env) ∧
        (ConLeche.consSumCtors p.nP rest env).find? p.cvT.name
          = some (.indInfo cvTa caps) ∧
        FormerData mp'.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll ∧
        (∀ ψ, mp'.base2.acval p.cvT.name ψ = leafT ψ) ∧
        ConsedAt mp'.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
          idxF dsF esF srcsF ctorsA ctorsA.length ∧
        Inv mp'.base2
  | [], k, env, mp, _, hk, hE, hfT, hFD, hleafT, hcons, _, hinv => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    exact ⟨mp, hE, hfT, hFD, hleafT, hcons, hinv⟩
  | cA :: rest, k, env, mp, hrest, hk, hE, hfT, hFD, hleafT, hcons, hpend, hinv => by
    have hcAk : ctorsA[k]? = some cA := by
      have := hrest 0; simpa using this.symm
    obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv hCtors
    have hkl : k < ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hcAk).1; omega
    obtain ⟨hnF, _, -, hCtor⟩ := hall k (ctors[k]) cA (List.getElem?_eq_getElem hkl) hcAk
    rw [← hnF] at hCtor
    obtain ⟨hfresh, htr, hidxRes, hCD⟩ := hpend k cA (Nat.le_refl _) hcAk
    have hlpsC : cA.1.levelParams = p.cvT.levelParams := hlpsA cA (List.mem_of_getElem? hcAk)
    have hTC : p.cvT.name ≠ cA.1.name := by
      intro h; rw [h, hfresh] at hfT; exact nomatch hfT
    have hFsj : ∀ ψ, (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))[k]?
        = some (((dsF k ψ).drop p.nP)) := by
      intro ψ
      rw [fssOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    have hEsj : ∀ ψ, (essOf (ctorDataList dsF esF ψ ctorsA 0))[k]? = some (esF k ψ) := by
      intro ψ
      rw [essOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    -- the stage
    have hfoldC : ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsAll ψ).take p.nP)).reverse ρ →
        ∀ bs : List V, SpineFit ρ (((dsF k ψ).drop p.nP)) bs →
          interp V (consList bs ρ) (ctorBodyAVI mp.base2 p.cvT.name p.nP cA.2 ψ (esF k ψ))
            = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
                (consList (idxValsAt ρ (esF k ψ) bs) ρ)
                (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                  (essOf (ctorDataList dsF esF ψ ctorsA 0)))) := by
      intro ψ ρ hρ bs hsp
      unfold ctorBodyAVI
      rw [hleafT ψ]
      exact hfold k cA hcAk ψ ρ hρ bs hsp
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfT)).2.2.1
    obtain ⟨mpC, hacC⟩ := stageCtorGen (j := k)
      (hEtaOther env cA (List.mem_of_getElem? hcAk) hfresh hE) mp hCtor hfresh htr hfT hlpsT hlpsC
      (fun m₂ hag hleafC₂ => by
        have hac : m₂.acval = acvalWith mp.base2.acval cA.1.name
            (fun ψ => m₂.acval cA.1.name ψ) := by
          funext n ψ
          by_cases hn : n = cA.1.name
          · subst hn; exact (congrFun acvalWith_self ψ).symm
          · rw [hag n hn]; exact (congrFun (acvalWith_ne hn) ψ).symm
        exact hTlawsOf m₂ k cA hcAk (hInv mp.base2 cA (fun ψ => m₂.acval cA.1.name ψ) m₂
            (List.mem_of_getElem? hcAk) hfresh hac hinv)
          (fun cvC nPc nFc h =>
            (ConstantInfo.ctorInfo.inj (Option.some.inj
              ((ConLeche.Env.find?_cons_self (.ctorInfo cA.1 p.nP cA.2) env).symm.trans
                h))).1.symm)
          (hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hcbT m₂ hac)
          (fun ψ => by rw [hag _ hTC]; exact hleafT ψ) hleafC₂)
      hFD hCD
      hfoldC hFsj hEsj hFssParams hFssBelow (hiff k cA hcAk)
      (fun ψ ρ hρ => hFssOkP ψ ρ ((hiff k cA hcAk ψ ρ).mpr hρ)) (hIdx k cA hcAk)
    -- the invariants at the extension
    have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ htr
    have hE' : EtaInv ⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts, env.tables⟩ :=
      hEtaCons env cA (List.mem_of_getElem? hcAk) hfresh hE
    have hfT' : (⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts, env.tables⟩ : Env).find? p.cvT.name
        = some (.indInfo cvTa caps) := ConLeche.Env.find?_cons_of_fresh hfresh hfT
    have hFD' : FormerData mpC.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
      hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hcbT mpC.base2 hacC
    have hleafT' : ∀ ψ, mpC.base2.acval p.cvT.name ψ = leafT ψ := by
      intro ψ
      rw [hacC]
      show acvalWith mp.base2.acval cA.1.name _ p.cvT.name ψ = _
      rw [acvalWith_ne hTC]
      exact hleafT ψ
    have hcons' : ConsedAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      rcases Nat.lt_or_ge i k with hlt | hge
      · obtain ⟨⟨hfi, hlpsi, hCDi⟩, hresi, hleaf⟩ := hcons i cAi hlt hcAi
        have hne : cAi.1.name ≠ cA.1.name := names_ne_of_nodup hnd hcAi hcAk (by omega)
        have hcbi : ConstsBound env cAi.1.type :=
          constsBound_of_constsResolve _
            (mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfi)).2.2.1
        refine ⟨⟨ConLeche.Env.find?_cons_of_fresh hfresh hfi, hlpsi,
          hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcbi
            (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hresi e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cAi.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleaf ψ
      · have hik : i = k := by omega
        subst hik
        obtain rfl := Option.some.inj (hcAk.symm.trans hcAi)
        refine ⟨⟨ConLeche.Env.find?_cons_self (.ctorInfo cA.1 p.nP cA.2) env, hlpsC,
          hCD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcbC
            (fun e he => constsBound_of_constsResolve _ (hidxRes e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hidxRes e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cA.1.name ψ = _
        rw [acvalWith_self]
    have hpend' : PendingAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      obtain ⟨hfreshi, htri, hresi, hCDi⟩ := hpend i cAi (by omega) hcAi
      have hne : cA.1.name ≠ cAi.1.name := names_ne_of_nodup hnd hcAk hcAi (by omega)
      refine ⟨?_, Expr.constsResolve_mono htri, fun e he => Expr.constsResolve_mono (hresi e he),
        hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC
          (constsBound_of_constsResolve _ htri)
          (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩
      rw [ConLeche.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hfreshi
    have hrest' : ∀ i, rest[i]? = ctorsA[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    have hinv' : Inv mpC.base2 :=
      hInv mp.base2 cA _ mpC.base2 (List.mem_of_getElem? hcAk) hfresh hacC hinv
    exact ctorsLoopEta hμ hCtors hnd hlpsT hlpsA hFssParams hFssBelow hiff hFssOkP hIdx Inv hInv
      caps leafT hTlawsOf EtaInv hEtaCons hEtaOther hfold rest (k + 1) _ mpC hrest'
      (by simp at hk; omega) hE' hfT' hFD' hleafT' hcons' hpend' hinv'




variable {V : Type w} [SetTheory V]

/-! ## Application spines over the point -/

/-- An application spine over a function whose reading is the point is
graded whenever the head and the arguments are: the `.app` clause is
witnessed at regime `0` by the singleton of the argument's reading. -/
theorem mkAppN_wellDenoted_of_pt :
    ∀ {f : Term} {args : List Term} {ρ : Nat → V},
      WellDenoted V ρ f → interp V ρ f = (pt : V) →
      (∀ a ∈ args, WellDenoted V ρ a) →
      WellDenoted V ρ (Term.mkAppN f args)
  | _, [], _, hf, _, _ => hf
  | f, a :: args, ρ, hf, hpt, hargs => by
    rw [Term.mkAppN_cons]
    have ha := hargs a List.mem_cons_self
    refine mkAppN_wellDenoted_of_pt (f := .app f a) ?_ ?_
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
    · rw [WellDenoted_app]
      refine ⟨hf, ha, 0, image (fun _ => interp V ρ a) unitSet, fun _ => unitSet, ?_, ?_, ?_,
        fun h => absurd rfl h⟩
      · rw [hpt]; exact pt_mem_piR_zero_of fun _ _ => pt_mem_unitSet
      · exact mem_image.mpr ⟨pt, pt_mem_unitSet, rfl⟩
      · intro _ _ _; rw [← univ_zero]; exact unitSet_mem_univ 0
    · rw [interp_app, hpt, app_pt]



open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)





open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  RecRule)


/-! ## The semantic data of a block -/

/-- The constructors' field lists. -/
@[expose] def fssOfR (nP : Nat) (cds : List CtorDatumR) : List (List Term) :=
  cds.map fun cd => (cd.2.2.1.drop nP)

/-- The constructors' index readings. -/
@[expose] def essOfR (cds : List CtorDatumR) : List (List Term) := cds.map fun cd => cd.2.2.2.1


omit [SetTheory V] in
theorem fssOfR_getElem? (nP : Nat) (cds : List CtorDatumR) (j : Nat) :
    (fssOfR nP cds)[j]? = (cds[j]?).map fun cd => (cd.2.2.1.drop nP) := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (essOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.1 := by simp [essOfR]


omit [SetTheory V] in
theorem fssOfR_length (nP : Nat) (cds : List CtorDatumR) : (fssOfR nP cds).length = cds.length := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_length (cds : List CtorDatumR) : (essOfR cds).length = cds.length := by simp [essOfR]

/-! ## Restricting an assignment to the level parameters -/

/-- The restriction of an assignment to a level-parameter list. -/
@[expose] def restrictΨ (lps : List Name) (ψ : Name → Nat) : Name → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem restrictΨ_agree (lps : List Name) (ψ : Name → Nat) :
    ∀ q ∈ lps, restrictΨ lps ψ q = ψ q := by
  intro q hq
  simp [restrictΨ, hq]

omit [SetTheory V] in
theorem restrictΨ_congr {lps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) : restrictΨ lps ψ₁ = restrictΨ lps ψ₂ := by
  funext q
  unfold restrictΨ
  split
  · next hq => exact h q hq
  · rfl

/-! ## The data at the parameters -/

omit [SetTheory V] in
/-- The constructor data at two assignments agreeing on the data. -/
theorem fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List Term}
    {esF₁ esF₂ : Nat → (Name → Nat) → List Term} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List Term)}
    {tssF₁ tssF₂ : Nat → (Name → Nat) → List (List Term)} {ψ₁ ψ₂ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (∀ i, i < cs.length → dsF₁ (j + i) ψ₁ = dsF₂ (j + i) ψ₂ ∧ esF₁ (j + i) ψ₁ = esF₂ (j + i) ψ₂ ∧
        eissF₁ (j + i) ψ₁ = eissF₂ (j + i) ψ₂ ∧ tssF₁ (j + i) ψ₁ = tssF₂ (j + i) ψ₂) →
      fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ₁ cs j = fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ₂ cs j
  | [], _, _ => rfl
  | c :: cs, j, h => by
    simp only [fixCtorDataList]
    obtain ⟨h1, h2, h3, h4⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h1 h2 h3 h4
    rw [h1, h2, h3, h4, fixCtorDataList_congr cs (j + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i from by omega] at this]

/-! ## The subsingleton criterion at a field -/

/-- An unsourced field of a source-bounded chain is a truth value at
every fitting prefix spine. -/
theorem fieldsBoundSrc_at {ρ : Nat → V} :
    ∀ {Fs : List Term} {srcs : List (Option Nat)} {i : Nat} {fs : List V},
      FieldsBoundSrc ρ Fs srcs → srcs[i]? = some none → SpineFit ρ (Fs.take i) fs → i < Fs.length →
      interp V (consList fs ρ) (Fs.getD i default) ∈ˢ (univ 0 : V)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hs, _, _ => by simp at hs
  | F :: Fs, s :: srcs, 0, fs, hb, hs, hsp, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    cases fs with
    | nil => exact hb.1 hs
    | cons a fs' => exact hsp.elim
  | F :: Fs, s :: srcs, i + 1, fs, hb, hs, hsp, hi => by
    cases fs with
    | nil => exact hsp.elim
    | cons a fs' =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons, List.getD_cons_succ]
      exact fieldsBoundSrc_at (hb.2 a ha) (by simpa using hs) hsp' (by simpa using hi)



/-! ## The two routes' data lists -/

omit [SetTheory V] in
/-- The recursive route's field chains are the sum route's. -/
theorem fssOfR_fixCtorDataList (nP : Nat) (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List Term))
    (tssF : Nat → (Name → Nat) → List (List Term)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = fssOf nP (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: fssOf nP (ctorDataList dsF esF ψ cs (k + 1))
    rw [fssOfR_fixCtorDataList nP dsF esF ksF eissF tssF ψ cs (k + 1)]

omit [SetTheory V] in
/-- The recursive route's index readings are the sum route's. -/
theorem essOfR_fixCtorDataList (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List Term))
    (tssF : Nat → (Name → Nat) → List (List Term)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = essOf (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: essOf (ctorDataList dsF esF ψ cs (k + 1))
    rw [essOfR_fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1)]

/-! ## The data lists, congruent in one component -/


omit [SetTheory V] in
theorem fssOfR_fixCtorDataList_getD {nP : Nat} {dsF : Nat → (Name → Nat) → List Term}
    {esF : Nat → (Name → Nat) → List Term} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List Term)}
    {tssF : Nat → (Name → Nat) → List (List Term)} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j []
      = ((dsF j ψ).drop nP) := by
  rw [List.getD_eq_getElem?_getD, fssOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

omit [SetTheory V] in
theorem essOfR_fixCtorDataList_getD {dsF : Nat → (Name → Nat) → List Term}
    {esF : Nat → (Name → Nat) → List Term} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List Term)}
    {tssF : Nat → (Name → Nat) → List (List Term)} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j [] = esF j ψ := by
  rw [List.getD_eq_getElem?_getD, essOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl


/-!
## The projection entry's law on the tagged carrier

The three clauses of `TowerEntryLaw` at a STRUCTURE-LIKE block — one
constructor, no index — whose carrier is the TAGGED tower: the
family's fibre at the (empty) index tuple is the sum route's
restricted tagged union over the one constructor,
`sumSet w (sumFibre w ρ [Fs ++ [idxEqAV []]])` (the block's `hfold`),
whose elements are `inj 0 (mkTower (fs ++ [pt]))` with `fs` fitting the
fields.  So field `i` is `projS (i + 1)` of a member (the tag in front;
every structure carries it), the tuple below the tag is `dropS 1`, and each
law has one pair component to cross:

* **(A) the typing law** (`fixEntryTypingCore`): a member projects at
  `i + 1` into the body's residual — the graph regime by the tower's
  projection membership below the tag, the squash regime by the point;
* **(B) the iota law** (`fixEntryIotaCore`/`fixEntryIotaCoreZero`): the
  projection of a graded constructor application is the selected field
  (`sumMkAV_fold`: the application folds to the tagged tuple);
* **(C) the η law** (`fixEntryEtaCore`): a member is the constructor at
  the parameters and its own projections below the tag.

`fixFibre_elim`/`fixFibre_zero_elim` are the one-constructor fibre's
eliminations, `wellDenoted_proj1_sum`/`wellDenoted_proj1_pt` grade the tag
projection.

**The former's leaf is ABSTRACT** (`L`): what the three laws read of it
is its FOLD (`hfold`) and — in (A) alone, to recover the parameter
spine from a graded application — that it is the parameters' λ-tower
(`hlam`).  So the cores serve every block member's leaf, as
`fibreUnitLaw` does for the fieldless capability laws.
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps ProjEntry)


/-! ## The one-constructor fibre -/

/-- The elements of the one-constructor fibre in the graph regime:
tagged point-terminated tuples fitting the fields, the tuple a member
of the restricted tower. -/
theorem fixFibre_elim {w : Nat} (hw : w ≠ 0) {ρ' : Nat → V} {Fs : List Term} {x : V}
    (hx : x ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    ∃ fs : List V, x = inj 0 (mkTower (fs ++ [pt])) ∧ SpineFit ρ' Fs fs ∧
      mkTower (fs ++ [pt]) ∈ˢ towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []])) := by
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    obtain ⟨fs, hfs, hsp, -⟩ := spineFit_append_idxEq.mp hfit
    refine ⟨fs, ?_, hsp, ?_⟩
    · rw [heta, hfs]
    · rw [← hfs, ← heta]; exact ha
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The one-constructor fibre in the squash regime: the point, with a
fitting field spine. -/
theorem fixFibre_zero_elim {ρ' : Nat → V} {Fs : List Term} {x : V}
    (hx : x ∈ˢ sumSet 0 (sumFibre 0 ρ' [Fs ++ [idxEqAV []]])) :
    x = pt ∧ ∃ fs : List V, SpineFit ρ' Fs fs := by
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨-, as, hfits⟩ := towerSet_zero_elim _ ha
    obtain ⟨fs, -, hsp, -⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfits)
    exact ⟨fs, hsp⟩
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The tuple below the tag. -/
theorem dropS_one_inj (j : Nat) (a : V) : dropS 1 (inj j a) = a := by
  show ssnd (spair (vnat j) a) = a
  exact ssnd_spair _ _

/-- A projection past the tag is the tuple's. -/
theorem projS_succ_inj (i j : Nat) (a : V) : projS (i + 1) (inj j a) = projS i a := by
  rw [projS_add_dropS, dropS_one_inj]

/-- The restricted chain of the one constructor at no index is the
unrestricted one. -/
theorem fieldsBound_append_idxEq {w : Nat} {ρ' : Nat → V} {Fs : List Term} (hw : w ≠ 0)
    (hok : FieldsOkB w ρ' Fs) : FieldsBound w ρ' (Fs ++ [idxEqAV []]) :=
  (FieldsOkB_append_idxEq hok fun _ _ _ he => absurd he List.not_mem_nil).toBound hw

/-! ## The tag projection's grading -/

/-- `.snd` of a member of the tagged union is graded: the union is a
Σ over the numerals whose fibres are bounded towers. -/
theorem wellDenoted_proj1_sum {w : Nat} (hw : w ≠ 0) {ρ' ρ : Nat → V} {Fs : List Term}
    {e : Term} (hb : FieldsBound w ρ' (Fs ++ [idxEqAV []]))
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, w, w, omega, natFibre (sumFibre w ρ' [Fs ++ [idxEqAV []]]), ?_, ?_, ?_⟩
  · rw [nat_max_self]; exact hval
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact omega_mem_univ_succ w'
  · intro k hk
    obtain ⟨j, rfl, hfib⟩ := natFibre_of_mem _ hk
    rw [hfib]
    cases j with
    | zero =>
      rw [sumFibre_of_getElem? rfl]
      exact towerSet_mem_univ _ (boundS_teleOfFields.mpr hb)
    | succ j =>
      rw [sumFibre_of_ge (by simp)]
      exact empty_mem_univ w

/-- `.snd` of the point is graded (the squash regime). -/
theorem wellDenoted_proj1_pt {ρ : Nat → V} {e : Term} (hok : WellDenoted V ρ e)
    (hpt : interp V ρ e = (pt : V)) : WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
    fun _ _ => unitSet_mem_univ 0⟩
  rw [hpt, nat_max_self]
  exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet

/-- The projection reading past the tag, graded at a member of the
one-constructor fibre (both regimes). -/
theorem wellDenoted_projNV_succ_fibre {w i : Nat} {ρ' ρ : Nat → V} {Fs : List Term}
    {e : Term} (hokB : w ≠ 0 → FieldsOkB w ρ' Fs)
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]]))
    (hi : i < Fs.length) : WellDenoted V ρ (projNV (i + 1) e) := by
  show WellDenoted V ρ (projNV i (.snd e))
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := fixFibre_zero_elim hval
    refine wellDenoted_projNV_pt (wellDenoted_proj1_pt hok hpt) ?_
    rw [interp_snd, hpt, ssnd_pt]
  · obtain ⟨fs, heq, -, hmem⟩ := fixFibre_elim hw hval
    have hb := fieldsBound_append_idxEq hw (hokB hw)
    refine wellDenoted_projNV_tower hb hmem (wellDenoted_proj1_sum hw hb hok hval) ?_
      (by rw [List.length_append, List.length_singleton]; omega)
    rw [interp_snd, heq]
    exact ssnd_spair _ _

/-! ## (A) the typing law -/

theorem fixEntryTypingCore {w nP nF i : Nat} {pps ds eds : List Term}
    {L R : Term} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP) (hlenEds : eds.length = nP + 1)
    (hiff : ∀ ρ : Nat → V, Sat V (pps).reverse ρ ↔
      Sat V ((ds.take nP)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP)).take j) as →
        interp V (consList as ρ) (((ds.drop nP)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hguard : w = 0 → (sorts.getD i .zero).eval ψ = 0 ∧
      ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : Term, (ds.drop nP).getD i default = X.liftN 1 (i - 1 - j))
    (hi : i < nF)
    -- the leaf is the parameters' λ-tower (the ONLY shape the law reads
    -- of it; the fixpoint content is `hfold`)
    (hlam : ∃ B, L = mkLamsAV pps B)
    -- the family at the parameters is the one-constructor fibre
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps) ts →
      ts.foldl SetTheory.app (interp V ρ L)
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP)) ++ [idxEqAV []]]))
    (hres : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP)).reverse (fun j => ρ (j + 1)) →
      interp V ρ R
        = interp V (consList (projList i (dropS 1 (ρ 0))) (fun j => ρ (j + 1)))
            (((ds.drop nP)).getD i default))
    (hokR : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP)).reverse (fun j => ρ (j + 1)) →
      WellDenoted V ρ R) :
    ∀ (ρ : Nat → V) (vs : List Term) (x rest : Term),
      vs.length = nP →
      WellDenoted V ρ (Term.mkAppN L vs) →
      interp V ρ (Term.mkAppN L vs) ≠ pt →
      WellDenoted V ρ x →
      interp V ρ x ∈ˢ interp V ρ (Term.mkAppN L vs) →
      Term.peelPis (mkPisAV eds R) (vs ++ [x]) = some rest →
      WellDenoted V ρ (projNV (i + 1) x) ∧ WellDenotedTy V ρ rest ∧
        interp V ρ (projNV (i + 1) x) ∈ˢ interp V ρ rest := by
  intro ρ vs x rest hlenVs hokApp hneApp hokx hmem hpeel
  have hlenFs : (((ds.drop nP))).length = nF := by simp [hlenDs]
  -- the parameter fit
  have hsp : SpineFit ρ (pps) (vs.map (interp V ρ)) := by
    obtain ⟨B, hB⟩ := hlam
    -- the family applied to the parameters is not the point (the law's
    -- premise: it is the type of `x`, "not pt" source (1) at the caller)
    have h := spineFit_of_wellDenoted_mkAppN_lam (lds := pps)
      (b := B) (σ := ρ)
      hokApp hneApp (by rw [hB]) (by simp [hlenVs, hlenPps])
    exact h
  have hlenAs : (vs.map (interp V ρ)).length = nP := by simp [hlenVs]
  -- the member of the fibre
  have hx : interp V ρ x ∈ˢ sumSet w
      (sumFibre w (consList (vs.map (interp V ρ)) ρ) [((ds.drop nP)) ++ [idxEqAV []]]) := by
    rw [interp_mkAppN_foldl, hfold ρ _ hsp] at hmem
    exact hmem
  -- the constructor's parameter frame
  have hspC : SpineFit ρ ((ds.take nP)) (vs.map (interp V ρ)) :=
    (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ _ (by simp [hlenVs, hlenPps])).mp hsp
  have hsatC : Sat V ((ds.take nP)).reverse (consList (vs.map (interp V ρ)) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspC
    rwa [List.append_nil] at this
  -- the frame at the subject's chain
  have hchain : chain V ρ (vs ++ [x]) = cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ) := by
    unfold chain
    rw [consN_eq_consList, List.map_append, consList_append]
    rfl
  have hframeX : (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) 0 ∈ˢ sumSet w
      (sumFibre w (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1))
        [((ds.drop nP)) ++ [idxEqAV []]]) := hx
  have hframeS : Sat V ((ds.take nP)).reverse
      (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1)) := hsatC
  -- the residual
  have hrest : rest = Term.instSeq (vs ++ [x]) nP R := by
    have h := peelPis_of_piTeleAV (nP + 1) (by rw [← hlenEds]; exact piTeleAV_mkPisAV eds R)
      (ws := vs ++ [x]) (by simp [hlenVs])
    rw [hpeel] at h
    have := Option.some.inj h
    rwa [Nat.add_sub_cancel] at this
  have hlen' : Term.instSeq (vs ++ [x]) nP R
      = Term.instSeq (vs ++ [x]) ((vs ++ [x]).length - 1) R := by
    simp [hlenVs]
  have hinterpRest : interp V ρ rest
      = interp V (consList (projList i (dropS 1 (interp V ρ x))) (consList (vs.map (interp V ρ)) ρ))
          (((ds.drop nP)).getD i default) := by
    rw [hrest, hlen', interp_instSeq, hchain, hres _ hframeX hframeS]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the projection's grading
    exact wellDenoted_projNV_succ_fibre (fun hw => hokB _ hsatC) hokx hx (by rw [hlenFs]; exact hi)
  · -- the residual's grading, and it is a type: the field's sort at a
    -- fitting prefix (squash: the point prefix agrees with one)
    refine ⟨?_, ?_⟩
    · rw [hrest, hlen']
      refine wellDenoted_instSeq _ ?_ ?_
      · intro w' hw'
        rcases List.mem_append.mp hw' with h | h
        · exact WellDenoted_mkAppN_args vs hokApp w' h
        · rw [List.mem_singleton] at h; subst h; exact hokx
      · rw [hchain]; exact hokR _ hframeX hframeS
    · rw [hinterpRest]
      by_cases hw : w = 0
      · subst hw
        obtain ⟨hpt, as', hspAs⟩ := fixFibre_zero_elim hx
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
        have hlenTake : (as'.take i).length = i :=
          spineFit_take_length hspAs (by rw [hlenFs]; omega)
        rw [hpt, dropS_pt, projList_pt]
        rw [interp_congr_lifts i
          (free_of_diff hlenDs hi (hsorts _ hsatC) (hguard rfl).2 hfree hspAs)
          (consList_prefix_agree hlenTake _).2]
        exact IsTy_of_mem_univ (hsorts _ hsatC i hi _ hpre)
      · obtain ⟨fs, heq, hspF, -⟩ := fixFibre_elim hw hx
        have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
        rw [heq, dropS_one_inj, projList_mkTower_take (by omega)]
        exact IsTy_of_mem_univ (hsorts _ hsatC i hi _
          (spineFit_prefix_next hspF (by rw [hlenFs]; exact hi)).1)
  · -- the membership
    rw [hinterpRest, projNV_interp]
    by_cases hw : w = 0
    · -- squash: the point in the proof field at the point prefix,
      -- which agrees with a fitting prefix at every used slot
      subst hw
      obtain ⟨hpt, as', hspAs⟩ := fixFibre_zero_elim hx
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
      have hz := hsorts _ hsatC i hi _ hpre
      rw [(hguard rfl).1] at hz
      have hval := mem_univ_zero hz hnext
      rw [hval] at hnext
      rw [hpt, projS_pt, dropS_pt, projList_pt]
      have hlenTake : (as'.take i).length = i := spineFit_take_length hspAs (by rw [hlenFs]; omega)
      rw [interp_congr_lifts i
        (free_of_diff hlenDs hi (hsorts _ hsatC) (hguard rfl).2 hfree hspAs)
        (consList_prefix_agree hlenTake _).2]
      exact hnext
    · -- graph: the tower's projection membership below the tag
      obtain ⟨fs, heq, -, hmem'⟩ := fixFibre_elim hw hx
      rw [heq, projS_succ_inj, dropS_one_inj]
      have h := projS_mem_teleOfFields (fun h0 => absurd h0 hw) hmem' (i := i)
        (by rw [List.length_append, List.length_singleton, hlenFs]; omega)
      rw [List.getElem_append_left (by rw [hlenFs]; exact hi)] at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenFs]; exact hi)]
      exact h

/-! ## (B) the iota law -/

theorem fixEntryIotaCore {w nP nF i : Nat} {ds : List Term} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP)))
    (ys : List Term) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds) (ys.map (interp V ρ))) :
    interp V ρ (projNV (i + 1) (Term.mkAppN
        (sumMkAV w 0 ds ((ds.drop nP)) (uChains [(ds.drop nP)])) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [show ds = (ds.take nP) ++ (ds.drop nP) from by
    rw [List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hsat : Sat V ((ds.take nP)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  have hokU : SumFieldsOkB w (consList as ρ) (uChains [(ds.drop nP)]) := by
    intro Fs' hFs'
    simp only [uChains, List.map_cons, List.map_nil, List.mem_singleton] at hFs'
    subst hFs'
    exact FieldsOkB_append_idxEq (hokB _ hsat) fun _ _ e he => absurd he List.not_mem_nil
  have hfold := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := 0) hw hsp₁ hsp₂
    hokU rfl
  rw [List.take_append_drop] at hfold
  rw [projNV_interp, interp_mkAppN_foldl, heq, hfold, projS_succ_inj,
    projS_mkTower_getD (by rw [hlenBs]; exact hi)]
  -- the selected argument
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD (l := ys), List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi), Option.getD_some]
  exact Option.some.inj h1

/-- The iota law at a squash instantiation: the constructor application
is the point, so is its projection, and the selected field is a
proposition's member. -/
theorem fixEntryIotaCoreZero {nP nF i : Nat} {ds : List Term} {ρ : Nat → V}
    {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP)).take j) as →
        interp V (consList as ρ) (((ds.drop nP)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0)
    (ys : List Term) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds) (ys.map (interp V ρ))) :
    interp V ρ (projNV (i + 1) (Term.mkAppN
        (sumMkAV 0 0 ds ((ds.drop nP)) (uChains [(ds.drop nP)])) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [projNV_interp, interp_mkAppN_foldl, sumMkAV_zero, foldl_app_pt', projS_pt]
  rw [show ds = (ds.take nP) ++ (ds.drop nP) from by
    rw [List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hlenFs : (((ds.drop nP))).length = nF := by simp [hlenDs]
  have hsat : Sat V ((ds.take nP)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hsp₂ (by rw [hlenFs]; exact hi)
  have hz' := hsorts _ hsat i hi _ hpre
  rw [hz] at hz'
  have hval : bs.getD i pt = pt := mem_univ_zero hz' hnext
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  have h2 : bs[i] = bs.getD i pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)]
    rfl
  rw [← Option.some.inj h1, h2, hval]

/-! ## (C) the η law -/

theorem fixEntryEtaCore {w nP nF : Nat} {pps ds : List Term}
    {L : Term} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps).reverse ρ ↔
      Sat V ((ds.take nP)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP)))
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps) ts →
      ts.foldl SetTheory.app (interp V ρ L)
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP)) ++ [idxEqAV []]]))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app (interp V ρ L)) :
    x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app
      (interp V ρ (sumMkAV w 0 ds ((ds.drop nP))
        (uChains [(ds.drop nP)]))) := by
  rw [hfold ρ ts hsp] at hx
  have hlenFs : (((ds.drop nP))).length = nF := by simp [hlenDs]
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := fixFibre_zero_elim hx
    rw [hpt, sumMkAV_zero, foldl_app_pt']
  · obtain ⟨fs, heq, hspF, -⟩ := fixFibre_elim hw hx
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    have hsp₁ : SpineFit ρ ((ds.take nP)) ts :=
      (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ ts (by simp [hlen, hlenPps])).mp hsp
    have hsat : Sat V ((ds.take nP)).reverse (consList ts ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      rwa [List.append_nil] at this
    have hokU : SumFieldsOkB w (consList ts ρ) (uChains [(ds.drop nP)]) := by
      intro Fs' hFs'
      simp only [uChains, List.map_cons, List.map_nil, List.mem_singleton] at hFs'
      subst hFs'
      exact FieldsOkB_append_idxEq (hokB _ hsat) fun _ _ e he => absurd he List.not_mem_nil
    have hfold' := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := 0) hw hsp₁ hspF
      hokU rfl
    rw [List.take_append_drop] at hfold'
    -- the projections past the tag are the tuple's fields
    have hprojs : ((List.range nF).map fun j => projS (j + 1) x) = fs := by
      rw [heq]
      have h1 : ((List.range nF).map fun j => projS (j + 1) (inj 0 (mkTower (fs ++ [pt]))))
          = (List.range nF).map fun j => projS j (mkTower (fs ++ [pt])) :=
        List.map_congr_left fun j _ => projS_succ_inj j 0 _
      rw [h1, ← projList_eq_map_range, ← hlenF, projList_mkTower_take (Nat.le_refl _),
        List.take_length]
    rw [hprojs, hfold', heq]


/-- A spine fitting a chain of truth values is all points. -/
theorem spineFit_pts_of_univZero {ρ : Nat → V} :
    ∀ {Fs : List Term} {fs : List V}, SpineFit ρ Fs fs →
      (∀ j, j < Fs.length → ∀ as : List V, SpineFit ρ (Fs.take j) as →
        interp V (consList as ρ) (Fs.getD j default) ∈ˢ (univZero : V)) →
      fs = List.replicate fs.length pt
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | F :: Fs, a :: as, h, hz => by
    have h0 : interp V ρ F ∈ˢ (univZero : V) := by
      simpa using hz 0 (by simp) [] trivial
    have ha : a = pt := eq_pt_of_mem_univZero h0 h.1
    have ih := spineFit_pts_of_univZero (ρ := cons a ρ) h.2 (fun j hj as' hsp' => by
      have := hz (j + 1) (by simp; omega) (a :: as') ⟨h.1, hsp'⟩
      simpa using this)
    rw [List.length_cons, List.replicate_succ]
    subst ha
    exact congrArg _ ih

/-- **(D) the η constructor's coherence** (task #342 L11b): a member's
parameters, then its projections below the tag, fit the constructor's
telescope — in the graph regime the projections are the tuple's fields
(`fixFibre_elim`), in the squash regime the member is the point, every
field a proof (`hzero`, the O5 bound at an η family), so its fitting
fields are the point's projections. -/
theorem fixEntryEtaFitCore {w nP nF : Nat} {pps ds : List Term}
    {L B : Term} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps).reverse ρ ↔
      Sat V ((ds.take nP)).reverse ρ)
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps) ts →
      ts.foldl SetTheory.app (interp V ρ L)
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP)) ++ [idxEqAV []]]))
    (hzero : w = 0 → ∀ ρ' : Nat → V, Sat V ((ds.take nP)).reverse ρ' →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ' (((ds.drop nP)).take j) as →
        interp V (consList as ρ') (((ds.drop nP)).getD j default)
          ∈ˢ (univZero : V))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app (interp V ρ L)) :
    ∃ restC : V, TeleFit V ρ (mkPisAV ds B)
      (ts ++ (List.range nF).map fun j => projS (j + 1) x) restC := by
  rw [hfold ρ ts hsp] at hx
  have hlenFs : (((ds.drop nP))).length = nF := by simp [hlenDs]
  have hsp₁ : SpineFit ρ ((ds.take nP)) ts :=
    (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ ts (by simp [hlen, hlenPps])).mp hsp
  have hsat : Sat V ((ds.take nP)).reverse (consList ts ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  suffices h : ∃ fs, SpineFit (consList ts ρ) ((ds.drop nP)) fs ∧
      ((List.range nF).map fun j => projS (j + 1) x) = fs by
    obtain ⟨fs, hspF, heq⟩ := h
    refine ⟨_, teleFit_mkPisAV_of_spineFit ?_⟩
    rw [heq, ← List.take_append_drop nP ds]
    exact hsp₁.append hspF
  by_cases hw : w = 0
  · subst hw
    obtain ⟨rfl, fs, hspF⟩ := fixFibre_zero_elim hx
    refine ⟨fs, hspF, ?_⟩
    have hrep := spineFit_pts_of_univZero hspF (fun j hj as hsp' =>
      hzero rfl _ hsat j (by rwa [hlenFs] at hj) as hsp')
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    rw [hrep, hlenF, List.map_congr_left (fun j _ => projS_pt (j + 1)), List.map_const',
      List.length_range]
  · obtain ⟨fs, heq, hspF, -⟩ := fixFibre_elim hw hx
    refine ⟨fs, hspF, ?_⟩
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    rw [heq]
    have h1 : ((List.range nF).map fun j => projS (j + 1) (inj 0 (mkTower (fs ++ [pt]))))
        = (List.range nF).map fun j => projS j (mkTower (fs ++ [pt])) :=
      List.map_congr_left fun j _ => projS_succ_inj j 0 _
    rw [h1, ← projList_eq_map_range, ← hlenF, projList_mkTower_take (Nat.le_refl _),
      List.take_length]


/-!
## The projection table's cons

`stageFixTable`: the P step at the projection **table** of a
STRUCTURE-LIKE block member (one constructor, no index), which
`stageBlockTables` takes at every table.  The family at the parameters
is the one-constructor fibre of the tagged union (`sumSet w (sumFibre w
ρ' [Fs ++ [idxEqAV []]])`, the block's `hfold`), so the subject of a
projection is a TAGGED point-terminated tuple and the fields sit at
projection offset `1`.  The three laws are the entry
cores above; the bodies' frames are `bodyFrames` at the fibre's frame.
The former's leaf is ABSTRACT here too (`L`, with `hlam`/`hfold`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  ProjEntry ProjTable RecRule RecFieldKind)


/-! ## Small facts -/

omit [SetTheory V] in
/-- Lifting by nothing is the identity on a field chain. -/
theorem liftFields_zero : ∀ (k : Nat) (Fs : List Term), liftFields 0 k Fs = Fs
  | _, [] => rfl
  | k, F :: Fs => by rw [liftFields_cons, Term.liftN_zero, liftFields_zero (k + 1) Fs]

omit [SetTheory V] in
/-- The one constructor's restricted chain at no index is its
unrestricted chain closed by the trivial index equation. -/
theorem rChains_single_nil (Fs : List Term) :
    rChains 0 0 [Fs] [[]] = [Fs ++ [idxEqAV []]] := by
  simp [rChains, rChain, idxEqsAt, liftFields_zero]

/-! ## The P step -/

set_option maxHeartbeats 3200000 in
/-- **The P step at a projection table**, against the one-constructor
fibre. -/

theorem stageFixTable (mp : EnvModelM V μ env)
    {T : Name} {lps : List Name} {nP : Nat} {resSort : Level} {isProp : Bool}
    {cvTa cvCa : ConstantVal} {nF : Nat} {sorts : List Level}
    {envOut : Env} {caps : IndCaps}
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name
      lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) cvCa env = .ok envOut)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hcaps : caps.eta = true → (Level.isEquiv resSort .zero == some true) = false ∧
      caps.etaCtor = cvCa.name ∧ caps.etaParams = nP ∧ caps.etaFields = nF)
    (hlpsT : cvTa.levelParams = lps)
    (hfC : env.find? cvCa.name = some (.ctorInfo cvCa nP nF))
    (hlpsC : cvCa.levelParams = lps)
    (hstripC : (cvCa.type.stripPis (nP + nF)).isSome = true)
    (hProp : isProp = (Level.isEquiv resSort .zero == some true))
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresR : ConLeche.reservedBasisNames.contains (T.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains cvCa.name = false)
    {pps ds : (Name → Nat) → List Term} {Es : (Name → Nat) → List Term}
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hCDread : ∀ ψ, denote mp.base2.acval env ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))))
    (hCDlen : ∀ ψ, (ds ψ).length = nP + nF)
    (hCDbelow : ∀ ψ, DomsBelow 0 (ds ψ))
    (hleq : ∀ k, k < nF → isProp = false → Level.leq (sorts.getD k .zero) resSort = some true)
    {L : (Name → Nat) → Term}
    (hleafT : ∀ ψ, mp.base2.acval T ψ = L ψ)
    (hleafC : ∀ ψ, mp.base2.acval cvCa.name ψ
      = sumMkAV (resSort.eval ψ) 0 (ds ψ) (((ds ψ).drop nP))
          (uChains [((ds ψ).drop nP)]))
    (hlam : ∀ ψ, ∃ B, L ψ = mkLamsAV (pps ψ) B)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList ts ρ)
            [((ds ψ).drop nP) ++ [idxEqAV []]]))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP)))
    (hboundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
        isProp = false → FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP)))
    (hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    ∃ (tbl : ProjTable) (mp' : EnvModelM V μ envOut),
      envOut = ⟨env.consts, tbl :: env.tables⟩ ∧ tbl.structName = T ∧
      env.findTable? T = none ∧
      mp'.base2.acval = mp.base2.acval := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, hTs, hT0, rfl⟩ := ConLeche.checkStructProjTable_inv hTbl
  let tbl : ProjTable := ⟨T, lps, nP, cvCa.name, nF, resSort,
    bodies, ConLeche.structProjGuards cvCa.type nP nF sorts⟩
  -- the field-chain facts, in the frames' spelling
  have hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ → resSort.eval ψ ≠ 0 →
      FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP)) := by
    intro ψ ρ hρ hw
    cases hp : isProp
    · exact hboundP ψ ρ hρ hp
    · exfalso
      apply hw
      rw [hp] at hProp
      exact Level.isEquiv_sound (beq_iff_eq.mp hProp.symm) ψ
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
      FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP)) :=
    fun ψ ρ h => hfields ψ ρ h
  -- the guards' content: the official join over the used earlier slots
  have hguardSem : ∀ k, k < nF → ∀ ψ : Name → Nat,
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 →
      (sorts.getD k .zero).eval ψ = 0 ∧
      ∀ j, j < k → ConLeche.structUsedLater cvCa.type nP j = true →
        (sorts.getD j .zero).eval ψ = 0 := by
    intro k hk ψ h0
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)] at h0
    exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
  have hguardOf : ∀ k, k < nF → ∀ ψ : Name → Nat,
      (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk ψ hall
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)]
    exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
  have hO5 : ∀ k, k < nF → (Level.isEquiv resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, resSort.eval ψ = 0 →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine hguardOf k hk ψ fun j hj => ?_
    have := Level.leq_sound (hleq j (by omega) (by rw [hProp]; exact hne)) ψ
    omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  have hlenA : fvsA.length = nP + nF := openPisAtFvars_length _ hopAll
  have hfree : ∀ (ψ : Name → Nat) (k : Nat), k < nF → ∀ (j : Nat), j < k →
      ConLeche.structUsedLater cvCa.type nP j = false →
      ∃ X : Term, (((ds ψ).drop nP)).getD k default = X.liftN 1 (k - 1 - j) := by
    intro ψ k hk j hj hun
    have hsome : (cvCa.type.stripPis (nP + j + 1)).isSome = true :=
      ConLeche.stripPis_isSome_of_le (by omega) hstripC
    obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
    have hrest : rest.hasLooseBVar 0 = false := by
      unfold ConLeche.structUsedLater at hun
      rw [hst] at hun
      have hun' : rest.hasLooseBVarB 0 = false := hun
      rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
      exact hun'
    obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (nP + nF) (nP + j) hopAll (by omega)
      hst hrest (by
        intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
        exact absurd hl List.not_mem_nil)
    obtain ⟨pps', b, hstA, -, -, hbind⟩ := denote_openPis (nP + nF) hopAll (hCDread ψ)
    have hppsEq : pps' = ds ψ := by
      have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
      rw [hCDlen ψ] at h2
      exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
    obtain ⟨x, hx⟩ : ∃ x, fvsA[nP + k]? = some x :=
      ⟨fvsA[nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨q, hq, hqread⟩ := hbind (nP + k) x hx
    rw [hppsEq] at hq
    have hW : Expr.WScoped (0 + (nP + k)) (Expr.fvarTypeD x) :=
      openPisAtFvars_typeWScoped (nP + nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
    have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ nP + j := by
      intro l hl
      have hsub : l ∈ x.fvarLeaves := by
        cases x with
        | fvar idx ty =>
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl
        | _ => exact hl
      have := hleavesK (nP + k) (by omega) x hx l hsub
      simpa using this
    obtain ⟨X, hX⟩ := denote_liftN_of_leaf_free mp.base2 (0 + (nP + k)) (Expr.fvarTypeD x) hW
      (q := nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
    refine ⟨X, ?_⟩
    have hFk : (((ds ψ).drop nP)).getD k default = q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, hq, Option.getD_some]
    rw [hFk, hX, show 0 + (nP + k) - 1 - (nP + j) = k - 1 - j from by omega]
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfC)).2.2.1
  -- the lookups at the extension
  have hfT₂ : (⟨env.consts, tbl :: env.tables⟩ : Env).find? T
      = some (.indInfo cvTa caps) := hfT
  have hfC₂ : (⟨env.consts, tbl :: env.tables⟩ : Env).find? cvCa.name
      = some (.ctorInfo cvCa nP nF) := hfC
  have hfTbl₂ : (⟨env.consts, tbl :: env.tables⟩ : Env).findTable? T = some tbl := by
    rw [ConLeche.Env.findTable?_pushTable, ite_eq_left ⟨rfl, hTs⟩]
  have hprev₂ : ∀ j, j < nF →
      ∃ entry, (⟨env.consts, tbl :: env.tables⟩ : Env).findProj? T j
        = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < nF → ConLeche.TowerHead env (tbl.entry i) :=
    fun i hi => ⟨hresT, hresR, hresC, hi, ⟨cvTa, caps, hfT, hlpsT⟩,
      ⟨cvCa, hfC, hlpsC, hstripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvModel V ⟨env.consts, tbl :: env.tables⟩,
      m₂.acval = mp.base2.acval →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', hac'⟩ :=
      declStep_preserves_of_pushTable mp (t := tbl) hT0 hwf' hhead hlaw
    exact ⟨tbl, mp', rfl, rfl, hT0, hac'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < nF := hi
  have hacT : ∀ ψ, m₂.acval T ψ = mp.base2.acval T ψ := by
    intro ψ
    rw [hac]
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = mp.base2.acval cvCa.name ψ := by
    intro ψ
    rw [hac]
  have hFD₂ : FormerData m₂ cvTa nP resSort pps :=
    hFD.pushTable (t := tbl) hT0 hcbT m₂ hac
  -- the constructor type's reading at the extension
  have hCDread₂ : ∀ ψ, denote m₂.acval ⟨env.consts, tbl :: env.tables⟩ ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI m₂ T nP nF ψ (Es ψ))) := by
    intro ψ
    have hbody : ctorBodyAVI m₂ T nP nF ψ (Es ψ)
        = ctorBodyAVI mp.base2 T nP nF ψ (Es ψ) := by
      unfold ctorBodyAVI; rw [hacT]
    rw [hbody, hac]
    exact denote_pushTable_mono (t := tbl) hT0 ψ 0 hcbC (hCDread ψ)
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, hcf⟩ :=
    ConLeche.structProjBody_open hbodies hstripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, caps, hfT₂, hlpsT, hcaps⟩,
    hO5 i hi, cvCa, hfC₂, hlpsC, ?_, ?_⟩
  · -- the per-instantiation laws
    intro us _
    -- the subject's frame: a member of the one-constructor fibre of
    -- the tagged union (offset 1)
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ hcf hCf hCb
      (fun j hj => hprev₂ j (by omega)) hi
      (hCDlen (Level.substFn φ lps us))
      (hCDbelow (Level.substFn φ lps us))
      (hCDread₂ (Level.substFn φ lps us))
      (fun ρ h => hfields _ ρ h) (hsortsF _)
      (used := ConLeche.structUsedLater cvCa.type nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ sumSet (resSort.eval (Level.substFn φ lps us))
        (sumFibre (resSort.eval (Level.substFn φ lps us)) (fun j => ρ (j + 1))
          [((ds (Level.substFn φ lps us)).drop nP) ++ [idxEqAV []]]))
      (fun ρ hx _ hw => by
        rw [hw] at hx
        exact fixFibre_zero_elim hx)
      (fun ρ hx _ hw => by
        obtain ⟨fs, heq, hsp, -⟩ := fixFibre_elim hw hx
        have hlenF : fs.length = nF := by
          rw [hsp.length_eq, List.length_drop, hCDlen, Nat.add_sub_cancel_left]
        rw [heq, dropS_one_inj, ← hlenF, projList_mkTower_take (Nat.le_refl _), List.take_length]
        exact hsp)
      (fun ρ hx hsat j hj => by
        refine wellDenoted_projNV_succ_fibre (fun _ => hokB _ _ hsat) trivial ?_ ?_
        · rw [interp_bvar]; exact hx
        · rw [List.length_drop, hCDlen, Nat.add_sub_cancel_left]; exact hj)
    have hread : denote m₂.acval ⟨env.consts, tbl :: env.tables⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (nP + 1) (.sort 0)) fdomA) := by
      show denote m₂.acval _ φ 0 (ConLeche.projTele (nP + 1)
        ((bodies.getD i default).instantiateLevelParams lps us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ lps us 0]
      exact denote_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hneApp hokx hmem hpeel
      have hguard' : resSort.eval (Level.substFn φ lps us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ lps us) = 0 ∧
          ∀ j, j < i → ConLeche.structUsedLater cvCa.type nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ lps us) = 0 :=
        fun h0 => hguardSem i hi _ (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = L (Level.substFn φ lps us) := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT, hleafT]
      rw [hacT'] at hokApp hneApp hmem
      exact fixEntryTypingCore (hCDlen _) (hFD.len _) (by simp) (hiff _) (hokB _)
        (hsortsF _) (used := ConLeche.structUsedLater cvCa.type nP) hguard' (hfree _ i hi) hi
        (hlam _) (hfold _) hresFd (hokFd (fun h0 => (hguard' h0).2)) ρ vs x rest hlenVs hokApp hneApp
        hokx hmem hpeel
    · -- (B): the constructor type's reading at the instantiation,
      -- then the two regimes
      refine ⟨mkPisAV (ds (Level.substFn φ lps us))
        (ctorBodyAVI m₂ T nP nF (Level.substFn φ lps us)
          (Es (Level.substFn φ lps us))), ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCDread₂ _
      · intro hguardAt ρ ys rest hlen hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = sumMkAV (resSort.eval (Level.substFn φ lps us)) 0
              (ds (Level.substFn φ lps us))
              (((ds (Level.substFn φ lps us)).drop nP))
              (uChains [((ds (Level.substFn φ lps us)).drop nP)]) := by
          show m₂.acval cvCa.name (Level.substFn φ lps us) = _
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        show interp V ρ (projNV (i + 1) _) = _
        have hsp : SpineFit ρ ((ds (Level.substFn φ lps us)))
            (ys.map (interp V ρ)) :=
          spineFit_of_teleFit (by simp only [List.length_map, hlen, hCDlen]; rfl) hfit
        by_cases hw : resSort.eval (Level.substFn φ lps us) = 0
        · -- squash: the certified fit pins the selected field to a
          -- proposition's domain
          rw [hw]
          exact fixEntryIotaCoreZero (hCDlen _) hi (hsortsF _)
            (hguardSem i hi _ (hguardAt hw)).1 ys hlen hsp
        · -- graph: the certified fit pins the spine (no "not pt" step)
          exact fixEntryIotaCore hw (hCDlen _) hi (hokB _) ys hlen hsp
  · -- (C)
    intro cvT capsT hf us _
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
    have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
        = L (Level.substFn φ lps us) := by
      show m₂.acval T (Level.substFn φ lps us) = _
      rw [hacT, hleafT]
    refine ⟨mkPisAV (pps (Level.substFn φ lps us))
      (.sort (resSort.eval (Level.substFn φ lps us))), ?_, hFD.okTy _, ?_, ?_⟩
    · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, hlpsT]
      exact hFD₂.read _
    rotate_left
    · -- (D) the coherence, at an η family: the fields of a squash
      -- instance are proofs (the O5 bound)
      intro heta cvC nPc nFc hfC'
      have hfC'' : (⟨env.consts, tbl :: env.tables⟩ : Env).find? cvCa.name
          = some (.ctorInfo cvC nPc nFc) := hfC'
      rw [hfC₂] at hfC''
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfC'')
      have hnP : isProp = false := by
        have h1 := (hcaps heta).1
        rw [hProp]; exact h1
      refine ⟨mkPisAV (ds (Level.substFn φ lps us))
        (ctorBodyAVI m₂ T nP nF (Level.substFn φ lps us)
          (Es (Level.substFn φ lps us))), ?_, fun ρ ts rest x hlents hfit hmem => ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCDread₂ _
      · have hsp := spineFit_of_teleFit (by rw [hFD.len]; exact hlents) hfit
        rw [hacT'] at hmem
        refine fixEntryEtaFitCore (hCDlen _) (hFD.len _) (hiff _) (hfold _)
          (fun hw ρ' hρ' j hj as hsp' => ?_) ts x hlents hsp hmem
        have hz : (sorts.getD j .zero).eval (Level.substFn φ lps us) = 0 := by
          have := Level.leq_sound (hleq j hj hnP) (Level.substFn φ lps us)
          omega
        have := hsortsF _ ρ' hρ' j hj as hsp'
        rwa [hz, univ_zero] at this
    · intro ρ ts rest x hlents hfit hmem
      have hsp := spineFit_of_teleFit (by rw [hFD.len]; exact hlents) hfit
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = sumMkAV (resSort.eval (Level.substFn φ lps us)) 0
            (ds (Level.substFn φ lps us))
            (((ds (Level.substFn φ lps us)).drop nP))
            (uChains [((ds (Level.substFn φ lps us)).drop nP)]) := by
        show m₂.acval cvCa.name (Level.substFn φ lps us) = _
        rw [hacC, hleafC]
      rw [hacT'] at hmem
      rw [hacC']
      show x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app _
      exact fixEntryEtaCore (hCDlen _) (hFD.len _) (hiff _) (hokB _) (hfold _) ts x hlents hsp hmem


/-!
## The reflexive telescopes' bounds

A reflexive field's type is a Π-tower over its telescope of the family
at the calls' tuples; at a `Type`-valued block (`w ≠ 0`) the family's
slot at such a field is the nested function space over the telescope, which
lives in `univ w` only when every telescope domain
does.  The install checks each field's sort against the block's
(`checkStructFieldSortsI`: `imax` of the domains' sorts and the
family's, at most `resSort`); at `w ≠ 0` the `imax` is a `max`, so
every domain's sort is at most `resSort` (the Π-inference walked along
the opening), and the sort claim of the tuple tier (`sortRow`) reads
each domain, at the frame under the earlier ones, into `univ w`
(`teleBound_walk`, the context discipline opened binder by binder).
-/


/-! ## The bound, walked along the telescope -/

/-- **The telescope's domains are bounded**, binder by binder: at a
frame satisfying the earlier domains, the next domain's reading is
graded and lies in `univ w` — the sort claim at the context opened by
the earlier binders. -/
theorem teleBound_walk (hμ : μ.isVerified = true) (mp : EnvModelM V μ env) (ψ : Name → Nat)
    {w : Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {Δ : List Term}
      {tl : List Term},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk mp.base2 ψ d Δ e → Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denote mp.base2.acval env ψ (d + k) a.fvarTypeD = some (tl.getD k default)) →
      (∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (d + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (d + k) t = .ok u ∧ Level.eval ψ u ≤ w) →
      ∀ k, k < n → ∀ ρ : Nat → V, Sat V (((tl.take k)).reverse ++ Δ) ρ →
        WellDenoted V ρ (tl.getD k default) ∧ interp V ρ (tl.getD k default) ∈ˢ (univ w : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf, k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body, hop, hws, hb =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases tl with
        | nil => exact absurd hlen (by simp)
        | cons t0 tl' =>
        have hlen' : tl'.length = n := by simpa using hlen
        have hws2 : Expr.WScoped d ty ∧ Expr.WScoped d body := by
          simp only [Expr.WScoped] at hws; exact hws
        -- the first domain's frame conditions
        have hbty : ty.looseBVarsBounded 0 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.1
        have hbb : body.looseBVarsBounded 1 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.2
        have hLty : Expr.LeavesBounded ty := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)
        have hLbody : Expr.LeavesBounded body := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)
        -- the first domain's row
        have hread0 : denote mp.base2.acval env ψ d ty = some t0 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨F, t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := (claimsAt_of hμ mp ψ F).sortRow hi hens hws2.1 hbty hLty hCty hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.reverse_nil, List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk mp.base2 ψ (d + 1) (t0 :: Δ) (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ =>
              ⟨(hrow ρ hρ).1, IsTy_of_mem_univ (hrow ρ hρ).2⟩
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denote mp.base2.acval env ψ (d + 1 + k) a.fvarTypeD = some (tl'.getD k default) := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
              ConLeche.inferTypeCore μ env F (d + 1 + k) a.fvarTypeD = .ok t ∧
              ConLeche.ensureSortCore μ env F (d + 1 + k) t = .ok u ∧ Level.eval ψ u ≤ w := by
            intro k a hk
            obtain ⟨F, t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨F, t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k)).reverse ++ (t0 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ
          have := teleBound_walk hμ mp ψ n hop' hlen' hC' hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _, hop, _, _
    | .letE _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [ConLeche.openPisAtFvars] at hop




/-!
## The fieldless one-constructor block's laws

A fieldless, index-free, one-constructor block (`Unit`-shaped;
`True`-shaped at `Prop`) claims
unit-likeness (`blockCapsAt`: not η — official's `try_eta_struct` at
zero fields is decided by `is_def_eq_unit_like` already), and the P
tier owes `UnitLaw` at every carrier from the former's cons on.  The
law reads off the former's fold alone: at the dummy former the family
is EMPTY (`fixEmptyUnitLaw`), at the block's leaf the fibre is the
one tagged empty tuple (`fibreUnitLaw`).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)


/-- **Unit-likeness at the dummy former's leaf**: the family with no
constructor chain is empty, so the law is vacuous. -/
theorem fixEmptyUnitLaw {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List Term}
    (hleaf : ∀ ψ, m.acval T ψ = sumTyAV (w ψ) (pps ψ) [])
    (hread : ∀ ψ, denote m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpar : ∀ ψ, caps.unitParams = (pps ψ).length) :
    UnitLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x y hlen hfit hx _
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfit
    rw [hleaf, sumTyAV_fold hsp (fun _ h => absurd h List.not_mem_nil)] at hx
    exfalso
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx
      obtain ⟨-, i, a, ha⟩ := sumSet_zero_elim hx
      rw [sumFibre_of_ge (Nat.zero_le _)] at ha
      exact not_mem_empty _ ha
    · obtain ⟨i, a, ha, -⟩ := sumSet_elim hw hx
      rw [sumFibre_of_ge (Nat.zero_le _)] at ha
      exact not_mem_empty _ ha

/-- **Unit-likeness at a fieldless one-constructor block's leaf**: the
fibre is the one tagged empty tuple (the point at a squash instance).

The leaf `L` is ABSTRACT — what the law reads of it is its FOLD, and
nothing else — so it serves a block member's (`blockTyG` through
`blockHoleFold_params`). -/
theorem fibreUnitLaw {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List Term}
    {L : (Name → Nat) → Term}
    (hleaf : ∀ ψ, m.acval T ψ = L ψ)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hread : ∀ ψ, denote m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpar : ∀ ψ, caps.unitParams = (pps ψ).length) :
    UnitLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x y hlen hfit hx hy
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfit
    rw [hleaf, hfold _ ρ ts hsp] at hx hy
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx hy
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hx
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hy
      rfl
    · obtain ⟨fs, rfl, hspx, -⟩ := fixFibre_elim (Fs := []) hw hx
      obtain ⟨gs, rfl, hspy, -⟩ := fixFibre_elim (Fs := []) hw hy
      cases fs with
      | cons _ _ => exact hspx.elim
      | nil =>
        cases gs with
        | cons _ _ => exact hspy.elim
        | nil => rfl

/-- **The fieldless η law**: a member is the one

tagged empty tuple, and the constructor along the parameters is that
tuple (the point at a squash instance). -/
theorem fibreEtaLaw0 {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps ds : (Name → Nat) → List Term}
    {L : (Name → Nat) → Term}
    (hleaf : ∀ ψ, m.acval T ψ = L ψ)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hleafC : ∀ ψ, m.acval caps.etaCtor ψ = sumMkAV (w ψ) 0 (ds ψ) [] (uChains [[]]))
    (hread : ∀ ψ, denote m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((pps ψ)) as → SpineFit ρ ((ds ψ)) as)
    (hpar : ∀ ψ, caps.etaParams = (pps ψ).length)
    (hreadC : ∀ (cvC : ConstantVal) (nPc nFc : Nat),
      env.find? caps.etaCtor = some (.ctorInfo cvC nPc nFc) →
      cvC.levelParams = cvT.levelParams ∧ ∃ B : (Name → Nat) → Term,
        ∀ ψ, denote m.acval env ψ 0 cvC.type = some (mkPisAV (ds ψ) (B ψ))) :
    EtaLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  rotate_left
  · -- the coherence: the parameters fit the constructor's telescope
    intro cvC nPc nFc hfC
    obtain ⟨hlpsC, B, hB⟩ := hreadC cvC nPc nFc hfC
    refine ⟨mkPisAV (ds (Level.substFn φ' cvT.levelParams us))
      (B (Level.substFn φ' cvT.levelParams us)), ?_, fun ρ ts rest x hlen hfitT _ => ?_⟩
    · rw [denotePInstLevels m φ' cvC.levelParams us 0 cvC.type, hlpsC]
      exact hB _
    · have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfitT
      exact ⟨_, teleFit_mkPisAV_of_spineFit (hfit _ ρ ts hsp)⟩
  · intro ρ ts rest x hlen hfitT hx
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfitT
    rw [hleaf, hfold _ ρ ts hsp] at hx
    rw [hleafC]
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hx
      rw [hw, sumMkAV_zero, foldl_app_pt']
    · obtain ⟨fs, rfl, hspx, -⟩ := fixFibre_elim (Fs := []) hw hx
      cases fs with
      | cons _ _ => exact hspx.elim
      | nil =>
        have hfd := sumMkAV_fold hw (j := 0) (pds := ds _) (fds := []) (Fss := uChains [[]])
          (ρ := ρ) (as := ts) (bs := []) (by simpa using hfit _ ρ ts hsp) trivial
          (SumFieldsOkB_uChains fun _ h => by
            simp only [List.mem_singleton] at h
            subst h; trivial) rfl
        simp only [List.append_nil] at hfd
        rw [hfd]

end ConLeche.Model
