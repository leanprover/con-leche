module

public import ConLeche.Model.Inductives.WhnfContentOfRun
public import ConLeche.Model.Inductives.NestedCtorLeaf
import ConLeche.Verify.Inductives.NestedCtorNames
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.FormerFront
import ConLeche.Verify.ProjSlots

public section

/-!
# The restored constructors' kit (task #279 M-D′ D3, DESIGN §M.54)

The small facts D3's run assembly (`NestedCtorRun.lean`) consumes,
each stated where the assembly needs it: a Π-telescope's openers carry
the telescope's own resolution and its projection-table discipline
through an opening (`openPisAtFvars_fvarTypeD_constsResolve`,
`Expr.projTablesOk_instantiate1`, `openPisAtFvars_projTablesOk`); a
reading transfers DOWN to the formers' environment when the subject
resolves AT `env₁` and its `.proj` nodes are table-backed at their own
slots (`down_of_resolve₁`, the K.13 twin of `down_of_resolve`); a
Π-tower all of whose codomain bits are zero has a `univZero` body at
every fitting spine (`annotValid_mkPisAV_zero`); a member's carrier
applied along its parameters and indices lives in its own universe
(`IndRep.app_mem_univ`); a restored constructor carries the position
bookkeeping of the auxiliary block's constructor it came from
(`restoredCtor_pos`); and a checked constructor's fields resolve
before the block, by kind (`ctorFieldsRes_of_chk`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType AuxStored NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The openers of a telescope -/

omit [SetTheory V] in
/-- A resolving telescope's openers carry resolving domains. -/
theorem openPisAtFvars_fvarTypeD_constsResolve {env : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {b : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, b) → e.constsResolve env = true →
      ∀ x ∈ fvs, x.fvarTypeD.constsResolve env = true
  | 0, e, d, fvs, b, h, _ => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun x hx => by simp at hx
  | n + 1, .forallE ty bd m, d, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars] at h
    split at h
    · next fvs' b' hop =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.constsResolve, Bool.and_eq_true] at he
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa [Expr.fvarTypeD] using he.1
      · exact openPisAtFvars_fvarTypeD_constsResolve n hop
          (Expr.constsResolve_instantiate1 he.1 0 he.2) x hx
    · exact nomatch h
  | n + 1, .bvar _, _, _, _, h, _ | n + 1, .fvar _ _, _, _, _, h, _
  | n + 1, .sort _, _, _, _, h, _ | n + 1, .const _ _, _, _, _, h, _
  | n + 1, .app _ _, _, _, _, h, _ | n + 1, .lam _ _ _, _, _, _, h, _
  | n + 1, .letE _ _ _, _, _, _, h, _ | n + 1, .lit _, _, _, _, h, _
  | n + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

omit [SetTheory V] in
/-- The projection-table discipline survives binder opening. -/
theorem Expr.projTablesOk_instantiate1 {env : Env} {d : Nat} {ty : Expr}
    (hty : ty.projTablesOk env = true) :
    ∀ {e : Expr} (k : Nat), e.projTablesOk env = true →
      (e.instantiate1 (.fvar d ty) k).projTablesOk env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [ConLeche.Expr.instantiate1, ConLeche.Expr.projTablesOk]
  case bvar i =>
    split
    · simpa [ConLeche.Expr.projTablesOk] using hty
    · split <;> simp [ConLeche.Expr.projTablesOk]

omit [SetTheory V] in
/-- A telescope whose `.proj` nodes are table-backed opens to a body
and openers whose `.proj` nodes are table-backed. -/
theorem openPisAtFvars_projTablesOk {env : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {b : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, b) → e.projTablesOk env = true →
      b.projTablesOk env = true ∧ ∀ x ∈ fvs, x.fvarTypeD.projTablesOk env = true
  | 0, e, d, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨he, fun x hx => by simp at hx⟩
  | n + 1, .forallE ty bd m, d, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars] at h
    split at h
    · next fvs' b' hop =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.projTablesOk, Bool.and_eq_true] at he
      obtain ⟨hb, hfvs⟩ := openPisAtFvars_projTablesOk n hop
        (Expr.projTablesOk_instantiate1 he.1 0 he.2)
      refine ⟨hb, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa [Expr.fvarTypeD] using he.1
      · exact hfvs x hx
    · exact nomatch h
  | n + 1, .bvar _, _, _, _, h, _ | n + 1, .fvar _ _, _, _, _, h, _
  | n + 1, .sort _, _, _, _, h, _ | n + 1, .const _ _, _, _, _, h, _
  | n + 1, .app _ _, _, _, _, h, _ | n + 1, .lam _ _ _, _, _, _, h, _
  | n + 1, .letE _ _ _, _, _, _, h, _ | n + 1, .lit _, _, _, _, h, _
  | n + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

/-! ## The downward transfer at resolution at `env₁` -/

/-- **A term resolving AT `env₁` transfers down** (the K.13 twin of
`down_of_resolve`): its blind mentions and its literals' support are
stored at `env₁` outright, and its `.proj` nodes sit at slots `env₁`
itself tables (`Expr.projTablesOk`), so none of them sits at a slot
`env₁` leaves empty. -/
theorem down_of_resolve₁ {μ : CheckMode} {env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    (hF : FindPreserved env₁ envAux)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    {ψ : Name → Nat} {dpt : Nat} {e : Expr} (hres : e.constsResolve env₁ = true)
    (hpt : e.projTablesOk env₁ = true)
    {ea : AnnotTerm} (h : denoteMeta mpAux.base2.acval envAux ψ dpt e = some ea) :
    denoteMeta mp₁.base2.acval env₁ ψ dpt e = some ea := by
  rw [denoteMeta_acval_congr hag]
  exact denoteMeta_down_blind hF dpt e
    (fun T hT => Expr.find?_isSome_of_mentionsConst e hres
      (Expr.mentionsConst_of_mentionsConstE e hT))
    (litsResolve_of_constsResolve _ hres)
    (fun sn i h1 _ => Expr.noProjAt_blank _ (Expr.noProjAt_of_projTablesOk h1 _ hpt))
    h

/-! ## A zero-bit Π-tower's body -/

/-- A Π-tower all of whose codomain bits are zero has a `univZero`
body at every fitting spine. -/
theorem annotValid_mkPisAV_zero {T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}, ds ≠ [] → (∀ d ∈ ds, d.2.1 = 0) →
      AnnotValid V σ (mkPisAV ds T) →
      ∀ as, SpineFit σ (ds.map (·.2.2)) as → interp V (consList as σ) T ∈ˢ (univZero : V)
  | [], _, hne, _, _, _, _ => absurd rfl hne
  | d :: ds, σ, _, hz, hv, as, hsp => by
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      rw [List.map_cons] at hsp
      simp only [mkPisAV, AnnotValid_pi] at hv
      rw [consList_cons]
      cases ds with
      | nil =>
        cases as with
        | nil => exact hv.2.2 (hz d List.mem_cons_self) a hsp.1
        | cons _ _ => exact hsp.2.elim
      | cons d' ds' =>
        exact annotValid_mkPisAV_zero (by simp) (fun x hx => hz x (List.mem_cons_of_mem _ hx))
          (hv.2.1 a hsp.1) as hsp.2

/-! ## A member's carrier, applied -/

namespace IndRep

/-- **A member's carrier, applied along fitting parameters and
indices, lives in the member's own universe**: the carrier is the
least fixed point's fibre (`leaf`), a member of `univ (d.w ψ)`
(`famSpace_app`). -/
theorem app_mem_univ {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (hrep : IndRep m T cvT cvR mI rP rules d mm) (ψ : Name → Nat) {ρ : Nat → V}
    {as is : List V} (has : SpineFit ρ (d.params ψ) as)
    (his : SpineFit (consList as ρ) (d.IdsM mm ψ) is) :
    (as ++ is).foldl SetTheory.app (interp V ρ (m.acval T ψ)) ∈ˢ (univ (d.w ψ) : V) := by
  rw [hrep.leaf ψ ρ as is has his]
  have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) has
    rwa [List.append_nil] at h
  have htup : d.tup ψ mm is ∈ˢ d.idx ψ (consList as ρ) := hrep.tupMem ψ _ hsat is his
  exact famSpace_app
    (lfpFamSet_mem (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) htup

end IndRep

/-! ## The restored constructor's position bookkeeping -/

/-- **A restored constructor is an auxiliary member's own constructor,
restored**: its position in the flatten names a real member `t` and a
block constructor index `J`, and its datum entry `cA` is the checked
constructor there — same name, same field count, the block's parameter
count, and its type `restoreNested`'d off the auxiliary one. -/
theorem restoredCtor_pos {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d) :
    ∀ c ∈ ctorsR.flatten, ∃ (t J : Nat) (cA : ConstantVal × Nat),
      t < p.k ∧ d.ctorsA[J]? = some cA ∧ d.mems J = t ∧
      ConLeche.restoreNested (ConLeche.restoreTbl p st) cA.1.type = .ok c.1.type ∧
      c.1.name = cA.1.name ∧ c.1.levelParams = p.lps ∧ c.2.1 = d.nP ∧ c.2.2 = cA.2 := by
  intro c hc
  -- locate `c` in the flatten
  obtain ⟨o, ho, hco⟩ := List.mem_flatten.mp hc
  obtain ⟨t, ht⟩ := List.getElem?_of_mem ho
  obtain ⟨l, hl⟩ := List.getElem?_of_mem hco
  -- the member's restore run
  obtain ⟨hlenR, hall⟩ := ConLeche.mapM_except_inv hctors
  have htk : t < p.k := by
    have h1 : t < ctorsR.length := (List.getElem?_eq_some_iff.mp ht).1
    have h2 : (stored.take p.k).length = min p.k stored.length := List.length_take
    omega
  have htl : t < (stored.take p.k).length := by
    have h1 : t < ctorsR.length := (List.getElem?_eq_some_iff.mp ht).1
    omega
  obtain ⟨a, o', ha, ho', hrun⟩ := hall t htl
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ht)
  rw [hoo] at hrun
  have hak : ConLeche.auxStored? envAux b t = some a := by
    rw [List.getElem?_take_of_lt htk] at ha
    exact (ConLeche.auxStoredAll_get hstored).2 t a ha
  obtain ⟨hlenO, hposO⟩ := ConLeche.restoreCtors_id hrun
  -- the auxiliary constructor behind `c`
  have hll : l < a.ctors.length := by
    have h1 : l < o.length := (List.getElem?_eq_some_iff.mp hl).1
    omega
  have hlen2 : a.ctors.length = (b.ownCtors t).length := ConLeche.auxStored?_ctors_length hak
  obtain ⟨q, hq⟩ : ∃ q, (b.ownCtors t)[l]? = some q :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨J, mc⟩ := q
  obtain ⟨y, hy, hfind⟩ := ConLeche.auxStored?_ctors hak l J mc hq
  obtain ⟨ty, hty, hceq⟩ := hposO l y c hy hl
  obtain ⟨hJctors, hmem⟩ := ConLeche.ownCtors_spec (List.mem_of_getElem? hq)
  -- the checked stage's constructor at `J`
  obtain ⟨_env₁, _fms, _f₀, ctorsA, _sortss, -, -, hctorsChk, hdA, -, hmems⟩ := hchk
  obtain ⟨hlenA, -, hallC⟩ := ConLeche.checkMutualCtors_inv hctorsChk
  have hJb : J < b.ctors.length := (List.getElem?_eq_some_iff.mp hJctors).1
  obtain ⟨cA, hcA⟩ : ∃ cA, ctorsA[J]? = some cA :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨-, _sorts, -, hrunC⟩ := hallC J mc cA hJctors hcA
  obtain ⟨⟨_ty', hff⟩, -, -⟩ := ConLeche.checkMutualCtor_front hrunC
  have hJd : d.ctorsA[J]? = some cA := by rw [hdA]; exact hcA
  have hmemJ : d.mems J = t := by
    rw [hmems, List.getD_eq_getElem?_getD, hJctors]
    exact hmem
  -- the datum's constructor at `J`, found at the same name in `envAux`
  have hkb : d.k = b.k := hreps.2.1
  have hbk : p.k ≤ b.k := by
    have := ConLeche.auxBlock_k hb
    omega
  obtain ⟨_s, _cvT, _cvR, _caps, _mI, _rP, _rules, -, -, -, -, hrep⟩ :=
    hreps.2.2.2.2.2.2.2 0 (by omega)
  have hDf : envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) := (hrep.ctors J cA hJd).1
  rw [hff.name, hfind] at hDf
  simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hDf
  obtain ⟨hx1, hx2, hx3⟩ := hDf
  have hc1 : c.1.type = ty := by rw [hceq]
  have hc2 : c.1.name = y.1.name := by rw [hceq]
  have hc3 : c.1.levelParams = p.lps := by rw [hceq]
  have hc4 : c.2.1 = y.2.1 := by rw [hceq]
  have hc5 : c.2.2 = y.2.2 := by rw [hceq]
  exact ⟨t, J, cA, htk, hJd, hmemJ, by rw [hc1, ← hx1]; exact hty, by rw [hc2, hx1], hc3,
    by rw [hc4]; exact hx2, by rw [hc5]; exact hx3⟩

/-! ## A checked constructor's fields, by kind -/

omit [SetTheory V] in
/-- **A checked constructor's fields resolve before the block, by
kind** (`mutualFieldsOk`, read positionally): the residual's index
arguments resolve, an ordinary field's domain resolves, a recursive
field's domain has resolving index arguments, and a reflexive field's
domain opens to resolving argument domains and a residual with
resolving index arguments. -/
theorem ctorFieldsRes_of_chk {μ : CheckMode} {F : Nat} {env : Env} {b : MutualBlock}
    {d : IndRepData V} (hchk : CtorsChecked μ F env b true d) (hnPb : d.nP = b.nP)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) {crest : Expr}
    (hop₁ : ConLeche.openPisAtFvars d.nP cA.1.type 0 = some (d.fvsPF J, crest))
    (hop₂ : ConLeche.openPisAtFvars cA.2 crest d.nP = some (d.xFvsF J, d.xrestF J)) :
    (∀ e ∈ (d.xrestF J).getAppArgs.drop d.nP, e.constsResolve env = true) ∧
    ∀ (i : Nat) (x : Expr), (d.xFvsF J)[i]? = some x →
      ((d.ksF J).getD i .ordinary = .ordinary → x.fvarTypeD.constsResolve env = true) ∧
      ((d.ksF J).getD i .ordinary = .recursive →
        ∀ e ∈ x.fvarTypeD.getAppArgs.drop d.nP, e.constsResolve env = true) ∧
      ((d.ksF J).getD i .ordinary = .reflexive →
        ∃ (afvs : List Expr) (body : Expr),
          ConLeche.openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (d.nP + i)
            = some (afvs, body) ∧
          (∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true) ∧
          ∀ e ∈ body.getAppArgs.drop d.nP, e.constsResolve env = true) := by
  obtain ⟨_env₁, _fms, _f₀, ctorsA, _sortss, -, -, -, hdA, hkinds, -⟩ := hchk
  obtain ⟨kinds, -, hfo, hksF⟩ := hkinds
  obtain ⟨-, hfoJ⟩ := mutualFieldsOk_inv hfo
  obtain ⟨ks, hksGet, hksLen', hopened⟩ := hfoJ J cA (by rw [← hdA]; exact hJ)
  obtain ⟨fvsP', crest', xFvs', xrest', hop₁', hop₂', hMO⟩ := mutualOpened_of hopened
  rw [← hnPb] at hop₁' hop₂' hMO
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₁'.symm.trans hop₁))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₂'.symm.trans hop₂))
  have hxLen : (d.xFvsF J).length = cA.2 := openPisAtFvars_length _ hop₂
  have hksEq : kinds.getD J [] = ks := by rw [List.getD_eq_getElem?_getD, hksGet]; rfl
  have hks : ∀ i, i < cA.2 → (d.ksF J).getD i .ordinary = kindAt ks i := by
    intro i hi
    have hiks : i < ks.length := by rw [hksLen']; exact hi
    rw [hksF _, hksEq, kindsOf_getD hiks]
  refine ⟨hMO.residRes, fun i x hx => ?_⟩
  have hi : i < cA.2 := by rw [← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨fun h => hMO.ord i x hx (by rw [← hks i hi]; exact h), fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, -, -, hres, -, -⟩ := hMO.recF i x hx (by rw [← hks i hi]; exact h)
    exact hres
  · obtain ⟨afvs, body, hop, -, hres₁, -, -, -, hres₂, -, -⟩ :=
      hMO.reflF i x hx (by rw [← hks i hi]; exact h)
    exact ⟨afvs, body, hop, hres₁, hres₂⟩
