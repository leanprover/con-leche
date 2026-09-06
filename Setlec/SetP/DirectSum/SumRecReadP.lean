import Setlec.SetP.Direct.DirectRecReadP
import Setlec.Verify.Direct.SumRec

/-!
# The generated sum recursor's readings (task #175 sum-types)

`Setlec/SetP/Direct/DirectRecReadP.lean` at a constructor list: the
generated recursor type reads to the Π-tower over `sumRecDataAV`
(parameters, motive, one minor per constructor, major), and rule `j`
reads to the λ-tower over `sumRuleDataAV` at constructor `j`'s field
data, with the core `minor_j f⃗`.  The minor entries are read by one
induction over the constructor list (`denoteP_minorsPis` /
`denoteP_minorsLams`), the accumulated variables (the motive first,
then the earlier minors) threaded as `extras`.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The entries -/

/-- The minor premise's domain reading at offset `o` (the motive and
`o - 1` earlier minors above the parameters): the constructor's field
data lifted `o` under, bits reset to `b`, over the motive at the
constructor spine. -/
def minorAVAt {env : Env} (m : EnvS2Core V env) (C : Name) (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AVExpr)) : AVExpr :=
  mkPisAV (rebit b (liftDoms o 0 (ds.drop nP)))
    (.app (.bvar (nF + o - 1))
      (AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)))

/-- The major premise's domain reading under the motive and `n`
minors: the family at the parameters. -/
def majorAVAt {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat) (nP n : Nat) :
    AVExpr :=
  AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + 1 + n))

/-- The minor entries, one per constructor datum `(C, nF, ds)`, from
offset `o`. -/
def sumMinorsData {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (nP b : Nat) :
    List (Name × Nat × List (Nat × Nat × AVExpr)) → Nat → List (Nat × Nat × AVExpr)
  | [], _ => []
  | (C, nF, ds) :: cs, o => (0, b, minorAVAt m C ψ nP nF b o ds) :: sumMinorsData m ψ nP b cs (o + 1)

theorem sumMinorsData_length {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) (o : Nat),
      (sumMinorsData m ψ nP b cds o).length = cds.length
  | [], _ => rfl
  | (_, _, _) :: cs, o => by simp [sumMinorsData, sumMinorsData_length cs (o + 1)]

theorem mem_sumMinorsData {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ {cds : List (Name × Nat × List (Nat × Nat × AVExpr))} {o : Nat}
      {d : Nat × Nat × AVExpr}, d ∈ sumMinorsData m ψ nP b cds o → d.2.1 = b
  | [], _, _, h => nomatch h
  | (_, _, _) :: cs, o, d, h => by
    simp only [sumMinorsData, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_sumMinorsData h

/-- **The generated sum recursor type's binder data.** -/
def sumRecDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP : Nat) (ℓ : Level) (pps : List (Nat × Nat × AVExpr))
    (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) : List (Nat × Nat × AVExpr) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ)] ++
    sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), majorAVAt m T ψ nP cds.length)]

/-- **Rule `j`'s binder data**: the recursor's parameter, motive and
minor entries, then constructor `j`'s field data lifted `n + 1`
under. -/
def sumRuleDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP : Nat) (ℓ : Level) (pps : List (Nat × Nat × AVExpr))
    (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) (ds : List (Nat × Nat × AVExpr)) :
    List (Nat × AVExpr) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ)] ++
    sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2)

/-- Rule `j`'s core: minor `j` at the field variables. -/
def sumRuleCoreAV (nF n j : Nat) : AVExpr :=
  AVExpr.mkAppN (.bvar (nF + n - 1 - j)) (fieldBvars nF)

/-! ## The per-constructor reading premise -/

/-- What the readings need of one constructor `(C, nF, cty)` and its
datum `(C, nF, ds)`. -/
structure CtorRead {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (lps : List Name)
    (nP : Nat) (c : Name × Nat × Expr) (cd : Name × Nat × List (Nat × Nat × AVExpr)) : Prop where
  name : cd.1 = c.1
  nF : cd.2.1 = c.2.1
  find : ∃ ci : ConstantInfo, env.find? c.1 = some ci ∧ ci.toConstantVal.levelParams = lps
  hasFvar : c.2.2.hasFvar = false
  bounded : c.2.2.looseBVarsBounded 0 = true
  strip : (c.2.2.stripPis (nP + c.2.1)).isSome = true
  read : ∃ bodyC : AVExpr, denoteP m.acval env ψ 0 c.2.2 = some (mkPisAV cd.2.2 bodyC)
  len : cd.2.2.length = nP + c.2.1

/-- The constructors' reading premises, positionally. -/
inductive CtorReads {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (lps : List Name)
    (nP : Nat) : List (Name × Nat × Expr) → List (Name × Nat × List (Nat × Nat × AVExpr)) → Prop
  | nil : CtorReads m ψ lps nP [] []
  | cons {c cd cs cds} : CtorRead m ψ lps nP c cd → CtorReads m ψ lps nP cs cds →
      CtorReads m ψ lps nP (c :: cs) (cd :: cds)

theorem CtorReads.length_eq {m : EnvS2Core V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat} :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))},
      CtorReads m ψ lps nP ctors cds → cds.length = ctors.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CtorReads.length_eq h]

theorem CtorReads.getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat} :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))},
      CtorReads m ψ lps nP ctors cds →
      ∀ {i : Nat} {c : Name × Nat × Expr}, ctors[i]? = some c →
        ∃ cd, cds[i]? = some cd ∧ CtorRead m ψ lps nP c cd
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hr htl, i, c, h => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hr⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨cd, hcd, hR⟩ := CtorReads.getElem? htl h
      exact ⟨cd, by simpa using hcd, hR⟩

/-! ## The cores -/

/-- The minor's core `motive (C p⃗ f⃗)`, read at the full field frame
at offset `o`. -/
theorem denoteP_minorCore_at {m : EnvS2Core V env} {ψ : Name → Nat} {C : Name}
    {lps : List Name} {ci : ConstantInfo} (hfC : env.find? C = some ci)
    (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF o : Nat} {tfvs xFvs : List Expr} {nmM : Name} {tyM : Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty) :
    denoteP m.acval env ψ (nP + o + nF)
        (.app (.fvar nP nmM tyM) (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)))
      = some (.app (.bvar (nF + o - 1))
          (AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF))) := by
  have hspP : DenoteSpineP m.acval env ψ (nP + o + nF) tfvs (paramBvarsAt nP (nP + o + nF)) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) tfvs 0
      (fun k x hx => by
        obtain ⟨nm, ty, h⟩ := hidxT k x hx
        exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩)
    rw [hlenT] at this
    have he : ((List.range nP).map fun k => AVExpr.bvar (nP + o + nF - 1 - (0 + k)))
        = paramBvarsAt nP (nP + o + nF) := by
      unfold paramBvarsAt
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    rwa [he] at this
  have hspX : DenoteSpineP m.acval env ψ (nP + o + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) xFvs
      (nP + o) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + o + nF - 1 - (nP + o + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  have hconst : denoteP m.acval env ψ (nP + o + nF) (.const C (lps.map .param))
      = some (m.acval C ψ) := by
    rw [denoteP_const hfC (by rw [hlpsC]; simp), hlpsC, Level.substFn_param_self]
  have hmk := denoteP_mkAppN (hspP.append hspX) hconst
  rw [denoteP_app, denoteP_fvar, hmk]
  show some (AVExpr.app (.bvar (nP + o + nF - 1 - nP)) _) = _
  rw [show nP + o + nF - 1 - nP = nF + o - 1 from by omega]

/-- Rule `j`'s core `minor_j f⃗`, read at the full frame under the
motive and `n` minors. -/
theorem denoteP_ruleCore_at {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF n j : Nat}
    {xFvs : List Expr} {nmK : Name} {tyK : Expr} (hlenX : xFvs.length = nF) (hj : j < n)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + 1 + n + k) nm ty) :
    denoteP m.acval env ψ (nP + 1 + n + nF) (Expr.mkAppN (.fvar (nP + 1 + j) nmK tyK) xFvs)
      = some (sumRuleCoreAV nF n j) := by
  have hspX : DenoteSpineP m.acval env ψ (nP + 1 + n + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nF) xFvs
      (nP + 1 + n) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + 1 + n + nF - 1 - (nP + 1 + n + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  rw [denoteP_mkAppN hspX (by rw [denoteP_fvar]),
    show nP + 1 + n + nF - 1 - (nP + 1 + j) = nF + n - 1 - j from by omega]
  rfl

/-! ## The minor premise -/

/-- **The minor premise at offset `o`**, instantiated at the
parameters and the `o` extras, reads to `minorAVAt`. -/
theorem denoteP_minorAt {m : EnvS2Core V env} {ψ : Name → Nat} {C : Name} {lps : List Name}
    {ci : ConstantInfo} (hfC : env.find? C = some ci) (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF : Nat} {pw : PropWhen} {cty mty : Expr} {extras : List Expr}
    (hmin : Setlec.directMinorTy C lps nP nF extras.length pw cty = some mty)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty = some (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a)
    (ho : 0 < extras.length)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) :
    denoteP m.acval env ψ (nP + extras.length)
        (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty)
      = some (minorAVAt m C ψ nP nF (pwBit ψ pw) extras.length ds) := by
  obtain ⟨cbs, crest0, hsC, hrep⟩ := Setlec.directMinorTy_unfold hmin
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE q a hq
    rfl
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this
  have hmin' := Setlec.replacePisPw_instSeq (tfvs ++ extras) (nP + extras.length - 1)
    (by simp [hlenT]; omega) hrep
  rw [Setlec.instSeq_minorTele tfvs extras hlenT hclT hcb0] at hmin'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + extras.length) hcstrip
  have hcreadO := ctorResidual_read_lift hcread hcw hlenD extras.length
  have hstX : stripPisAV nF (mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      (bodyC.liftN extras.length nF))
      = some (liftDoms extras.length 0 (ds.drop nP), bodyC.liftN extras.length nF) := by
    have := stripPisAV_mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      (bodyC.liftN extras.length nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcreadO hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mfv, hhead⟩ : ∃ mfv, extras[0]? = some mfv :=
    ⟨_, List.getElem?_eq_getElem ho⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE 0 mfv hhead
  rw [Nat.add_zero] at hhead
  rw [Setlec.instSeq_minorBody_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead,
    denoteP_minorCore_at hfC hlpsC hlenT hlenX hidxT hidxX, Option.map_some] at hminor
  exact hminor

/-! ## The minors' telescopes -/

set_option maxHeartbeats 1600000 in
/-- **The `∀`-telescope of minors** reads to the Π-tower over
`sumMinorsData`, the body read under the motive and all minors. -/
theorem denoteP_minorsPis {m : EnvS2Core V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))}
      {body mins : Expr} {extras : List Expr},
      CtorReads m ψ lps nP ctors cds →
      Setlec.directMinorsPis lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkPisAV (sumMinorsData m ψ nP (pwBit ψ pw) cds extras.length))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Setlec.directMinorsPis_nil hmin]
    simp only [List.length_nil, Nat.add_zero, sumMinorsData]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    subst hC' hnF'
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨bodyC, hCread⟩ := hc.read
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Setlec.directMinorsPis_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    -- the binder
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_forallE,
      denoteP_minorAt hfC hlpsC hmty hc.hasFvar hc.bounded hc.strip hCread hc.len hlenT hidxT hspW
        ho hidxE]
    -- the rest, at the minor's variable
    generalize hmk : Expr.fvar (nP + extras.length) (Setlec.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp at this
          omega
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Setlec.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Setlec.directMinorsPis lps nP pw cs (extras ++ [mkfv]).length body = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsPis hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **The `λ`-telescope of minors** reads to the λ-tower over
`sumMinorsData`'s domains, the body read under the motive and all
minors. -/
theorem denoteP_minorsLams {m : EnvS2Core V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))}
      {body mins : Expr} {extras : List Expr},
      CtorReads m ψ lps nP ctors cds →
      Setlec.directMinorsLams lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkLamsAV ((sumMinorsData m ψ nP (pwBit ψ pw) cds extras.length).map
                fun d => (d.2.1, d.2.2)))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Setlec.directMinorsLams_nil hmin]
    simp only [List.length_nil, Nat.add_zero, sumMinorsData, List.map_nil]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    subst hC' hnF'
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨bodyC, hCread⟩ := hc.read
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Setlec.directMinorsLams_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Setlec.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_lam,
      denoteP_minorAt hfC hlpsC hmty hc.hasFvar hc.bounded hc.strip hCread hc.len hlenT hidxT hspW
        ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length) (Setlec.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp at this
          omega
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Setlec.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Setlec.directMinorsLams lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsLams hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

/-! ## The generated type -/

set_option maxHeartbeats 3200000 in
/-- **The generated sum recursor type reads to the Π-tower over
`sumRecDataAV`.** -/
theorem denoteP_directRecTy_sum {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))}
    (hcr : CtorReads m ψ lps nP ctors cds)
    {tty recTy : Expr}
    (hgen : Setlec.directRecTy T lps elim large nP tty ctors = some recTy)
    (hTf : tty.hasFvar = false)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {pps : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV pps (.sort w)))
    (hlenP : pps.length = nP) :
    denoteP m.acval env ψ 0 recTy
      = some (mkPisAV (sumRecDataAV m T ψ nP (Setlec.directElimLevel elim large) pps cds)
          (.app (.bvar (cds.length + 1)) (.bvar 0))) := by
  obtain ⟨minors, hmin, hrec⟩ := Setlec.directRecTy_unfold hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  generalize hn : ctors.length = n at hmin hlenC
  generalize hℓ : Setlec.directElimLevel elim large = ℓ at hrec hmin ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hrec hmin ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV pps (.sort w)) = some (pps, .sort w) := by
    rw [← hlenP]; exact stripPisAV_mkPisAV pps _
  rw [denoteP_replacePisPw nP hrec hopT hTread hst, Nat.zero_add]
  -- the motive binder, instantiated at the parameters
  have e1 : Expr.instSeq tfvs (nP - 1) (Setlec.directMotiveTy T lps nP ℓ)
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩ := by
    unfold Setlec.directMotiveTy
    rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega), Setlec.directFam_eq,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      show nP - 1 = 0 + nP - 1 from by omega,
      Setlec.map_instSeq_directPsAt tfvs 0 nP hclT (by omega), List.take_of_length_le (by omega)]
  rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega), e1,
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hfamR : ∀ D, denoteP m.acval env ψ D (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) :=
    fun D => famSpine_read hfT hlpsT hlenT hidxT D ψ
  have hmotive : denoteP m.acval env ψ nP
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
        (.sort ℓ) ⟨.default, .never⟩) = some (motiveAV m T ψ nP ℓ) := by
    rw [denoteP_forallE, hfamR, Expr.instantiate1_sort, denoteP_sort]
    rfl
  rw [denoteP_forallE, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      (.sort ℓ) ⟨.default, .never⟩)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Setlec.directMinorsPis lps nP pw ctors [mfv].length
      (.forallE (.str .anonymous "t") (Setlec.directFam T lps nP (n + 1))
        (.app (.bvar (n + 1)) (.bvar 0)) ⟨.default, pw⟩) = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsPis hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the major and the conclusion
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras', a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE' a h
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  obtain ⟨mfv', hhead⟩ : ∃ x, extras'[0]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE' 0 mfv' hhead
  rw [Nat.add_zero] at hhead
  have e2 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1) (Setlec.directFam T lps nP (n + 1))
      = Expr.mkAppN (.const T (lps.map .param)) tfvs := by
    rw [Setlec.directFam_eq, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + 1 + n - 1 = (n + 1) + nP - 1 from by omega,
      Setlec.map_instSeq_directPsAt (tfvs ++ extras') (n + 1) nP hclTE (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have e3 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + 1) (Expr.app (.bvar (n + 1)) (.bvar 0))
      = .app (.fvar nP nmM tyM) (.bvar 0) := by
    rw [Expr.instSeq_app, Setlec.instSeq_bvar_lt (tfvs ++ extras') _ 0 (by rw [hlenTE]; omega)]
    have := Expr.instSeq_bvar (tfvs ++ extras') (nP + 1 + n - 1 + 1) (n + 1) hclTE (by omega)
      (by rw [hlenTE]; omega)
    rw [show nP + 1 + n - 1 + 1 - (n + 1) = nP from by omega,
      List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
    rw [← Option.some.inj this]
  rw [Expr.instSeq_forallE (tfvs ++ extras') (nP + 1 + n - 1) _ _ _ _ (by rw [hlenTE]; omega),
    e2, e3, denoteP_forallE, hfamR (nP + 1 + n)]
  simp +decide only [Expr.instantiate1, ↓reduceIte]
  rw [denoteP_app, denoteP_fvar, denoteP_fvar,
    show nP + 1 + n + 1 - 1 - nP = n + 1 from by omega,
    show nP + 1 + n + 1 - 1 - (nP + 1 + n) = 0 from by omega]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold sumRecDataAV majorAVAt
  rw [mkPisAV_append, mkPisAV_append, mkPisAV_append, hlenC]
  rfl

/-! ## The generated rule -/

set_option maxHeartbeats 3200000 in
/-- **Rule `j` reads to the λ-tower over `sumRuleDataAV`** at
constructor `j`'s data, with the core `minor_j f⃗`. -/
theorem denoteP_directRecRhs_sum {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP j : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr)} {cds : List (Name × Nat × List (Nat × Nat × AVExpr))}
    (hcr : CtorReads m ψ lps nP ctors cds)
    {tty rhs : Expr}
    (hgen : Setlec.directRecRhs T lps elim large nP tty ctors j = some rhs)
    (hTf : tty.hasFvar = false)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {pps : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV pps (.sort w)))
    (hlenP : pps.length = nP)
    {C : Name} {nF : Nat} {ds : List (Nat × Nat × AVExpr)} (hjd : cds[j]? = some (C, nF, ds)) :
    denoteP m.acval env ψ 0 rhs
      = some (mkLamsAV (sumRuleDataAV m T ψ nP (Setlec.directElimLevel elim large) pps cds ds)
          (sumRuleCoreAV nF cds.length j)) := by
  obtain ⟨C₀, nF₀, cty, cbs, crest0, inner, minors, hj, hsC, hinner, hmin, hr⟩ :=
    Setlec.directRecRhs_unfold hgen
  obtain ⟨cd, hjd', hc⟩ := hcr.getElem? hj
  obtain ⟨rfl⟩ := Option.some.inj (hjd'.symm.trans hjd)
  have hC0 : C = C₀ := hc.name
  have hnF0 : nF = nF₀ := hc.nF
  subst hC0 hnF0
  obtain ⟨ci, hfC, hlpsC⟩ := hc.find
  obtain ⟨bodyC, hCread⟩ := hc.read
  have hlenD : ds.length = nP + nF := hc.len
  have hCb : cty.looseBVarsBounded 0 = true := hc.bounded
  have hCf : cty.hasFvar = false := hc.hasFvar
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := hc.strip
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  have hjn : j < ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  generalize hn : ctors.length = n at hinner hlenC hjn
  generalize hℓ : Setlec.directElimLevel elim large = ℓ at hr hmin hinner ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hr hmin hinner ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV pps (.sort w)) = some (pps, .sort w) := by
    rw [← hlenP]; exact stripPisAV_mkPisAV pps _
  rw [denoteP_pisToLamsPw nP hr hopT hTread hst, Nat.zero_add]
  -- the motive binder
  have e1 : Expr.instSeq tfvs (nP - 1) (Setlec.directMotiveTy T lps nP ℓ)
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩ := by
    unfold Setlec.directMotiveTy
    rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega), Setlec.directFam_eq,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      show nP - 1 = 0 + nP - 1 from by omega,
      Setlec.map_instSeq_directPsAt tfvs 0 nP hclT (by omega), List.take_of_length_le (by omega)]
  rw [Setlec.instSeq_lam tfvs (nP - 1) _ _ _ _ (by omega), e1,
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hfamR : ∀ D, denoteP m.acval env ψ D (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) :=
    fun D => famSpine_read hfT hlpsT hlenT hidxT D ψ
  have hmotive : denoteP m.acval env ψ nP
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
        (.sort ℓ) ⟨.default, .never⟩) = some (motiveAV m T ψ nP ℓ) := by
    rw [denoteP_forallE, hfamR, Expr.instantiate1_sort, denoteP_sort]
    rfl
  rw [denoteP_lam, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      (.sort ℓ) ⟨.default, .never⟩)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Setlec.directMinorsLams lps nP pw ctors [mfv].length inner = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsLams hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the inner λ-telescope, at the motive's and the minors' variables
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this
  have hinner' := Setlec.pisToLamsPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hinner
  have hres := Setlec.instSeq_minorTele tfvs extras' hlenT hclT hcb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hinner'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1 + n) hcstrip
  have hcreadN : denoteP m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP)) (bodyC.liftN (n + 1) nF)) := by
    have := ctorResidual_read_lift hcread hcw hlenD (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega] at this
  have hstX : stripPisAV nF (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP)) (bodyC.liftN (n + 1) nF))
      = some (liftDoms (n + 1) 0 (ds.drop nP), bodyC.liftN (n + 1) nF) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ds.drop nP)) (bodyC.liftN (n + 1) nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hinnerR := denoteP_pisToLamsPw (acval := m.acval) (env := env) (φ := ψ) nF hinner' hopX
    hcreadN hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mkfv, hjE⟩ : ∃ x, extras'[j + 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨nmK, tyK, rfl⟩ := hidxE' (j + 1) mkfv hjE
  have hrb := Setlec.instSeq_ruleBody_at tfvs extras' xFvs hlenT hlenX hclT hclE' hclX hjE
  rw [hlenE', show nP + (n + 1) - 1 + nF = nP + 1 + n - 1 + nF from by omega,
    show nF + (n + 1 - 1) - 1 - j = nF + n - 1 - j from by omega] at hrb
  rw [hrb, show nP + 1 + n + nF = nP + 1 + n + nF from rfl] at hinnerR
  have hidxX' : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + 1 + n + k) nm ty := hidxX
  rw [show Expr.fvar (nP + (j + 1)) nmK tyK = Expr.fvar (nP + 1 + j) nmK tyK from by
      congr 1; omega,
    denoteP_ruleCore_at hlenX hjn hidxX', Option.map_some] at hinnerR
  rw [hinnerR]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold sumRuleDataAV
  rw [List.map_append, List.map_append, List.map_append, mkLamsAV_append, mkLamsAV_append,
    mkLamsAV_append, rebit_map_lam, rebit_map_lam, hlenC]
  rfl

end Setlec.SetP
