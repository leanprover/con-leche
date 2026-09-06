import Lech.SetP.Direct.DirectRecKit2P
import Lech.Verify.Direct.DirectRec

/-!
# The generated recursor, read (task #175 S2)

The direct install stores the recursor it generates
(`directRecTy`/`directRecRhs`), so its reading is **syntactic**: the
generated type reads to the Π-tower

    mkPisAV (params (bit ℓ) ++ [motive, minor, major]) (motive t)

whose three special entries are spelled out (`motiveAV`, `minorAV`,
`majorAV`) over the type former's and the constructor's readings, and
the generated rule reads to the λ-tower over the same data
(`denoteP_directRecRhs`).  No frame pin is consumed: the recursor's
data (`recData_of`) comes from these readings, the fabricated type's
own inference run (its grading, `inferRow`) and the elimination datum
the generator wrote (its bits, `zeronessOf_sound`).

The two generic pieces are the readings of the binder walks
(`denoteP_replacePisPw`, `denoteP_pisToLamsPw`): a walk over an
opened telescope reads to the tower over the telescope's own domain
readings, bits reset, over the body instantiated at the opening's
variables.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## Bits reset -/

/-- Binder data with every codomain bit reset to `b`. -/
def rebit (b : Nat) (ds : List (Nat × Nat × AVExpr)) : List (Nat × Nat × AVExpr) :=
  ds.map fun d => (d.1, b, d.2.2)

@[simp] theorem rebit_nil (b : Nat) : rebit b [] = [] := rfl

@[simp] theorem rebit_cons (b : Nat) (d : Nat × Nat × AVExpr) (ds : List (Nat × Nat × AVExpr)) :
    rebit b (d :: ds) = (d.1, b, d.2.2) :: rebit b ds := rfl

@[simp] theorem rebit_length (b : Nat) (ds : List (Nat × Nat × AVExpr)) :
    (rebit b ds).length = ds.length := by simp [rebit]

@[simp] theorem rebit_map_dom (b : Nat) (ds : List (Nat × Nat × AVExpr)) :
    (rebit b ds).map (·.2.2) = ds.map (·.2.2) := by simp [rebit]

theorem rebit_take (b : Nat) (ds : List (Nat × Nat × AVExpr)) (n : Nat) :
    (rebit b ds).take n = rebit b (ds.take n) := by simp [rebit, List.map_take]

theorem rebit_getD (b : Nat) (ds : List (Nat × Nat × AVExpr)) (j : Nat) (hj : j < ds.length) :
    (rebit b ds).getD j default = ((ds.getD j default).1, b, (ds.getD j default).2.2) := by
  simp only [rebit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

theorem mem_rebit {b : Nat} {ds : List (Nat × Nat × AVExpr)} {d : Nat × Nat × AVExpr}
    (h : d ∈ rebit b ds) : d.2.1 = b := by
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp h
  rfl

theorem DomsBelow.rebit {k b : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)}, DomsBelow k ds → DomsBelow k (rebit b ds)
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.rebit h.2⟩

/-! ## The binder walks, read -/

/-- **The `∀`-walk's reading**: the telescope's own domain readings,
bits reset, over the body at the opening's variables. -/
theorem denoteP_replacePisPw {pw : PropWhen} :
    ∀ (k : Nat) {d : Nat} {e b r : Expr} {fvs : List Expr} {o : Expr} {ea : AVExpr}
      {pds : List (Nat × Nat × AVExpr)} {R : AVExpr},
      Expr.replacePisPw pw k e b = some r →
      openPisAtFvars k e d = some (fvs, o) →
      denoteP acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      denoteP acval env φ d r
        = (denoteP acval env φ (d + k) (Expr.instSeq fvs (k - 1) b)).map
            (mkPisAV (rebit (pwBit φ pw) pds))
  | 0, d, e, b, r, fvs, o, ea, pds, R, hr, hop, _, hst => by
    simp only [Expr.replacePisPw, Option.some.injEq] at hr
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hop
    obtain ⟨rfl, -⟩ := hst
    subst hr
    simp only [Nat.add_zero, Expr.instSeq, rebit_nil, mkPisAV, Option.map_id']
  | k + 1, d, e, b, r, fvs, o, ea, pds, R, hr, hop, hea, hst => by
    match e, hr, hop with
    | .forallE n ty rest m, hr, hop =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hr'' := Lech.replacePisPw_instantiate1 (v := .fvar d n ty) k 0 hr'
        rw [Nat.zero_add] at hr''
        have ih := denoteP_replacePisPw k hr'' hop' hba hst'
        rw [denoteP_forallE, hta]
        show (denoteP acval env φ (d + 1) (r'.instantiate1 (.fvar d n ty)) >>= fun ba =>
          some (AVExpr.pi 0 (pwBit φ pw) ta ba)) = _
        rw [ih, show d + (k + 1) = d + 1 + k from by omega]
        show _ = (denoteP acval env φ (d + 1 + k)
          (Expr.instSeq fvs' (k + 1 - 1 - 1) (b.instantiate1 (.fvar d n ty) (k + 1 - 1)))).map _
        rw [show k + 1 - 1 = k from rfl]
        cases denoteP acval env φ (d + 1 + k)
            (Expr.instSeq fvs' (k - 1) (b.instantiate1 (.fvar d n ty) k)) <;> rfl
      · exact nomatch hop
    | .bvar _, hr, _ | .fvar _ _ _, hr, _ | .sort _, hr, _ | .const _ _, hr, _
    | .app _ _, hr, _ | .lam _ _ _ _, hr, _ | .letE _ _ _ _, hr, _ | .lit _, hr, _
    | .proj _ _ _, hr, _ => simp [Expr.replacePisPw] at hr

/-- **The `λ`-walk's reading**: the λ-tower over the telescope's
domain readings with bit `pw`, over the body at the opening's
variables. -/
theorem denoteP_pisToLamsPw {pw : PropWhen} :
    ∀ (k : Nat) {d : Nat} {e b r : Expr} {fvs : List Expr} {o : Expr} {ea : AVExpr}
      {pds : List (Nat × Nat × AVExpr)} {R : AVExpr},
      Expr.pisToLamsPw pw k e b = some r →
      openPisAtFvars k e d = some (fvs, o) →
      denoteP acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      denoteP acval env φ d r
        = (denoteP acval env φ (d + k) (Expr.instSeq fvs (k - 1) b)).map
            (mkLamsAV (pds.map fun p => (pwBit φ pw, p.2.2)))
  | 0, d, e, b, r, fvs, o, ea, pds, R, hr, hop, _, hst => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at hr
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hop
    obtain ⟨rfl, -⟩ := hst
    subst hr
    simp only [Nat.add_zero, Expr.instSeq, List.map_nil, mkLamsAV, Option.map_id']
  | k + 1, d, e, b, r, fvs, o, ea, pds, R, hr, hop, hea, hst => by
    match e, hr, hop with
    | .forallE n ty rest m, hr, hop =>
      simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hr'' := Lech.pisToLamsPw_instantiate1 (v := .fvar d n ty) k 0 hr'
        rw [Nat.zero_add] at hr''
        have ih := denoteP_pisToLamsPw k hr'' hop' hba hst'
        rw [denoteP_lam, hta]
        show (denoteP acval env φ (d + 1) (r'.instantiate1 (.fvar d n ty)) >>= fun ba =>
          some (AVExpr.lam (pwBit φ pw) ta ba)) = _
        rw [ih, show d + (k + 1) = d + 1 + k from by omega]
        show _ = (denoteP acval env φ (d + 1 + k)
          (Expr.instSeq fvs' (k + 1 - 1 - 1) (b.instantiate1 (.fvar d n ty) (k + 1 - 1)))).map _
        rw [show k + 1 - 1 = k from rfl]
        cases denoteP acval env φ (d + 1 + k)
            (Expr.instSeq fvs' (k - 1) (b.instantiate1 (.fvar d n ty) k)) <;> rfl
      · exact nomatch hop
    | .bvar _, hr, _ | .fvar _ _ _, hr, _ | .sort _, hr, _ | .const _ _, hr, _
    | .app _ _, hr, _ | .lam _ _ _ _, hr, _ | .letE _ _ _ _, hr, _ | .lit _, hr, _
    | .proj _ _ _, hr, _ => simp [Expr.pisToLamsPw] at hr

/-! ## Syntactic bookkeeping -/

/-- A closed-argument instantiation sequence keeps a telescope's strip. -/
theorem instSeq_stripPis_isSome :
    ∀ (sp : List Expr) (t : Nat) {e : Expr} {n : Nat},
      (e.stripPis n).isSome = true → ((Expr.instSeq sp t e).stripPis n).isSome = true
  | [], _, _, _, h => h
  | a :: sp, t, _, n, h =>
    instSeq_stripPis_isSome sp (t - 1) (Expr.stripPis_instantiate1_isSome (v := a) n t h)

/-- The tail of a longer strip strips the remainder. -/
theorem stripPis_isSome_drop :
    ∀ (k : Nat) {m : Nat} {e : Expr} {bs : List (Name × Expr × BinderMeta)} {mid : Expr},
      (e.stripPis (k + m)).isSome = true → e.stripPis k = some (bs, mid) →
      (mid.stripPis m).isSome = true
  | 0, m, e, bs, mid, h, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simpa using h
  | k + 1, m, e, bs, mid, h, hs => by
    rw [show k + 1 + m = (k + m) + 1 from by omega] at h
    match e, h, hs with
    | .forallE n ty rest mb, h, hs =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      simp only [Expr.stripPis] at hs
      cases hs' : rest.stripPis k with
      | none => rw [hs'] at hs; exact nomatch hs
      | some q =>
        rw [hs'] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl⟩ := hs
        exact stripPis_isSome_drop k h hs'
    | .bvar _, h, _ | .fvar _ _ _, h, _ | .sort _, h, _ | .const _ _, h, _
    | .app _ _, h, _ | .lam _ _ _ _, h, _ | .letE _ _ _ _, h, _ | .lit _, h, _
    | .proj _ _ _, h, _ => simp [Expr.stripPis] at h

/-- An instantiation sequence's index is immaterial at the empty
sequence. -/
theorem instSeq_idx_congr {sp : List Expr} {t t' : Nat} (e : Expr)
    (h : sp = [] ∨ t = t') : Expr.instSeq sp t e = Expr.instSeq sp t' e := by
  rcases h with rfl | rfl <;> rfl

/-- The variables of an opening at depth `0` are closed and indexed by
position, scoped one above their index. -/
theorem opening_vars {n : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e 0 = some (fvs, o)) (hcl : e.hasFvar = false) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) ∧
    (∀ (i : Nat) (a : Expr), fvs[i]? = some a → Expr.WScoped (0 + i + 1) a) := by
  have hidx := openPisAtFvars_index n e 0 hop
  refine ⟨openPisAtFvars_length n hop, fun k x hx => by
    obtain ⟨nm, ty, h⟩ := hidx k x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidx q a hq
    rfl
  · intro i a ha
    obtain ⟨nm, ty, rfl⟩ := hidx i a ha
    have hw := openPisAtFvars_typeWScoped n hop (Expr.WScoped.of_not_hasFvar hcl) i _ ha
    simp only [Expr.fvarTypeD, Nat.zero_add] at hw
    simp only [Expr.WScoped, Nat.zero_add]
    exact ⟨Nat.lt_succ_self i, hw⟩

/-- The variables of an opening at any depth: one per binder, indexed
by position from the depth, closed. -/
theorem opening_vars_at {n d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o)) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ nm ty, x = Expr.fvar (d + k) nm ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) :=
  ⟨openPisAtFvars_length n hop, openPisAtFvars_index n e d hop, fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index n e d hop q a hq
    rfl⟩

/-! ## The three special entries -/

/-- The motive's domain reading `∀ (t : T p⃗), Sort ℓ` at the
parameters' frame. -/
def motiveAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat) (nP : Nat)
    (ℓ : Level) : AVExpr :=
  .pi 0 (pwBit ψ PropWhen.never) (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP nP))
    (.sort (ℓ.eval ψ))

/-- The field variables' spine at the minor's core. -/
def fieldBvars (nF : Nat) : List AVExpr :=
  (List.range nF).map fun k => AVExpr.bvar (nF - 1 - k)

/-- The minor premise's domain reading: the constructor's field data
lifted one under the motive, bits reset to `b`, over the motive at the
constructor spine. -/
def minorAV {env : Env} (m : EnvS2Core V env) (C : Name) (ψ : Name → Nat) (nP nF b : Nat)
    (ds : List (Nat × Nat × AVExpr)) : AVExpr :=
  mkPisAV (rebit b (liftDoms 1 0 (ds.drop nP)))
    (.app (.bvar nF)
      (AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + 1 + nF) ++ fieldBvars nF)))

/-- The major premise's domain reading: the family at the parameters,
two under. -/
def majorAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat) (nP : Nat) :
    AVExpr :=
  AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + 2))

/-- **The generated recursor type's binder data.** -/
def recDataAV {env : Env} (m : EnvS2Core V env) (T C : Name) (ψ : Name → Nat)
    (nP nF : Nat) (ℓ : Level) (pps ds : List (Nat × Nat × AVExpr)) :
    List (Nat × Nat × AVExpr) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ),
     (0, pwBit ψ (Level.zeronessOf ℓ), minorAV m C ψ nP nF (pwBit ψ (Level.zeronessOf ℓ)) ds),
     (0, pwBit ψ (Level.zeronessOf ℓ), majorAV m T ψ nP)]

/-- **The generated rule's binder data**: the recursor's first `nP + 2`
entries and the constructor's field data lifted two under. -/
def ruleDataAV {env : Env} (m : EnvS2Core V env) (T C : Name) (ψ : Name → Nat)
    (nP nF : Nat) (ℓ : Level) (pps ds : List (Nat × Nat × AVExpr)) :
    List (Nat × AVExpr) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ),
     (0, pwBit ψ (Level.zeronessOf ℓ), minorAV m C ψ nP nF (pwBit ψ (Level.zeronessOf ℓ)) ds)] ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms 2 0 (ds.drop nP))).map
    fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2)

/-! ## The constructor telescope's residual -/

/-- The constructor's field telescope at the parameter variables: its
reading at depth `nP`, its scoping, and its strip. -/
theorem ctorResidual {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF : Nat} {cty : Expr}
    (hCf : cty.hasFvar = false)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty = some (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF)
    {cbs : List (Name × Expr × BinderMeta)} {crest0 : Expr}
    (hsC : cty.stripPis nP = some (cbs, crest0))
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    denoteP m.acval env ψ nP (Expr.instSeq tfvs (nP - 1) crest0)
        = some (mkPisAV (ds.drop nP) bodyC) ∧
      Expr.WScoped nP (Expr.instSeq tfvs (nP - 1) crest0) ∧
      ((Expr.instSeq tfvs (nP - 1) crest0).stripPis nF).isSome = true := by
  obtain ⟨cdoms, hci⟩ := Lech.instPisAt_of_stripPis tfvs (by rw [hlenT]; exact hsC)
  rw [hlenT] at hci
  have hidxT' : ∀ (q : Nat) (x : Expr), tfvs[q]? = some x → ∃ nm t, x = Expr.fvar (0 + q) nm t :=
    fun q x hx => by
      obtain ⟨nm, t, h⟩ := hidxT q x hx
      exact ⟨nm, t, by rw [h, Nat.zero_add]⟩
  have hteleP := piTeleP_of_stripPisAV (stripPisAV_mkPisAV_take nP ds bodyC (by omega))
  refine ⟨?_, ?_, ?_⟩
  · have := instPisAt_openerResP tfvs hci hidxT' hCread (by rw [hlenT]; exact hteleP)
    rwa [hlenT, Nat.zero_add] at this
  · have := instPisAt_res_WScoped tfvs (d := 0) hci (Expr.WScoped.of_not_hasFvar hCf) hspW
    rwa [hlenT, Nat.zero_add] at this
  · exact instSeq_stripPis_isSome tfvs (nP - 1) (stripPis_isSome_drop nP hstripC hsC)

/-- The reading of the constructor's residual, one under (the motive):
the field data lifted once. -/
theorem ctorResidual_read_lift {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF : Nat}
    {crest : Expr} {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hread : denoteP m.acval env ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF) (e : Nat) :
    denoteP m.acval env ψ (nP + e) crest
      = some (mkPisAV (liftDoms e 0 (ds.drop nP)) (bodyC.liftN e nF)) := by
  rw [denoteP_lift m.acval_closed hw (nP + e) (by omega), hread, Option.map_some,
    show nP + e - nP = e from by omega, liftN_mkPisAV, Nat.zero_add]
  congr 3
  simp [hlenD]

/-- The minor's core `motive (C p⃗ f⃗)`, read at the full field frame. -/
theorem denoteP_minorCore {m : EnvS2Core V env} {ψ : Name → Nat} {C : Name} {lps : List Name}
    {ci : ConstantInfo} (hfC : env.find? C = some ci) (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF : Nat} {tfvs xFvs : List Expr} {nmM : Name} {tyM : Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + 1 + k) nm ty) :
    denoteP m.acval env ψ (nP + 1 + nF)
        (.app (.fvar nP nmM tyM) (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs)))
      = some (.app (.bvar nF)
          (AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + 1 + nF) ++ fieldBvars nF))) := by
  have hspP : DenoteSpineP m.acval env ψ (nP + 1 + nF) tfvs (paramBvarsAt nP (nP + 1 + nF)) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + nF) tfvs 0
      (fun k x hx => by
        obtain ⟨nm, ty, h⟩ := hidxT k x hx
        exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩)
    rw [hlenT] at this
    have he : ((List.range nP).map fun k => AVExpr.bvar (nP + 1 + nF - 1 - (0 + k)))
        = paramBvarsAt nP (nP + 1 + nF) := by
      unfold paramBvarsAt
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    rwa [he] at this
  have hspX : DenoteSpineP m.acval env ψ (nP + 1 + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + nF) xFvs
      (nP + 1) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + 1 + nF - 1 - (nP + 1 + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  have hconst : denoteP m.acval env ψ (nP + 1 + nF) (.const C (lps.map .param))
      = some (m.acval C ψ) := by
    rw [denoteP_const hfC (by rw [hlpsC]; simp), hlpsC, Level.substFn_param_self]
  have hmk := denoteP_mkAppN (hspP.append hspX) hconst
  rw [denoteP_app, denoteP_fvar, hmk]
  show some (AVExpr.app (.bvar (nP + 1 + nF - 1 - nP)) _) = _
  rw [show nP + 1 + nF - 1 - nP = nF from by omega]

/-! ## The generated type -/

set_option maxHeartbeats 3200000 in
/-- **The generated recursor type reads to the Π-tower over
`recDataAV`.** -/
theorem denoteP_directRecTy {m : EnvS2Core V env} {ψ : Name → Nat} {T C : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nF : Nat}
    {ciT ciC : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    (hfC : env.find? C = some ciC) (hlpsC : ciC.toConstantVal.levelParams = lps)
    {tty cty recTy : Expr}
    (hgen : Lech.directRecTy T lps elim large nP tty [(C, nF, cty)] = some recTy)
    (hTf : tty.hasFvar = false)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {pps : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV pps (.sort w)))
    (hlenP : pps.length = nP)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty = some (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF) :
    denoteP m.acval env ψ 0 recTy
      = some (mkPisAV (recDataAV m T C ψ nP nF (Lech.directElimLevel elim large) pps ds)
          (.app (.bvar 2) (.bvar 0))) := by
  obtain ⟨cbs, crest0, minorTy, hsC, hmin, hrec⟩ := Lech.directRecTy_single hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hrec hmin ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hrec hmin ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV pps (.sort w)) = some (pps, .sort w) := by
    rw [← hlenP]; exact stripPisAV_mkPisAV pps _
  rw [denoteP_replacePisPw nP hrec hopT hTread hst, Nat.zero_add]
  -- the post-parameter telescope, instantiated at the parameters
  have hfamCl : (Expr.mkAppN (.const T (lps.map .param)) tfvs).looseBVarsBounded 0 = true :=
    Lech.looseBVarsBounded_mkAppN rfl hclT
  have hfamI : ∀ (v : Expr) (k : Nat),
      (Expr.mkAppN (.const T (lps.map .param)) tfvs).instantiate1 v k
        = Expr.mkAppN (.const T (lps.map .param)) tfvs :=
    fun v k => Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k) hfamCl)
  have e1 : Expr.instSeq tfvs (nP - 1) (Lech.directMotiveTy T lps nP ℓ)
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩ := by
    unfold Lech.directMotiveTy
    rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega), Lech.directFam_eq,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      show nP - 1 = 0 + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt tfvs 0 nP hclT (by omega), List.take_of_length_le (by omega)]
  have e2 : Expr.instSeq tfvs (nP + 1) (Lech.directFam T lps nP 2)
      = Expr.mkAppN (.const T (lps.map .param)) tfvs := by
    rw [Lech.directFam_eq, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + 1 = 2 + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt tfvs 2 nP hclT (by omega), List.take_of_length_le (by omega)]
  have e3 : Expr.instSeq tfvs (nP + 2) (Expr.app (.bvar 2) (.bvar 0)) = .app (.bvar 2) (.bvar 0) :=
    Lech.instSeq_eq_self_of_bounded tfvs _ (k := 3) (by simp [Expr.looseBVarsBounded]) (by omega)
  have hbody : Expr.instSeq tfvs (nP - 1)
      (.forallE (.str .anonymous "motive") (Lech.directMotiveTy T lps nP ℓ)
        (.forallE (Lech.Name.lastStr C) minorTy
          (.forallE (.str .anonymous "t") (Lech.directFam T lps nP 2)
            (.app (.bvar 2) (.bvar 0)) ⟨.default, pw⟩)
          ⟨.default, pw⟩) ⟨.default, pw⟩)
      = .forallE (.str .anonymous "motive")
          (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
            (.sort ℓ) ⟨.default, .never⟩)
          (.forallE (Lech.Name.lastStr C) (Expr.instSeq tfvs nP minorTy)
            (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
              (.app (.bvar 2) (.bvar 0)) ⟨.default, pw⟩)
            ⟨.default, pw⟩) ⟨.default, pw⟩ := by
    rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega),
      Expr.instSeq_forallE tfvs (nP - 1 + 1) _ _ _ _ (by omega),
      Expr.instSeq_forallE tfvs (nP - 1 + 1 + 1) _ _ _ _ (by omega), e1,
      instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minorTy hnil,
      instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1 + 1) (t' := nP + 1) _
        (by rcases hnil with h | h; exact Or.inl h; right; omega),
      instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1 + 1 + 1) (t' := nP + 2) _
        (by rcases hnil with h | h; exact Or.inl h; right; omega), e2, e3]
  rw [hbody]
  -- the motive
  have hfamR : ∀ D, denoteP m.acval env ψ D (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) :=
    fun D => famSpine_read hfT hlpsT hlenT hidxT D ψ
  have hmotive : denoteP m.acval env ψ nP
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
        (.sort ℓ) ⟨.default, .never⟩) = some (motiveAV m T ψ nP ℓ) := by
    rw [denoteP_forallE, hfamR, Expr.instantiate1_sort, denoteP_sort]
    rfl
  -- the minor, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      (.sort ℓ) ⟨.default, .never⟩)) = mfv
  obtain ⟨nmM, tyM, rfl⟩ : ∃ nmM tyM, mfv = Expr.fvar nP nmM tyM := ⟨_, _, hmfv.symm⟩
  have hclM : (Expr.fvar nP nmM tyM).looseBVarsBounded 0 = true := rfl
  have hX : (Expr.instSeq tfvs nP minorTy).instantiate1 (Expr.fvar nP nmM tyM) 0
      = Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP minorTy := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  have hmin' := Lech.replacePisPw_instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP (by simp [hlenT]) hmin
  have hres := Lech.instSeq_minorTele tfvs [Expr.fvar nP nmM tyM] hlenT hclT
    (by have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this)
  simp only [List.length_singleton, Nat.add_sub_cancel] at hres
  rw [hres] at hmin'
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1) hcstrip
  have hcread1 := ctorResidual_read_lift hcread hcw hlenD 1
  have hstX : stripPisAV nF (mkPisAV (liftDoms 1 0 (ds.drop nP)) (bodyC.liftN 1 nF))
      = some (liftDoms 1 0 (ds.drop nP), bodyC.liftN 1 nF) := by
    have := stripPisAV_mkPisAV (liftDoms 1 0 (ds.drop nP)) (bodyC.liftN 1 nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcread1 hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  rw [Lech.instSeq_minorBody tfvs xFvs (Expr.fvar nP nmM tyM) hlenT hlenX hclT hclM hclX,
    denoteP_minorCore hfC hlpsC hlenT hlenX hidxT hidxX, Option.map_some] at hminor
  -- the major and the conclusion, bottom-up
  have hmaj : denoteP m.acval env ψ (nP + 2)
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
        (.app (Expr.fvar nP nmM tyM) (.bvar 0)) ⟨.default, pw⟩)
      = some (AVExpr.pi 0 (pwBit ψ pw) (majorAV m T ψ nP) (.app (.bvar 2) (.bvar 0))) := by
    rw [denoteP_forallE, hfamR (nP + 2)]
    simp +decide only [Expr.instantiate1, ↓reduceIte]
    rw [denoteP_app, denoteP_fvar, denoteP_fvar]
    show some (AVExpr.pi 0 (pwBit ψ pw) (majorAV m T ψ nP)
      (.app (.bvar (nP + 2 + 1 - 1 - nP)) (.bvar (nP + 2 + 1 - 1 - (nP + 2))))) = _
    rw [show nP + 2 + 1 - 1 - nP = 2 from by omega,
      show nP + 2 + 1 - 1 - (nP + 2) = 0 from by omega]
  have hmk : denoteP m.acval env ψ (nP + 1)
      (.forallE (Lech.Name.lastStr C) (Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP minorTy)
        (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.app (Expr.fvar nP nmM tyM) (.bvar 0)) ⟨.default, pw⟩) ⟨.default, pw⟩)
      = some (AVExpr.pi 0 (pwBit ψ pw) (minorAV m C ψ nP nF (pwBit ψ pw) ds)
          (AVExpr.pi 0 (pwBit ψ pw) (majorAV m T ψ nP) (.app (.bvar 2) (.bvar 0)))) := by
    rw [denoteP_forallE, hminor]
    simp +decide only [Expr.instantiate1, hfamI, ↓reduceIte]
    rw [show nP + 1 + 1 = nP + 2 from rfl, hmaj]
    rfl
  have hmot : denoteP m.acval env ψ nP
      (.forallE (.str .anonymous "motive")
        (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩)
        (.forallE (Lech.Name.lastStr C) (Expr.instSeq tfvs nP minorTy)
          (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
            (.app (.bvar 2) (.bvar 0)) ⟨.default, pw⟩)
          ⟨.default, pw⟩) ⟨.default, pw⟩)
      = some (AVExpr.pi 0 (pwBit ψ pw) (motiveAV m T ψ nP ℓ)
          (AVExpr.pi 0 (pwBit ψ pw) (minorAV m C ψ nP nF (pwBit ψ pw) ds)
            (AVExpr.pi 0 (pwBit ψ pw) (majorAV m T ψ nP) (.app (.bvar 2) (.bvar 0))))) := by
    rw [denoteP_forallE, hmotive, hmfv]
    simp +decide only [Expr.instantiate1, hfamI, ↓reduceIte]
    rw [hX, hmk]
    rfl
  rw [hmot]
  subst hpw
  unfold recDataAV
  rw [mkPisAV_append]
  rfl

/-! ## The generated rule -/

theorem mkLamsAV_append :
    ∀ (l₁ l₂ : List (Nat × AVExpr)) (b : AVExpr),
      mkLamsAV (l₁ ++ l₂) b = mkLamsAV l₁ (mkLamsAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkLamsAV, mkLamsAV_append l₁ l₂ b]

theorem rebit_map_lam (b : Nat) (ds : List (Nat × Nat × AVExpr)) :
    (rebit b ds).map (fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2))
      = ds.map fun d => (b, d.2.2) := by
  simp [rebit, List.map_map, Function.comp_def]

/-- The rule's body `minor f⃗`, read at the full frame. -/
theorem denoteP_ruleCore {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF : Nat}
    {xFvs : List Expr} {nmK : Name} {tyK : Expr} (hlenX : xFvs.length = nF)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + 2 + k) nm ty) :
    denoteP m.acval env ψ (nP + 2 + nF) (Expr.mkAppN (.fvar (nP + 1) nmK tyK) xFvs)
      = some (AVExpr.mkAppN (.bvar nF) (fieldBvars nF)) := by
  have hspX : DenoteSpineP m.acval env ψ (nP + 2 + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 2 + nF) xFvs
      (nP + 2) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + 2 + nF - 1 - (nP + 2 + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  rw [denoteP_mkAppN hspX (by rw [denoteP_fvar]),
    show nP + 2 + nF - 1 - (nP + 1) = nF from by omega]

set_option maxHeartbeats 3200000 in
/-- **The generated rule reads to the λ-tower over `ruleDataAV`.** -/
theorem denoteP_directRecRhs {m : EnvS2Core V env} {ψ : Name → Nat} {T C : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nF : Nat}
    {ciT ciC : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    (hfC : env.find? C = some ciC) (hlpsC : ciC.toConstantVal.levelParams = lps)
    {tty cty rhs : Expr}
    (hgen : Lech.directRecRhs T lps elim large nP tty [(C, nF, cty)] 0 = some rhs)
    (hTf : tty.hasFvar = false)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {pps : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV pps (.sort w)))
    (hlenP : pps.length = nP)
    {ds : List (Nat × Nat × AVExpr)} {bodyC : AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty = some (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF) :
    denoteP m.acval env ψ 0 rhs
      = some (mkLamsAV (ruleDataAV m T C ψ nP nF (Lech.directElimLevel elim large) pps ds)
          (AVExpr.mkAppN (.bvar nF) (fieldBvars nF))) := by
  obtain ⟨cbs, crest0, minorTy, inner, hsC, hmin, hinner, hr⟩ := Lech.directRecRhs_single hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hr hmin hinner ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hr hmin hinner ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV pps (.sort w)) = some (pps, .sort w) := by
    rw [← hlenP]; exact stripPisAV_mkPisAV pps _
  rw [denoteP_pisToLamsPw nP hr hopT hTread hst, Nat.zero_add]
  -- the post-parameter telescope, instantiated at the parameters
  have hfamCl : (Expr.mkAppN (.const T (lps.map .param)) tfvs).looseBVarsBounded 0 = true :=
    Lech.looseBVarsBounded_mkAppN rfl hclT
  have hfamI : ∀ (v : Expr) (k : Nat),
      (Expr.mkAppN (.const T (lps.map .param)) tfvs).instantiate1 v k
        = Expr.mkAppN (.const T (lps.map .param)) tfvs :=
    fun v k => Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k) hfamCl)
  have e1 : Expr.instSeq tfvs (nP - 1) (Lech.directMotiveTy T lps nP ℓ)
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩ := by
    unfold Lech.directMotiveTy
    rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega), Lech.directFam_eq,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      show nP - 1 = 0 + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt tfvs 0 nP hclT (by omega), List.take_of_length_le (by omega)]
  have hbody : Expr.instSeq tfvs (nP - 1)
      (.lam (.str .anonymous "motive") (Lech.directMotiveTy T lps nP ℓ)
        (.lam (Lech.Name.lastStr C) minorTy inner ⟨.default, pw⟩) ⟨.default, pw⟩)
      = .lam (.str .anonymous "motive")
          (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
            (.sort ℓ) ⟨.default, .never⟩)
          (.lam (Lech.Name.lastStr C) (Expr.instSeq tfvs nP minorTy)
            (Expr.instSeq tfvs (nP + 1) inner) ⟨.default, pw⟩) ⟨.default, pw⟩ := by
    rw [Lech.instSeq_lam tfvs (nP - 1) _ _ _ _ (by omega),
      Lech.instSeq_lam tfvs (nP - 1 + 1) _ _ _ _ (by omega), e1,
      instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minorTy hnil,
      instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1 + 1) (t' := nP + 1) inner
        (by rcases hnil with h | h; exact Or.inl h; right; omega)]
  rw [hbody]
  -- the motive
  have hfamR : ∀ D, denoteP m.acval env ψ D (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) :=
    fun D => famSpine_read hfT hlpsT hlenT hidxT D ψ
  have hmotive : denoteP m.acval env ψ nP
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
        (.sort ℓ) ⟨.default, .never⟩) = some (motiveAV m T ψ nP ℓ) := by
    rw [denoteP_forallE, hfamR, Expr.instantiate1_sort, denoteP_sort]
    rfl
  -- the minor, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
      (.sort ℓ) ⟨.default, .never⟩)) = mfv
  obtain ⟨nmM, tyM, rfl⟩ : ∃ nmM tyM, mfv = Expr.fvar nP nmM tyM := ⟨_, _, hmfv.symm⟩
  have hclM : (Expr.fvar nP nmM tyM).looseBVarsBounded 0 = true := rfl
  have hX : (Expr.instSeq tfvs nP minorTy).instantiate1 (Expr.fvar nP nmM tyM) 0
      = Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP minorTy := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this
  have hmin' := Lech.replacePisPw_instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP (by simp [hlenT]) hmin
  have hres := Lech.instSeq_minorTele tfvs [Expr.fvar nP nmM tyM] hlenT hclT hcb0
  simp only [List.length_singleton, Nat.add_sub_cancel] at hres
  rw [hres] at hmin'
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1) hcstrip
  have hcread1 := ctorResidual_read_lift hcread hcw hlenD 1
  have hstX : stripPisAV nF (mkPisAV (liftDoms 1 0 (ds.drop nP)) (bodyC.liftN 1 nF))
      = some (liftDoms 1 0 (ds.drop nP), bodyC.liftN 1 nF) := by
    have := stripPisAV_mkPisAV (liftDoms 1 0 (ds.drop nP)) (bodyC.liftN 1 nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcread1 hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  rw [Lech.instSeq_minorBody tfvs xFvs (Expr.fvar nP nmM tyM) hlenT hlenX hclT hclM hclX,
    denoteP_minorCore hfC hlpsC hlenT hlenX hidxT hidxX, Option.map_some] at hminor
  -- the inner λ-telescope, at the motive's and the minor's variables
  generalize hmkfv : (Expr.fvar (nP + 1) (Lech.Name.lastStr C)
    (Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP minorTy)) = mkfv
  obtain ⟨nmK, tyK, rfl⟩ : ∃ nmK tyK, mkfv = Expr.fvar (nP + 1) nmK tyK := ⟨_, _, hmkfv.symm⟩
  have hclK : (Expr.fvar (nP + 1) nmK tyK).looseBVarsBounded 0 = true := rfl
  have hY : ((Expr.instSeq tfvs (nP + 1) inner).instantiate1 (Expr.fvar nP nmM tyM) 1).instantiate1
        (Expr.fvar (nP + 1) nmK tyK) 0
      = Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM, Expr.fvar (nP + 1) nmK tyK]) (nP + 1) inner := by
    rw [Expr.instSeq_append, hlenT, show nP + 1 - nP = 1 from by omega]
    rfl
  have hinner' := Lech.pisToLamsPw_instSeq (tfvs ++ [Expr.fvar nP nmM tyM, Expr.fvar (nP + 1) nmK tyK])
    (nP + 1) (by simp [hlenT]) hinner
  have hres2 : Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM, Expr.fvar (nP + 1) nmK tyK]) (nP + 1)
      (crest0.liftLooseBVars 2 0) = Expr.instSeq tfvs (nP - 1) crest0 :=
    Lech.instSeq_minorTele tfvs [Expr.fvar nP nmM tyM, Expr.fvar (nP + 1) nmK tyK] hlenT hclT hcb0
  rw [hres2] at hinner'
  obtain ⟨xFvs2, xrest2, hopX2⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 2) hcstrip
  have hcread2 := ctorResidual_read_lift hcread hcw hlenD 2
  have hstX2 : stripPisAV nF (mkPisAV (liftDoms 2 0 (ds.drop nP)) (bodyC.liftN 2 nF))
      = some (liftDoms 2 0 (ds.drop nP), bodyC.liftN 2 nF) := by
    have := stripPisAV_mkPisAV (liftDoms 2 0 (ds.drop nP)) (bodyC.liftN 2 nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hinnerR := denoteP_pisToLamsPw (acval := m.acval) (env := env) (φ := ψ) nF hinner' hopX2
    hcread2 hstX2
  obtain ⟨hlenX2, hidxX2, hclX2⟩ := opening_vars_at hopX2
  rw [Lech.instSeq_ruleBody tfvs xFvs2 (Expr.fvar nP nmM tyM) (Expr.fvar (nP + 1) nmK tyK)
      hlenT hlenX2 hclT hclM hclK hclX2,
    denoteP_ruleCore hlenX2 hidxX2, Option.map_some] at hinnerR
  -- assembly, bottom-up
  have hmk : denoteP m.acval env ψ (nP + 1)
      (.lam (Lech.Name.lastStr C) (Expr.instSeq (tfvs ++ [Expr.fvar nP nmM tyM]) nP minorTy)
        ((Expr.instSeq tfvs (nP + 1) inner).instantiate1 (Expr.fvar nP nmM tyM) 1) ⟨.default, pw⟩)
      = some (AVExpr.lam (pwBit ψ pw) (minorAV m C ψ nP nF (pwBit ψ pw) ds)
          (mkLamsAV ((liftDoms 2 0 (ds.drop nP)).map fun p => (pwBit ψ pw, p.2.2))
            (AVExpr.mkAppN (.bvar nF) (fieldBvars nF)))) := by
    rw [denoteP_lam, hminor, hmkfv, hY, show nP + 1 + 1 = nP + 2 from rfl, hinnerR]
    rfl
  have hmot : denoteP m.acval env ψ nP
      (.lam (.str .anonymous "motive")
        (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) tfvs)
          (.sort ℓ) ⟨.default, .never⟩)
        (.lam (Lech.Name.lastStr C) (Expr.instSeq tfvs nP minorTy)
          (Expr.instSeq tfvs (nP + 1) inner) ⟨.default, pw⟩) ⟨.default, pw⟩)
      = some (AVExpr.lam (pwBit ψ pw) (motiveAV m T ψ nP ℓ)
          (AVExpr.lam (pwBit ψ pw) (minorAV m C ψ nP nF (pwBit ψ pw) ds)
            (mkLamsAV ((liftDoms 2 0 (ds.drop nP)).map fun p => (pwBit ψ pw, p.2.2))
              (AVExpr.mkAppN (.bvar nF) (fieldBvars nF))))) := by
    rw [denoteP_lam, hmotive, hmfv]
    simp only [Expr.instantiate1]
    rw [hX, hmk]
    rfl
  rw [hmot]
  subst hpw
  unfold ruleDataAV
  rw [List.map_append, List.map_append, mkLamsAV_append, mkLamsAV_append, rebit_map_lam,
    rebit_map_lam]
  rfl

/-! ## The recursor's data, from the stage -/

/-- **The recursor's data**, read off the generated type: the reading
is syntactic (`denoteP_directRecTy`), the bits are the elimination
datum's (`zeronessOf_sound`), the grading is the fabricated type's own
inference run (`inferRow`). -/
theorem recData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr} {caps : IndCaps}
    (hRec : Lech.checkDirectRec (Lech.fueledOps μ F) env p cvTa cvCa = .ok (cvRa, rhsA))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds) :
    RecData mp.base2 cvRa p.nP (elimLevel p) (fun ψ =>
      recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p) (pps ψ) (ds ψ)) := by
  obtain ⟨cvRi, recTy, sty, rhsTy, u, -, hgen, -, htp, -, hbt, hRf, -, -, -, -, hsty, -, -, -, rfl⟩ :=
    Lech.checkDirectRec_shape hRec
  obtain ⟨hTf, -, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hTf hCf hCb
  have hread : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 recTy
      = some (mkPisAV (recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (.app (.bvar 2) (.bvar 0))) := fun ψ =>
    denoteP_directRecTy hfT hlpsT hfC hlpsC hgen hTf hCf hCb
      hstripC hopT (hFD.read ψ) (hFD.len ψ) (hCD.read ψ) (hCD.len ψ)
  have hw : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hRf
  have hL : Expr.LeavesBounded recTy := Expr.LeavesBounded.of_not_hasFvar hRf
  have hnil : recTy.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf
  have hlen : ∀ ψ, (recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
      (pps ψ) (ds ψ)).length = p.nP + 3 := by
    intro ψ
    simp [recDataAV, hFD.len ψ]
  refine ⟨hread, hlen, ?_, ?_, ?_, ?_⟩
  · intro ψ d hd
    have hb : d.2.1 = pwBit ψ (Level.zeronessOf (elimLevel p)) := by
      simp only [recDataAV, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hd
      rcases hd with h | rfl | rfl | rfl
      · exact mem_rebit h
      · rfl
      · rfl
      · rfl
    rw [hb, pwBit_eq_zero_iff, Lech.PropWhen.zeronessOf_sound, beq_iff_eq]
  · intro ψ ρ
    have hc := claimsAtP_of hμ mp ψ F
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hsty hw hbt hL (CtxOkP.nil hnil) (hread ψ)
    exact hokT ρ (Sat2_nil V ρ)
  · intro ψ
    have hst := stripPisAV_mkPisAV (recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF
      (elimLevel p) (pps ψ) (ds ψ)) (AVExpr.app (.bvar 2) (.bvar 0))
    exact (stripPisAV_below hst (bvarsBelow_of_reading hw hbt (hread ψ))).1
  · intro ψ₁ ψ₂ hφ
    have h2 := hread ψ₂
    have h1 : denoteP mp.base2.acval env ψ₂ 0 recTy
        = some (mkPisAV (recDataAV mp.base2 p.cvT.name p.cvC.name ψ₁ p.nP p.nF (elimLevel p)
            (pps ψ₁) (ds ψ₁)) (.app (.bvar 2) (.bvar 0))) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 recTy htp]
      exact hread ψ₁
    exact (mkPisAV_inj (by rw [hlen ψ₁, hlen ψ₂]) (Option.some.inj (h1.symm.trans h2))).1

/-- **The rule's data**: its reading at every assignment, graded by
its own inference run. -/
theorem ruleData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr} {caps : IndCaps}
    (hRec : Lech.checkDirectRec (Lech.fueledOps μ F) env p cvTa cvCa = .ok (cvRa, rhsA))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds) :
    (∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhsA
      = some (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF)))) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF)))) := by
  obtain ⟨cvRi, recTy, sty, rhsTy, u, -, -, hgen, -, -, -, -, -, -, hbr, hrf, -, -, -, hrty, -⟩ :=
    Lech.checkDirectRec_shape hRec
  obtain ⟨hTf, -, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hTf hCf hCb
  have hread : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhsA
      = some (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))) := fun ψ =>
    denoteP_directRecRhs hfT hlpsT hfC hlpsC hgen hTf hCf hCb
      hstripC hopT (hFD.read ψ) (hFD.len ψ) (hCD.read ψ) (hCD.len ψ)
  refine ⟨hread, fun ψ ρ => ?_⟩
  have hw : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrf
  have hL : Expr.LeavesBounded rhsA := Expr.LeavesBounded.of_not_hasFvar hrf
  have hnil : rhsA.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hrf
  have hc := claimsAtP_of hμ mp ψ F
  obtain ⟨-, -, hokR, -, -⟩ := hc.inferRow hrty hw hbr hL (CtxOkP.nil hnil) (hread ψ)
  exact hokR ρ (Sat2_nil V ρ)

end Lech.SetP
