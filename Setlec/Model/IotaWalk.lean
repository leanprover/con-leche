import Setlec.Kernel.Checker
import Setlec.Model.TypeChecker
import Setlec.Model.InstFrames

/-!
# Frame-crossing interpretation of opened telescopes

The defeq-based iota-rule install opens the stored `iota_j` theorem's
telescope at its *own* free variables (indices `0..`), while the fold
obligation's value spines arrive as telescope fits at *arbitrary*
frames.  The bridge is `interp_instSeq_fvarFrames`: the interpretation
of a closed expression instantiated along a free-variable spine is
determined by the spine's *values* — two spines with pointwise equal
values (at possibly unrelated frames) yield equal interpretations.

On top of it, `instPisAt`/`openPisAtFvars` are characterized as
instantiation sequences of the stripped telescope, and the *walk*
lemmas rebuild telescope fits at the theorem's frame:

* `peel_walk` builds a fit from pointwise memberships in the
  telescope's own (instantiated) domains;
* `pi_walk` transfers memberships along per-binder definitional
  equalities (`isDefEqCore` facts from the kernel's install checks),
  building the theorem-side fit from source-side memberships.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-! ## Fueled spine equalities -/

omit [SetTheory V] in
theorem fueledOpsW_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps F).isDefEq env d a b = isDefEqCore env F d a b := rfl

/-- Pairwise fueled definitional equality of two spines (the semantic
content of a successful `checkDefEqList`). -/
def DefEqListOk (F : Nat) (env : Env) (d : Nat) :
    List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    isDefEqCore env F d a b = .ok true ∧ DefEqListOk F env d as bs
  | _, _ => False

omit [SetTheory V] in
theorem DefEqListOk.length {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk F env d as bs →
      as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => rfl
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨_, h⟩ => simpa using ih h

omit [SetTheory V] in
theorem DefEqListOk.pointwise {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk F env d as bs →
      ∀ (i : Nat) {a b : Expr}, as[i]? = some a → bs[i]? = some b →
        isDefEqCore env F d a b = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h i a b ha hb
    exact nomatch ha
  | cons a₀ as ih =>
    intro bs h i a b ha hb
    match bs, h with
    | b₀ :: bs, ⟨h₀, h⟩ =>
      match i, ha, hb with
      | 0, ha, hb =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        exact h₀
      | i + 1, ha, hb => exact ih h i (by simpa using ha) (by simpa using hb)

/-- Invert a successful `checkDefEqList` run. -/
theorem checkDefEqList_inv {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr} {u : Unit},
    checkDefEqList (fueledOps F) env d as bs = .ok u →
    DefEqListOk F env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs u h
    match bs with
    | [] => trivial
    | _ :: _ =>
      simp only [checkDefEqList] at h
      exact nomatch h
  | cons a as ih =>
    intro bs u h
    match bs with
    | [] =>
      simp only [checkDefEqList] at h
      exact nomatch h
    | b :: bs =>
      simp only [checkDefEqList, fueledOpsW_isDefEq, Bind.bind,
        Except.bind] at h
      revert h
      cases hde : isDefEqCore env F d a b with
      | error e => intro h; exact nomatch h
      | ok v =>
        cases v with
        | false =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        | true =>
          intro h
          simp only [↓reduceIte, pure, Except.pure] at h
          exact ⟨hde, ih h⟩

omit [SetTheory V] in
/-- Invert the boolean equality-head test. -/
theorem isEqHead_inv {e : Expr} (h : isEqHead e = true) :
    ∃ ℓA, e = .const eqName [ℓA] := by
  match e, h with
  | .const c [ℓ], h =>
    refine ⟨ℓ, ?_⟩
    have hc : (c == eqName) = true := by simpa [isEqHead] using h
    rw [eq_of_beq hc]
  | .const _ [], h => simp [isEqHead] at h
  | .const _ (_ :: _ :: _), h => simp [isEqHead] at h
  | .bvar _, h => simp [isEqHead] at h
  | .fvar _ _ _, h => simp [isEqHead] at h
  | .sort _, h => simp [isEqHead] at h
  | .app _ _, h => simp [isEqHead] at h
  | .lam _ _ _ _, h => simp [isEqHead] at h
  | .forallE _ _ _ _, h => simp [isEqHead] at h
  | .letE _ _ _ _, h => simp [isEqHead] at h
  | .lit _, h => simp [isEqHead] at h
  | .proj _ _ _, h => simp [isEqHead] at h


/-! ## Characterizing the kernel's telescope openers -/

/-! ## The defeq-transfer telescope walk -/

/-- The two-sided defeq-transfer walk: the theorem-side telescope
(whose walk domains are the opening variables' annotations) and a
source-side telescope, opened at the *same* free-variable spine, with
per-binder fueled definitional equality of the domains.  Values known
to inhabit the source domains fit both telescopes, and every spine
variable's typing facts (`FvarsOk`) are established. -/
theorem pi_walk {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {tyS tyR : Expr}
      {dsR : List Expr} {restS restR : Expr},
      Expr.instPisAt spine tyS = some (spine.map Expr.fvarTypeD, restS) →
      Expr.instPisAt spine tyR = some (dsR, restR) →
      DefEqListOk F env D (spine.map Expr.fvarTypeD) dsR →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D tyS → tyS.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyS → FvarsOk V m.val env φ D ρ tyS →
      AnnotOk V m.val env φ D ρ tyS →
      WScoped D tyR → tyR.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyR → FvarsOk V m.val env φ D ρ tyR →
      AnnotOk V m.val env φ D ρ tyR →
      (∃ PS, interpExpr V m.val env φ D ρ tyS = some PS) →
      (∃ PR, interpExpr V m.val env φ D ρ tyR = some PR) →
      (∀ (k : Nat) (a : Expr) (v : V), dsR[k]? = some a →
        vs[k]? = some v →
        ∃ B, interpExpr V m.val env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V m.val env φ D ρ tyS spine vs restS ∧
      TeleFitI V m.val env φ D ρ tyR spine vs restR ∧
      (∀ a ∈ spine, FvarsOk V m.val env φ D ρ a) := by
  intro spine
  induction spine with
  | nil =>
    intro vs tyS tyR dsR restS restR hopS hopR hde hsp hws hWS hbS hLS
      hFS hAS hWR hbR hLR hFR hAR hIS hIR hmem
    simp only [List.map_nil, Expr.instPisAt, Option.some.injEq,
      Prod.mk.injEq] at hopS hopR
    obtain ⟨-, rfl⟩ := hopS
    obtain ⟨rfl, rfl⟩ := hopR
    match vs, hsp with
    | [], _ =>
      exact ⟨TeleFitI.nil, TeleFitI.nil, fun a ha => nomatch ha⟩
  | cons fv spine' ih =>
    intro vs tyS tyR dsR restS restR hopS hopR hde hsp hws hWS hbS hLS
      hFS hAS hWR hbR hLR hFR hAR hIS hIR hmem
    -- destructure the value spine and the fvar
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    -- destructure the two walks
    obtain ⟨nS, domS, bodyS, mS, dsS', rfl, hdsS, hS0⟩ :=
      instPisAt_cons_inv hopS
    obtain ⟨nR, domR, bodyR, mR, dsR', rfl, hdsRc, hR0⟩ :=
      instPisAt_cons_inv hopR
    have hdomS : domS = tfv ∧ dsS' = spine'.map Expr.fvarTypeD := by
      rw [List.map_cons] at hdsS
      injection hdsS with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    obtain ⟨hdomS1, rfl⟩ := hdomS
    subst domS
    subst hdsRc
    -- the defeq fact at this binder
    have hde0 : isDefEqCore env F D tfv domR = .ok true := by
      rw [List.map_cons] at hde
      exact hde.1
    have hde' : DefEqListOk F env D (spine'.map Expr.fvarTypeD) dsR' := by
      rw [List.map_cons] at hde
      exact hde.2
    -- structural facts
    have hWdomS : WScoped D tfv ∧ WScoped D bodyS := by
      simpa [WScoped] using hWS
    have hWdomR : WScoped D domR ∧ WScoped D bodyR := by
      simpa [WScoped] using hWR
    have hbdomS : tfv.looseBVarsBounded 0 = true ∧
        bodyS.looseBVarsBounded 1 = true := by
      revert hbS; simp [Expr.looseBVarsBounded]
    have hbdomR : domR.looseBVarsBounded 0 = true ∧
        bodyR.looseBVarsBounded 1 = true := by
      revert hbR; simp [Expr.looseBVarsBounded]
    have hLdomS := LeavesBounded.of_forallE_ty hLS
    have hLdomR := LeavesBounded.of_forallE_ty hLR
    have hFdomS : FvarsOk V m.val env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFS
    have hFdomR : FvarsOk V m.val env φ D ρ domR :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFR
    have hAS' := hAS
    simp only [AnnotOk] at hAS'
    obtain ⟨hAdomS, ⟨codS, hcodS⟩, hcondS⟩ := hAS'
    have hAR' := hAR
    simp only [AnnotOk] at hAR'
    obtain ⟨hAdomR, ⟨codR, hcodR⟩, hcondR⟩ := hAR'
    -- interpretations of the two domains
    obtain ⟨PS, hPS⟩ := hIS
    obtain ⟨PR, hPR⟩ := hIR
    have hIdomS : ∃ AS, interpExpr V m.val env φ D ρ tfv = some AS := by
      revert hPS
      simp only [interpExpr, hcodS]
      cases hAS0 : interpExpr V m.val env φ D ρ tfv with
      | none => intro hPS; exact nomatch hPS
      | some AS => intro _; exact ⟨AS, rfl⟩
    obtain ⟨AS, hASi⟩ := hIdomS
    obtain ⟨B, hBi, hvB⟩ := hmem 0 domR v rfl rfl
    -- the defeq identifies the domains' interpretations
    have hASB : AS = B :=
      isDefEqCore_sound m F hde0 hWdomS.1 hWdomR.1 hbdomS.1 hbdomR.1
        hLdomS hLdomR hFdomS hFdomR hAdomS hAdomR hASi hBi
    have hvAS : v ∈ˢ AS := by rw [hASB]; exact hvB
    -- the opening variable's own facts
    have hifv : interpExpr V m.val env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    have hFfv : FvarsOk V m.val env φ D ρ (.fvar i nfv tfv) := by
      intro l hl
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨hiD, hAdomS, AS, hASi, by rw [hval]; exact hvAS⟩
      · exact hFdomS l hl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hLfv : Expr.LeavesBounded (.fvar i nfv tfv) :=
      LeavesBounded.fvar hbdomS.1 hLdomS
    -- step both bodies
    obtain ⟨hAopS, hfibS⟩ := hcondS v AS hASi hvAS
    obtain ⟨hAopR, hfibR⟩ := hcondR v B hBi hvB
    have hAbodyS : AnnotOk V m.val env φ D ρ
        (bodyS.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWdomS.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAopS
    have hAbodyR : AnnotOk V m.val env φ D ρ
        (bodyR.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWdomR.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAopR
    obtain ⟨wS, hwS, -⟩ := hfibS codS hcodS
    obtain ⟨wR, hwR, -⟩ := hfibR codR hcodR
    have hIbodyS : ∃ P, interpExpr V m.val env φ D ρ
        (bodyS.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨wS, ?_⟩
      rw [interp_beta (n := nS) (ty := tfv) hWdomS.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwS
    have hIbodyR : ∃ P, interpExpr V m.val env φ D ρ
        (bodyR.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨wR, ?_⟩
      rw [interp_beta (n := nR) (ty := domR) hWdomR.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwR
    -- recursive call
    have hrec := ih (vs := vs') (dsR := dsR')
      (restS := restS) (restR := restR)
      hS0 hR0
      hde' hsp' (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWdomS.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbdomS.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hLS)
        hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 bodyS 0 hl with hl' | hl'
        · exact hFS l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbodyS
      (WScoped.instantiate1_gen hwfv 0 hWdomR.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbdomR.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hLR)
        hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 bodyR 0 hl with hl' | hl'
        · exact hFR l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbodyR hIbodyS hIbodyR
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show (domR :: dsR')[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    obtain ⟨hfitS, hfitR, hspineF⟩ := hrec
    refine ⟨?_, ?_, ?_⟩
    · exact TeleFitI.cons hASi hifv hvAS hWdomS.2.fvarsBelow hwfv
        (by rfl) (by simp [AnnotOk]) hfitS
    · exact TeleFitI.cons hBi hifv hvB hWdomR.2.fvarsBelow hwfv
        (by rfl) (by simp [AnnotOk]) hfitR
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hFfv
      · exact hspineF a ha

/-! ## Renaming and telescope bookkeeping -/

omit [SetTheory V] in
theorem hasFvar_renameConsts {f : Name → Name} :
    ∀ (e : Expr), (e.renameConsts f).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.hasFvar]

omit [SetTheory V] in
/-- Renaming maps a stripped telescope pointwise. -/
theorem stripPis_renameConsts {f : Name → Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis n = some (bs, body) →
      (e.renameConsts f).stripPis n =
        some (bs.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
          body.renameConsts f) := by
  intro n
  induction n with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro e bs body h
    match e, h with
    | .forallE nm dom b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hbs, hbody⟩ : (nm, dom, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbs hbody
        show ((b.renameConsts f).stripPis n).map _ = _
        rw [ih hs]
        rfl

/-- Forward renaming transport for annotation truthfulness. -/
theorem AnnotOk.renameConsts {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env φ d ρ e →
      AnnotOk V cval env φ d ρ (e.renameConsts f)
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro ty d ρ haty, hcod, ?_⟩
    intro x A hity hx
    rw [interp_renameConsts hro ty d ρ] at hity
    obtain ⟨hbody, hw⟩ := hcond x A hity hx
    have hopen : ((body.renameConsts f).instantiate1
        (.fvar d n (ty.renameConsts f))) =
        (body.instantiate1 (.fvar d n ty)).renameConsts f := by
      rw [Expr.renameConsts_instantiate1]
    constructor
    · rw [hopen]
      exact AnnotOk.renameConsts hro _ (d + 1) (updV V ρ d x) hbody
    · intro v hv
      obtain ⟨w, hwi, hwu⟩ := hw v hv
      refine ⟨w, ?_, hwu⟩
      rw [hopen, interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
      exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro ty d ρ haty, hcod, ?_⟩
    intro x A hity hx
    rw [interp_renameConsts hro ty d ρ] at hity
    obtain ⟨hbody, hw⟩ := hcond x A hity hx
    have hopen : ((body.renameConsts f).instantiate1
        (.fvar d n (ty.renameConsts f))) =
        (body.instantiate1 (.fvar d n ty)).renameConsts f := by
      rw [Expr.renameConsts_instantiate1]
    constructor
    · rw [hopen]
      exact AnnotOk.renameConsts hro _ (d + 1) (updV V ρ d x) hbody
    · intro v hv
      obtain ⟨w, B, hwi, hwB, hBu⟩ := hw v hv
      refine ⟨w, B, ?_, hwB, hBu⟩
      rw [hopen, interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
      exact hwi
  | .app g a, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨hg, haa, vf, va, vE, A, B, hif, hia, hp, hm, hfib⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro g d ρ hg,
      AnnotOk.renameConsts hro a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hp, hm, hfib⟩
    · rw [interp_renameConsts hro g d ρ]; exact hif
    · rw [interp_renameConsts hro a d ρ]; exact hia
  | .proj s i e, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨he, hi2, ve, u, v, A, Bf, hie, hs, hAu, hBf⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro e d ρ he, hi2,
      ve, u, v, A, Bf, ?_, hs, hAu, hBf⟩
    rw [interp_renameConsts hro e d ρ]
    exact hie
  | .bvar _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .fvar _ _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .sort _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .const _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .letE _ _ _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .lit _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ## One-sided walks -/

/-- Build a `∀`-telescope fit at a free-variable frame from pointwise
memberships in the walk's own (instantiated) domains. -/
theorem peel_walk {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {ty : Expr} {ds : List Expr}
      {rest : Expr},
      Expr.instPisAt spine ty = some (ds, rest) →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D ty →
      AnnotOk V cval env φ D ρ ty →
      (∃ P, interpExpr V cval env φ D ρ ty = some P) →
      (∀ (k : Nat) (a : Expr) (v : V), ds[k]? = some a →
        vs[k]? = some v →
        ∃ B, interpExpr V cval env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V cval env φ D ρ ty spine vs rest ∧
      (∃ P', interpExpr V cval env φ D ρ rest = some P') := by
  intro spine
  induction spine with
  | nil =>
    intro vs ty ds rest hop hsp hws hW hA hI hmem
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact ⟨TeleFitI.nil, hI⟩
  | cons fv spine' ih =>
    intro vs ty ds rest hop hsp hws hW hA hI hmem
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m, ds', rfl, rfl, h0⟩ := instPisAt_cons_inv hop
    have hWd : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    obtain ⟨B, hBi, hvB⟩ := hmem 0 dom v rfl rfl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V cval env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    obtain ⟨hAop, hfib⟩ := hcond v B hBi hvB
    have hAbody : AnnotOk V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨w, hwi, -⟩ := hfib cod hcod
    have hIbody : ∃ P, interpExpr V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨w, ?_⟩
      rw [interp_beta (n := n) (ty := dom) hWd.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwi
    obtain ⟨hfit, hIrest⟩ := ih h0 hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2) hAbody hIbody
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show (dom :: ds')[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    exact ⟨TeleFitI.cons hBi hifv hvB hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) hfit, hIrest⟩

/-- The λ-tower walk: the rule's λ-domains are definitionally the
opening variables' annotations, whose typing packages (`FvarsOk` of
the variables) carry the values' memberships; the values then fit the
λ-tower itself. -/
theorem lam_walk {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {tyL : Expr} {dsL : List Expr}
      {restL : Expr},
      Expr.instLamsAt spine tyL = some (dsL, restL) →
      DefEqListOk F env D (spine.map Expr.fvarTypeD) dsL →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      (∀ a ∈ spine, FvarsOk V m.val env φ D ρ a) →
      (∀ a ∈ spine, Expr.LeavesBounded a) →
      WScoped D tyL → tyL.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyL → FvarsOk V m.val env φ D ρ tyL →
      AnnotOk V m.val env φ D ρ tyL →
      (∃ L, interpExpr V m.val env φ D ρ tyL = some L) →
      TeleFitLam m.val env φ D ρ tyL spine vs restL := by
  intro spine
  induction spine with
  | nil =>
    intro vs tyL dsL restL hop hde hsp hws hFs hLs hW hb hL hF hA hI
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact TeleFitLam.nil
  | cons fv spine' ih =>
    intro vs tyL dsL restL hop hde hsp hws hFs hLs hW hb hL hF hA hI
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m', ds', rfl, rfl, h0⟩ :=
      instLamsAt_cons_inv hop
    -- the λ-side structural facts
    have hWd : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hbd : dom.looseBVarsBounded 0 = true ∧
        body.looseBVarsBounded 1 = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hLdom : Expr.LeavesBounded dom := by
      intro l hl
      exact hL l (by simp only [fvarLeaves, List.mem_append]
                     exact Or.inl hl)
    have hLbody : Expr.LeavesBounded body := by
      intro l hl
      exact hL l (by simp only [fvarLeaves, List.mem_append]
                     exact Or.inr hl)
    have hFdom : FvarsOk V m.val env φ D ρ dom :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hF
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    -- the opening variable's package
    have hFfv := hFs _ List.mem_cons_self
    have hhead := hFfv (i, nfv, tfv) (by simp [fvarLeaves])
    obtain ⟨-, hAann, T, hTi, hvT⟩ := hhead
    rw [hval] at hvT
    have hWann : WScoped D tfv := by
      have := hws _ List.mem_cons_self
      have h2 : i < D ∧ WScoped i tfv := by simpa [WScoped] using this
      exact h2.2.mono (by omega)
    have hLann : Expr.LeavesBounded tfv := by
      intro l hl
      exact hLs _ List.mem_cons_self l (by
        simp only [fvarLeaves, List.mem_cons]
        exact Or.inr hl)
    have hbann : tfv.looseBVarsBounded 0 = true := by
      have := hLs _ List.mem_cons_self (i, nfv, tfv)
        (by simp [fvarLeaves])
      exact this
    have hFann : FvarsOk V m.val env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_cons]
        exact Or.inr hl) hFfv
    -- λ-domain interpretation is defined
    obtain ⟨L, hLi⟩ := hI
    have hIdom : ∃ A, interpExpr V m.val env φ D ρ dom = some A := by
      revert hLi
      simp only [interpExpr, hcod]
      cases hd : interpExpr V m.val env φ D ρ dom with
      | none => intro hLi; exact nomatch hLi
      | some A => intro _; exact ⟨A, rfl⟩
    obtain ⟨A, hAi⟩ := hIdom
    -- the defeq identifies the λ-domain with the annotation
    have hde0 : isDefEqCore env F D tfv dom = .ok true := by
      rw [List.map_cons] at hde
      exact hde.1
    have hTA : T = A :=
      isDefEqCore_sound m F hde0 hWann hWd.1 hbann hbd.1 hLann hLdom
        hFann hFdom hAann hAdom hTi hAi
    have hvA : v ∈ˢ A := by rw [← hTA]; exact hvT
    -- step the body
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V m.val env φ D ρ (.fvar i nfv tfv) =
        some v := by
      simp only [interpExpr]
      rw [hval]
    obtain ⟨hAop, hfib⟩ := hcond v A hAi hvA
    have hAbody : AnnotOk V m.val env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hfib cod hcod
    have hIbody : ∃ P, interpExpr V m.val env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨w, ?_⟩
      rw [interp_beta (n := n) (ty := dom) hWd.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwi
    have hLfv : Expr.LeavesBounded (Expr.fvar i nfv tfv) :=
      hLs _ List.mem_cons_self
    refine TeleFitLam.cons hAi hifv hvA hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) ?_
    refine ih h0 (by
        rw [List.map_cons] at hde
        exact hde.2) hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (fun a ha => hFs a (List.mem_cons_of_mem _ ha))
      (fun a ha => hLs a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbd.2)
      (LeavesBounded.instantiate1 hLbody hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hF l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbody hIbody

/-! ## More telescope bookkeeping -/

/-- One-sided variant of `pi_walk`: the telescope's walk domains are
the opening variables' annotations, memberships are given directly,
and every opening variable's typing package is established. -/
theorem self_walk {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {ty : Expr} {rest : Expr},
      Expr.instPisAt spine ty = some (spine.map Expr.fvarTypeD, rest) →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → FvarsOk V cval env φ D ρ ty →
      AnnotOk V cval env φ D ρ ty →
      (∀ (k : Nat) (a : Expr) (v : V),
        (spine.map Expr.fvarTypeD)[k]? = some a → vs[k]? = some v →
        ∃ B, interpExpr V cval env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V cval env φ D ρ ty spine vs rest ∧
      (∀ a ∈ spine, FvarsOk V cval env φ D ρ a) := by
  intro spine
  induction spine with
  | nil =>
    intro vs ty rest hop hsp hws hW hb hL hF hA hmem
    simp only [List.map_nil, Expr.instPisAt, Option.some.injEq,
      Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact ⟨TeleFitI.nil, fun a ha => nomatch ha⟩
  | cons fv spine' ih =>
    intro vs ty rest hop hsp hws hW hb hL hF hA hmem
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m, ds', rfl, hdsS, h0⟩ := instPisAt_cons_inv hop
    have hdomS : dom = tfv ∧ ds' = spine'.map Expr.fvarTypeD := by
      rw [List.map_cons] at hdsS
      injection hdsS with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    obtain ⟨hdomS1, rfl⟩ := hdomS
    subst dom
    have hWd : WScoped D tfv ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hbd : tfv.looseBVarsBounded 0 = true ∧
        body.looseBVarsBounded 1 = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hLdom := LeavesBounded.of_forallE_ty hL
    have hFdom : FvarsOk V cval env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hF
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    obtain ⟨B, hBi, hvB⟩ := hmem 0 tfv v (by simp [Expr.fvarTypeD]) rfl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V cval env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    have hFfv : FvarsOk V cval env φ D ρ (.fvar i nfv tfv) := by
      intro l hl
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨hiD, hAdom, B, hBi, by rw [hval]; exact hvB⟩
      · exact hFdom l hl
    have hLfv : Expr.LeavesBounded (.fvar i nfv tfv) :=
      LeavesBounded.fvar hbd.1 hLdom
    obtain ⟨hAop, hfib⟩ := hcond v B hBi hvB
    have hAbody : AnnotOk V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨hfit, hspineF⟩ := ih h0 hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbd.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hL) hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hF l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbody
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show ((Expr.fvar i nfv tfv :: spine').map
            Expr.fvarTypeD)[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    refine ⟨TeleFitI.cons hBi hifv hvB hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) hfit, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hFfv
    · exact hspineF a ha


/-- Renaming inside an opening-variable instantiation sequence is
interpretation-invariant. -/
theorem interp_instSeq_ren {f : Name → Name} (hro : RenameOk cval env f)
    {spine : List Expr} {t : Nat} {X : Expr} {D : Nat} {ρ : Nat → V}
    (hfv : ∀ a ∈ spine, ∃ i nm ty, a = .fvar i nm ty) :
    interpExpr V cval env φ D ρ (instSeq spine t (X.renameConsts f)) =
    interpExpr V cval env φ D ρ (instSeq spine t X) := by
  have hee := instSeq_renameConsts (f := f) spine t (X := X)
    (fun a ha => by
      obtain ⟨i, nm, ty, rfl⟩ := hfv a ha
      exact rfl)
  rw [← interp_erasedEq hee D ρ]
  exact interp_renameConsts hro _ D ρ


omit [SetTheory V] in
theorem looseBVarsBounded_renameConsts {f : Name → Name} :
    ∀ (e : Expr) (k : Nat),
      (e.renameConsts f).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.renameConsts, Expr.looseBVarsBounded]


omit [SetTheory V] in
theorem renameConsts_mkAppN {f : Name → Name} :
    ∀ (xs : List Expr) (h : Expr),
      (Expr.mkAppN h xs).renameConsts f =
        Expr.mkAppN (h.renameConsts f) (xs.map (·.renameConsts f))
  | [], h => rfl
  | x :: xs, h => by
    show (Expr.mkAppN (.app h x) xs).renameConsts f = _
    rw [renameConsts_mkAppN xs (.app h x)]
    rfl

/-- A free-variable spine interprets pointwise to its values. -/
theorem InterpSpine_of_FvarSpine {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      InterpSpine cval env φ D ρ as vs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, v :: vs, h => by
    obtain ⟨⟨i, n, ty, rfl, hiD, hval⟩, h'⟩ := h
    exact ⟨by simp [interpExpr, hval], InterpSpine_of_FvarSpine h'⟩


theorem InterpSpine.pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      InterpSpine cval env φ D ρ as vs →
      ∀ (k : Nat) {a : Expr} {v : V}, as[k]? = some a → vs[k]? = some v →
        interpExpr V cval env φ D ρ a = some v
  | [], [], _, k, a, v, ha, _ => nomatch ha
  | [], _ :: _, h, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _ => nomatch h
  | a₀ :: as, v₀ :: vs, h, k, a, v, ha, hv => by
    cases k with
    | zero =>
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hv
      exact h.1
    | succ k =>
      exact InterpSpine.pointwise h.2 k (by simpa using ha)
        (by simpa using hv)

theorem InterpSpine.of_pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      as.length = vs.length →
      (∀ (k : Nat) (a : Expr) (v : V), as[k]? = some a →
        vs[k]? = some v → interpExpr V cval env φ D ρ a = some v) →
      InterpSpine cval env φ D ρ as vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a₀ :: as, v₀ :: vs, hlen, hpt => by
    refine ⟨hpt 0 a₀ v₀ rfl rfl, ?_⟩
    exact InterpSpine.of_pointwise (by simpa using hlen)
      (fun k a v ha hv => hpt (k + 1) a v (by simpa using ha)
        (by simpa using hv))


omit [SetTheory V] in
/-- A canonical rule's constructor parameters are among the recursor's
prefix. -/
theorem recRulePlain_le {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) :
    cnP ≤ rP := by
  rw [Expr.recRulePlain, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1

omit [SetTheory V] in
/-- A canonical rule's prefix fits under the major's position. -/
theorem recRulePlain_le_mI {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) :
    rP ≤ mI := by
  rw [Expr.recRulePlain, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

omit [SetTheory V] in
/-- A canonical rule pins the recursor type's telescope. -/
theorem recRulePlain_strip {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) :
    (recTy.stripPis mI).isSome = true := by
  rw [Expr.recRulePlain, Bool.and_eq_true] at h
  have h2 := h.2
  revert h2
  cases hs : recTy.stripPis mI with
  | none => intro h2; exact nomatch h2
  | some p => intro _; rfl

end Setlec
