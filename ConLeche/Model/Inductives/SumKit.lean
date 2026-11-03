module

import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Semantics.Tower.SumTower
public import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Reading.Levels
import ConLeche.Model.IndPointKit

public section

/-!
# Block library: constructor lists over an indexed family

The single-constructor library at a constructor list over an indexed
family: the sum leaves' P packages; the constructors' data and
frames; the former's walks and a constructor's cons; the constructors'
loop facts.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `Term` bookkeeping -/

theorem DenoteSpine.unique {acval : Name → (Name → Nat) → Term} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List Term},
      DenoteSpine acval env φ d as vs → DenoteSpine acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteSpine.unique h h']

/-! ## The entries -/

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List Term × List Term


/-!
## The constructor data and frames

`CtorDataI`: the constructor's type at an indexed family reads to the Π-tower over its field data ending in the family at the
parameter variables and the **index readings** `Es` (the readings of
the residual's index expressions at the constructor's own frame), and
the field **sources** `srcs` (per field: the index position the field
literally is, or none — the squash-regime recursor body applies its
minor to the sources; a field without a source at a large-eliminating
`Prop` family is propositional, `FieldsBoundSrc`).  `sumCtorData_of`
reads them off `checkSumCtor`'s run (the residual `T p⃗ e⃗` at
the opened frame, its spine inverted), and `ctorFramesGen` gives the
constructor's frames: the parameter frames identified, the field
chain graded, the index expressions graded and **fitting the former's
index telescope** — read off the residual's own grading
(`spineFit_of_wellDenoted_lams`: an application spine graded against a
λ-tower fits the tower's domains, since a graph determines its
domain).
-/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)


/-! ## Kit -/

/-- The arguments of a bounded spine are bounded. -/
theorem bvarsBelow_mkAppN_inv {k : Nat} :
    ∀ {as : List Term} {f : Term}, Term.bvarsBelow k (Term.mkAppN f as) →
      Term.bvarsBelow k f ∧ ∀ a ∈ as, Term.bvarsBelow k a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hf, hall⟩ := bvarsBelow_mkAppN_inv (as := as) (f := .app f a) h
    exact ⟨hf.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hf.2
      · exact hall a' ha'⟩

/-- The head and the arguments of a graded spine are graded. -/
theorem WellDenoted.mkAppN_inv {ρ : Nat → V} :
    ∀ {args : List Term} {f : Term}, WellDenoted V ρ (Term.mkAppN f args) →
      WellDenoted V ρ f ∧ ∀ a ∈ args, WellDenoted V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [Term.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := WellDenoted.mkAppN_inv h
    rw [WellDenoted_app] at hfa
    exact ⟨hfa.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hfa.2.1
      · exact hall a' ha'⟩

/-- Equal graphs have equal domains. -/
theorem graph_eq_dom {F G : V → V} {A D : V} (h : graph F A = graph G D) : A = D := by
  apply SetTheory.ext
  intro x
  constructor
  · intro hx
    have : kpair x (F x) ∈ˢ graph G D := h ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'
  · intro hx
    have : kpair x (G x) ∈ˢ graph F A := h.symm ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'

/-- **A spine graded against a λ-tower fits its domains**, where the
applied spine is not the point: then no partial application is the
point (`app_pt`), so each λ is a graph (`lamV_eq_graph`), and a graph
determines its domain, the slot's. -/
theorem spineFit_of_wellDenoted_lams {b : Term} :
    ∀ {args : List Term} {ds : List Term} {σ ρ : Nat → V} {f : Term},
      args.length ≤ ds.length →
      WellDenoted V ρ (Term.mkAppN f args) →
      interp V ρ (Term.mkAppN f args) ≠ pt →
      interp V ρ f = interp V σ (mkLamsAV ds b) →
      SpineFit σ ((ds.take args.length)) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: args, d :: ds, σ, ρ, f, hlen, hok, hne, hf => by
    rw [Term.mkAppN_cons] at hok hne
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hf' : interp V ρ f
        = lamV (interp V σ d) fun x => interp V (cons x σ) (mkLamsAV ds b) := by
      rw [hf]; rfl
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      apply hne
      have hpt : ∀ (as : List Term) (g : Term), interp V ρ g = pt →
          interp V ρ (Term.mkAppN g as) = pt := by
        intro as
        induction as with
        | nil => intro g hg; exact hg
        | cons x xs ih => intro g hg; exact ih (.app g x) (by rw [interp_app, hg, app_pt])
      exact hpt args _ (by rw [interp_app, h0, app_pt])
    rw [hf'] at hfm hfne
    have hv : v ≠ 0 := by
      rintro rfl; exact hfne (eq_pt_of_mem_piR_zero hfm)
    have hg := (mem_piR_pos hv hfm).1
    rw [lamV_eq_graph hfne] at hg
    have hA : A = interp V σ d := graph_eq_dom hg
    rw [hA] at ham
    have happ : interp V ρ (.app f a) = interp V (cons (interp V ρ a) σ) (mkLamsAV ds b) := by
      rw [interp_app, hf', app_lamV ham]
    have ih := spineFit_of_wellDenoted_lams (args := args) (ds := ds) (σ := cons (interp V ρ a) σ)
      (ρ := ρ) (f := .app f a) (by simpa using hlen) hok hne happ
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    exact ⟨ham, ih⟩

/-- **The body of a graded Π-tower that is a type is a type** at every
fitting spine (`WellDenoted`'s Π clause: the fibres are types). -/
theorem IsTy_body_of_mkPisAV {R : Term} :
    ∀ {ds : List Term} {ρ : Nat → V} {vs : List V},
      WellDenoted V ρ (mkPisAV ds R) → IsTy (interp V ρ (mkPisAV ds R)) →
      SpineFit ρ (ds) vs → IsTy (interp V (consList vs ρ) R)
  | [], _, [], _, hT, _ => hT
  | [], _, _ :: _, _, _, hsp => hsp.elim
  | _ :: _, _, [], _, _, hsp => hsp.elim
  | d :: ds, ρ, v :: vs, hok, _, hsp => by
    have hok' : WellDenoted V ρ (.pi d (mkPisAV ds R)) := hok
    rw [WellDenoted_pi] at hok'
    rw [consList_cons]
    exact IsTy_body_of_mkPisAV (hok'.2.2.1 v hsp.1) (hok'.2.2.2 v hsp.1) hsp.2

/-- The body of a closed graded Π-type is a type under every valuation
satisfying the type's telescope. -/
theorem IsTy_body_of_sat {R : Term} {ds : List Term} {σ : Nat → V}
    (hT : ∀ ρ : Nat → V, WellDenotedTy V ρ (mkPisAV ds R))
    (hsat : Sat V ((ds).reverse) σ) : IsTy (interp V σ R) := by
  have hsp := spineFit_of_sat (Ds := ds) (Δ₀ := []) (by simpa using hsat)
  rw [← frameIdx_eq_reverse_map] at hsp
  have h := IsTy_body_of_mkPisAV (hT _).1 (hT _).2 hsp
  rwa [show (fun j => σ (j + (ds).length)) = shiftE (ds).length 0 σ from by
      funext j; simp [shiftE], consList_frameIdx] at h

/-- A read spine crosses a cons its terms do not mention. -/
theorem DenoteSpine.cons_mono {acval : Name → (Name → Nat) → Term}
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term} (hfresh : env.find? c₀.name = none)
    {ψ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List Term}, (∀ a ∈ as, ConstsBound env a) →
      DenoteSpine acval env ψ d as vs →
      DenoteSpine (acvalWith acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hcb, .cons ha htl =>
    .cons (denote_cons_mono hfresh ψ d (hcb a List.mem_cons_self) ha)
      (DenoteSpine.cons_mono hfresh (fun a' ha' => hcb a' (List.mem_cons_of_mem _ ha')) htl)

omit [SetTheory V] in
/-- A valuation agreeing with the parameters below `nP`. -/
theorem consList_params_apply {nP : Nat} (ρ X : Nat → V) {i : Nat} (hi : i < nP) :
    consList ((List.range nP).reverse.map ρ) X i = ρ i := by
  have hlt : ((List.range nP).reverse.map ρ).length - 1 - i < ((List.range nP).reverse.map ρ).length := by
    simp; omega
  have h1 := consList_apply_lt ((List.range nP).reverse.map ρ) X i (by simpa using hi)
  have h2 := consList_apply_lt ((List.range nP).reverse.map ρ) (fun j => ρ (j + nP)) i
    (by simpa using hi)
  rw [consList_range_reverse] at h2
  rw [List.getElem?_eq_getElem hlt, Option.getD_some] at h1 h2
  rw [h1, h2]

/-! ## The field sources -/

/-- The first position of an expression in a list. -/
def firstIdx (x : Expr) : List Expr → Option Nat
  | [] => none
  | a :: as => if a = x then some 0 else (firstIdx x as).map (· + 1)

theorem firstIdx_some : ∀ {l : List Expr} {x : Expr} {i : Nat},
    firstIdx x l = some i → l[i]? = some x
  | [], _, _, h => by simp [firstIdx] at h
  | a :: as, x, i, h => by
    simp only [firstIdx] at h
    split at h
    · next hax =>
      obtain rfl := Option.some.inj h
      simp [hax]
    · obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using firstIdx_some hi'

theorem firstIdx_of_mem : ∀ {l : List Expr} {x : Expr}, x ∈ l → ∃ i, firstIdx x l = some i
  | [], _, h => nomatch h
  | a :: as, x, h => by
    simp only [firstIdx]
    by_cases hax : a = x
    · exact ⟨0, by rw [ite_eq_left hax]⟩
    · rw [ite_eq_right hax]
      obtain ⟨i, hi⟩ := firstIdx_of_mem (l := as) (x := x)
        (by rcases List.mem_cons.mp h with rfl | h'; exact absurd rfl hax; exact h')
      exact ⟨i + 1, by rw [hi]; rfl⟩

/-- The sources of the fields: a field whose sort is `Prop` is a proof
(`none`); otherwise the first index position the field variable
occupies. -/
def srcsOf (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map fun j =>
    if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
    else firstIdx (xFvs.getD j default) idxArgs

theorem srcsOf_length (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) :
    (srcsOf xFvs idxArgs sorts nF).length = nF := by simp [srcsOf]

theorem srcsOf_getElem? (xFvs idxArgs : List Expr) (sorts : List Level) (nF j : Nat) (hj : j < nF) :
    (srcsOf xFvs idxArgs sorts nF)[j]?
      = some (if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
          else firstIdx (xFvs.getD j default) idxArgs) := by
  simp [srcsOf, hj]

/-- The fields not sourced by an index are propositions: each such
field's domain is a truth value, hereditarily. -/
@[expose] def FieldsBoundSrc (ρ : Nat → V) : List Term → List (Option Nat) → Prop
  | [], _ => True
  | _ :: _, [] => True
  | F :: Fs, s :: ss => (s = none → interp V ρ F ∈ˢ (univ 0 : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBoundSrc (cons a ρ) Fs ss

/-- `fieldsBound_of_frame` at the sourced fields. -/
theorem fieldsBoundSrc_of_frame {Γ : List Term} {k nP nF : Nat} {srcs : List (Option Nat)}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → srcs[j]? = some none → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ 0 : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    cases hs : srcs.drop j with
    | nil => trivial
    | cons s ss =>
      have hsj : srcs[j]? = some s := by
        have := congrArg (·[0]?) hs
        simpa [List.getElem?_drop] using this
      have hss : srcs.drop (j + 1) = ss := by
        rw [← List.drop_drop, hs]
        rfl
      refine ⟨fun hsn => hbnd j hlt (hsn ▸ hsj) ρ hρ, fun a ha => ?_⟩
      rw [← hss]
      refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
      rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
      have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
        rw [List.getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
      exact Sat_cons V hρ ha

/-! ## The constructor's data -/

/-- The family at the parameter variables and the index readings,
read at the constructor's full frame. -/
@[expose] def ctorBodyAVI {env : Env} (m : EnvModel V env) (T : Name) (nP nF : Nat)
    (ψ : Name → Nat) (Es : List Term) : Term :=
  Term.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)

/-- **A constructor's data at an indexed family**: its stored type
reads to the Π-tower over `ds ψ` ending in the family at the
parameters and the index readings `Es ψ`; the index readings read the
residual's index expressions `idxArgs` at the constructor's frame; the
sources `srcs` name, per field, the index it literally is, and at a
large-eliminating `Prop` family the other fields are
propositional. -/
structure CtorDataI {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name)
    (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (idxArgs : List Expr)
    (ds : (Name → Nat) → List Term) (Es : (Name → Nat) → List Term)
    (srcs : List (Option Nat)) : Prop where
  resid : ∃ (cbs : List Expr) (es : List Expr),
    cvC.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
    es.length = nIdx
  read : ∀ ψ : Name → Nat, denote m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  lenE : ∀ ψ : Name → Nat, (Es ψ).length = nIdx
  idxLen : idxArgs.length = nIdx
  idxRead : ∀ ψ : Name → Nat, DenoteSpine m.acval env ψ (nP + nF) idxArgs (Es ψ)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedTy V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  belowE : ∀ ψ : Name → Nat, ∀ E ∈ Es ψ, Term.bvarsBelow (nP + nF) E
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) →
    ds ψ₁ = ds ψ₂ ∧ Es ψ₁ = Es ψ₂
  srcLen : srcs.length = nF
  srcBnd : ∀ s ∈ srcs, ∀ l, s = some l → l < nIdx
  srcIdx : ∀ j l, srcs[j]? = some (some l) → ∀ ψ : Name → Nat,
    (Es ψ)[l]? = some (Term.bvar (nF - 1 - j))
  srcProp : large = true → ∀ ψ : Name → Nat, resSort.eval ψ = 0 → ∀ ρ : Nat → V,
    Sat V (((ds ψ).take nP)).reverse ρ →
    FieldsBoundSrc ρ (((ds ψ).drop nP)) srcs

/-- The constructor type's reading is graded (`okTy` without its `IsTy`). -/
theorem CtorDataI.okTyV {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List Term} {Es : (Name → Nat) → List Term}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ))) :=
  (h.okTy ψ ρ).1

/-- The data crosses a cons whose head is neither the former nor
mentioned. -/
theorem CtorDataI.cross {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List Term} {Es : (Name → Nat) → List Term}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m₂ T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ
    unfold ctorBodyAVI
    rw [hac, acvalWith_ne hT]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hac, hbody]
    exact denote_cons_mono hfresh ψ 0 hcb (h.read ψ)
  · rw [hac]
    exact DenoteSpine.cons_mono hfresh hcbI (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ


/-- The constructor's data, from its stage run at the environment
holding the former. -/
theorem sumCtorData_of (hμ : μ.isVerified = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {bs : List Expr}
    {sorts : List Level} {sT : Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT)) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List Term)
      (Es : (Name → Nat) → List Term) (srcs : List (Option Nat)),
      (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        idxArgs = xrest.getAppArgs.drop nP) ∧
      CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  obtain ⟨⟨heq, hccv⟩, hresid, fvsP, crest, tfvs, trest, xFvs, idxArgs, hopC, -, -, hopX, hlenI,
    -, hres, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, hlbt, hitf, stype, u, htp', -, hst, hens⟩ :=
    ConLeche.checkConstantVal_inv hccv
  rw [← heq] at hlbt hitf htp' hst
  have htf' := hitf
  have hbt' := hlbt
  have hw : Expr.WScoped 0 cvCa.type := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded cvCa.type := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : cvCa.type.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP cvCa.type 0 hopC
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨F', tb, vb, hib, hensb, -⟩ :=
    piBits_of_infer (CheckMode.vc hμ) (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ idxArgs) hib
  obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : ConLeche.inferTypeCore μ env F' (nP + nF)
      (.const T (lps.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ idxArgs) htfT
    (by rw [List.length_append, hlenP, hlenI]; exact hstripT) hib
  -- the per-assignment reading
  have hper : ∀ ψ : Name → Nat, ∃ (ds : List Term) (Es : List Term),
      denote mp.base2.acval env ψ 0 cvCa.type
        = some (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es)) ∧
      ds.length = nP + nF ∧ Es.length = nIdx ∧
      DenoteSpine mp.base2.acval env ψ (nP + nF) idxArgs Es ∧
      (∀ ρ : Nat → V, WellDenotedTy V ρ (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es))) ∧
      DomsBelow 0 ds ∧ (∀ E ∈ Es, Term.bvarsBelow (nP + nF) E) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenoted V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    have hokT'' : ∀ ρ : Nat → V, WellDenotedTy V ρ Ta := fun ρ =>
      ⟨hokT' ρ, IsTy_of_mem_univ ((hc.sort (CtxOk.nil hnil) hw hbt' hL hst
        (ConLeche.ensureSortCore_inv hens) hTa) ρ (Sat_nil V ρ)).2⟩
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hopAll htf' hbt' hTa hokT'
    -- the residual's spine, inverted
    obtain ⟨fa, vs, hfa, hsp, hR⟩ := denote_mkAppN_inv hop'.body
    have hfa' : fa = mp.base2.acval T ψ := by
      have hconst := denote_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := nP + nF) hfT
        (show (lps.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (lps.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (lps.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (lps.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hconst, hsubst] at hfa
      exact (Option.some.inj hfa).symm
    subst hfa'
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteSpine.split _ hsp
    have hvs₁ : vs₁ = paramBvars nP nF := by
      have := DenoteSpine.unique hsp₁
        (denoteSpine_fvars (acval := mp.base2.acval) (env := env) (φ := ψ) (nP + nF)
          fvsP 0 hidx)
      rw [this, hlenP]
      unfold paramBvars
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    subst hvs₁
    have hR' : R = ctorBodyAVI mp.base2 T nP nF ψ vs₂ := hR
    subst hR'
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    have hbelowAll := stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)
    refine ⟨ds, vs₂, hTa, hlen, by rw [← hsp₂.length, hlenI], hsp₂,
      hokT'', hbelowAll.1, ?_⟩
    intro E hE
    have hb := hbelowAll.2
    rw [Nat.zero_add] at hb
    unfold ctorBodyAVI at hb
    exact (bvarsBelow_mkAppN_inv hb).2 _
      (List.mem_append_right _ hE)
  -- the sources
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hspec : ∀ ψ, _ := fun ψ => Classical.choose_spec (Classical.choose_spec (hper ψ))
  refine ⟨idxArgs, fun ψ => Classical.choose (hper ψ),
    fun ψ => Classical.choose (Classical.choose_spec (hper ψ)),
    srcsOf xFvs idxArgs sorts nF, hres, ⟨fvsP, crest, xFvs, _, hopC, hopX, ?_⟩, ?_⟩
  · rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' hlenP]
  refine ⟨hresid, fun ψ => (hspec ψ).1, fun ψ => (hspec ψ).2.1, fun ψ => (hspec ψ).2.2.1,
    hlenI, fun ψ => (hspec ψ).2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.2, ?_,
    srcsOf_length _ _ _ _, ?_, ?_, ?_⟩
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have h2 := (hspec ψ₂).1
    have h1 : denote mp.base2.acval env ψ₂ 0 cvCa.type
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAVI mp.base2 T nP nF ψ₁ (Classical.choose (Classical.choose_spec (hper ψ₁))))) := by
      rw [← denote_params_ext mp.base2 hφ 0 cvCa.type htp']
      exact (hspec ψ₁).1
    obtain ⟨hds, hbody⟩ := mkPisAV_inj
      (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1]) (Option.some.inj (h1.symm.trans h2))
    refine ⟨hds, ?_⟩
    obtain ⟨-, hargs⟩ := Term.mkAppN_inj (f := mp.base2.acval T ψ₁) (g := mp.base2.acval T ψ₂) hbody
      (by rw [List.length_append, List.length_append, (hspec ψ₁).2.2.1, (hspec ψ₂).2.2.1])
    exact List.append_cancel_left hargs
  · -- the sources are index positions
    intro s hs l hsl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hj
    have hj' := Option.some.inj hj
    rw [hsl] at hj'
    split at hj'
    · exact nomatch hj'
    · have := firstIdx_some hj'
      rw [← hlenI]
      exact (List.getElem?_eq_some_iff.mp this).1
  · -- an index source reads to the field variable
    intro j l hjl ψ
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hjl).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hjl
    have hjl' := Option.some.inj hjl
    split at hjl'
    · exact nomatch hjl'
    · have hidxl := firstIdx_some hjl'
      obtain ⟨fv, hfv⟩ : ∃ fv, xFvs[j]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := hidxX j fv hfv
      rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some] at hidxl
      obtain ⟨v, hv, hread⟩ := denoteSpine_getElem?' ((hspec ψ).2.2.2.1) _ _ hidxl
      rw [denote_fvar, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega] at hread
      rw [hv, Option.some.inj hread]
  · -- the unsourced fields are propositional at a large-eliminating
    -- family instantiated at `Prop`
    intro hl ψ hw0 ρ hρ
    have hc := claimsAt_of hμ mp ψ F
    have hC : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs))
        (((Classical.choose (hper ψ))).reverse)
        (ctorBodyAVI mp.base2 T nP nF ψ (Classical.choose (Classical.choose_spec (hper ψ)))) :=
      opened_of_peel hopAll htf' hbt' (hspec ψ).1 (hspec ψ).2.1 (fun ρ => ((hspec ψ).2.2.2.2.1 ρ).1)
    have hlenDs : (Classical.choose (hper ψ)).length = nP + nF := (hspec ψ).2.1
    have hΓlen : ((((Classical.choose (hper ψ))).reverse)).length = nP + nF := by
      rw [List.length_reverse, hlenDs]
    have hρ' : Sat V (((((Classical.choose (hper ψ))).reverse)).drop
        (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := Classical.choose (hper ψ)) (nP := nP) (nF := nF) hlenDs
    rw [← hFsEq]
    have h := fieldsBoundSrc_of_frame (Γ := ((Classical.choose (hper ψ))).reverse)
      (srcs := srcsOf xFvs idxArgs sorts nF) rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
    · rw [List.drop_zero] at h; exact h
    intro j hj hsj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
    have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
    have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hC.doms (nP + j) fv hfvA
    have hmem := (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    -- the source is `none`: the sort evaluates to `0`
    have hu0 : u.eval ψ = 0 := by
      cases hp : isProp with
      | false =>
        have hle := Level.leq_sound (hleq hp) ψ
        omega
      | true =>
        rw [srcsOf_getElem? _ _ _ _ _ hj] at hsj
        have hsj' := Option.some.inj hsj
        have hsu : sorts.getD j .zero = u := by
          rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
        rw [hsu] at hsj'
        split at hsj'
        · next hequ => exact Level.isEquiv_sound (beq_iff_eq.mp hequ) ψ
        · rcases hz hp hl with h | h
          · exact Level.isEquiv_sound (beq_iff_eq.mp h) ψ
          · exfalso
            have hfvx : xFvs.getD j default = fv := by
              rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some]
            rw [hfvx] at hsj'
            obtain ⟨i, hi'⟩ := firstIdx_of_mem (List.contains_iff_mem.mp h)
            rw [hi'] at hsj'
            exact nomatch hsj'
    rw [hu0] at hmem
    exact hmem

/-! ## The constructor's frames -/

/-- **The constructor's frames**: the parameter frames identified, and
under the parameters the field chain graded (at the block's level),
bounded when the family is not `Prop`, and the index
expressions graded and fitting the former's index telescope at every
fitting field spine. -/
theorem ctorFramesGen (hμ : μ.isVerified = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List Term}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    {idxArgs : List Expr} {ds : (Name → Nat) → List Term}
    {Es : (Name → Nat) → List Term} {srcs : List (Option Nat)}
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsAV (ppsAll ψ) B) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
          (∀ E ∈ Es ψ, WellDenoted V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP)) (idxValsAt ρ (Es ψ) bs))) ∧
    -- the fields' sorts, as the stage read them (task #210 Part A: the
    -- projection table's guard levels at a structure-like block): one
    -- per field, each bounded by the result sort at a non-`Prop` family,
    -- and the field's reading along a fitting prefix a member of its
    -- sort's universe
    (sorts.length = nF ∧
      (∀ j, j < nF → isProp = false → Level.leq (sorts.getD j .zero) resSort = some true) ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take nP)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
  obtain ⟨⟨heq, hccv⟩, -, fvsP, crest, tfvs, trest, xFvs, idxArgs', hopC, hopT, hdoms, hopX,
    -, -, -, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, hlbt, hitf, -, -, -, -⟩ := ConLeche.checkConstantVal_inv hccv
  rw [← heq] at hlbt hitf
  have htf' := hitf
  have hbt' := hlbt
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hpins := ConLeche.checkStructDomsAt_inv hdoms
  have hlenX : xFvs.length = nF := openPisAtFvars_length _ hopX
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
          (∀ E ∈ Es ψ, WellDenoted V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP)) (idxValsAt ρ (Es ψ) bs))) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    -- the former, opened at the parameters
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hopT hTf hTb (hFD.read ψ) (hFD.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take nP (ppsAll ψ) (Term.sort (resSort.eval ψ))
      (by rw [hFD.len ψ]; omega)
    obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
    subst hΓt
    have hC : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs'))
        ((ds ψ)).reverse (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
      opened_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (fun ρ => (hCD.okTy ψ ρ).1)
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hlenF : ((((ds ψ).drop nP))).length = nF := by simp [hlenDs]
    have hiff : ∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ := by
      intro ρ
      have := (hpf nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    have hrow : ∀ j, j < nF → ∃ u, sorts[j]? = some u ∧
        (isProp = false → Level.leq u resSort = some true) ∧
        ∀ ρ : Nat → V,
          Sat V ((((ds ψ)).reverse).drop (nP + nF - (nP + j))) ρ →
          interp V ρ ((((ds ψ)).reverse).getD
            (nP + nF - 1 - (nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, -⟩ := hfields j hj
      refine ⟨u, hu, hleq, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
      have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
      have hread := hC.doms (nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hsortsPart : ∀ ρ : Nat → V, Sat V (((ds ψ).take nP)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) := by
      intro ρ hρ j hj as hsp
      obtain ⟨u, hu, -, hmem⟩ := hrow j hj
      have hsat := sat_of_spineFit (Δ₀ := (((ds ψ).take nP)).reverse) hρ hsp
      have hdropj : ((((ds ψ)).reverse)).drop (nP + nF - (nP + j))
          = ((((ds ψ).drop nP)).take j).reverse ++
            (((ds ψ).take nP)).reverse := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - (nP + j) = nF - j from by omega,
          List.drop_append_of_le_length (by rw [List.length_reverse, hlenF]; exact Nat.sub_le _ _),
          List.drop_reverse, hlenF, show nF - (nF - j) = j from by omega]
      have hentj : ((((ds ψ)).reverse)).getD (nP + nF - 1 - (nP + j)) default
          = (((ds ψ).drop nP)).getD j default := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_reverse, hlenF]; omega),
          List.getElem?_reverse (by rw [hlenF]; omega), hlenF,
          show nF - 1 - (nF - 1 - j) = j from by omega, ← List.getD_eq_getElem?_getD]
      have := hmem (consList as ρ) (by rw [hdropj]; exact hsat)
      rw [hentj] at this
      rw [List.getD_eq_getElem?_getD (l := sorts), hu]
      exact this
    refine ⟨hiff, fun ρ hρ => ?_, hsortsPart⟩
    have hΓlen : (((ds ψ)).reverse).length = nP + nF := by
      simp [hlenDs]
    have hρ' : Sat V ((((ds ψ)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    refine ⟨?_, ?_, ?_⟩
    · rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      by_cases hnp : isProp = true
      · exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · intro hnp
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      have hle := Level.leq_sound (hleq hnp) ψ
      exact univ_mono hle _ (hmem ρ hρ)
    · -- the index expressions at a fitting field spine
      intro bs hsp
      have hlenB : bs.length = nF := by rw [hsp.length_eq, hlenF]
      have hsat : Sat V (((ds ψ)).reverse) (consList bs ρ) := by
        have := sat_of_spineFit (Δ₀ := (((ds ψ).take nP)).reverse) hρ hsp
        rwa [← reverse_map_take_drop] at this
      have hokR := hC.okR _ hsat
      have hRty := IsTy_body_of_sat (hCD.okTy ψ) hsat
      unfold ctorBodyAVI at hokR hRty
      obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokR
      refine ⟨fun E hE => hargs E (List.mem_append_right _ hE), ?_⟩
      -- the spine fits the former's leaf
      obtain ⟨B, hB⟩ := hleafT ψ
      have hfit := spineFit_of_wellDenoted_lams
        (b := B) (args := paramBvars nP nF ++ Es ψ)
        (ds := ppsAll ψ) (σ := consList bs ρ) (ρ := consList bs ρ) (f := mp.base2.acval T ψ)
        (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]) hokR hRty.ne_pt (by rw [hB])
      rw [List.take_of_length_le (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]),
        ← List.take_append_drop nP (ppsAll ψ), List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = nP := by
        rw [h1.length_eq, List.length_take, hFD.len ψ]; omega
      have hps : (paramBvars nP nF).map (interp V (consList bs ρ))
          = (List.range nP).reverse.map ρ := by
        rw [paramBvars_eq_paramBvarsAt]
        exact map_paramBvarsAt_interp (fun j => by rw [← hlenB]; exact consList_apply_add bs ρ j)
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvars])
      rw [hps] at h2
      show SpineFit ρ (((ppsAll ψ).drop nP)) ((Es ψ).map (interp V (consList bs ρ)))
      refine spineFit_congr_below (DomsBelow.drop nP (hFD.below ψ)) ?_ h2
      intro i hi
      rw [Nat.zero_add] at hi
      exact consList_params_apply ρ _ hi
  refine ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2.1, hlenS, ?_, fun ψ => (hframes ψ).2.2⟩
  intro j hj hnp
  obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hfields j hj
  rw [List.getD_eq_getElem?_getD, hu]
  exact hleq hnp


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  RecRule)


variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The constructors' data, positionally -/

/-- The constructor data list from position-indexed data functions. -/
@[expose] def ctorDataList (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatum
  | [], _ => []
  | c :: cs, j => (c.1.name, c.2, dsF j ψ, esF j ψ) :: ctorDataList dsF esF ψ cs (j + 1)

theorem ctorDataList_getElem? (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (ctorDataList dsF esF ψ cs j)[i]? = cs[i]?.map fun c => (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ)
  | [], _, _ => by simp [ctorDataList]
  | c :: cs, j, 0 => by simp [ctorDataList]
  | c :: cs, j, i + 1 => by
    simp only [ctorDataList, List.getElem?_cons_succ]
    rw [ctorDataList_getElem? dsF esF ψ cs (j + 1) i, show j + 1 + i = j + (i + 1) from by omega]

theorem ctorDataList_params {dsF : Nat → (Name → Nat) → List Term}
    {esF : Nat → (Name → Nat) → List Term} {ψ₁ ψ₂ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {j : Nat},
      (∀ i, i < cs.length → dsF (j + i) ψ₁ = dsF (j + i) ψ₂ ∧ esF (j + i) ψ₁ = esF (j + i) ψ₂) →
      ctorDataList dsF esF ψ₁ cs j = ctorDataList dsF esF ψ₂ cs j
  | [], _, _ => rfl
  | _ :: cs, j, h => by
    simp only [ctorDataList]
    obtain ⟨h0d, h0e⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h0d h0e
    rw [h0d, h0e]
    congr 1
    exact ctorDataList_params fun i hi => by
      rw [show j + 1 + i = j + (i + 1) from by omega]
      exact h (i + 1) (by simpa using hi)

/-- What the readings need of every constructor at its position:
stored, at the block's level parameters, and its data. -/
@[expose] def CtorFactsAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (srcsF : Nat → List (Option Nat))
    (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j) (srcsF j)


/-! ## The sum former's walks -/


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)


/-- **The sum former leaf's hereditary premise**, from the former's
data and the chains' grading at the parameter frame. -/
theorem formerWalksS {m : EnvModel V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List Term}
    (hFD : FormerData m cvT nP resSort pps)
    {Fss : (Name → Nat) → List (List Term)}
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkS (resSort.eval ψ) ρ (Fss ψ) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ)).reverse).length = nP := by
    simp [hFD.len ψ]
  have hent : ∀ i, i < nP → ∃ p, (pps ψ)[i]? = some p ∧
      p = (((pps ψ)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ)).reverse).drop (nP - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  have hw := hereditaryWalk (V := V)
    (Q := fun ρ ds => ParamsOkS (resSort.eval ψ) ρ (Fss ψ) ds)
    hlenΓ (hFD.len ψ) hent okΓ
    (fun ρ hρ => hFssOk ψ ρ hρ)
    (fun ρ d ds hd hok hrec => ⟨hok.1, hok.2, hrec⟩)
    0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
  simpa using hw


/-!
## A sum constructor's cons

`stageCtorGen`: the P step at constructor `j`'s cons — onto the
environment holding the former and the earlier constructors — with
the leaf `sumMkAV (resSort.eval ψ) j (ds ψ) Fs_j (uChains Fss)`.
The constructor's run was taken at the former's environment
(`checkSumCtor`) and its data crossed to the cons's environment
(`CtorDataI.cross`); the family application at the bottom — the
family at the parameters and the constructor's index expressions —
folds the former's leaf along the parameters and the index values,
landing in the fibre at the constructor's own index tuple, where the
point-terminated tuple lives by the index equation
(`restricted_member_intro`).
-/


/-! ## Kit -/

omit [SetTheory V] in
/-- The frame's index tuple at a consed index spine. -/
theorem frameIdx_consList {nIdx : Nat} {is : List V} (hlen : is.length = nIdx) (X : Nat → V) :
    frameIdx nIdx (consList is X) = is := by
  apply List.ext_getElem
  · simp [frameIdx, hlen]
  · intro l h1 h2
    have hl : l < nIdx := by simpa [frameIdx] using h1
    simp only [frameIdx, List.getElem_map, List.getElem_range]
    rw [consList_apply_lt _ _ _ (by omega), hlen,
      show nIdx - 1 - (nIdx - 1 - l) = l from by omega, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- **The constructor leaf's hereditary premise**: `MkPreS` along the
parameters. -/
theorem ctorWalksGen {m : EnvModel V env} {T : Name} {lps : List Name} {cvT cvC : ConstantVal}
    {nP nF nIdx j : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List Term} {Es : (Name → Nat) → List Term}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List Term)}
    (_hFD : FormerData m cvT (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
        interp V (consList bs ρ) (ctorBodyAVI m T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ))
    (_hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP)) (idxValsAt ρ (Es ψ) bs))
    (ψ : Name → Nat) (ρ : Nat → V) :
    MkPreS (resSort.eval ψ) j ρ (((ds ψ).drop nP)) (uChains (Fss ψ))
        (ctorBodyAVI m T nP nF ψ (Es ψ)) ((ds ψ).take nP) := by
  have hlenDs := hCD.len ψ
  have hlenP : ((ds ψ).take nP).length = nP := List.length_take_of_le (by omega)
  let Fs : List Term := ((ds ψ).drop nP)
  have hlenFs : Fs.length = nF := by simp [Fs, hlenDs]
  have hst := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ))
  rw [hlenDs] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => (hCD.okTy ψ ρ).1)
  simp only [List.append_nil] at okΓ
  have hΓplen : ((((ds ψ).take nP)).reverse).length = nP := by
    rw [List.length_reverse, hlenP]
  have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
      Sat V (((((ds ψ).take nP)).reverse).drop (nP - i)) ρ →
      WellDenotedTy V ρ (((((ds ψ).take nP)).reverse).getD (nP - 1 - i) default) := by
    intro i hi ρ hρ
    rw [← getD_reverse_take hlenDs hi]
    refine okΓ i (by omega) ρ ?_
    rw [drop_fields_eq hlenDs i (by omega)]
    exact hρ
  have hentP : ∀ i, i < nP → ∃ q, ((ds ψ).take nP)[i]? = some q ∧
      q = ((((ds ψ).take nP)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < ((ds ψ).take nP).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
  have hchain : (rChains nIdx nIdx (Fss ψ) (Ess ψ))[j]? = some (rChain nIdx nIdx Fs (Es ψ)) := by
    rw [rChains_getElem?, hFsj ψ, hEsj ψ]
  have hw := hereditaryWalk (V := V)
    (Q := fun ρ pds => MkPreS (resSort.eval ψ) j ρ Fs (uChains (Fss ψ))
      (ctorBodyAVI m T nP nF ψ (Es ψ)) pds)
    hΓplen hlenP hentP okΓp
    (fun ρ hρ => ?_)
    (fun ρ d ds' _ hok hrec => ⟨hok.1, hok.2, hrec⟩)
    0 (Nat.zero_le _) ρ (by
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
      exact Sat_nil V ρ)
  · rw [List.drop_zero] at hw; exact hw
  -- the base: at the parameter frame
  have hρt : Sat V (((ppsAll ψ).take nP)).reverse ρ := (hiff ψ ρ).mpr hρ
  have hokFss := hFssOkP ψ ρ hρ
  refine ⟨SumFieldsOkB_uChains hokFss, by rw [uChains_getElem?, hFsj ψ]; rfl, fun bs hsp => ?_⟩
  have hlenI : (idxValsAt ρ (Es ψ) bs).length = nIdx := by
    simp [idxValsAt, hCD.lenE ψ]
  refine ⟨sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
    (rChains nIdx nIdx (Fss ψ) (Ess ψ)), ?_, ?_⟩
  · exact hfold ψ ρ hρt bs hsp
  · -- the point-terminated tuple lives in the fibre at the index tuple
    rw [sumFibre_of_getElem? hchain]
    have hshift : shiftE nIdx 0 (consList (idxValsAt ρ (Es ψ) bs) ρ) = ρ := by
      rw [← hlenI]; exact shiftE_consList _ _
    refine restricted_member_intro (Fs := liftFields nIdx 0 Fs) ?_ ?_
    · rw [spineFit_liftFields, hshift]
      exact hsp
    · rw [EqAll_idxEqsAt (hCD.lenE ψ) hsp.length_eq, hshift, frameIdx_consList hlenI]

/-- **The P step at a sum-shaped constructor's cons**, for a given fibre fold. -/
theorem stageCtorGen {T : Name}
    {F : Nat} {lps : List Name} {nP nF nIdx j : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    -- **the other stored families' η constructors are not this one**
    -- (`capsOk_cons_native`'s `hother`): at ONE family it is closure
    -- (`etaCtor_ne_of_closed`); at a BLOCK a still-pending member's η
    -- constructor is one of ITS OWN constructors, which the block's
    -- distinct names refute
    (hE : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      env.find? T' = some (.indInfo cvT' caps') → T' ≠ T →
      ConLeche.reservedBasisNames.contains T' = false → caps'.eta = true →
      ConLeche.EtaFamilyStored ⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩ T' caps' →
      caps'.etaCtor ≠ cvCa.name)
    (mp : EnvModelM V μ env)
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env₁ T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    -- the constructor is fresh at the cons's environment and its type
    -- resolves there
    (hfresh : env.find? cvCa.name = none)
    (htr : cvCa.type.constsResolve env = true)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hlpsC : cvCa.levelParams = lps)
    {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List Term} {Es : (Name → Nat) → List Term}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List Term)}
    -- the block's own capability laws at the cons (task #210 Parts A
    -- and B), at any carrier agreeing with this one off the
    -- constructor's name and storing the constructor's leaf there
    (hTlaws : ∀ m₂ : EnvModel V ⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩,
      (∀ n, n ≠ cvCa.name → m₂.acval n = mp.base2.acval n) →
      (∀ ψ, m₂.acval cvCa.name ψ
        = sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP)) (uChains (Fss ψ))) →
      CapsLawsAt m₂ T cvTa caps)
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
        interp V (consList bs ρ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ lps, ψ₁ q = ψ₂ q) → Fss ψ₁ = Fss ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ Fss ψ, DomsBelow nP Fs)
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((ds ψ).take nP)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ))
    (hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP)) (idxValsAt ρ (Es ψ) bs)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvCa.name
        (fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP))
          (uChains (Fss ψ))) := by
  obtain ⟨⟨hty, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, hnres, -, hlbt, hitf, -, -, htp, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hccv
  have htf' := hitf
  have hbt' := hlbt
  have hCname : cvCa.name = cvC.name := by rw [hty]
  have hcb : ConstsBound env cvCa.type := constsBound_of_constsResolve _ htr
  have hTC : T ≠ cvCa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF ?_ ?_ (Expr.constsResolve_mono htr) ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · show cvCa.type.hasFvar = false; rw [hty]; exact htf'
    · show cvCa.type.allLevelParamsDefined cvCa.levelParams = true; rw [hty]; exact htp
    · show cvCa.type.looseBVarsBounded 0 = true; rw [hty]; exact hbt'
  let Fs : (Name → Nat) → List Term := fun ψ => ((ds ψ).drop nP)
  let A : (Name → Nat) → Term :=
    fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (Fs ψ) (uChains (Fss ψ))
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ) := fun ψ =>
    sumMkAV_below (hCD.below ψ)
      (DomsBelow.drop nP (hCD.below ψ))
      (by rw [Nat.zero_add]; exact uChains_below (hFssBelow ψ))
      (by show nP + (((ds ψ).drop nP)).length = (ds ψ).length
          simp [hCD.len ψ])
  have hwalks := ctorWalksGen hFD hCD hfold hFsj hEsj hiff hFssOkP hIdx
  have hreadC : ∀ ψ : Name → Nat,
      denote (acvalWith mp.base2.acval cvCa.name A)
        ⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩ ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := fun ψ =>
    denote_cons_mono (c₀ := .ctorInfo cvCa nP nF) hfresh ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa nP nF).name = false := by
    show ConLeche.reservedBasisNames.contains cvCa.name = false
    rw [hCname]; exact hnres
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvCa nP nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHead.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ _ _ _ h => nomatch h))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    have hφT : ∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q := by rw [hlpsT, ← hlpsC]; exact hφ
    obtain ⟨-, hw⟩ := hFD.params ψ₁ ψ₂ hφT
    show sumMkAV _ j (ds ψ₁) (((ds ψ₁).drop nP)) (uChains (Fss ψ₁))
      = sumMkAV _ j (ds ψ₂) (((ds ψ₂).drop nP)) (uChains (Fss ψ₂))
    rw [hw, (hCD.params ψ₁ ψ₂ hφ).1, hFssParams ψ₁ ψ₂ (by rw [← hlpsC]; exact hφ)]
  · intro ψ ρ
    have := sumMkAV_wellDenoted (V := V) (hwalks ψ ρ)
    rw [List.take_append_drop] at this
    exact this
  · exact fun ψ => ⟨_, hreadC ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hCD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    have := sumMkAV_mem (V := V) (hwalks ψ ρ)
    rw [List.take_append_drop] at this
    exact this
  · -- `caps_ok`: nothing is claimed by the block's family
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvCa nP nF) (A := A)
      (T := T) hfresh
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape hfam
      exact hE T' cvT' caps' hf hne hres hcape hfam
    · intro cvT caps' hf _
      have hfT' : (⟨.ctorInfo cvCa nP nF :: env.consts, env.tables⟩ : Env).find? T
          = some (.indInfo cvTa caps) := by
        rw [ConLeche.Env.find?_cons, ite_eq_right (fun h => hTC h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      refine hTlaws m₂ (fun n hn => ?_) (fun ψ => ?_)
      · rw [hac]
        exact acvalWith_ne hn
      · rw [hac]
        exact congrFun acvalWith_self ψ


open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
 )


/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
@[expose] def fssOf (nP : Nat) (cds : List CtorDatum) : List (List Term) :=
  cds.map fun cd => (cd.2.2.1.drop nP)

/-- The index readings of the constructor data. -/
@[expose] def essOf (cds : List CtorDatum) : List (List Term) :=
  cds.map fun cd => cd.2.2.2

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP) := by
  simp [fssOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]


variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Distinct names -/

/-- Distinct names, positionally. -/
theorem names_ne_of_nodup {ctorsA : List (ConstantVal × Nat)}
    (hnd : (ctorsA.map (·.1.name)).Nodup) {i j : Nat} {cAi cAj : ConstantVal × Nat}
    (hi : ctorsA[i]? = some cAi) (hj : ctorsA[j]? = some cAj) (hne : i ≠ j) :
    cAi.1.name ≠ cAj.1.name := by
  have hil : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp := List.pairwise_iff_getElem.mp hnd
  have hi' : ctorsA[i] = cAi := by
    have := List.getElem?_eq_getElem hil; rw [hi] at this; exact (Option.some.inj this).symm
  have hj' : ctorsA[j] = cAj := by
    have := List.getElem?_eq_getElem hjl; rw [hj] at this; exact (Option.some.inj this).symm
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := hp i j (by simpa using hil) (by simpa using hjl) hlt
    simp only [List.getElem_map, hi', hj'] at this
    exact this
  · have := hp j i (by simpa using hjl) (by simpa using hil) hgt
    simp only [List.getElem_map, hi', hj'] at this
    exact fun h => this h.symm

/-! ## The constructors' loop -/

/-- The facts about the pending constructors at an environment. -/
@[expose] def PendingAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, k ≤ i → ctorsA[i]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF i) (dsF i) (esF i) (srcsF i)

/-- The facts about the consed constructors at an environment. -/
@[expose] def ConsedAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List Term)
    (esF : Nat → (Name → Nat) → List Term) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, i < k → ctorsA[i]? = some cA →
    CtorFactsAt m T lps nP nIdx resSort isProp large idxF dsF esF srcsF i cA ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV (resSort.eval ψ) i (dsF i ψ) (((dsF i ψ).drop nP))
          (uChains (fssOf nP (ctorDataList dsF esF ψ ctorsA 0)))

end ConLeche.Model
