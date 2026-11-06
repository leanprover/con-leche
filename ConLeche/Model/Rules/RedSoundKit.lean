module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.Closed
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Denote.StrLit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.Inst

public section

/-!
# The reduction kit (task #305)

The semantic facts the reduction rules' soundness needs.  Nothing in
this file mentions a run.

Sections, in the order the rules consume them:

* the level crossing and the assignment-independent literal slots
  (`Model/Reading/Levels.lean`'s `acval_*`/`denotePInstLevels`,
  imported);
* the two `Nat` constructor readings and the literal expansions'
  blindness;
* the δ identity (`denote_unfoldDefinition`);
* **the shared telescope kit** — `frame_spine`,
  `mkAppN_of_fitA`, the `PiChain` guard with `piChain_of_stripPis`
  and `peelPis_of_piChain`, and the stored entry's telescope.  This
  is the LOWEST kit of the four, so a fact more than one rules file
  needs lives here and nowhere else.  `DenoteSpine`'s own list
  algebra, `denote_mkAppN(_inv)` and the tower entry's two
  readings are `Verify/Denote/Lemmas.lean`'s, imported.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {m : EnvModel V env}

/-! ## The level crossing — `Model/Reading/Levels.lean`, imported

`acval_isEmpty`, `acval_oneParam`, `acval_scalar`, `acval_one`,
`acval_natPair` and `denotePInstLevels`: that file is impl-free, so
the kit imports it and there is ONE copy. -/

/-! ## ζ: the reduct of a `let`

Shared by `Red.zeta_sound` and `Infer.letE_sound`: a framed `let`'s
reduct is framed, has no new leaf, and reads as the body's reading
instantiated at the value's (`denote_beta`, at the value where β
has the argument).  The type is not involved. -/

/-- The ζ-reduct's frame, leaves and reading. -/
theorem zeta_syntax {d : Nat} {ty v body : Expr} {va ba : Term}
    (hf : Frame d (.letE ty v body))
    (hva : denote m.acval env φ d v = some va)
    (hba : denote m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some ba) :
    Frame d (body.instantiate1 v) ∧
      LeavesSub (body.instantiate1 v) (.letE ty v body) ∧
      denote m.acval env φ d (body.instantiate1 v) = some (ba.inst va) := by
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hsub : LeavesSub (body.instantiate1 v) (.letE ty v body) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  refine ⟨⟨ConLeche.Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2,
      ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2,
      fun l hl => hLb l (hsub l hl)⟩, hsub, ?_⟩
  rw [denote_beta m.acval_closed (acval_inst_self m)
    (ty := ty) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0, hba]
  rfl

/-- The value of a framed `let` is framed, with no new leaf. -/
theorem letE_val_frame {d : Nat} {ty v body : Expr}
    (hf : Frame d (.letE ty v body)) :
    Frame d v ∧ LeavesSub v (.letE ty v body) := by
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hsub : LeavesSub v (.letE ty v body) := fun l hl => by
    simp [Expr.fvarLeaves, hl]
  exact ⟨⟨hws.2.1, hb.1.2, fun l hl => hLb l (hsub l hl)⟩, hsub⟩

/-! ## The two `Nat` constructor readings and the literal expansions -/

theorem denoteNatZeroConst {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denote acval env φ d (.const ConLeche.natZeroName [])
      = some (acval ConLeche.natZeroName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? ConLeche.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h2
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [ConLeche.natZeroOk] at h2
    rw [denote_const hf (by simp [hlp]), hlp]

theorem denoteNatSuccConst {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denote acval env φ d (.const ConLeche.natSuccName [])
      = some (acval ConLeche.natSuccName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? ConLeche.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h3
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [ConLeche.natSuccOk] at h3
    rw [denote_const hf (by simp [hlp]), hlp]

/-- `denote` is blind to the `Nat`-literal constructor expansion. -/
theorem denote_natLitToConstructor
    {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.natLitSupported env = true) (d n : Nat) :
    denote acval env φ d (ConLeche.natLitToConstructor n)
      = denote acval env φ d (.lit (.natVal n)) := by
  match n with
  | 0 =>
    rw [ConLeche.natLitToConstructor, denoteNatZeroConst hg,
      denote_natLit hg]
    rfl
  | k + 1 =>
    rw [ConLeche.natLitToConstructor, denote_app, denoteNatSuccConst hg,
      denote_natLit hg, denote_natLit hg]
    rfl

theorem denoteConstNolevels
    {acval : Name → (Name → Nat) → Term} {c : Name}
    {ci : ConLeche.ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denote acval env φ d (.const c [])
      = some (acval c (Level.substFn φ [] [])) := by
  rw [denote_const hf (by simp [hlp]), hlp]

theorem denoteNilTerm {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denote acval env φ d
        (.app (.const ConLeche.listNilName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listNilName
          (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciN, p, hfN, hlpN, -⟩ := listNil_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciN.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listNilName := by
    simp [levelParamsAt, hfN]
  rw [denote, denote_const hfN (by simp [hlpN]),
    denoteConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteConsTerm {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    denote acval env φ d
        (.app (.const ConLeche.listConsName [.zero])
          (.const ConLeche.charName []))
      = some (.app (acval ConLeche.listConsName
          (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
            [.zero]))
        (acval ConLeche.charName (Level.substFn φ [] []))) := by
  obtain ⟨ciC', p, hfC', hlpC', -⟩ := listCons_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpa : ciC'.toConstantVal.levelParams
      = levelParamsAt env ConLeche.listConsName := by
    simp [levelParamsAt, hfC']
  rw [denote, denote_const hfC' (by simp [hlpC']),
    denoteConstNolevels hfC hlpC d, hlpa]
  rfl

theorem denoteStrLitList
    {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denote acval env φ d (ConLeche.strLitList cs)
        = some (charListT
          (.app (acval ConLeche.listNilName
            (Level.substFn φ (levelParamsAt env ConLeche.listNilName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (.app (acval ConLeche.listConsName
            (Level.substFn φ (levelParamsAt env ConLeche.listConsName)
              [.zero]))
            (acval ConLeche.charName (Level.substFn φ [] [])))
          (acval ConLeche.charOfNatName (Level.substFn φ [] []))
          (acval ConLeche.natZeroName (Level.substFn φ [] []))
          (acval ConLeche.natSuccName (Level.substFn φ [] []))
          cs) := by
  have hnat : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciF, hfF, hlpF, -⟩ := charOfNat_shape hg
  intro cs
  induction cs with
  | nil =>
    rw [ConLeche.strLitList, charListT]; exact denoteNilTerm hg d
  | cons c cs ih =>
    rw [ConLeche.strLitList, charListT, denote, denote,
      denoteConsTerm hg d, denote,
      denoteConstNolevels hfF hlpF d, denote_natLit hnat, ih]
    rfl

/-- `denote` is blind to the string-literal constructor expansion. -/
theorem denote_strLitToConstructor
    {acval : Name → (Name → Nat) → Term}
    (hg : ConLeche.strLitSupported env = true) (d : Nat) (s : String) :
    denote acval env φ d (ConLeche.strLitToConstructor s)
      = denote acval env φ d (.lit (.strVal s)) := by
  obtain ⟨ciO, hfO, hlpO, -⟩ := stringOfList_shape hg
  rw [ConLeche.strLitToConstructor_eq, denote,
    denoteConstNolevels hfO hlpO d, denoteStrLitList hg d,
    denote, ite_eq_left hg]
  rfl

/-! ## The application congruence at the reading -/

/-- The frame of a closed atom. -/
theorem frame_atom {d : Nat} {e : Expr} (h : e.fvarLeaves = [])
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true) :
    Frame d e ∧ ∀ (x : Expr), LeavesSub e x :=
  ⟨⟨hw, hb, fun l hl => by rw [h] at hl; exact nomatch hl⟩,
   fun _ l hl => by rw [h] at hl; exact nomatch hl⟩

/-- An application's grading depends on its two components only through
their VALUES, so it transfers along equal-valued graded replacements
(stated once, for either slot). -/
theorem appCongrV {σ : Nat → V} {f a f' a' : Term}
    (heqf : interp V σ f = interp V σ f')
    (heqa : interp V σ a = interp V σ a')
    (hgf' : WellDenoted V σ f') (hga' : WellDenoted V σ a')
    (h : WellDenoted V σ (.app f a)) : WellDenoted V σ (.app f' a') := by
  have h1 := h
  rw [WellDenoted_app] at h1 ⊢
  obtain ⟨-, -, v, A, B, h2, h3, h4⟩ := h1
  exact ⟨hgf', hga', v, A, B, heqf ▸ h2, heqa ▸ h3, h4⟩

/-! ## `projNV`'s grading under equal-valued subjects -/

namespace ProjAV

/-- The subject of a graded projection spine is graded. -/
theorem hoist :
    ∀ {i : Nat} {e : Term} {σ : Nat → V},
      WellDenoted V σ (projNV i e) → WellDenoted V σ e
  | 0, e, σ, h => (cast (WellDenoted_fst V σ e) h).1
  | i + 1, e, σ, h =>
    (cast (WellDenoted_snd V σ e) ((hoist (i := i) (e := .snd e) h))).1

/-- **`projNV`'s truthfulness transfers to an equal-valued graded
subject.** -/
theorem congr :
    ∀ {i : Nat} {e e' : Term} {σ : Nat → V},
      interp V σ e = interp V σ e' → WellDenoted V σ e' →
      WellDenoted V σ (projNV i e) → WellDenoted V σ (projNV i e')
  | 0, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (.fst e')
    have h : WellDenoted V σ (.fst e) := hok
    rw [WellDenoted_fst] at h ⊢
    obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := h
    exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩
  | i + 1, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (projNV i (.snd e'))
    have hok1 : WellDenoted V σ (.snd e) :=
      hoist (i := i) (e := .snd e) hok
    refine congr (i := i) (e := .snd e) (e' := .snd e') ?_ ?_ hok
    · simp only [interp_snd, heq]
    · rw [WellDenoted_snd] at hok1 ⊢
      obtain ⟨-, u, v, A, Bf, hs, hA, hB⟩ := hok1
      exact ⟨hok', u, v, A, Bf, heq ▸ hs, hA, hB⟩

/-- `WellDenoted` form of the congruence. -/
theorem congrV {i : Nat} {e e' : Term} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') (hok' : WellDenoted V σ e')
    (hok : WellDenoted V σ (projNV i e)) : WellDenoted V σ (projNV i e') :=
  congr heq hok' hok

/-- `WellDenoted` of the subject, off the spine's. -/
theorem hoistV {i : Nat} {e : Term} {σ : Nat → V}
    (hok : WellDenoted V σ (projNV i e)) : WellDenoted V σ e :=
  hoist hok

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp_congr {i : Nat} {e e' : Term} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') :
    interp V σ (projNV i e) = interp V σ (projNV i e') := by
  rw [projNV_interp, projNV_interp, heq]

end ProjAV

/-! ## The β step at the currency -/

/-- **The graded β step** at a redex that is not the point
(`WellDenoted_beta`). -/
theorem betaV {A b a : Term} {ρ : Nat → V}
    (h : WellDenoted V ρ (.app (.lam A b) a))
    (hne : interp V ρ (.app (.lam A b) a) ≠ pt) :
    interp V ρ (.app (.lam A b) a) = interp V ρ (b.inst a) ∧
      WellDenoted V ρ (b.inst a) :=
  (WellDenoted_beta V h hne).2

/-! ## The telescope walk's one-slot kit -/

/-- **A `TeleFitPA` fit plus the type's grading grades the applied
spine**, and places it in the residual's reading. -/
theorem mkAppN_of_fitA {ρ : Nat → V} :
    ∀ (vs : List Term) {Ta f rest : Term},
      WellDenoted V ρ Ta → WellDenoted V ρ f →
      (∀ x ∈ vs, WellDenoted V ρ x) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      TeleFitPA V ρ Ta vs rest →
      WellDenoted V ρ (Term.mkAppN f vs) ∧
        interp V ρ (Term.mkAppN f vs) ∈ˢ interp V ρ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f rest _ hf _ hmem hfit
    cases hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f rest hokT hf hoks hmem hfit
    cases hfit with
    | @cons A B _ _ _ hx hfit' =>
      have hpi := cast (WellDenoted_pi V ρ A B) hokT
      have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenoted V (cons y ρ) B :=
        fun y hy => hpi.2.2.1 y hy
      have hokx : WellDenoted V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenoted V ρ (.app f x) :=
        WellDenoted_app_of V hf hokx hmem hx hpi.2.1
      rw [interp_pi] at hmem
      have hmem' : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
        rw [interp_inst0, interp_app]
        exact app_mem_piV hmem hx
      exact ih ((WellDenoted_inst0 _ hokx).mpr (hokB _ hx)) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-- The head of a graded spine is graded. -/
theorem mkAppN_head {ρ : Nat → V} :
    ∀ (as : List Term) {f : Term},
      WellDenoted V ρ (Term.mkAppN f as) → WellDenoted V ρ f
  | [], _, h => h
  | a :: as, f, h => by
    have h' : WellDenoted V ρ (.app f a) := mkAppN_head as h
    exact (cast (WellDenoted_app V ρ f a) h').1

/-- **The ι-slot transfer, one slot**: a graph member of two function
spaces fixes their common domain; a member of a truth-value slot is the
point, which no graph is. -/
theorem slotTransfer {v v' : Nat} {A A' f a : V} {B B' : V → V}
    (hv : v ≠ 0) (hf : f ∈ˢ piR v A B)
    (hslot : f ∈ˢ piR v' A' B') (ha : a ∈ˢ A') : a ∈ˢ A := by
  by_cases hv' : v' = 0
  · subst hv'
    exact absurd (eq_pt_of_mem_piR_zero hslot) (mem_piR_pos hv hf).2.2.2
  · rw [piR_dom_unique hv hv' hf hslot]; exact ha

/-! ## The spine kit — `Verify/Denote/Lemmas.lean`, imported

`DenoteSpine` and its list algebra (`length`, `getD_read`,
`take`, `drop`, `append`, `map_list`, `snoc`, `getD`, `mem`),
`denote_mkAppN(_inv)` and the tower entry's two readings are
that file's, and there is ONE copy of each.
What is still stated here is what mentions the rules tier's own
`Graded`/`Frame` abbreviations. -/

/-! ## The per-valuation splitters (task #342, L9) -/

theorem _root_.ConLeche.Semantics.WellDenoted.app_fn {ρ : Nat → V} {f x : Term}
    (h : WellDenoted V ρ (.app f x)) : WellDenoted V ρ f :=
  (cast (WellDenoted_app V ρ f x) h).1

theorem _root_.ConLeche.Semantics.WellDenoted.app_arg {ρ : Nat → V} {f x : Term}
    (h : WellDenoted V ρ (.app f x)) : WellDenoted V ρ x :=
  (cast (WellDenoted_app V ρ f x) h).2.1

theorem _root_.ConLeche.Semantics.WellDenoted.pi_dom {ρ : Nat → V} {A B : Term}
    (h : WellDenoted V ρ (.pi A B)) : WellDenotedTy V ρ A :=
  ⟨(cast (WellDenoted_pi V ρ A B) h).1, (cast (WellDenoted_pi V ρ A B) h).2.1⟩

theorem _root_.ConLeche.Semantics.WellDenoted.pi_body {ρ : Nat → V} {A B : Term}
    (h : WellDenoted V ρ (.pi A B)) :
    ∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) B := fun x hx =>
  (cast (WellDenoted_pi V ρ A B) h).2.2.1 x hx

/-- A graded Π-type's fibres are types. -/
theorem _root_.ConLeche.Semantics.WellDenoted.pi_fib {ρ : Nat → V}
    {A B : Term} (h : WellDenoted V ρ (.pi A B)) :
    ∀ x, x ∈ˢ interp V ρ A → IsTy (interp V (cons x ρ) B) := fun x hx =>
  (cast (WellDenoted_pi V ρ A B) h).2.2.2 x hx

theorem _root_.ConLeche.Semantics.WellDenoted.lam_dom {ρ : Nat → V} {A b : Term}
    (h : WellDenoted V ρ (.lam A b)) : WellDenotedTy V ρ A :=
  ⟨(cast (WellDenoted_lam V ρ A b) h).1, (cast (WellDenoted_lam V ρ A b) h).2.1⟩

theorem _root_.ConLeche.Semantics.WellDenoted.lam_body {ρ : Nat → V} {A b : Term}
    (h : WellDenoted V ρ (.lam A b)) :
    ∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) b := fun x hx =>
  (cast (WellDenoted_lam V ρ A b) h).2.2.1 x hx

/-- "Not pt" source (1): a graded type is not the point. -/
theorem _root_.ConLeche.Model.WellDenotedTy.ne_pt {ρ : Nat → V} {e : Term}
    (h : WellDenotedTy V ρ e) : interp V ρ e ≠ pt := h.2.ne_pt

/-- Every argument of a graded application spine is graded, and so is
its head, at one valuation. -/
theorem hoist_spineV {ρ : Nat → V} :
    ∀ (asa : List Term) {fa : Term},
      WellDenoted V ρ (Term.mkAppN fa asa) →
      WellDenoted V ρ fa ∧ ∀ x ∈ asa, WellDenoted V ρ x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨happ.app_fn, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact happ.app_arg
    · exact hrest x hx'

/-- The leaves of every argument of a spine are graded where the
spine's are. -/
theorem leavesGr_spine {d : Nat} {a : Expr} {ρ : Nat → V}
    (hL : LeavesGr m φ d a ρ) :
    ∀ x ∈ a.getAppArgs, LeavesGr m φ d x ρ := fun _ hx =>
  hL.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)

/-- The frame conditions of every argument of a spine (`frame_spine`). -/
theorem frame_spine {d : Nat} {Δa : List Term} {a : Expr}
    (hf : Frame d a) (hC : CtxOkS m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Frame d x ∧ CtxOkS m φ d Δa x := fun x hx =>
  ⟨⟨hf.1.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hf.2.1 x hx,
      fun l hl => hf.2.2 l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩,
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)⟩

/-! ## The tower entry's telescope (the entry's two READINGS are
`Verify/Denote/Lemmas.lean`'s) -/

/-- A stored tower entry's body telescope is closed. -/
theorem towerEntry_tele_closed (hwf : ConLeche.EnvWF env) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    (us : List Level) :
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).hasFvar = false ∧
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).looseBVarsBounded 0
      = true := by
  rw [ConLeche.projTele_hasFvar, ConLeche.projTele_looseBVarsBounded,
    Nat.zero_add]
  exact ⟨ConLeche.projEntry_body_hasFvar hwf hfe us,
    ConLeche.projEntry_body_looseBVars hwf hfe us⟩

/-- **The body telescope's reading is depth-free.** -/
theorem towerEntry_tele_at_depth {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : Term}
    (hTa : denote m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) :
    (∀ d : Nat, denote m.acval env φ d
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) ∧
    ∀ k : Nat, Ta.liftN 1 k = Ta := by
  obtain ⟨hnf, hb⟩ := towerEntry_tele_closed m.wf hfe us
  have hcl : ∀ k : Nat, Ta.liftN 1 k = Ta := fun k =>
    denote_liftN_eq_self m.cval_closed hnf hb hTa 1 k
  exact ⟨denote_depth_of_closed m.acval_closed hnf hcl hTa, hcl⟩

/-! ## The ∀-chain guard and the fit's un-instantiation -/

/-- The reading's first `n` heads are `.pi` nodes (`PiChain`). -/
@[expose] def PiChain : Nat → Term → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ B => PiChain n B
    | _ => False

theorem piChain_succ_inv {n : Nat} {e : Term} (h : PiChain (n + 1) e) :
    ∃ A B, e = .pi A B ∧ PiChain n B := by
  match e with
  | .pi A B => exact ⟨A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .letE _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

theorem PiChain.inst : ∀ {n : Nat} {e : Term} (a : Term) (k : Nat),
    PiChain n e → PiChain n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv h
    exact ih a (k + 1) hB

/-- **A syntactic ∀-telescope reads to a ∀-chain**
(`piChain_of_stripPis`). -/
theorem piChain_of_stripPis {acval : Name → (Name → Nat) → Term} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : Term},
      (e.stripPis n).isSome = true →
      denote acval env φ d e = some ea → PiChain n ea := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro d e ea hs hd
    match e, hs with
    | .bvar _, hs => exact nomatch hs
    | .fvar _ _, hs => exact nomatch hs
    | .sort _, hs => exact nomatch hs
    | .const _ _, hs => exact nomatch hs
    | .app _ _, hs => exact nomatch hs
    | .lam _ _, hs => exact nomatch hs
    | .letE _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE ty bd, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denote_forallE_inv hd
      simp only [ConLeche.Expr.stripPis, Option.isSome_map] at hs
      exact ih (ConLeche.Expr.stripPis_instantiate1_isSome n 0 hs) hba

/-- A ∀-chain of a list's length peels along it
(`peelPis_of_piChain`).  Shared: the defeq and ι rules both peel a
stored telescope against a spine. -/
theorem peelPis_of_piChain : ∀ (as : List Term) {T : Term},
    PiChain as.length T →
      ∃ rest, Term.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv h
    exact peelPis_of_piChain as (PiChain.inst a 0 hB)

/-- **The fit un-instantiates, under the ∀-chain guard**
(`teleFit_of_inst`). -/
theorem teleFit_of_inst {aa : Term} :
    ∀ {L : List V} {E : Term} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V ρ (E.inst aa k) L rest →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    obtain rfl : rest = interp V ρ (E.inst aa k) := teleFit_nil_inv h
    rw [interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [Term.inst_pi] at h
    cases h with
    | cons hmem hfit =>
      refine .cons (by rwa [interp_inst] at hmem) ?_
      have hrec := ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit
      rw [shiftE_succ_cons] at hrec
      rw [cons_instE]
      exact hrec

theorem teleFit_of_inst0 {aa : Term} {L : List V} {E : Term}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V ρ (E.inst aa) L rest) :
    TeleFit V (cons (interp V ρ aa) ρ) E L rest := by
  have := teleFit_of_inst hpc h
  rwa [shiftE_zero_zero, instE_zero] at this

/-- **The fit re-instantiates, under the ∀-chain guard** (the converse
of `teleFit_of_inst`). -/
theorem teleFit_inst_of {aa : Term} :
    ∀ {L : List V} {E : Term} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      TeleFit V ρ (E.inst aa k) L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    rw [teleFit_nil_inv h, ← interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [Term.inst_pi]
    cases h with
    | cons hmem hfit =>
      refine .cons (by rw [interp_inst]; exact hmem) ?_
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      exact ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit

/-- `teleFit_inst_of` at the head binder. -/
theorem teleFit_inst0_of {aa : Term} {L : List V} {E : Term}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V (cons (interp V ρ aa) ρ) E L rest) :
    TeleFit V ρ (E.inst aa) L rest := by
  refine teleFit_inst_of (k := 0) hpc ?_
  rwa [shiftE_zero_zero, instE_zero]

/-- **A reading-level fit is a value-level fit**
(`teleFit_of_teleFitPA`). -/
theorem teleFit_of_teleFitPA {ρ : Nat → V} :
    ∀ {T : Term} {as : List Term} {resta : Term},
      PiChain as.length T → TeleFitPA V ρ T as resta →
      TeleFit V ρ T (as.map (interp V ρ)) (interp V ρ resta) := by
  intro T as resta hpc h
  revert hpc
  induction h with
  | nil => intro _; exact .nil
  | @cons A B rest a as hmem hfit ih =>
    intro hpc
    have hpcB : PiChain as.length B := hpc
    exact .cons hmem (teleFit_of_inst0 (by rw [List.length_map]; exact hpcB)
      (ih (PiChain.inst a 0 hpcB)))

/-- A value-level fit's length is a ∀-chain of the telescope. -/
theorem piChain_of_teleFit {ρ : Nat → V} {T : Term} {L : List V} {rest : V}
    (h : TeleFit V ρ T L rest) : PiChain L.length T := by
  induction h with
  | nil => trivial
  | cons _ _ ih => exact ih

/-- **A value-level fit at a spine's readings is a reading-level
fit** (`teleFit_of_teleFitPA`'s converse), under the ∀-chain guard. -/
theorem teleFitPA_of_teleFit {ρ : Nat → V} :
    ∀ (vs : List Term) {T : Term} {rest : V},
      PiChain vs.length T → TeleFit V ρ T (vs.map (interp V ρ)) rest →
      ∃ resta, TeleFitPA V ρ T vs resta
  | [], T, _, _, _ => ⟨T, .nil⟩
  | x :: xs, T, rest, hpc, h => by
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv hpc
    cases h with
    | cons hmem hfit =>
      obtain ⟨resta, hres⟩ := teleFitPA_of_teleFit xs (PiChain.inst x 0 hB)
        (teleFit_inst0_of (by rw [List.length_map]; exact hB) hfit)
      exact ⟨resta, .cons hmem hres⟩

/-- **Two fits of one graded telescope, equal where neither value is the
point, are equal** (`spineFit_eq_of_cond` at a `TeleFit`): each domain
is a type (`WellDenoted`'s Π clause), so `IsTy.eq_of_ne_pt` decides the
point case position by position. -/
theorem teleFit_eq_of_cond :
    ∀ {as bs : List V} {T : Term} {ρ : Nat → V} {r₁ r₂ : V},
      WellDenoted V ρ T → TeleFit V ρ T as r₁ → TeleFit V ρ T bs r₂ →
      as.length = bs.length →
      (∀ p ∈ as.zip bs, p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) → as = bs
  | [], [], _, _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, _, _, hl, _ => by simp at hl
  | a :: as, b :: bs, _, ρ, _, _, hT, ha, hb, hl, h => by
    cases ha with
    | @cons _ A B _ _ _ hma hfa =>
      cases hb with
      | cons hmb hfb =>
        rw [WellDenoted_pi] at hT
        have hab : a = b :=
          hT.2.1.eq_of_ne_pt hma hmb (h (a, b) List.mem_cons_self)
        subst hab
        rw [teleFit_eq_of_cond (hT.2.2.1 a hma) hfa hfb (by simpa using hl)
          fun p hp => h p (List.mem_cons_of_mem _ hp)]

/-! ## The δ identity -/

/-- The instantiated form of `AcvalDefnInst`, by the level crossing. -/
theorem denoteDefnInst {m : EnvModel V env} (hdi : AcvalDefnInst m)
    (φ : Name → Nat) {cv : ConstantVal} {value : Expr} {us : List Level}
    (hmem : ∃ hint : ConLeche.ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) :
    ∃ t, denote m.acval env φ 0 (value.instantiateLevelParams cv.levelParams us) = some t ∧
      LeafReads V (m.acval cv.name (Level.substFn φ cv.levelParams us)) t := by
  rw [denotePInstLevels m φ cv.levelParams us 0 value]
  exact hdi _ cv value hmem

/-- **Two heads that interpret alike, the grading carried, carry both
along a spine.** -/
theorem wd_interp_mkAppN {ρ : Nat → V} :
    ∀ (vs : List Term) {f g : Term},
      (WellDenoted V ρ f → WellDenoted V ρ g) → interp V ρ f = interp V ρ g →
      (WellDenoted V ρ (Term.mkAppN f vs) → WellDenoted V ρ (Term.mkAppN g vs)) ∧
        interp V ρ (Term.mkAppN f vs) = interp V ρ (Term.mkAppN g vs)
  | [], _, _, hw, hi => ⟨hw, hi⟩
  | a :: vs, f, g, hw, hi => by
    refine wd_interp_mkAppN vs (f := .app f a) (g := .app g a) (fun h => ?_) ?_
    · rw [WellDenoted_app] at h ⊢
      obtain ⟨hf, ha, v, A, B, hm, rest⟩ := h
      exact ⟨hw hf, ha, v, A, B, hi ▸ hm, rest⟩
    · rw [interp_app, interp_app, hi]

/-- The δ identity's core: the unfolded head, applied to the subject's
arguments, reads as the subject, or — at a proof's canonical leaf — as a
graded proof that interprets as the subject does. -/
private theorem deltaCore (m : EnvModel V env)
    {d : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea t : Term}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hcl : ∀ k : Nat, t.liftN 1 k = t)
    (hval : denote m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us) = some t)
    (hlr : LeafReads V (m.acval ci.name (Level.substFn φ cv.levelParams us)) t)
    (hea : denote m.acval env φ d e = some ea) :
    ∃ ea', denote m.acval env φ d
        (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs) = some ea' ∧
      ∀ ρ : Nat → V, WellDenoted V ρ ea → WellDenoted V ρ ea' ∧ interp V ρ ea = interp V ρ ea' := by
  obtain rfl : ci.name = n := by
    rw [ConLeche.Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    ConLeche.Expr.mkAppN_getApp e
  rw [← he] at hea
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denote_mkAppN_inv hea
  rw [hfn, denote, hfind] at hfa
  simp only [hcvt] at hfa
  rw [ite_eq_left hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  have hvd : denote m.acval env φ d (value.instantiateLevelParams cv.levelParams us) = some t :=
    denote_depth_of_closed m.acval_closed
      (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hnofv) hcl hval d
  refine ⟨Term.mkAppN t vs, denote_mkAppN hsp hvd, fun ρ hw => ?_⟩
  rcases hlr with rfl | ⟨hprf, ht⟩
  · exact ⟨hw, rfl⟩
  · have hr := wd_interp_mkAppN (ρ := ρ) vs
      (f := m.acval ci.name (Level.substFn φ cv.levelParams us)) (g := t)
      (fun _ => (ht ρ).1) (by rw [hprf, (ht ρ).2]; rfl)
    exact ⟨hr.1 hw, hr.2⟩

/-- **The δ step is invisible to the reading**: the unfolding reads,
and where the subject is graded the unfolding is graded and interprets
as the subject does. -/
theorem denote_unfoldDefinition {m : EnvModel V env} (hdi : AcvalDefnInst m)
    {d : Nat} {e e' : Expr} {ea : Term}
    (hud : ConLeche.unfoldDefinition env e = some e')
    (hea : denote m.acval env φ d e = some ea) :
    ∃ ea', denote m.acval env φ d e' = some ea' ∧
      ∀ ρ : Nat → V, WellDenoted V ρ ea → WellDenoted V ρ ea' ∧ interp V ρ ea = interp V ρ ea' := by
  unfold ConLeche.unfoldDefinition at hud
  split at hud
  · next n us hfn =>
    split at hud
    · next cv value hint hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        obtain ⟨-, -, -, -, hd, -⟩ := m.wf.consts _ (ConLeche.Env.find?_mem hfind)
        obtain ⟨hnf, -, -, hlb⟩ := hd cv value hint rfl
        have hmem : ∃ hint', ConstantInfo.defnInfo cv value hint' ∈ env.consts :=
          ⟨hint, ConLeche.Env.find?_mem hfind⟩
        obtain ⟨t, ht, hlr⟩ := denoteDefnInst (us := us) hdi φ hmem
        obtain ⟨t₀, ht₀, -⟩ := hdi (Level.substFn φ cv.levelParams us) cv value hmem
        have hcl : ∀ k : Nat, t.liftN 1 k = t := by
          rw [denotePInstLevels m φ cv.levelParams us 0 value, ht₀] at ht
          obtain rfl := Option.some.inj ht
          exact fun k => denote_liftN_eq_self m.cval_closed hnf hlb ht₀ 1 k
        exact deltaCore m hfn hfind rfl hlen hnf hcl ht hlr hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud

/-! ## The graph-regime fit of a graded spine (task #342 L10) -/

/-- A spine headed by the point is the point. -/
theorem interp_mkAppN_of_pt {ρ : Nat → V} {f : Term} (hf : interp V ρ f = pt) :
    ∀ (as : List Term), interp V ρ (Term.mkAppN f as) = pt
  | [] => hf
  | a :: as => by
    show interp V ρ (Term.mkAppN (.app f a) as) = pt
    exact interp_mkAppN_of_pt (by rw [interp_app, hf, app_pt]) as

/-- **A graded application that is not the point fits its head's
∀-telescope** ("not pt" source (2)): every prefix of the spine is not
the point (`app_pt`), so a prefix's type is in the graph regime
(`eq_pt_of_mem_piR_zero`), and the argument's own application slot
puts it in the telescope's domain (`slotTransfer`). -/
theorem teleFitPA_of_graded_ne_pt {ρ : Nat → V} :
    ∀ (vs : List Term) {T f : Term},
      PiChain vs.length T → WellDenoted V ρ T → interp V ρ f ∈ˢ interp V ρ T →
      WellDenoted V ρ (Term.mkAppN f vs) →
      interp V ρ (Term.mkAppN f vs) ≠ pt →
      ∃ rest, TeleFitPA V ρ T vs rest
  | [], T, _, _, _, _, _, _ => ⟨T, .nil⟩
  | x :: xs, T, f, hpc, hT, hmem, hg, hne => by
    obtain ⟨A, B, rfl, hpcB⟩ := piChain_succ_inv hpc
    have hg' : WellDenoted V ρ (Term.mkAppN (.app f x) xs) := hg
    have hne' : interp V ρ (Term.mkAppN (.app f x) xs) ≠ pt := hne
    have happ : WellDenoted V ρ (.app f x) := mkAppN_head xs hg'
    obtain ⟨v', A', B', hslot, hx, -⟩ := (cast (WellDenoted_app V ρ f x) happ).2.2
    have hmem' := hmem
    rw [interp_pi] at hmem'
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) xs)
    have hgr : interp V ρ f ∈ˢ piR 1 (interp V ρ A) fun y => interp V (cons y ρ) B := by
      rw [piR_pos Nat.one_ne_zero]; exact mem_piSet_of_mem_piV hmem' hfne
    have hxA : interp V ρ x ∈ˢ interp V ρ A := slotTransfer Nat.one_ne_zero hgr hslot hx
    have hokx : WellDenoted V ρ x := happ.app_arg
    have hBx : WellDenoted V ρ (B.inst x) :=
      (WellDenoted_inst0 _ hokx).mpr (hT.pi_body _ hxA)
    have hmemB : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
      rw [interp_inst0, interp_app]
      exact app_mem_piV hmem' hxA
    obtain ⟨rest, hfit⟩ :=
      teleFitPA_of_graded_ne_pt xs (PiChain.inst x 0 hpcB) hBx hmemB hg' hne'
    exact ⟨rest, .cons hxA hfit⟩

/-- A fit's residual is graded where the telescope and the spine are. -/
theorem teleFitPA_rest_graded {ρ : Nat → V} :
    ∀ {T : Term} {vs : List Term} {rest : Term},
      TeleFitPA V ρ T vs rest → WellDenoted V ρ T →
      (∀ x ∈ vs, WellDenoted V ρ x) → WellDenoted V ρ rest := by
  intro T vs rest h
  induction h with
  | nil => intro hT _; exact hT
  | @cons A B rest' a as hmem _ ih =>
    intro hT hvs
    have hokA : WellDenoted V ρ a := hvs a List.mem_cons_self
    exact ih ((WellDenoted_inst0 _ hokA).mpr (hT.pi_body _ hmem))
      (fun x hx => hvs x (List.mem_cons_of_mem a hx))

/-- **A fit's residual is a type** when the fitted Π-type is one: each
step's fibre is a type (the Π's grading), and the residual is the last
fibre ("not pt" source (1) for a constructor's codomain). -/
theorem teleFitPA_rest_isTy {ρ : Nat → V} :
    ∀ {T : Term} {vs : List Term} {rest : Term},
      TeleFitPA V ρ T vs rest → WellDenotedTy V ρ T →
      (∀ x ∈ vs, WellDenoted V ρ x) → IsTy (interp V ρ rest) := by
  intro T vs rest h
  induction h with
  | nil => intro hT _; exact hT.2
  | @cons A B rest' a as hmem _ ih =>
    intro hT hvs
    have hokA : WellDenoted V ρ a := hvs a List.mem_cons_self
    refine ih ⟨(WellDenoted_inst0 _ hokA).mpr (hT.1.pi_body _ hmem), ?_⟩
      (fun x hx => hvs x (List.mem_cons_of_mem a hx))
    rw [interp_inst0]
    exact (cast (WellDenoted_pi V ρ A B) hT.1).2.2.2 _ hmem

end ConLeche.Model.Rules
