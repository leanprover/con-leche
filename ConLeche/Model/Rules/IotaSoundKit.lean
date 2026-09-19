module

public import ConLeche.Model.Rules.Inputs
-- lane S-red's transplanted kit: `ReadSpine.length`, `PiChain`,
-- `frame_spine`, `hoist_spine`, `mkAppN_of_fitA` … are shared rather
-- than transplanted twice (the two lanes met in the middle).
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitShift
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InstSpine

public section

/-!
# The ι lane's transplanted kit (task #305, lane S-iota)

The spine, frame and fit lemmas the ι rule and the three stuck-major
rescues need, restated over `Motive.lean`'s `ReadSpine` and proved
here rather than imported: `Model/Steps/*` is off the rules tier's
proof path by design (`tests/proofdeps.sh` pins the closure), so every
row this lane mines is TRANSPLANTED — the argument, not the import.

Provenance, row by row (the original is the docstring's citation):

* the `ReadSpine` API and `readSpine_mkAppN`/`_inv` —
  `DenoteMetaSpine` and `denoteMeta_mkAppN(_inv)`
  (`Model/Steps/Stuck.lean:94-140`, `CapsRows.lean`);
* `interp_mkAppN_congrK`, `hoist_spineK`, `frame_spineK` —
  `Model/Steps/Stuck.lean:146-206`;
* `fitA_grades` — `wellDenotedV_mkAppN_of_fitA`
  (`Model/Steps/IotaKit.lean:370`);
* `constTy_pkg` — `constType_pkg` (`Model/Steps/IotaRows.lean:200`);
* `denoteMeta_const_arityK` — `denoteMeta_const_arity` (`:233`);
* the annotated `take`/`drop`/`getD` list algebra — `IotaRows.lean:107-153`.

Nothing here is new mathematics; the statements are the originals'
with `DenoteMetaSpine` replaced by `ReadSpine` and the `Frame`/
`Graded`/`LeavesSub` abbreviations of `Motive.lean` in place of the
claims' spelled-out conjunctions.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The `ReadSpine` API -/

namespace ReadSpine

variable {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}

theorem mem {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ x ∈ as, ∃ v, denoteMeta acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, ha⟩
    · exact ih x hx'

theorem take {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ n : Nat, ReadSpine acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using ReadSpine.nil
  | cons ha _ ih =>
    intro n
    cases n with
    | zero => simpa using ReadSpine.nil
    | succ k => simpa using ReadSpine.cons ha (ih k)

theorem drop {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ n : Nat, ReadSpine acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using ReadSpine.nil
  | cons ha ht ih =>
    intro n
    cases n with
    | zero => simpa using ReadSpine.cons ha ht
    | succ k => simpa using ih k

theorem append {as bs : List Expr} {vs ws : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) (h' : ReadSpine acval env φ d bs ws) :
    ReadSpine acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => simpa using h'
  | cons ha _ ih => simpa using ReadSpine.cons ha ih

theorem getD {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ (dflt : Expr) (i : Nat), i < as.length →
      denoteMeta acval env φ d (as.getD i dflt) = some (vs.getD i default) := by
  induction h with
  | nil => intro dflt i hi; exact absurd hi (by simp)
  | @cons a v as vs ha _ ih =>
    intro dflt i hi
    cases i with
    | zero => simpa [List.getD] using ha
    | succ k =>
      have : k < as.length := by simpa using hi
      simpa [List.getD] using ih dflt k this

/-- A spine of uniformly-reading expressions (the fabricated
projection lists). -/
theorem map_list {β : Type _} (f : β → Expr) (g : β → AnnotTerm) :
    ∀ (l : List β), (∀ x ∈ l, denoteMeta acval env φ d (f x) = some (g x)) →
      ReadSpine acval env φ d (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => intro _; exact ReadSpine.nil
  | cons x xs ih =>
    intro h
    exact ReadSpine.cons (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Every list of readable expressions has a reading spine. -/
theorem exists_of_all :
    ∀ (as : List Expr), (∀ x ∈ as, ∃ v, denoteMeta acval env φ d x = some v) →
      ∃ vs, ReadSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil => intro _; exact ⟨[], .nil⟩
  | cons a as ih =>
    intro h
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun y hy => h y (List.mem_cons_of_mem a hy))
    exact ⟨v :: vs, .cons hv hvs⟩

end ReadSpine

/-- An application spine reads to the `AnnotTerm` application
(`denoteMeta_mkAppN`, `Model/Steps/CapsRows.lean`). -/
theorem readSpine_mkAppN {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm} (h : ReadSpine acval env φ d as vs)
    {f : Expr} {fa : AnnotTerm} (hf : denoteMeta acval env φ d f = some fa) :
    denoteMeta acval env φ d (Expr.mkAppN f as)
      = some (AnnotTerm.mkAppN fa vs) := by
  induction h generalizing f fa with
  | nil => exact hf
  | @cons a v as vs ha _ ih =>
    exact ih (f := .app f a) (fa := .app fa v)
      (by rw [denoteMeta_app, hf, ha]; rfl)

/-- **The application spine, inverted at the validated reading**
(`denoteMeta_mkAppN_inv`, `Model/Steps/Stuck.lean:128`). -/
theorem readSpine_mkAppN_inv {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : AnnotTerm},
    denoteMeta acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denoteMeta acval env φ d f = some fa ∧
      ReadSpine acval env φ d as vs ∧ ea = AnnotTerm.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denoteMeta_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

/-- **The spine congruence at `interp`** (`interp_mkAppN_congr`,
`Model/Steps/Stuck.lean:146`). -/
theorem interp_mkAppN_congrK {ρ : Nat → V} :
    ∀ (asa bsa : List AnnotTerm) {fa fb : AnnotTerm},
      interp V ρ fa = interp V ρ fb →
      asa.map (interp V ρ) = bsa.map (interp V ρ) →
      interp V ρ (AnnotTerm.mkAppN fa asa)
        = interp V ρ (AnnotTerm.mkAppN fb bsa) := by
  intro asa
  induction asa with
  | nil =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => exact hf
    | cons _ _ => simp at hall
  | cons a as ih =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => simp at hall
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hall
      exact ih bs (by simp only [interp_app, hf, hall.1]) hall.2

/-- Every argument of a graded application spine is graded, and so is
its head (`hoist_spine`, `Model/Steps/Stuck.lean:169`). -/
theorem hoist_spineK {Δa : List AnnotTerm} :
    ∀ (asa : List AnnotTerm) {fa : AnnotTerm},
      Graded V Δa (AnnotTerm.mkAppN fa asa) →
      Graded V Δa fa ∧ ∀ x ∈ asa, Graded V Δa x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · exact ((WellDenoted_app V ρ fa a) ▸ (happ ρ hρ).1).1
    · exact ((AnnotValid_app V ρ fa a) ▸ (happ ρ hρ).2).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fun ρ hρ =>
          ⟨((WellDenoted_app V ρ fa x) ▸ (happ ρ hρ).1).2.1,
            ((AnnotValid_app V ρ fa x) ▸ (happ ρ hρ).2).2⟩
      · exact hrest x hx'

/-- The frame and context of every argument of a spine (`frame_spine`,
`Model/Steps/Stuck.lean:192`, at `Motive.lean`'s `Frame`). -/
theorem frame_spineK {m : EnvModel V env} {d : Nat} {Δa : List AnnotTerm}
    {a : Expr} (hf : Frame d a) (hC : CtxOk m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Frame d x ∧ CtxOk m φ d Δa x := fun x hx =>
  ⟨⟨hf.1.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hf.2.1 x hx,
      fun l hl => hf.2.2 l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩,
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)⟩

/-- The frame of an application built over framed parts. -/
theorem frame_mkAppN {d : Nat} {f : Expr} {as : List Expr}
    (hf : Frame d f) (has : ∀ x ∈ as, Frame d x) :
    Frame d (Expr.mkAppN f as) := by
  refine ⟨ConLeche.Expr.WScoped.mkAppN hf.1 (fun y hy => (has y hy).1),
    ConLeche.looseBVarsBounded_mkAppN hf.2.1 (fun y hy => (has y hy).2.1),
    fun l hl => ?_⟩
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf.2.2 l hl'
  · exact (has y hy).2.2 l hly

/-- The leaves of an application are its parts' (`fvarLeaves_mkAppN`,
packaged at `Motive.lean`'s `LeavesSub`). -/
theorem leavesSub_mkAppN {f e : Expr} {as : List Expr}
    (hf : LeavesSub f e) (has : ∀ x ∈ as, LeavesSub x e) :
    LeavesSub (Expr.mkAppN f as) e := by
  intro l hl
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf l hl'
  · exact has y hy l hly

/-- A closed expression has no leaves at all. -/
theorem leavesSub_of_not_hasFvar {f e : Expr} (h : f.hasFvar = false) :
    LeavesSub f e := by
  intro l hl
  rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  exact nomatch hl

/-! ## The stored data -/

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and closed (`constType_pkg`,
`Model/Steps/IotaRows.lean:200`). -/
theorem constTy_pkg {m : EnvModel V env} (hct : ConstTy m φ)
    {n : Name} {ci : ConLeche.ConstantInfo} (hf : env.find? n = some ci)
    (hnt : ci.isTowerEntry = false) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : AnnotTerm,
      (∀ d : Nat, denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hnt hlen
  have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hta 1 k)
      hta,
    hok, hmem, hnf, hbd⟩

/-- A closed stored type is framed and in context at every depth. -/
theorem frame_of_not_hasFvar {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {e : Expr} (hnf : e.hasFvar = false)
    (hbd : e.looseBVarsBounded 0 = true) (hlen : Δa.length = d) :
    Frame d e ∧ CtxOk m φ d Δa e :=
  ⟨⟨ConLeche.Expr.WScoped.of_not_hasFvar hnf, hbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    ⟨hlen, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl
      exact nomatch hl⟩⟩

/-- A `.const` that reads was applied at the stored arity, and its
reading is the leaf (`denoteMeta_const_arity`,
`Model/Steps/IotaRows.lean:233`). -/
theorem denoteMeta_const_arityK {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    {ea : AnnotTerm} (hf : env.find? n = some ci)
    (h : denoteMeta acval env φ d (.const n us) = some ea) :
    us.length = ci.toConstantVal.levelParams.length ∧
      ea = acval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [denoteMeta, hf] at h
  dsimp only at h
  split at h
  · next hlen => exact ⟨hlen, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The fit -/

/-- **A `TeleFitPA` fit plus the type's grading grades the applied
spine** (`wellDenotedV_mkAppN_of_fitA`, `Model/Steps/IotaKit.lean:370`). -/
theorem fitA_grades {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f rest : AnnotTerm},
      WellDenotedV V ρ Ta → WellDenotedV V ρ f →
      (∀ x ∈ vs, WellDenotedV V ρ x) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      TeleFitPA V ρ Ta vs rest →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) ∧
        interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ interp V ρ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f rest _ hf _ hmem hfit
    cases hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f rest hokT hf hoks hmem hfit
    cases hfit with
    | @cons u v A B _ _ _ hx hfit' =>
      have hokA : WellDenotedV V ρ A :=
        ⟨((WellDenoted_pi V ρ u v A B) ▸ hokT.1).1,
          ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V ρ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V ρ A →
          interp V (cons y ρ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      have hokx : WellDenotedV V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenotedV V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hokx.1, v, interp V ρ A,
            (fun y => interp V (cons y ρ) B), hmem, hx, hfib⟩
        · rw [AnnotValid_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
        rw [interp_inst0, interp_app]
        exact app_mem_piR hmem hx hfib
      exact ih ((WellDenotedV_inst0 hokx).mpr (hokB _ hx)) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-! ## The ∀-chain guard and the tower entries

`PiChainK`/`peelPisK_of_piChain`/`piChainK_of_stripPis`
(`Model/Steps/CapsRows.lean:79-130`, `:452`) and the two tower-entry
rows (`denoteMeta_proj_towerK`, `towerEntry_tele_at_depthK`,
`Model/Steps/TowerKit.lean:47`, `:173`), transplanted. -/

/-- The reading's first `n` heads are `.pi` nodes (`PiChain`,
`Model/Steps/CapsRows.lean:79`). -/
@[expose] def PiChainK : Nat → AnnotTerm → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ _ _ B => PiChainK n B
    | _ => False

theorem piChainK_succ_inv {n : Nat} {e : AnnotTerm} (h : PiChainK (n + 1) e) :
    ∃ u v A B, e = .pi u v A B ∧ PiChainK n B := by
  match e with
  | .pi u v A B => exact ⟨u, v, A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

theorem PiChainK.inst : ∀ {n : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    PiChainK n e → PiChainK n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChainK_succ_inv h
    exact ih a (k + 1) hB

/-- A ∀-chain of a list's length peels along it (`peelPis_of_piChain`,
`Model/Steps/CapsRows.lean:114`). -/
theorem peelPisK_of_piChain : ∀ (as : List AnnotTerm) {T : AnnotTerm},
    PiChainK as.length T →
      ∃ rest, ConLeche.Model.AnnotTerm.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChainK_succ_inv h
    exact peelPisK_of_piChain as (PiChainK.inst a 0 hB)

/-- **A syntactic ∀-telescope reads to a ∀-chain**
(`piChain_of_stripPis`, `Model/Steps/CapsRows.lean:452`). -/
theorem piChainK_of_stripPis {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm},
      (e.stripPis n).isSome = true →
      denoteMeta acval env φ d e = some ea → PiChainK n ea := by
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
    | .lam _ _ _, hs => exact nomatch hs
    | .letE _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE ty bd mb, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hd
      simp only [ConLeche.Expr.stripPis, Option.isSome_map] at hs
      exact ih (ConLeche.Expr.stripPis_instantiate1_isSome n 0 hs) hba

/-- The clause at a stored entry (`denoteMeta_proj_tower`,
`Model/Steps/TowerKit.lean:47`). -/
theorem denoteMeta_proj_towerK {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (he : denoteMeta acval env φ d e = some ia) :
    denoteMeta acval env φ d (.proj s i e) = some (projAV (i + entry.off) ia) := by
  rw [denoteMeta_proj, he]
  show (match env.findProj? s i with
    | some entry => some (projAV (i + entry.off) ia)
    | none => AnnotTerm.projPair? i ia)
      = some (projAV (i + entry.off) ia)
  rw [hfe]

/-- **The body telescope's reading is depth-free**
(`towerEntry_tele_at_depth`, `Model/Steps/TowerKit.lean:173`, with
`towerEntry_tele_closed`, `:160`). -/
theorem towerEntry_tele_at_depthK {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) :
    ∀ d : Nat, denoteMeta m.acval env φ d
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta := by
  have hnf : (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).hasFvar = false ∧
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams
          us)).looseBVarsBounded 0 = true := by
    rw [ConLeche.projTele_hasFvar, ConLeche.projTele_looseBVarsBounded,
      Nat.zero_add]
    exact ⟨ConLeche.projEntry_body_hasFvar m.wf hfe us,
      ConLeche.projEntry_body_looseBVars m.wf hfe us⟩
  exact denoteMeta_depth_of_closed m.acval_closed hnf.1
    (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf.1 hnf.2 hTa 1 k)
    hTa

/-! ## The annotated list algebra

`map_interp_getD_eq`, `getD_takeA`, `getD_dropA`, `take_getD_splitA`
(`Model/Steps/IotaRows.lean:107-153`), transplanted verbatim. -/

/-- Pointwise reading of a map equality at `getD` slots. -/
theorem map_interp_getD_eqK {ρ : Nat → V} {as bs : List AnnotTerm}
    (h : as.map (interp V ρ) = bs.map (interp V ρ))
    {i : Nat} (hi : i < as.length) :
    interp V ρ (as.getD i default) = interp V ρ (bs.getD i default) := by
  have hlen : as.length = bs.length := by
    have := congrArg List.length h
    simpa using this
  have h1 : (as.map (interp V ρ))[i]? = (bs.map (interp V ρ))[i]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)] at h1
  simpa using h1

/-- `getD` through `take`, below the cut. -/
theorem getD_takeAK {as : List AnnotTerm} {k i : Nat} (hi : i < k) :
    (as.take k).getD i default = as.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi]

/-- `getD` through `drop`. -/
theorem getD_dropAK (as : List AnnotTerm) (k i : Nat) :
    (as.drop k).getD i default = as.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A list of length `k + 1` splits as its prefix plus its last element. -/
theorem take_getD_splitAK {as : List AnnotTerm} {k : Nat}
    (h : as.length = k + 1) :
    as = as.take k ++ [as.getD k default] := by
  have hlen : (as.drop k).length = 1 := by
    rw [List.length_drop, h]; omega
  obtain ⟨a, ha⟩ : ∃ a, as.drop k = [a] := by
    match hd : as.drop k with
    | [a] => exact ⟨a, rfl⟩
    | [] => rw [hd] at hlen; simp at hlen
    | a :: b :: t => rw [hd] at hlen; simp at hlen
  have hget : a = as.getD k default := by
    have h0 : (as.drop k).getD 0 default = a := by rw [ha]; rfl
    rw [getD_dropAK, Nat.add_zero] at h0
    exact h0.symm
  calc as = as.take k ++ as.drop k := (List.take_append_drop k as).symm
    _ = as.take k ++ [as.getD k default] := by rw [ha, hget]

/-! ## The redex's own slots

`AnnotTerm.mkAppN_append`, `wellDenotedV_app_congr_arg` and
`wellDenotedV_mkAppN_snoc_congr` (`Model/Steps/IotaGate.lean:81-115`):
the subject's grading is about the ORIGINAL major slot and the licensed
walk is handed the prepared one, so the last argument is exchanged
along the reduction's own `interp` equation. -/

theorem AnnotTerm.mkAppN_appendK (f : AnnotTerm) :
    ∀ (as bs : List AnnotTerm),
      AnnotTerm.mkAppN f (as ++ bs) = AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs
  | [], _ => rfl
  | _ :: as, bs => AnnotTerm.mkAppN_appendK _ as bs

/-- **An app's argument may be exchanged for an interpretation-equal
graded one**. -/
theorem wellDenotedV_app_congr_argK {ρ : Nat → V} {f a a' : AnnotTerm}
    (h : WellDenotedV V ρ (.app f a)) (ha' : WellDenotedV V ρ a')
    (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (.app f a') := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  obtain ⟨hf, -, v, A, B, hslot, hmem, hcod⟩ := h1
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hf, ha'.1, v, A, B, hslot, heq ▸ hmem, hcod⟩
  · rw [AnnotValid_app]
    exact ⟨h2.1, ha'.2⟩

/-- The same at a spine's last argument. -/
theorem wellDenotedV_mkAppN_snoc_congrK {ρ : Nat → V} {f a a' : AnnotTerm}
    {as : List AnnotTerm}
    (h : WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a])))
    (ha' : WellDenotedV V ρ a') (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a'])) := by
  rw [AnnotTerm.mkAppN_appendK] at h ⊢
  exact wellDenotedV_app_congr_argK h ha' heq

/-! ## The fired rule's right-hand side and the telescope residual -/

/-- The fired rule's right-hand side reads at every depth
(`recRhs_depth`, `Model/Steps/IotaRows.lean:296`). -/
theorem recRhs_depthK {m : EnvModel V env}
    {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) {us : List Level} {Ra : AnnotTerm}
    (hRa0 : denoteMeta m.acval env φ 0
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
      = some Ra) :
    (∀ d : Nat, denoteMeta m.acval env φ d
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra) ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).hasFvar = false ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP rules rfl rl hmem
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hRnf
  have hbd : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hRa0 1 k)
      hRa0,
    hnf, hbd⟩

/-- The frame of a `∀`-telescope's residual (`piResidual_frame`,
`Model/Steps/IotaRows.lean:155`, at `Motive.lean`'s `Frame`). -/
theorem piResidual_frameK {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      ConLeche.piResidual T args = some rest →
      Frame d T → CtxOk m φ d Δa T →
      (∀ x ∈ args, Frame d x ∧ CtxOk m φ d Δa x) →
      Frame d rest ∧ CtxOk m φ d Δa rest := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hfr hCt _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact ⟨hfr, hCt⟩
  | cons a as ih =>
    intro rest h hfr hCt hfrA
    obtain ⟨hw, hb, hL⟩ := hfr
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _ _, h => exact nomatch h
    | .letE _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE ty body mb, h =>
    obtain ⟨⟨hwa, hba, hLa⟩, hCa⟩ := hfrA a (by simp)
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ih h ⟨Expr.WScoped.instantiate1_gen hwa 0 hw.2,
        Expr.looseBVarsBounded_instantiate1_gen hba hb.2, fun l hl => ?_⟩
      ⟨hCt.1, fun l hl => ?_⟩ (fun x hx => hfrA x (by simp [hx])) <;>
    · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · first
        | exact hL l (by simp [Expr.fvarLeaves, h2])
        | exact hCt.2 l (by simp [Expr.fvarLeaves, h2])
      · first
        | exact hLa l h2
        | exact hCa.2 l h2

/-- **A `TeleFitPA` fit's residual is the reading of the checker's own
`piResidual`** (`teleFitPA_residual`, `Model/Steps/IotaKit.lean:174`). -/
theorem teleFitPA_residualK {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {ρ : Nat → V} {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {Ta restA : AnnotTerm}
      {vs : List AnnotTerm},
      ConLeche.piResidual ty args = some rest →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteMeta acval env φ d ty = some Ta →
      ReadSpine acval env φ d args vs →
      TeleFitPA V ρ Ta vs restA →
      denoteMeta acval env φ d rest = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest Ta restA vs hpr _ _ hty hsp hfit
    obtain rfl : rest = ty := (Option.some.inj hpr).symm
    cases hsp
    cases hfit
    exact hty
  | cons a as ih =>
    intro ty rest Ta restA vs hpr hwty hargs hty hsp hfit
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body mb, hpr, hwty, hty => ?_
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hty
    have hbody' : denoteMeta acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteMeta_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    cases hfit with
    | cons _ hfit' =>
      exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp' hfit'

/-! ## The reverse opening, read

`denoteMeta_openRev_base` and `denoteMeta_openRev`
(`Model/Steps/IotaKit.lean:66`, `:103`), transplanted: the `.nested`
fire's comparands are stored pins instantiated at the recursor's
parameter prefix, and this is what turns the law's OPEN reading at
depth `rP` into the instantiated comparand's reading at the ambient
depth. -/

/-- **The base-independence of the opened validated reading**. -/
theorem denoteMeta_openRev_baseK {acval : Name → (Name → Nat) → AnnotTerm}
    {cval : TConstVal}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denoteMeta acval env φ (d + n) (openRev d n e)
      = denoteMeta acval env φ n (openRev 0 n e) := by
  intro d
  induction d with
  | zero => rw [Nat.zero_add]
  | succ d ih =>
    have h1 : openRev (d + 1) n e = (openRev d n e).shiftFrom 0 :=
      (openRev_shiftFrom hnf d n).symm
    rw [show d + 1 + n = (d + n) + 1 from by omega, h1,
      denoteMeta_shiftFrom (p := 0) hacl (openRev d n e) (d + n)
        (Nat.zero_le _)
        (openRev_WScoped (Expr.WScoped.of_not_hasFvar hnf) n),
      ih]
    cases hden : denoteMeta acval env φ n (openRev 0 n e) with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Nat.sub_zero]
      refine AnnotTerm.liftN_eq_self v ?_ 1
      have hws : Expr.WScoped n (openRev 0 n e) := by
        have h2 := openRev_WScoped (d := 0)
          (Expr.WScoped.of_not_hasFvar hnf) n
        rwa [Nat.zero_add] at h2
      have hbv := denote_bvarsBelow (cval := cval) (env := env) (φ := φ)
        hcl n (openRev 0 n e) hws
        (openRev_bounded n 0 (by simpa using hb))
        (denoteMeta_erase hlink n (openRev 0 n e) hden)
      exact hbv.mono (by omega)

/-- **Real-argument instantiation, read through the reverse opening**. -/
theorem denoteMeta_openRevK {m : EnvModel V env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (m.acval n ψ).inst y k = m.acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List AnnotTerm}, ReadSpine m.acval env φ d as vs →
      denoteMeta m.acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denoteMeta m.acval env φ (d + as.length)
            (openRev d as.length e)).map (AnnotTerm.instRevChain vs) := by
  intro as
  induction as with
  | nil =>
    intro e d _ _ _ vs hsp
    cases hsp
    show denoteMeta m.acval env φ d e = (denoteMeta m.acval env φ (d + 0) e).map _
    cases denoteMeta m.acval env φ d e <;> rfl
  | cons a as ih =>
    intro e d hargs hfb hb vs hsp
    cases hsp with
    | @cons _ va _ vs' ha hsp' => ?_
    have hargs' : ∀ x ∈ as, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true :=
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    show denoteMeta m.acval env φ d
      (Expr.instSeq as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))) = _
    rw [show (a :: as).length - 1 - 1 = as.length - 1 from by simp,
      show (a :: as).length - 1 = as.length from by simp]
    rw [ih (e := e.instantiate1 a as.length) hargs'
      (Expr.fvarsBelow_instantiate1_gen hwa.fvarsBelow _ hfb)
      (Expr.looseBVarsBounded_instantiate1_gen hba (by simpa using hb))
      hsp']
    rw [openRev_instantiate1_top hba d as.length e]
    have ha' : denoteMeta m.acval env φ (d + as.length) a
        = some (va.liftN as.length) := by
      rw [denoteMeta_lift hacl hwa (d + as.length) (by omega), ha,
        show d + as.length - d = as.length from by omega]
      rfl
    rw [denoteMeta_beta (ty := .sort .zero) hacl hainst
      (openRev_fvarsBelow hfb as.length) (hwa.mono (by omega)) hba ha' 0]
    show ((denoteMeta m.acval env φ (d + as.length + 1)
      (openRev d (as.length + 1) e)).map
        (AnnotTerm.inst · (va.liftN as.length) 0)).map
        (AnnotTerm.instRevChain vs') = _
    rw [Option.map_map,
      show d + as.length + 1 = d + (a :: as).length from by
        simp only [List.length_cons]
        omega,
      show (a :: as).length = as.length + 1 from rfl]
    cases denoteMeta m.acval env φ (d + (as.length + 1))
        (openRev d (as.length + 1) e) with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
      show AnnotTerm.instRevChain vs' (X.inst (va.liftN as.length) 0) = _
      rw [show AnnotTerm.instRevChain (va :: vs') X
        = AnnotTerm.instRevChain vs' (X.inst (va.liftN vs'.length) 0) from rfl,
        hsp'.length]

/-- A list member is the value at one of its indices (the shape the
`∀ x ∈ bsa` grading premises need when the fact is indexed). -/
theorem mem_getD_index {α : Type _} [Inhabited α] {l : List α} {x : α}
    (h : x ∈ l) : ∃ j, j < l.length ∧ l.getD j default = x := by
  obtain ⟨j, hj, hx⟩ := List.getElem_of_mem h
  exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hx]; rfl⟩

end ConLeche.Model.Rules
