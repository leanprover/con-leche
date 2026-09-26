module

public import Fragment.InstallScope
public import Fragment.InstallRead1
public import Fragment.InstallRead3

@[expose] public section

/-!
# Installing an inductive block, part 1: the block's model and the
types of its constants

From the checker's verdict `IndOk env S` (`Decl.lean`) and a model of
`env`: the final assignment `M₃` (`IndSem.lean`) is a reader of the
block at every valuation; the environments holding the former, then
the constructors, have models at `M₃`; the two facts the constructor
checks supply beyond the types' invariants — the domains met along a
fitting instance are members of the universe (`domsBounded_of`) and,
under the subsingleton criterion, the fibre's witness is unique
(`uniq_of`) — and the three `type_ok` laws: the former's set is in
its type (`type_ok_ind`), each constructor's in its (`type_ok_ctor`),
the recursor's in its (`type_ok_rec`: the recursor's typing,
`recSem_mem`, or at a proposition the motive's inhabitation,
`motive_inhabited`, through the recursor's context read in both the
block's own reader and the final one).
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

namespace IndSpec

variable {env : Env} {S : IndSpec}

/-! ## The setting -/

/-- The block's names are fresh. -/
theorem Ok.fresh (hok : S.Ok env) : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none :=
  hok.2.1

theorem Ok.freshI (hok : S.Ok env) : env.find? S.name = none := hok.fresh _ (by simp)

theorem Ok.scoped (hok : S.Ok env) : S.Scoped env := hok.2.2.1

theorem Ok.nodup (hok : S.Ok env) : (S.name :: S.recName :: S.ctors.map (·.name)).Nodup := hok.1

theorem Ok.nodup_ctors (hok : S.Ok env) : (S.ctors.map (·.name)).Nodup := hok.nodup.of_cons.of_cons

theorem Ok.name_not_mem (hok : S.Ok env) : S.name ∉ S.recName :: S.ctors.map (·.name) :=
  (List.nodup_cons.mp hok.nodup).1

theorem Ok.rec_not_mem (hok : S.Ok env) : S.recName ∉ S.ctors.map (·.name) :=
  (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).1

theorem Ok.name_ne_rec (hok : S.Ok env) : S.name ≠ S.recName :=
  fun h => hok.name_not_mem (by rw [h]; exact List.mem_cons_self)

theorem Ok.ctorOf?_name (hok : S.Ok env) : S.ctorOf? S.name = none := by
  apply S.ctorOf?_none
  intro c hc h
  exact hok.name_not_mem (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, h⟩))

theorem Ok.ctorOf?_rec (hok : S.Ok env) : S.ctorOf? S.recName = none := by
  apply S.ctorOf?_none
  intro c hc h
  exact hok.rec_not_mem (List.mem_map.mpr ⟨c, hc, h⟩)

theorem Ok.ctor_ne_rec (hok : S.Ok env) {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) :
    c.name ≠ S.recName :=
  fun h => hok.rec_not_mem (List.mem_map.mpr ⟨c, List.mem_of_getElem? hc, h⟩)

/-- The final assignment agrees with the old one on the stored
constants. -/
theorem agree_M₃ (hok : S.Ok env) (M : Name → List Nat → V) : AgreeOn env M (S.M₃ M) := by
  intro n hn ls
  have hne : ∀ x ∈ S.name :: S.recName :: S.ctors.map (·.name), n ≠ x := by
    intro x hx h
    subst h
    rw [hok.fresh n hx] at hn
    simp at hn
  simp only [M₃, M₂, M₁]
  rw [if_neg (hne _ (by simp))]
  rw [S.ctorOf?_none fun c hc h => hne c.name
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))) h.symm]
  rw [if_neg (hne _ (by simp))]

/-- The final assignment reads the former and the constructors. -/
theorem reader₃ (hok : S.Ok env) (M : Name → List Nat → V) (φ : Name → Nat) :
    S.Reader₂ (env := env) M φ (S.M₃ M) φ where
  R :=
    { agree := agree_M₃ hok M
      fam := fun ls' => by
        simp [M₃, M₂, M₁, hok.name_ne_rec, hok.ctorOf?_name]
      val := fun _ _ => rfl }
  ctor := fun j c hc ls' => by
    simp [M₃, M₂, hok.ctor_ne_rec hc, S.ctorOf?_of_getElem? hok.nodup_ctors hc]

/-- The model with the former, as a reader of the constructors' sets
too (it does not read them, but the reader structure asks). -/
theorem reader₂ (hok : S.Ok env) (M : Name → List Nat → V) (φ : Name → Nat) {φ' : Name → Nat}
    (hφ : ∀ n ∈ S.lparams, φ' n = φ n) :
    S.Reader₂ (env := env) M φ (S.M₂ M) φ' where
  R :=
    { agree := fun n hn ls => by
        have h₃ := agree_M₃ hok M n hn ls
        simp only [M₃] at h₃
        have hne : n ≠ S.recName := fun h => by
          subst h; rw [hok.fresh _ (by simp)] at hn; simp at hn
        rwa [if_neg hne] at h₃
      fam := fun ls' => by
        simp [M₂, M₁, hok.ctorOf?_name]
      val := hφ }
  ctor := fun j c hc ls' => by
    simp [M₂, S.ctorOf?_of_getElem? hok.nodup_ctors hc]

/-- The block's own valuation, from concrete levels: the master
valuation for the readings at those levels. -/
theorem lparams_map_substVal (hok : S.Ok env) (φ : Name → Nat) {ls : List Level}
    (hls : ls.length = S.lparams.length) :
    S.lparams.map (Level.substVal φ S.lparams ls) = ls.map (Level.eval φ) :=
  map_substVal_eq φ hok.scoped.2.2.2.2.2 hls

/-! ## The model of the environment with the former -/

variable (hs : Env.Scoped env) (m : EnvModel V env) (hok : S.Ok env)
include hs m hok

/-- The old model at the final assignment. -/
noncomputable def m₃ : EnvModel V env := m.transport hs (S.M₃ m.M) (agree_M₃ hok m.M)

theorem m₃_M : (m₃ hs m hok).M = S.M₃ m.M := rfl

/-- **The former's type law**: its type is well-denoted and its set is
a member. -/
theorem type_ok_ind (φ : Name → Nat) (ρ : Nat → V) {ls : List Level}
    (hls : ls.length = S.indInfo.lparams.length) :
    WellDenoted (S.M₃ m.M) φ ρ (S.indInfo.type.instL S.indInfo.lparams ls) ∧
    S.M₃ m.M S.name (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃ m.M) φ ρ (S.indInfo.type.instL S.indInfo.lparams ls) := by
  obtain ⟨T, hT⟩ := hok.2.2.2.1
  simp only [indInfo] at hls ⊢
  have hsound := (infer_sound (m := m₃ hs m hok) (φ := Level.substVal φ S.lparams ls) hT ρ
    (Sat_nil _ _ _)).1
  rw [m₃_M] at hsound
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr hsound, ?_⟩
  rw [interp_instL, (reader₃ hok m.M φ).R.fam, ← lparams_map_substVal hok φ hls]
  exact (reader₃ hok m.M (Level.substVal φ S.lparams ls)).R.famSet_mem hok.scoped ρ

/-- The environment with the former has a model at the final
assignment. -/
noncomputable def mInd : EnvModel V (S.envInd env) where
  M := S.M₃ m.M
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · rename_i h
      subst h
      cases hfind
      exact type_ok_ind hs m hok φ ρ hls
    · exact (m₃ hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo, ConstInfo.value?, ConstKind.value?] at hv
    · exact (m₃ hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo] at hkind
    · rw [S.envInd_find?] at hcij
      split at hcij
      · rename_i h
        -- the constructor of a stored rule is stored, so it is not the fresh former
        exfalso
        have := ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
        rw [h, hok.freshI] at this
        simp at this
      · exact (m₃ hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij

theorem mInd_M : (mInd hs m hok).M = S.M₃ m.M := rfl

/-- A constructor's type is well-denoted at every valuation. -/
theorem wd_ctorType {c : CtorSpec} (hc : c ∈ S.ctors) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted (S.M₃ m.M) φ ρ (S.ctorType c) := by
  obtain ⟨T, hT⟩ := (hok.2.2.2.2.1 c hc).1
  have := (infer_sound (m := mInd hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mInd_M] at this

/-! ## The domains met along a fitting instance are members -/

omit [LevelOracle] hs m hok in
theorem fieldCtx_drop (S : IndSpec) : ∀ (fields : List Field) (n : Nat),
    (S.fieldCtx fields).drop n = S.fieldCtx (fields.drop n)
  | [], _ => by simp [fieldCtx]
  | _ :: _, 0 => rfl
  | _ :: fields, n + 1 => by simp [fieldCtx, fieldCtx_drop S fields n]

omit [LevelOracle] hs m hok in
theorem FitsVals_drop (M' : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {Γ : List Expr} {vs : List V} (n : Nat), FitsVals M' φ ρ Γ vs → FitsVals M' φ ρ (Γ.drop n) (vs.drop n)
  | _, _, 0, h => h
  | [], [], _ + 1, _ => trivial
  | _ :: Γ, _ :: vs, n + 1, h => FitsVals_drop M' φ (Γ := Γ) (vs := vs) n h.1
  | [], _ :: _, _ + 1, h => h.elim
  | _ :: _, [], _ + 1, h => h.elim

omit [LevelOracle] hs m hok in
theorem Sat_drop (M' : Name → List Nat → V) (φ : Name → Nat) :
    ∀ {Γ : List Expr} {ρ : Nat → V} (n : Nat), Sat M' φ Γ ρ → Sat M' φ (Γ.drop n) (shiftE n 0 ρ)
  | _, ρ, 0, h => by rwa [shiftE_zero_zero]
  | [], _, _ + 1, _ => trivial
  | _ :: Γ, ρ, n + 1, h => by
    have := Sat_drop M' φ (Γ := Γ) (ρ := fun i => ρ (i + 1)) n h.1
    rw [List.drop_succ_cons]
    rw [shiftE_zero] at this ⊢
    have e : (fun i => ρ (i + (n + 1))) = fun i => ρ (i + n + 1) := by
      funext i; rw [Nat.add_assoc]
    rw [e]; exact this

omit [LevelOracle] hs m hok in
theorem CtxWD_append_of (M' : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} {Δ : List Expr}
    (hΔ : CtxWD M' φ ρ Δ) :
    ∀ {Γ : List Expr}, (∀ ws, FitsVals M' φ ρ Δ ws → CtxWD M' φ (consList ws ρ) Γ) →
      CtxWD M' φ ρ (Γ ++ Δ)
  | [], _ => hΔ
  | A :: Γ, h => by
    rw [List.cons_append, CtxWD_cons]
    refine ⟨CtxWD_append_of M' φ hΔ fun ws hws => by
      have h' := h ws hws; rw [CtxWD_cons] at h'; exact h'.1, ?_⟩
    intro vs hvs
    have hl := FitsVals_length M' φ hvs
    obtain ⟨vs₁, ws, rfl, hlen⟩ : ∃ vs₁ ws, vs = vs₁ ++ ws ∧ vs₁.length = Γ.length := by
      refine ⟨vs.take Γ.length, vs.drop Γ.length, (List.take_append_drop _ _).symm, ?_⟩
      simp at hl; simp [hl]
    obtain ⟨hws, hvs₁⟩ := (FitsVals_append M' φ hlen).mp hvs
    rw [consList_append]
    have h' := h ws hws; rw [CtxWD_cons] at h'
    exact h'.2 vs₁ hvs₁

omit [LevelOracle] hs m hok in
theorem CtxWD_getElem? (M' : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {Γ : List Expr} {i : Nat} {A : Expr}, CtxWD M' φ ρ Γ → Γ[i]? = some A →
      ∀ vs, FitsVals M' φ ρ (Γ.drop (i + 1)) vs → WellDenoted M' φ (consList vs ρ) A
  | [], _, _, _, h, _, _ => by simp at h
  | B :: Γ, 0, A, hwd, hA, vs, hvs => by
    simp at hA; subst hA
    rw [CtxWD_cons] at hwd
    exact hwd.2 vs hvs
  | _ :: Γ, i + 1, A, hwd, hA, vs, hvs => by
    rw [CtxWD_cons] at hwd
    exact CtxWD_getElem? M' φ (Γ := Γ) (i := i) hwd.1 (by simpa using hA) vs hvs

omit [LevelOracle] hs m hok in
theorem CtxAgree_drop {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat} {ρ₁ ρ₂ : Nat → V}
    {Γ : List Expr} (h : CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ Γ) (n : Nat) :
    CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ (Γ.drop n) := by
  intro i A hA vs hvs
  rw [List.getElem?_drop] at hA
  refine h (n + i) A hA vs ?_
  rw [List.drop_drop] at hvs
  rw [show n + i + 1 = n + (i + 1) by omega]
  exact hvs

/-- The sort of a field's domain bounds its set (the universe bound),
read off the checker's sort facts at a satisfying environment. -/
theorem univ_of_sort {Γ : List Expr} {A s : Expr} {v : Level}
    (hI : Infer (S.envInd env) Γ A s) (hR : Red (S.envInd env) Γ s (.sort v)) (φ : Name → Nat)
    {ρ : Nat → V} (hsat : Sat (S.M₃ m.M) φ Γ ρ) :
    interp (S.M₃ m.M) φ ρ A ∈ˢ (univ (Level.eval φ v) : V) := by
  obtain ⟨-, hws, hmem⟩ := infer_sound (m := mInd hs m hok) (φ := φ) hI ρ hsat
  obtain ⟨-, heq⟩ := red_sound (m := mInd hs m hok) (φ := φ) hR ρ hsat hws
  rw [mInd_M] at hmem heq
  rw [heq, interp_sort] at hmem
  exact hmem

/-- **The domains met along a fitting instance are members of the
result universe**, from the checker's universe bound on every field
and every binder of a reflexive field's telescope. -/
theorem domsBounded_of (φ : Name → Nat) (ρ : Nat → V) {ps : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) :
    S.DomsBounded m.M (S.lparams.map φ) ps := by
  intro hz c hc fs hfit k f hpos hk
  have R := (reader₃ hok m.M φ).R
  have hS := hok.scoped
  -- the constructor's type is well-denoted: its contexts are
  have hwd := wd_ctorType hs m hok hc φ ρ
  unfold ctorType at hwd
  rw [WellDenoted_mkPis] at hwd
  obtain ⟨hctx, -⟩ := hwd
  obtain ⟨hpar, hfld⟩ := CtxWD_append' hctx
  have hp' : FitsVals (S.M₃ m.M) φ ρ S.params ps := (R.fits_params hS).mpr hp
  have hwdF := hfld ps hp'
  have hsc := (hS.2.2.2.1 c hc).1
  have hfs := (R.fits_fieldCtx hS hsc hps hp hwdF (vs := fs)).1.mpr hfit
  have hl := S.FitsFields_length m.M _ hfit
  -- the position, and the field's own context satisfied
  have hki : c.fields.length - 1 - k + 1 = c.fields.length - k := by omega
  have hkk : c.fields.length - 1 - (c.fields.length - 1 - k) = k := by omega
  have hget : (S.fieldCtx c.fields)[c.fields.length - 1 - k]? = some (S.fieldDom k f) := by
    rw [S.fieldCtx_getElem?, hpos, hkk]; rfl
  have hsc' : S.fieldScoped env k f := by
    have := hsc _ f hpos
    rw [hkk] at this
    exact this
  have hearlier : earlier fs k = fs.drop (c.fields.length - 1 - k + 1) := by
    rw [earlier, hl, hki]
  have hel : (earlier fs k).length = k := by simp [earlier, hl]; omega
  have hfsE : FitsVals (S.M₃ m.M) φ (consList ps ρ)
      ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1)) (earlier fs k) := by
    rw [hearlier]; exact FitsVals_drop _ _ _ hfs
  have hsatF : Sat (S.M₃ m.M) φ ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1) ++ S.params)
      (consList (earlier fs k ++ ps) ρ) := by
    refine Sat_of_fits _ _ (CtxWD_append_of _ _ hpar fun ws hws => CtxWD_drop _ _ _ (hfld ws hws)) ?_
    exact (FitsVals_append _ _ (by simp [hel, S.length_fieldCtx]; omega)).mpr ⟨hp', hfsE⟩
  -- the universe bound on the field
  have hz' : S.u₀ (S.lparams.map φ) ≠ 0 := fun h0 => by simp [(S.z_iff _).mpr h0] at hz
  have hu₀ := R.u₀_eq hS.2.2.1
  have hbound : ∀ {v : Level}, S.FieldBound v → Level.eval φ v ≤ S.u₀ (S.lparams.map φ) := by
    intro v hb
    rcases hb with h | h
    · exfalso
      have := (LevelOracle.eq_iff _ _).mp h φ
      simp only [Level.eval_zero] at this
      exact hz' (by rw [hu₀, this])
    · rw [hu₀]; exact (LevelOracle.le_iff _ _).mp h φ
  cases f with
  | recursive _ => trivial
  | ordinary A =>
    obtain ⟨s, v, hI, hR, hb, -⟩ := (hok.2.2.2.2.1 c hc).2.1 _ A hget
    have hmem := univ_of_sort hs m hok hI hR φ hsatF
    rw [consList_append] at hmem
    rw [R.read hsc' (vs := earlier fs k) (ps := ps) (ρ := ρ) (by simp [hel, hps]; omega)] at hmem
    exact univ_mono (hbound hb) hmem
  | reflexive tele es =>
    -- the telescope is well-denoted at every fitting frame
    have hwdT : ∀ ws ws', FitsVals (S.M₃ m.M) φ ρ S.params ws →
        FitsVals (S.M₃ m.M) φ (consList ws ρ)
          ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1)) ws' →
        CtxWD (S.M₃ m.M) φ (consList ws' (consList ws ρ)) tele := by
      intro ws ws' hws hws'
      have := CtxWD_getElem? _ _ (hfld ws hws) hget ws' hws'
      simp only [fieldDom] at this
      rw [WellDenoted_mkPis] at this
      exact this.1
    have hagT := R.agree_tele hsc'.1 hel hps (ρ := ρ)
    refine toTeleS_bounded_of m.M (S.ψ _) _ tele.reverse _ fun t T hT ys hys => ?_
    have ht : t < tele.length := by
      have := (List.getElem?_eq_some_iff.mp hT).1; simpa using this
    rw [List.getElem?_reverse ht] at hT
    rw [List.reverse_reverse, List.length_reverse] at hys
    have hdrop : tele.drop (tele.length - 1 - t + 1) = tele.drop (tele.length - t) := by
      congr 1; omega
    obtain ⟨s, w, hI, hR, hb⟩ := (hok.2.2.2.2.1 c hc).2.2.1 _ tele es hpos _ T hT
    rw [hdrop] at hI hR
    -- the telescope entry's context, satisfied
    have hys' : FitsVals (S.M₃ m.M) φ (consList (earlier fs k) (consList ps ρ)) (tele.drop (tele.length - t)) ys :=
      (FitsVals_congr₂ (CtxAgree_drop hagT _)).mpr hys
    have hyl : ys.length = t := by
      have := FitsVals_length _ _ hys'; simp at this; omega
    have hsat : Sat (S.M₃ m.M) φ (tele.drop (tele.length - t) ++
        (S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1) ++ S.params)
        (consList (ys ++ earlier fs k ++ ps) ρ) := by
      refine Sat_of_fits _ _ ?_ ?_
      · refine CtxWD_append_of _ _ hpar fun ws hws => ?_
        refine CtxWD_append_of _ _ (CtxWD_drop _ _ _ (hfld ws hws)) fun ws' hws' => ?_
        rw [← hdrop]
        exact CtxWD_drop _ _ _ (hwdT ws ws' hws hws')
      · refine (FitsVals_append _ _ (by simp [hyl, hel, S.length_fieldCtx]; omega)).mpr ⟨hp', ?_⟩
        exact (FitsVals_append _ _ (by simp [hyl]; omega)).mpr ⟨hfsE, hys'⟩
    have hmem := univ_of_sort hs m hok hI hR φ hsat
    rw [consList_append, consList_append] at hmem
    rw [← consList_append,
      R.read (hsc'.1 _ T hT) (vs := ys ++ earlier fs k) (ps := ps) (ρ := ρ)
        (by simp [hyl, hel, hps]; omega), consList_append] at hmem
    exact univ_mono (hbound hb) hmem

/-! ## Uniqueness of witnesses under the subsingleton criterion -/

omit [LevelOracle] hs m hok in
/-- A member of a product at a proposition is the point when the
body's members are. -/
theorem eq_pt_of_mem_piCtx_true (M' : Name → List Nat → V) (φ : Name → Nat) :
    ∀ {Γ : List Expr} {ρ : Nat → V} {G : (Nat → V) → V},
      (∀ ρ' y, y ∈ˢ G ρ' → y = pt) → ∀ {x : V}, x ∈ˢ piCtx M' φ true ρ Γ G → x = pt
  | [], _, _, hG, _, hx => hG _ _ hx
  | _ :: Γ, ρ, G, hG, x, hx => by
    rw [piCtx_cons] at hx
    exact eq_pt_of_mem_piCtx_true M' φ (Γ := Γ) (fun _ _ hy => eq_pt_of_mem_piR_true hy) hx

/-- An ordinary field's set is in the universe its sort names, at
fitting fields, and the checker's criteria on that sort hold. -/
theorem ordinary_univ (φ : Name → Nat) (ρ : Nat → V) {ps : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) {c : CtorSpec} (hc : c ∈ S.ctors)
    {fs : List V} (hfit : S.FitsFields m.M (S.lparams.map φ) (S.bound m.M (S.lparams.map φ))
      (S.Mem m.M (S.lparams.map φ)) ps c.fields fs) {k : Nat} {A : Expr}
    (hpos : c.fields[c.fields.length - 1 - k]? = some (.ordinary A)) (hk : k < c.fields.length) :
    ∃ v : Level, S.FieldBound v ∧ S.SubsingletonField v (c.fields.length - 1 - k) c.idx ∧
      interp m.M (S.ψ (S.lparams.map φ)) (consList (earlier fs k) (envP ps)) A ∈ˢ
        (univ (Level.eval φ v) : V) := by
  have R := (reader₃ hok m.M φ).R
  have hS := hok.scoped
  have hwd := wd_ctorType hs m hok hc φ ρ
  unfold ctorType at hwd
  rw [WellDenoted_mkPis] at hwd
  obtain ⟨hctx, -⟩ := hwd
  obtain ⟨hpar, hfld⟩ := CtxWD_append' hctx
  have hp' : FitsVals (S.M₃ m.M) φ ρ S.params ps := (R.fits_params hS).mpr hp
  have hwdF := hfld ps hp'
  have hsc := (hS.2.2.2.1 c hc).1
  have hfs := (R.fits_fieldCtx hS hsc hps hp hwdF (vs := fs)).1.mpr hfit
  have hl := S.FitsFields_length m.M _ hfit
  have hki : c.fields.length - 1 - k + 1 = c.fields.length - k := by omega
  have hkk : c.fields.length - 1 - (c.fields.length - 1 - k) = k := by omega
  have hget : (S.fieldCtx c.fields)[c.fields.length - 1 - k]? = some A := by
    rw [S.fieldCtx_getElem?, hpos, hkk]; rfl
  have hsc' : S.fieldScoped env k (.ordinary A) := by
    have := hsc _ _ hpos
    rw [hkk] at this
    exact this
  have hearlier : earlier fs k = fs.drop (c.fields.length - 1 - k + 1) := by
    rw [earlier, hl, hki]
  have hel : (earlier fs k).length = k := by simp [earlier, hl]; omega
  have hfsE : FitsVals (S.M₃ m.M) φ (consList ps ρ)
      ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1)) (earlier fs k) := by
    rw [hearlier]; exact FitsVals_drop _ _ _ hfs
  have hsatF : Sat (S.M₃ m.M) φ ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1) ++ S.params)
      (consList (earlier fs k ++ ps) ρ) := by
    refine Sat_of_fits _ _ (CtxWD_append_of _ _ hpar fun ws hws => CtxWD_drop _ _ _ (hfld ws hws)) ?_
    exact (FitsVals_append _ _ (by simp [hel, S.length_fieldCtx]; omega)).mpr ⟨hp', hfsE⟩
  obtain ⟨s, v, hI, hR, hb, hsub⟩ := (hok.2.2.2.2.1 c hc).2.1 _ A hget
  refine ⟨v, hb, hsub, ?_⟩
  have hmem := univ_of_sort hs m hok hI hR φ hsatF
  rw [consList_append] at hmem
  rw [R.read hsc' (vs := earlier fs k) (ps := ps) (ρ := ρ) (by simp [hel, hps]; omega)] at hmem
  exact hmem

/-- **Uniqueness of the fibre's witness** under the subsingleton
criterion: at a proposition with a large eliminator the checker admits
at most one constructor, every field of which is a proposition or one
of the indices. -/
theorem uniq_of (φ : Name → Nat) (hz : S.z (S.lparams.map φ) = true) (hlarge : S.large = true) :
    S.Uniq m.M (S.lparams.map φ) := by
  have hnp : ¬ S.NeverProp := fun h => by
    have := (LevelOracle.le_iff _ _).mp h (S.ψ (S.lparams.map φ))
    simp only [Level.eval_succ, Level.eval_zero] at this
    have h0 := (S.z_iff _).mp hz
    unfold u₀ at h0
    omega
  refine S.uniq_of_subsingleton m.M _ ⟨hok.2.2.2.2.2.1 hlarge hnp, ?_⟩
  intro c hc ps hp fs hfit k hk
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hp; simpa [nP] using this
  obtain ⟨f, hpos⟩ : ∃ f, c.fields[c.fields.length - 1 - k]? = some f :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩
  have hget := S.FitsFields_get m.M _ hfit hpos hk
  cases f with
  | recursive es =>
    left
    simp only [fieldSet, hz] at hget
    exact (mem_fibreR_true.mp hget).1
  | reflexive tele es =>
    left
    simp only [fieldSet, hz] at hget
    exact eq_pt_of_mem_piCtx_true _ _ (fun _ _ hy => (mem_fibreR_true.mp hy).1) hget
  | ordinary A =>
    obtain ⟨v, -, hsub, hmem⟩ := ordinary_univ hs m hok φ base hps hp hc hfit hpos hk
    rcases hsub hlarge hnp with hv | hidx
    · left
      have := (LevelOracle.eq_iff _ _).mp hv φ
      simp only [Level.eval_zero] at this
      rw [this] at hmem
      simp only [fieldSet] at hget
      exact eq_pt_of_mem_univ_zero hmem hget
    · right; exact hidx

/-! ## The constructors' type laws and the model with the constructors -/

omit [IndLib V] hs m in
/-- No field reads an earlier recursive field. -/
theorem noRecDep : S.NoRecDep := fun c hc => (hok.scoped.2.2.2.1 c hc).2.1

/-- **A constructor's type law.** -/
theorem type_ok_ctor {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) (φ : Name → Nat)
    (ρ : Nat → V) {ls : List Level} (hls : ls.length = (S.ctorInfo c).lparams.length) :
    WellDenoted (S.M₃ m.M) φ ρ ((S.ctorInfo c).type.instL (S.ctorInfo c).lparams ls) ∧
    S.M₃ m.M c.name (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃ m.M) φ ρ ((S.ctorInfo c).type.instL (S.ctorInfo c).lparams ls) := by
  simp only [ctorInfo] at hls ⊢
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr (wd_ctorType hs m hok hcm _ ρ), ?_⟩
  rw [interp_instL, (reader₃ hok m.M φ).ctor j c hc, ← lparams_map_substVal hok φ hls]
  exact (reader₃ hok m.M (Level.substVal φ S.lparams ls)).ctorSet_mem hok.scoped hok.freshI hc
    (wd_ctorType hs m hok hcm _ ρ) (noRecDep hok)
    fun ps hp => domsBounded_of hs m hok _ ρ (by have := FitsVals_length _ _ hp; simpa [nP] using this) hp

/-- The environment with the former and the constructors has a model
at the final assignment. -/
noncomputable def mCtors : EnvModel V (S.envCtors env) where
  M := S.M₃ m.M
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · rename_i j c' hco
      cases hfind
      obtain ⟨hc', rfl⟩ := S.ctorOf?_some hco
      exact type_ok_ctor hs m hok hc' φ ρ hls
    · exact (mInd hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · cases hfind; simp [ctorInfo, ConstInfo.value?, ConstKind.value?] at hv
    · exact (mInd hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · cases hfind; simp [ctorInfo] at hkind
    · rw [S.envCtors_find? env hok.nodup_ctors] at hcij
      -- a stored rule's constructor is stored in `env`, so it is not one of the new ones
      have hstored : ((S.envInd env).find? rl.ctor).isSome := by
        rw [S.envInd_find?] at hfind ⊢
        split at hfind
        · cases hfind; simp [indInfo] at hkind
        · have := ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
          split
          · simp
          · exact this
      have hnone : S.ctorOf? rl.ctor = none := by
        apply S.ctorOf?_none
        intro c' hc' h
        rw [S.envInd_find?] at hstored
        split at hstored
        · rename_i h'
          rw [h'] at h
          exact hok.name_not_mem (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', h⟩))
        · rw [← h, hok.fresh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨c', hc', rfl⟩)))] at hstored
          simp at hstored
      rw [hnone] at hcij
      exact (mInd hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij

theorem mCtors_M : (mCtors hs m hok).M = S.M₃ m.M := rfl

/-- The recursor's type is well-denoted at every valuation. -/
theorem wd_recType (φ : Name → Nat) (ρ : Nat → V) : WellDenoted (S.M₃ m.M) φ ρ S.recType := by
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2
  have := (infer_sound (m := mCtors hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtors_M] at this

/-- A rule's type is well-denoted at every valuation. -/
theorem wd_ruleType {c : CtorSpec} (hc : c ∈ S.ctors) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted (S.M₃ m.M) φ ρ (S.ruleType c) := by
  obtain ⟨T, hT⟩ := (hok.2.2.2.2.1 c hc).2.2.2
  have := (infer_sound (m := mCtors hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtors_M] at this

/-! ## The recursor's type law -/

omit [IndLib V] [LevelOracle] hs m hok in
/-- A small eliminator's level is zero, so a nonzero elimination level
comes from a large eliminator. -/
theorem large_of_q_false {φ' : Name → Nat} (hq : S.q.holds φ' = false) : S.large = true := by
  cases hl : S.large with
  | true => rfl
  | false =>
    rw [S.q_holds] at hq
    unfold ℓ at hq
    rw [hl] at hq
    simp at hq

omit [IndLib V] [LevelOracle] hs m hok in
/-- The recursor's valuation at concrete levels agrees with the
substituted one on its level parameters. -/
theorem recVal_agree (φ : Name → Nat) {lsr : List Level} (hlsr : lsr.length = S.recLparams.length) :
    ∀ n ∈ S.recLparams, valOf S.recLparams (lsr.map (Level.eval φ)) n
      = Level.substVal φ S.recLparams lsr n :=
  fun _ hn => valOf_map_eval φ hlsr hn

omit [IndLib V] [LevelOracle] hs m hok in
theorem block_levels_eq (φ : Name → Nat) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.lparams.map (valOf S.recLparams (lsr.map (Level.eval φ)))
      = S.lparams.map (Level.substVal φ S.recLparams lsr) :=
  List.map_congr_left fun n hn => recVal_agree φ hlsr n (S.lparams_sub_recLparams hn)

omit [IndLib V] [LevelOracle] hs m hok in
theorem recAgree_of (φ : Name → Nat) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    RecAgree (valOf S.recLparams (lsr.map (Level.eval φ))) (Level.substVal φ S.recLparams lsr) S :=
  Level.eval_congr (recVal_agree φ hlsr) S.ℓ_paramsIn

omit [LevelOracle] hs m hok in
/-- The recursor's body, read at values of its context. -/
theorem recF_read (S : IndSpec) (M' : Name → List Nat → V) (ls : List Nat) (q : Bool)
    {t : V} {is mins : List V} {m : V} {ps : List V} (hi : is.length = S.nI)
    (hmins : mins.length = S.n) (hps : ps.length = S.nP) (X : Nat → V) :
    S.recSem M' ls q (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 (consList (t :: is ++ mins ++ [m] ++ ps) X)))
        (consList (t :: is ++ mins ++ [m] ++ ps) X (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 (consList (t :: is ++ mins ++ [m] ++ ps) X)))
        (readEnv S.nI (shiftE 1 0 (consList (t :: is ++ mins ++ [m] ++ ps) X)))
        (consList (t :: is ++ mins ++ [m] ++ ps) X 0)
      = S.recSem M' ls q ps m mins is t := by
  have e : consList (t :: is ++ mins ++ [m] ++ ps) X
      = consList (t :: is) (consList mins (consList [m] (consList ps X))) := by
    simp [consList_append]
  have hs1 : ∀ Y : Nat → V, shiftE 1 0 (consList (t :: is) Y) = consList is Y :=
    fun Y => shiftE_consList' (vs := [t]) rfl (consList is Y)
  have hs2 : ∀ Y : Nat → V, shiftE (1 + S.nI) 0 (consList (t :: is) Y) = Y :=
    fun Y => shiftE_consList' (by simp [hi]; omega) Y
  have hs3 : ∀ Y : Nat → V,
      shiftE (1 + S.nI + S.n + 1) 0 (consList (t :: is) (consList mins (consList [m] Y))) = Y := by
    intro Y
    rw [← consList_append, ← consList_append]
    exact shiftE_consList' (by simp [hi, hmins]; omega) Y
  have hm : consList (t :: is) (consList mins (consList [m] (consList ps X))) (1 + S.nI + S.n) = m := by
    rw [← consList_append, show 1 + S.nI + S.n = 0 + (t :: is ++ mins).length by simp [hi, hmins]; omega,
      consList_ge]
    rfl
  simp only [e]
  rw [hs1, hs2, hs3, hm, readEnv_consList hi, readEnv_consList hmins, readEnv_consList hps]
  rfl

omit [LevelOracle] hs m hok in
/-- The recursor type's body `motive indices major`, read at values of
its context. -/
theorem read_recBody (S : IndSpec) (M' : Name → List Nat → V) (φ' : Name → Nat)
    {t : V} {is mins : List V} {m : V} {ps : List V} (hi : is.length = S.nI)
    (hmins : mins.length = S.n) (X : Nat → V) :
    interp M' φ' (consList (t :: is ++ mins ++ [m] ++ ps) X)
        (Expr.mkAppN (.bvar (1 + S.nI + S.n)) (Expr.varsAt 1 S.nI ++ [.bvar 0]))
      = appList m (is.reverse ++ [t]) := by
  have e : consList (t :: is ++ mins ++ [m] ++ ps) X
      = consList (t :: is) (consList mins (consList [m] (consList ps X))) := by
    simp [consList_append]
  have hs1 : ∀ Y : Nat → V, shiftE 1 0 (consList (t :: is) Y) = consList is Y :=
    fun Y => shiftE_consList' (vs := [t]) rfl (consList is Y)
  have hm : consList (t :: is) (consList mins (consList [m] (consList ps X))) (1 + S.nI + S.n) = m := by
    rw [← consList_append, show 1 + S.nI + S.n = 0 + (t :: is ++ mins).length by simp [hi, hmins]; omega,
      consList_ge]
    rfl
  rw [interp_mkAppN_appList, interp_bvar, List.map_append, interp_varsAt, List.map_singleton,
    interp_bvar, e, hm, hs1, readEnv_consList hi]
  rfl

/-- **The minors' typing gives `MinorOk`** for every constructor, from
the minors fitting their context — and the minor's application chain
along the fields and hypotheses is well-formed. -/
theorem minorOk_of_fits (φr : Name → Nat) (ρ : Nat → V) {ps : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φr)) base S.params ps) {m' : V}
    (hm : m' ∈ˢ interp (S.M₃ m.M) φr (consList ps ρ) S.motiveTy) {mins : List V}
    (hmins : mins.length = S.n)
    (hmn : FitsVals (S.M₃ m.M) φr (cons m' (consList ps ρ)) S.minorsCtx mins) :
    ∀ j c, S.ctors[j]? = some c →
      ∀ fs, S.FitsFields m.M (S.lparams.map φr) (S.bound m.M (S.lparams.map φr))
          (S.Mem m.M (S.lparams.map φr)) ps c.fields fs →
        ∀ ihs, ListRel (S.IhTyped m.M (S.lparams.map φr) (S.q.holds φr) ps m' fs) c.recFields ihs →
          appList (S.minorAt mins j) (fs.reverse ++ ihs) ∈ˢ
            appList m' ((S.idxVals m.M (S.lparams.map φr) (consList fs (envP ps)) c.idx).reverse ++
              [S.ctorVal (S.lparams.map φr) j fs]) ∧
          SpineOk (S.minorAt mins j) (fs.reverse ++ ihs) := by
  intro j c hc
  have hS := hok.scoped
  have R₃ := reader₃ hok m.M φr
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
  rw [minorsCtx_eq] at hmn
  have hmem := S.fits_minorsFrom S.ctors 0 _ mins hmn j c hc
  rw [Nat.zero_add] at hmem
  have hminsE : (mins.drop (S.n - j)).length = j := by simp [hmins]; omega
  have hidx := R₃.R.idxFit_of_wd hS hcm (wd_ctorType hs m hok hcm φr ρ) hps hp
  exact R₃.minorOk hS hok.freshI hc hminsE hps hp hidx.1 (fun fs hfit => (hidx.2 fs hfit).2.2)
    (R₃.R.motiveOk_of_mem hS hps hp hm) (noRecDep hok) (domsBounded_of hs m hok φr ρ hps hp) hmem

/-- **The recursor's set is in the recursor's type.** -/
theorem recSet_mem (φ : Name → Nat) (ρ : Nat → V) {lsr : List Level}
    (hlsr : lsr.length = S.recLparams.length) :
    S.recSet m.M (lsr.map (Level.eval φ)) ∈ˢ
      interp (S.M₃ m.M) (Level.substVal φ S.recLparams lsr) ρ S.recType := by
  have hS := hok.scoped
  have hagr := recAgree_of (S := S) φ hlsr
  have hval : ∀ n ∈ S.lparams, valOf S.recLparams (lsr.map (Level.eval φ)) n
      = Level.substVal φ S.recLparams lsr n :=
    fun n hn => recVal_agree φ hlsr n (S.lparams_sub_recLparams hn)
  have hls := block_levels_eq (S := S) φ hlsr
  have R₃ := reader₃ hok m.M (Level.substVal φ S.recLparams lsr)
  have R₂ := reader₂ hok m.M (Level.substVal φ S.recLparams lsr) hval
  have hwdC : ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals m.M (S.ψ (S.lparams.map (Level.substVal φ S.recLparams lsr))) base S.params ps →
      CtxWD (S.M₃ m.M) (Level.substVal φ S.recLparams lsr) (consList ps ρ) (S.fieldCtx c.fields) :=
    fun c hc ps hps hp => (R₃.R.idxFit_of_wd hS hc (wd_ctorType hs m hok hc _ ρ) hps hp).1
  have hagree := R₂.agree_recCtx hS R₃ hagr hok.freshI base ρ hwdC
  rw [recType_eq, interp_mkPis]
  show lamCtx (S.M₂ m.M) (valOf S.recLparams (lsr.map (Level.eval φ)))
      (S.q.holds (valOf S.recLparams (lsr.map (Level.eval φ)))) base S.recCtx
      (fun ρ' => S.recSem m.M (S.lparams.map (valOf S.recLparams (lsr.map (Level.eval φ))))
        (S.q.holds (valOf S.recLparams (lsr.map (Level.eval φ))))
        (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)) ∈ˢ _
  rw [hls, hagr.q_holds]
  rw [lamCtx_congr₂ hagree (G := fun ρ' =>
      S.recSem m.M (S.lparams.map (Level.substVal φ S.recLparams lsr))
        (S.q.holds (Level.substVal φ S.recLparams lsr))
        (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0))
    fun vs hvs => by
      obtain ⟨t, is, mins, m', ps, rfl, hi, hmins, hps⟩ := S.fits_recCtx_split hvs
      rw [recF_read S m.M _ _ hi hmins hps, recF_read S m.M _ _ hi hmins hps]]
  refine lamCtx_mem_piCtx' _ _ (by simp [recCtx]) ?_ ?_
  · intro hq vs hvs
    obtain ⟨t, is, mins, m', ps, rfl, hi, hmins, hps⟩ := S.fits_recCtx_split hvs
    obtain ⟨hp, hm, hmn, his, ht⟩ := (R₃.R.fits_recCtx_iff hS hi hmins hps).mp hvs
    rw [recF_read S m.M _ _ hi hmins hps, read_recBody S _ _ hi hmins]
    have hu : S.Uniq m.M (S.lparams.map (Level.substVal φ S.recLparams lsr)) :=
      fun hz => uniq_of hs m hok _ hz (large_of_q_false hq) hz
    exact S.recSem_mem m.M _ _ hu hp m' mins
      (fun j c hc fs hfit ihs hihs => (minorOk_of_fits hs m hok _ ρ hps hp hm hmins hmn j c hc fs hfit ihs hihs).1)
      (fun h => nomatch hq.symm.trans h) ht
  · intro hq vs hvs
    obtain ⟨t, is, mins, m', ps, rfl, hi, hmins, hps⟩ := S.fits_recCtx_split hvs
    obtain ⟨hp, hm, hmn, his, ht⟩ := (R₃.R.fits_recCtx_iff hS hi hmins hps).mp hvs
    rw [read_recBody S _ _ hi hmins]
    -- at a proposition the motive's fibres are truth values
    have hz := S.q_holds (Level.substVal φ S.recLparams lsr)
    rw [hq, Bool.true_eq, beq_iff_eq] at hz
    have hmo : ∀ is t, t ∈ˢ S.Fam m.M (S.lparams.map (Level.substVal φ S.recLparams lsr)) ps is →
        appList m' (is.reverse ++ [t]) ∈ˢ (univ 0 : V) := fun is t ht => by
      rw [← hz]
      refine R₃.R.motiveOk_of_mem hS hps hp hm is (S.idx_fits_of_mem_Fam m.M _ ?_ ht) t ht
      intro j c hc fs hfit
      have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
      exact ((R₃.R.idxFit_of_wd hS hcm (wd_ctorType hs m hok hcm _ ρ) hps hp).2 fs hfit).2.2
    obtain ⟨v, hv⟩ := S.motive_inhabited m.M _ _ m' mins
      (fun j c hc fs hfit ihs hihs => (minorOk_of_fits hs m hok _ ρ hps hp hm hmins hmn j c hc fs hfit ihs hihs).1)
      (fun _ => hmo) ht
    exact eq_one_of_mem_univ_zero (hmo is t ht) hv

/-- **The recursor's type law.** -/
theorem type_ok_rec (φ : Name → Nat) (ρ : Nat → V) {ls : List Level}
    (hls : ls.length = S.recInfo.lparams.length) :
    WellDenoted (S.M₃ m.M) φ ρ (S.recInfo.type.instL S.recInfo.lparams ls) ∧
    S.M₃ m.M S.recName (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃ m.M) φ ρ (S.recInfo.type.instL S.recInfo.lparams ls) := by
  simp only [recInfo] at hls ⊢
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr (wd_recType hs m hok _ ρ), ?_⟩
  rw [interp_instL]
  have : S.M₃ m.M S.recName (ls.map (Level.eval φ)) = S.recSet m.M (ls.map (Level.eval φ)) := by
    simp [M₃]
  rw [this]
  exact recSet_mem hs m hok φ ρ hls

end IndSpec

end Fragment
