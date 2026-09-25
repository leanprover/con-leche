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

end IndSpec

end Fragment
