module

public import Fragment.BlockModel
public import Fragment.NestRead
public import Fragment.NestScope
public import Fragment.InstallIota

@[expose] public section

/-!
# Installing a nested block

From the checker's verdict `OkN` (`Decl.lean`) and a block model of the
environment (`BlockModel.lean`): the final assignment `M₃N` — the
former's family, the constructors' graphs, the two recursors — is a
model of the installed environment, and the block laws survive.

The steps, in order:

* **the container's facts** (`nestFacts`): the container's block law in
  the model, the nested checks (N3, the member domain's sort, the
  class's arguments fit — read off the class having a sort in the
  environment holding the former, through a model of that environment
  which needs nothing of the class yet, `mIndN`) and the scope give
  `NestFacts`, hence the class's guard `ContGood` (`contGood_of`) and
  the class's laws (`classLaws_of`);
* **the constructors**: as for a plain block, with a container field's
  value in the class's bound (`contInBound_of`);
* **the recursors**: their sets are in their types (`recSetN_mem`,
  `rec1Set_mem`: the recursors' typing `recSemN_mem`, or at a
  proposition the motives' inhabitation `motive_inhabitedN`, through
  the recursors' contexts read in both the block's own reader and the
  final one);
* **the ι laws**: of `T.rec`'s rules as for a plain block, with a
  container field's hypothesis read as a `T.rec_1` call; of `T.rec_1`'s
  rules in both forms (`RecRuleLaw` for `Red.iota`, `RecRuleLawN` for
  `Red.iotaNested`), the major's membership in the class pinning its
  fields (`ClassLaws.inv`).

Con-leche: `Model/Inductives/DeclNative.lean` with the class rows of
`GenClsSem.lean` and `ClassGenUniq.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

namespace IndSpec

variable {env : Env} {S : IndSpec} {N : NestInfo}

/-! ## The setting -/

theorem OkN.nest (hok : S.OkN N env) : S.nest = some N := hok.1

theorem OkN.nodup (hok : S.OkN N env) : (S.name :: S.recName :: N.aux :: S.ctors.map (·.name)).Nodup :=
  hok.2.1

theorem OkN.fresh (hok : S.OkN N env) :
    ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none := hok.2.2.1

theorem OkN.freshI (hok : S.OkN N env) : env.find? S.name = none := hok.fresh _ (by simp)

theorem OkN.scoped (hok : S.OkN N env) : S.Scoped env := hok.2.2.2.1

theorem OkN.nestScoped (hok : S.OkN N env) : S.NestScoped env := hok.scoped.2.2.2.2.2.2

theorem OkN.nodup_ctors (hok : S.OkN N env) : (S.ctors.map (·.name)).Nodup :=
  hok.nodup.of_cons.of_cons.of_cons

theorem OkN.name_ne_rec (hok : S.OkN N env) : S.name ≠ S.recName := by
  have := (List.nodup_cons.mp hok.nodup).1
  intro h; apply this; rw [h]; exact List.mem_cons_self

theorem OkN.name_ne_aux (hok : S.OkN N env) : S.name ≠ N.aux := by
  have := (List.nodup_cons.mp hok.nodup).1
  intro h; apply this; rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem OkN.rec_ne_aux (hok : S.OkN N env) : S.recName ≠ N.aux := by
  have := (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).1
  intro h; apply this; rw [h]; exact List.mem_cons_self

theorem OkN.ctor_ne_rec (hok : S.OkN N env) {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) :
    c.name ≠ S.recName := by
  have := (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).1
  intro h; apply this; rw [← h]
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, List.mem_of_getElem? hc, rfl⟩)

theorem OkN.ctor_ne_aux (hok : S.OkN N env) {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) :
    c.name ≠ N.aux := by
  have := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).2).1
  intro h; apply this; rw [← h]
  exact List.mem_map.mpr ⟨c, List.mem_of_getElem? hc, rfl⟩

theorem OkN.ctorOf?_name (hok : S.OkN N env) : S.ctorOf? S.name = none := by
  apply S.ctorOf?_none
  intro c hc h
  exact (List.nodup_cons.mp hok.nodup).1
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, h⟩)))

theorem OkN.ctorOf?_rec (hok : S.OkN N env) : S.ctorOf? S.recName = none := by
  apply S.ctorOf?_none
  intro c hc h
  exact (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).1
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, h⟩))

theorem OkN.ctorOf?_aux (hok : S.OkN N env) : S.ctorOf? N.aux = none := by
  apply S.ctorOf?_none
  intro c hc h
  exact (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hok.nodup).2).2).1
    (List.mem_map.mpr ⟨c, hc, h⟩)

/-- The container's stored specification is `N.K.spec`. -/
theorem OkN.K_stored (hok : S.OkN N env) :
    ∃ ci, env.find? N.K.name = some ci ∧ ci.kind = .induct N.nPK 0 (N.K.ctors.map (·.name)) N.K.spec :=
  hok.2.2.2.2.2.2.1

/-- The large eliminator of a nested block is on a never-`Prop` sort. -/
theorem OkN.large_never (hok : S.OkN N env) : S.large = true → S.NeverProp :=
  hok.2.2.2.2.2.2.2.2.2.2.1

/-- The final assignment agrees with the old one on the stored
constants. -/
theorem agree_M₃N (hok : S.OkN N env) (M : Name → List Nat → V) : AgreeOn env M (S.M₃N M N) := by
  intro n hn ls
  have hne : ∀ x ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), n ≠ x := by
    intro x hx h
    subst h
    rw [hok.fresh n hx] at hn
    simp at hn
  simp only [M₃N, M₂, M₁]
  rw [if_neg (hne _ (by simp)), if_neg (hne _ (by simp))]
  rw [S.ctorOf?_none fun c hc h => hne c.name
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨c, hc, rfl⟩)))) h.symm]
  rw [if_neg (hne _ (by simp))]

/-- The final assignment reads the former and the constructors (a bare
reader, before the class's guard is known). -/
theorem reader₃₀ (hok : S.OkN N env) (M : Name → List Nat → V) (φ : Name → Nat) :
    S.Reader (env := env) M φ (S.M₃N M N) φ where
  agree := agree_M₃N hok M
  fam := fun ls' => by
    simp [M₃N, M₂, M₁, hok.name_ne_rec, hok.name_ne_aux, hok.ctorOf?_name]
  val := fun _ _ => rfl

/-- The block's own valuation, from concrete levels. -/
theorem lparams_map_substValN (hok : S.OkN N env) (φ : Name → Nat) {ls : List Level}
    (hls : ls.length = S.lparams.length) :
    S.lparams.map (Level.substVal φ S.lparams ls) = ls.map (Level.eval φ) :=
  map_substVal_eq φ hok.scoped.2.2.2.2.2.1 hls

/-! ## The container's facts -/

variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

omit hs in
/-- The container's block law, in the model. -/
theorem K_law : N.KS.Scoped env ∧ N.KS.NoCont ∧
    env.find? N.K.name = some N.KS.indInfo ∧
    (∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → env.find? c.name = some (N.KS.ctorInfo c)) ∧
    (∀ ls, m.M N.K.name ls = N.KS.famSet m.M ls) ∧
    (∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c →
      ∀ ls, m.M c.name ls = N.KS.ctorSet m.M ls j c) ∧
    (∀ ls ps, FitsVals m.M (N.KS.ψ ls) base N.KS.params ps → N.KS.DomsBounded m.M ls ps) := by
  obtain ⟨ci, hfind, hkind⟩ := hok.K_stored
  exact m.blocks N.K.name ci _ _ _ N.K.spec hfind hkind rfl

/-- The old model at the final assignment. -/
noncomputable def m₃N : EnvModel V env := m.toEnvModel.transport hs (S.M₃N m.M N) (agree_M₃N hok m.M)

theorem m₃N_M : (m₃N hs m hok).M = S.M₃N m.M N := rfl

/-- **The former's type law.** -/
theorem type_ok_indN (φ : Name → Nat) (ρ : Nat → V) {ls : List Level}
    (hls : ls.length = S.indInfo.lparams.length) :
    WellDenoted (S.M₃N m.M N) φ ρ (S.indInfo.type.instL S.indInfo.lparams ls) ∧
    S.M₃N m.M N S.name (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) φ ρ (S.indInfo.type.instL S.indInfo.lparams ls) := by
  obtain ⟨T, hT⟩ := hok.2.2.2.2.1
  simp only [indInfo] at hls ⊢
  have hsound := (infer_sound (m := m₃N hs m hok) (φ := Level.substVal φ S.lparams ls) hT ρ
    (Sat_nil _ _ _)).1
  rw [m₃N_M] at hsound
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr hsound, ?_⟩
  rw [interp_instL, (reader₃₀ hok m.M φ).fam, ← lparams_map_substValN hok φ hls]
  exact (reader₃₀ hok m.M (Level.substVal φ S.lparams ls)).famSet_mem hok.scoped ρ

/-- The environment with the former has a model at the final
assignment. -/
noncomputable def mIndN : EnvModel V (S.envInd env) where
  M := S.M₃N m.M N
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · rename_i h
      subst h
      cases hfind
      exact type_ok_indN hs m hok φ ρ hls
    · exact (m₃N hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo, ConstInfo.value?, ConstKind.value?] at hv
    · exact (m₃N hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo] at hkind
    · rw [S.envInd_find?] at hcij
      split at hcij
      · rename_i h
        exfalso
        have := ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
        rw [h, hok.freshI] at this
        simp at this
      · exact (m₃N hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij
  rec_rules_nested := fun c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij hcijk => by
    rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo] at hkind
    · rw [S.envInd_find?] at hcij
      split at hcij
      · rename_i h
        exfalso
        have := ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
        rw [h, hok.freshI] at this
        simp at this
      · exact (m₃N hs m hok).rec_rules_nested c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst
          hinst cij I nPc nf hcij hcijk

theorem mIndN_M : (mIndN hs m hok).M = S.M₃N m.M N := rfl

omit [LevelOracle] hs m hok in
/-- An abstraction over a level-instantiated context is the
abstraction over the context at the substituted valuation. -/
theorem lamCtx_instL (M : Name → List Nat → V) (φ : Name → Nat) (ps : List Name) (ls : List Level)
    (p : Bool) : ∀ (Γ : List Expr) (ρ : Nat → V) (F : (Nat → V) → V),
    lamCtx M φ p ρ (Γ.map (Expr.instL ps ls)) F = lamCtx M (Level.substVal φ ps ls) p ρ Γ F
  | [], _, _ => rfl
  | A :: Γ, ρ, F => by
    simp only [List.map_cons, lamCtx_cons]
    rw [lamCtx_instL M φ ps ls p Γ ρ]
    congr 1
    funext ρ'
    rw [interp_instL]

omit [LevelOracle] hs m hok in
theorem FitsVals_instL (M : Name → List Nat → V) (φ : Name → Nat) (ps : List Name) (ls : List Level) :
    ∀ (Γ : List Expr) (ρ : Nat → V) (vs : List V),
    FitsVals M φ ρ (Γ.map (Expr.instL ps ls)) vs ↔ FitsVals M (Level.substVal φ ps ls) ρ Γ vs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | A :: Γ, ρ, v :: vs => by
    simp only [List.map_cons, FitsVals_cons]
    rw [FitsVals_instL M φ ps ls Γ ρ vs, interp_instL]

omit hs m in
/-- The container's levels at the instantiation, at a valuation of the
block's parameters. -/
theorem lsK_eq_map (φ : Name → Nat) : S.lsK (S.lparams.map φ) N = N.lsK.map (Level.eval φ) := by
  unfold IndSpec.lsK
  refine List.map_congr_left fun l hl => ?_
  exact Level.eval_congr (fun n hn => (ψ_map_agree S φ n hn).symm)
    ((hok.nestScoped N hok.nest).2.2.2.1 l hl)

omit hs in
/-- The container's parameter context reads alike in the final
assignment at the substituted valuation and in the old model at the
container's valuation. -/
theorem agree_paramsK (φ : Name → Nat) (ρ : Nat → V) :
    CtxAgree (S.M₃N m.M N) m.M (Level.substVal φ N.K.lparams N.lsK)
      (N.KS.ψ (S.lsK (S.lparams.map φ) N)) ρ base N.KS.params := by
  have hKS := (K_law m hok).1
  have hlsK := hok.nestScoped N hok.nest |>.2.2.1
  rw [lsK_eq_map hok φ]
  intro i A hA vs hvs
  have hl := FitsVals_length _ _ hvs
  have hi : i < N.KS.params.length := (List.getElem?_eq_some_iff.mp hA).1
  refine interp_spec (hKS.1 i A hA) (fun c hc ls => (agree_M₃N hok m.M c hc ls).symm)
    (fun n hn => (valOf_map_eval φ (ps := N.K.lparams) hlsK hn).symm) fun j hj => ?_
  have hnP : N.KS.nP = N.KS.params.length := rfl
  exact consList_agree_lt j (by simp [hl, List.length_drop] at *; omega)

omit hs in
/-- **The container's set, read in the final assignment**: the
abstraction over its level-instantiated parameter context of its
family. -/
theorem famSetK_eq (φ : Name → Nat) :
    N.KS.famSet m.M (S.lsK (S.lparams.map φ) N)
      = lamCtx (S.M₃N m.M N) φ false base (N.KS.params.map (Expr.instL N.K.lparams N.lsK))
          fun ρ' => N.KS.Fam m.M (S.lsK (S.lparams.map φ) N) (readEnv N.KS.nP ρ') [] := by
  have hidx : N.KS.indices = [] := (hok.nestScoped N hok.nest).2.2.2.2.2.2.2.2.1.1
  unfold famSet
  rw [lamCtx_instL, hidx, List.nil_append]
  show lamCtx m.M _ false base N.KS.params _ = _
  refine (lamCtx_congr₂ (agree_paramsK m hok φ base) fun vs hvs => ?_).symm
  simp only [nI, hidx, List.length_nil, shiftE_zero_zero, readEnv]
  rfl

omit hs in
/-- The member parameter's domain level is the block's universe (the
check on the member domain's sort). -/
theorem memberLevel_eq (φ : Name → Nat) {ℓ : Level}
    (hℓp : N.K.params[N.nPK - 1 - N.p]? = some (.sort ℓ)) :
    Level.eval (N.KS.ψ (S.lsK (S.lparams.map φ) N)) ℓ = S.u₀ (S.lparams.map φ) := by
  have hK := K_law m hok
  have hNS := hok.nestScoped N hok.nest
  have hlsK : N.lsK.length = N.K.lparams.length := hNS.2.2.1
  have hml : N.memberLevel = ℓ := by simp [NestInfo.memberLevel, hℓp]
  have h := (LevelOracle.eq_iff _ _).mp hok.2.2.2.2.2.2.2.2.1 (S.ψ (S.lparams.map φ))
  rw [hml, Level.eval_subst] at h
  unfold u₀
  rw [← h]
  have hsc : Expr.Scoped env N.KS.lparams (N.KS.nP + (N.KS.params.length - 1 - (N.nPK - 1 - N.p)))
      (.sort ℓ) := hK.1.1 _ _ hℓp
  exact (Level.eval_congr (fun n hn => (valOf_map_eval (S.ψ (S.lparams.map φ)) hlsK hn).symm)
    hsc.2.2).symm

omit [LevelOracle] hs m hok in
/-- A context split around one entry: the values before, the value at
the entry, the values after. -/
theorem FitsVals_split {M : Name → List Nat → V} {φ : Name → Nat} {ρ : Nat → V} {Γ₁ Γ₂ : List Expr}
    {D : Expr} {vs₁ vs₂ : List V} {x : V} (h₁ : vs₁.length = Γ₁.length) :
    FitsVals M φ ρ (Γ₁ ++ D :: Γ₂) (vs₁ ++ x :: vs₂) ↔
      FitsVals M φ ρ Γ₂ vs₂ ∧ x ∈ˢ interp M φ (consList vs₂ ρ) D ∧
        FitsVals M φ (consList (x :: vs₂) ρ) Γ₁ vs₁ := by
  rw [FitsVals_append M φ h₁, FitsVals_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

omit hs in
/-- **The member set may be any set of the universe**: the class's
arguments fitting the container's parameters at one member set fit at
any member set of the block's universe — the member's domain is a
sort of that universe, and no later parameter's domain mentions the
member (positivity). -/
theorem FitsVals_psK_replace (φ : Name → Nat) {ps : List V} {G X : V}
    (hfit : FitsVals m.M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) base N.KS.params
      (S.psK m.M (S.lparams.map φ) N ps G))
    (hX : X ∈ˢ (univ (S.u₀ (S.lparams.map φ)) : V)) :
    FitsVals m.M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) base N.KS.params
      (S.psK m.M (S.lparams.map φ) N ps X) := by
  have hNS := hok.nestScoped N hok.nest
  have hpos : N.Positive := hNS.2.2.2.2.2.2.2.2.1
  have hlen : N.args.length + 1 = N.nPK := hNS.2.2.2.2.1
  have hpK : N.p < N.nPK := hpos.2.1
  obtain ⟨ℓ, hℓp⟩ := hpos.2.2.1
  have hnP : N.KS.params.length = N.nPK := rfl
  -- the container's parameters around the member's
  have hsplit : N.KS.params = N.KS.params.take (N.nPK - 1 - N.p) ++
      Expr.sort ℓ :: N.KS.params.drop (N.nPK - 1 - N.p + 1) := by
    have h1 := (List.take_append_drop (N.nPK - 1 - N.p) N.KS.params).symm
    rw [List.drop_eq_getElem_cons (by rw [hnP]; omega)] at h1
    have hget : N.KS.params[N.nPK - 1 - N.p]'(by rw [hnP]; omega) = Expr.sort ℓ :=
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hℓp)
    rw [hget] at h1
    exact h1
  have hl₁ : (S.argsAfter m.M (S.lparams.map φ) N ps).reverse.length
      = (N.KS.params.take (N.nPK - 1 - N.p)).length := by
    rw [List.length_reverse, S.length_argsAfter _ _ N hlen hpK, List.length_take, hnP]
    omega
  have hpsK : ∀ Y, S.psK m.M (S.lparams.map φ) N ps Y
      = (S.argsAfter m.M (S.lparams.map φ) N ps).reverse ++
          Y :: (S.argsBefore m.M (S.lparams.map φ) N ps).reverse := by
    intro Y
    unfold psK classArgsV argsAfter argsBefore
    simp [List.reverse_append]
  rw [hsplit, hpsK, FitsVals_split hl₁] at hfit
  rw [hsplit, hpsK, FitsVals_split hl₁]
  obtain ⟨h1, -, h3⟩ := hfit
  refine ⟨h1, ?_, ?_⟩
  · rw [interp_sort, memberLevel_eq m hok φ hℓp]
    exact hX
  · refine (FitsVals_congr₂ ?_).mp h3
    intro i A hA vs hvs
    have hl := FitsVals_length _ _ hvs
    have hi : i < (N.KS.params.take (N.nPK - 1 - N.p)).length := (List.getElem?_eq_some_iff.mp hA).1
    rw [List.length_take, hnP] at hi
    rw [List.getElem?_take_of_lt (by omega)] at hA
    have hu := hpos.2.2.2.1 i A hA (by omega)
    rw [consList_cons, consList_cons]
    refine interp_usesVar fun j hj => ?_
    refine consList_cons_agree _ _ _ _ j fun hji => ?_
    have : j = N.nPK - 2 - i - N.p := by
      rw [hji, hl, List.length_drop, List.length_take, hnP]; omega
    rw [this, hu] at hj
    exact Bool.false_ne_true hj

/-- **The class's arguments fit the container's parameters** at every
member set in the result universe — from the class having a sort at
the block's parameters (the check), read in the model of the
environment with the former: the container's set is a graph tower, so
the class application being well-denoted puts its arguments in the
tower's domains (`appList_of_wd`); the member's domain is a sort of
the block's universe (the check N3 on the member domain), and no later
parameter's domain mentions the member (positivity), so the member
set can be any set of the universe. -/
theorem argsFit_of (φ : Name → Nat) {ps : List V}
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) {X : V}
    (hX : X ∈ˢ (univ (S.u₀ (S.lparams.map φ)) : V)) :
    FitsVals m.M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) base N.KS.params
      (S.psK m.M (S.lparams.map φ) N ps X) := by
  have hN := hok.nest
  have hNS := hok.nestScoped N hN
  have hK := K_law m hok
  have hKS := hK.1
  have hpos : N.Positive := hNS.2.2.2.2.2.2.2.2.1
  have hlen : N.args.length + 1 = N.nPK := hNS.2.2.2.2.1
  have hpK : N.p < N.nPK := hpos.2.1
  have hlsK : N.lsK.length = N.K.lparams.length := hNS.2.2.1
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hp; simpa [nP] using this
  have R₀ := reader₃₀ hok m.M φ
  -- the check, read in the model with the former at the parameters
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2.2.2.2.1
  have hwdI := (type_ok_indN hs m hok φ base (ls := S.lvls) (by simp [indInfo, lvls])).1
  simp only [indInfo] at hwdI
  rw [WellDenoted_instL] at hwdI
  simp only [lvls] at hwdI
  rw [Level.substVal_self] at hwdI
  unfold indType at hwdI
  rw [WellDenoted_mkPis] at hwdI
  have hwdP := (CtxWD_append' hwdI.1).1
  have hp' : FitsVals (S.M₃N m.M N) φ base S.params ps := (R₀.fits_params hok.scoped).mpr hp
  have hsat : Sat (S.M₃N m.M N) φ S.params (consList ps base) := Sat_of_fits _ _ hwdP hp'
  have hsem := (infer_sound (m := mIndN hs m hok) (φ := φ) hT (consList ps base) hsat).1
  rw [mIndN_M] at hsem
  -- the container's set is a graph tower: the arguments fit its parameters
  unfold classTy at hsem
  have hf : interp (S.M₃N m.M N) φ (consList ps base) (.const N.K.name N.lsK)
      = lamCtx (S.M₃N m.M N) φ false base (N.KS.params.map (Expr.instL N.K.lparams N.lsK))
          fun ρ' => N.KS.Fam m.M (S.lsK (S.lparams.map φ) N) (readEnv N.KS.nP ρ') [] := by
    rw [interp_const, ← lsK_eq_map hok φ, ← agree_M₃N hok m.M _ hNS.1, hK.2.2.2.2.1,
      famSetK_eq m hok φ]
  have hlenA : (S.classArgs N 0).length = (N.KS.params.map (Expr.instL N.K.lparams N.lsK)).length := by
    rw [S.length_classArgs N hlen hpK, List.length_map]; rfl
  obtain ⟨hfit, -⟩ := appList_of_wd (S.M₃N m.M N) φ hsem hf hlenA
    (G := fun _ => univ (N.KS.u₀ (S.lsK (S.lparams.map φ) N)))
    (fun _ _ => N.KS.Fam_mem_univ m.M _ _ _)
  rw [FitsVals_instL, FitsVals_congr₂ (agree_paramsK m hok φ base)] at hfit
  -- the arguments' values: the class's arguments at the member's reading
  have hvals : (S.classArgs N 0).map (interp (S.M₃N m.M N) φ (consList ps base))
      = S.classArgsV m.M (S.lparams.map φ) N ps
          (interp (S.M₃N m.M N) φ (consList ps base) (S.famAt 0 (N.idx.map (Expr.liftN 0 ·)))) := by
    unfold classArgs classArgsV
    simp only [List.map_append, List.map_map, List.map_singleton]
    have hread : ∀ a ∈ N.args, interp (S.M₃N m.M N) φ (consList ps base) (Expr.liftN 0 a)
        = interp m.M (S.ψ (S.lparams.map φ)) (envP ps) a := by
      intro a ha
      rw [interp_liftN, shiftE_zero_zero]
      have := R₀.read (hNS.2.2.2.2.2.2.1 a ha) (vs := []) (ps := ps) (ρ := base) (by simp [hps])
      simpa [envP] using this
    congr 1
    · congr 1
      exact List.map_congr_left fun a ha => hread a (List.mem_of_mem_take ha)
    · exact List.map_congr_left fun a ha => hread a (List.mem_of_mem_drop ha)
  rw [hvals] at hfit
  -- the member set may be any set of the universe
  exact FitsVals_psK_replace m hok φ hfit hX

/-- **The container's facts** at every valuation: from its block law,
the nested checks and the scope. -/
theorem nestFacts (φ : Name → Nat) : S.NestFacts m.M (S.lparams.map φ) N := by
  have hK := K_law m hok
  have hNS := hok.nestScoped N hok.nest
  have hlsK : N.lsK.length = N.K.lparams.length := hNS.2.2.1
  refine ⟨hK.2.2.2.2.1, hK.2.1, hNS.2.2.2.2.2.2.2.2.1, fun c hc => (hK.1.2.2.2.1 c hc).2.1,
    fun ps' hps' => hK.2.2.2.2.2.2 _ ps' hps', fun ps hp X hX => argsFit_of hs m hok φ hp hX, ?_,
    hNS.2.2.2.2.1⟩
  -- N3: the container's sort at the instantiation is the block's
  have h3 := (LevelOracle.eq_iff _ _).mp hok.2.2.2.2.2.2.2.1 (S.ψ (S.lparams.map φ))
  rw [Level.eval_subst] at h3
  unfold u₀
  rw [← h3]
  exact (Level.eval_congr (fun n hn => (valOf_map_eval (S.ψ (S.lparams.map φ)) hlsK hn).symm)
    hK.1.2.2.1).symm

/-- The final assignment reads the former and the constructors, under
the class's guard. -/
theorem reader₃N (φ : Name → Nat) : S.Reader₂ (env := env) m.M φ (S.M₃N m.M N) φ where
  R := { toReader := reader₃₀ hok m.M φ, good := S.contGood_of (nestFacts hs m hok φ) hok.nest }
  ctor := fun j c hc ls' => by
    simp [M₃N, M₂, hok.ctor_ne_rec hc, hok.ctor_ne_aux hc, S.ctorOf?_of_getElem? hok.nodup_ctors hc]

/-- The model with the former and the constructors, as a reader of
the block's own valuation (the recursors' sets are abstractions over
contexts read there). -/
theorem reader₂N (φ : Name → Nat) {φ' : Name → Nat} (hφ : ∀ n ∈ S.lparams, φ' n = φ n) :
    S.Reader₂ (env := env) m.M φ (S.M₂ m.M) φ' where
  R :=
    { agree := fun n hn ls => by
        have h₃ := agree_M₃N hok m.M n hn ls
        simp only [M₃N] at h₃
        have hne : n ≠ S.recName := fun h => by
          subst h; rw [hok.fresh _ (by simp)] at hn; simp at hn
        have hne' : n ≠ N.aux := fun h => by
          subst h; rw [hok.fresh _ (by simp)] at hn; simp at hn
        rwa [if_neg hne', if_neg hne] at h₃
      fam := fun ls' => by
        simp [M₂, M₁, hok.ctorOf?_name]
      val := hφ
      good := S.contGood_of (nestFacts hs m hok φ) hok.nest }
  ctor := fun j c hc ls' => by
    simp [M₂, S.ctorOf?_of_getElem? hok.nodup_ctors hc]

/-- The class's laws at the block's parameters, above a proposition. -/
theorem classLaws (φ : Name → Nat) (hz : S.z (S.lparams.map φ) = false) {ps : List V}
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) :
    S.ClassLaws m.M (S.lparams.map φ) N ps :=
  S.classLaws_of m.M _ N (nestFacts hs m hok φ) (hok.nestScoped N hok.nest).2.2.2.2.1
    (hok.nestScoped N hok.nest).2.2.1 (K_law m hok).1 hok.nest hz hp

omit hs m in
/-- Above a proposition whenever the eliminator is large: a nested
block's large eliminator is on a never-`Prop` sort. -/
theorem z_false_of_large (φ : Name → Nat) (hlarge : S.large = true) :
    S.z (S.lparams.map φ) = false := by
  have h := (LevelOracle.le_iff _ _).mp (hok.large_never hlarge) (S.ψ (S.lparams.map φ))
  simp only [Level.eval_succ, Level.eval_zero] at h
  cases hz : S.z (S.lparams.map φ)
  · rfl
  · have := (S.z_iff _).mp hz
    unfold u₀ at this
    omega

omit hs m in
theorem z_false_of_q (φ : Name → Nat) {φ' : Name → Nat} (hq : S.q.holds φ' = false) :
    S.z (S.lparams.map φ) = false :=
  z_false_of_large hok φ (large_of_q_false hq)

/-! ## The constructors -/

/-- A constructor's type is well-denoted at every valuation. -/
theorem wd_ctorTypeN {c : CtorSpec} (hc : c ∈ S.ctors) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted (S.M₃N m.M N) φ ρ (S.ctorType c) := by
  obtain ⟨T, hT⟩ := (hok.2.2.2.2.2.1 c hc).1
  have := (infer_sound (m := mIndN hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mIndN_M] at this

/-- The sort of a field's domain bounds its set (the universe bound),
read off the checker's sort facts at a satisfying environment. -/
theorem univ_of_sortN {Γ : List Expr} {A s : Expr} {v : Level}
    (hI : Infer (S.envInd env) Γ A s) (hR : Red (S.envInd env) Γ s (.sort v)) (φ : Name → Nat)
    {ρ : Nat → V} (hsat : Sat (S.M₃N m.M N) φ Γ ρ) :
    interp (S.M₃N m.M N) φ ρ A ∈ˢ (univ (Level.eval φ v) : V) := by
  obtain ⟨-, hws, hmem⟩ := infer_sound (m := mIndN hs m hok) (φ := φ) hI ρ hsat
  obtain ⟨-, heq⟩ := red_sound (m := mIndN hs m hok) (φ := φ) hR ρ hsat hws
  rw [mIndN_M] at hmem heq
  rw [heq, interp_sort] at hmem
  exact hmem

/-- **The domains met along a fitting instance are members of the
result universe**, from the checker's universe bound on every field
and every binder of a reflexive field's telescope. -/
theorem domsBounded_ofN (φ : Name → Nat) (ρ : Nat → V) {ps : List V} (hps : ps.length = S.nP)
    (hp : FitsVals m.M (S.ψ (S.lparams.map φ)) base S.params ps) :
    S.DomsBounded m.M (S.lparams.map φ) ps := by
  intro hz c hc fs hfit k f hpos hk
  have R := (reader₃N hs m hok φ).R
  have hS := hok.scoped
  have hwd := wd_ctorTypeN hs m hok hc φ ρ
  unfold ctorType at hwd
  rw [WellDenoted_mkPis] at hwd
  obtain ⟨hctx, -⟩ := hwd
  obtain ⟨hpar, hfld⟩ := CtxWD_append' hctx
  have hp' : FitsVals (S.M₃N m.M N) φ ρ S.params ps := (R.fits_params hS).mpr hp
  have hwdF := hfld ps hp'
  have hsc := (hS.2.2.2.1 c hc).1
  have hfs := (R.fits_fieldCtx hS hsc hps hp hwdF (vs := fs)).1.mpr hfit
  have hl := S.FitsFields_length m.M _ hfit
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
  have hfsE : FitsVals (S.M₃N m.M N) φ (consList ps ρ)
      ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1)) (earlier fs k) := by
    rw [hearlier]; exact FitsVals_drop _ _ _ hfs
  have hsatF : Sat (S.M₃N m.M N) φ ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1) ++ S.params)
      (consList (earlier fs k ++ ps) ρ) := by
    refine Sat_of_fits _ _ (CtxWD_append_of _ _ hpar fun ws hws => CtxWD_drop _ _ _ (hfld ws hws)) ?_
    exact (FitsVals_append _ _ (by simp [hel, S.length_fieldCtx]; omega)).mpr ⟨hp', hfsE⟩
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
  | container => trivial
  | ordinary A =>
    obtain ⟨s, v, hI, hR, hb⟩ := (hok.2.2.2.2.2.1 c hc).2.1 _ A hget
    have hmem := univ_of_sortN hs m hok hI hR φ hsatF
    rw [consList_append] at hmem
    rw [R.read hsc' (vs := earlier fs k) (ps := ps) (ρ := ρ) (by simp [hel, hps]; omega)] at hmem
    exact univ_mono (hbound hb) hmem
  | reflexive tele es =>
    have hwdT : ∀ ws ws', FitsVals (S.M₃N m.M N) φ ρ S.params ws →
        FitsVals (S.M₃N m.M N) φ (consList ws ρ)
          ((S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1)) ws' →
        CtxWD (S.M₃N m.M N) φ (consList ws' (consList ws ρ)) tele := by
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
    obtain ⟨s, w, hI, hR, hb⟩ := (hok.2.2.2.2.2.1 c hc).2.2.1 _ tele es hpos _ T hT
    rw [hdrop] at hI hR
    have hys' : FitsVals (S.M₃N m.M N) φ (consList (earlier fs k) (consList ps ρ)) (tele.drop (tele.length - t)) ys :=
      (FitsVals_congr₂ (CtxAgree_drop hagT _)).mpr hys
    have hyl : ys.length = t := by
      have := FitsVals_length _ _ hys'; simp at this; omega
    have hsat : Sat (S.M₃N m.M N) φ (tele.drop (tele.length - t) ++
        (S.fieldCtx c.fields).drop (c.fields.length - 1 - k + 1) ++ S.params)
        (consList (ys ++ earlier fs k ++ ps) ρ) := by
      refine Sat_of_fits _ _ ?_ ?_
      · refine CtxWD_append_of _ _ hpar fun ws hws => ?_
        refine CtxWD_append_of _ _ (CtxWD_drop _ _ _ (hfld ws hws)) fun ws' hws' => ?_
        rw [← hdrop]
        exact CtxWD_drop _ _ _ (hwdT ws ws' hws hws')
      · refine (FitsVals_append _ _ (by simp [hyl, hel, S.length_fieldCtx]; omega)).mpr ⟨hp', ?_⟩
        exact (FitsVals_append _ _ (by simp [hyl]; omega)).mpr ⟨hfsE, hys'⟩
    have hmem := univ_of_sortN hs m hok hI hR φ hsat
    rw [consList_append, consList_append] at hmem
    rw [← consList_append,
      R.read (hsc'.1 _ T hT) (vs := ys ++ earlier fs k) (ps := ps) (ρ := ρ)
        (by simp [hyl, hel, hps]; omega), consList_append] at hmem
    exact univ_mono (hbound hb) hmem

omit [IndLib V] hs m in
/-- No field reads an earlier recursive field. -/
theorem noRecDepN : S.NoRecDep := fun c hc => (hok.scoped.2.2.2.1 c hc).2.1

/-- **A constructor's type law.** -/
theorem type_ok_ctorN {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) (φ : Name → Nat)
    (ρ : Nat → V) {ls : List Level} (hls : ls.length = (S.ctorInfo c).lparams.length) :
    WellDenoted (S.M₃N m.M N) φ ρ ((S.ctorInfo c).type.instL (S.ctorInfo c).lparams ls) ∧
    S.M₃N m.M N c.name (ls.map (Level.eval φ)) ∈ˢ
      interp (S.M₃N m.M N) φ ρ ((S.ctorInfo c).type.instL (S.ctorInfo c).lparams ls) := by
  simp only [ctorInfo] at hls ⊢
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  refine ⟨(WellDenoted_instL _ _ _ _ _ _).mpr (wd_ctorTypeN hs m hok hcm _ ρ), ?_⟩
  rw [interp_instL, (reader₃N hs m hok φ).ctor j c hc, ← lparams_map_substValN hok φ hls]
  exact (reader₃N hs m hok (Level.substVal φ S.lparams ls)).ctorSet_mem hok.scoped hok.freshI hc
    (wd_ctorTypeN hs m hok hcm _ ρ) (noRecDepN hok)
    (fun ps hp => domsBounded_ofN hs m hok _ ρ (by have := FitsVals_length _ _ hp; simpa [nP] using this) hp)
    (fun ps hp => S.contInBound_of (nestFacts hs m hok _) hok.nest hp)

/-- The environment with the former and the constructors has a model
at the final assignment. -/
noncomputable def mCtorsN : EnvModel V (S.envCtors env) where
  M := S.M₃N m.M N
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · rename_i j c' hco
      cases hfind
      obtain ⟨hc', rfl⟩ := S.ctorOf?_some hco
      exact type_ok_ctorN hs m hok hc' φ ρ hls
    · exact (mIndN hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · cases hfind; simp [ctorInfo, ConstInfo.value?, ConstKind.value?] at hv
    · exact (mIndN hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · cases hfind; simp [ctorInfo] at hkind
    · rw [S.envCtors_find? env hok.nodup_ctors] at hcij
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
          exact (List.nodup_cons.mp hok.nodup).1
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', h⟩)))
        · rw [← h, hok.fresh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨c', hc', rfl⟩))))] at hstored
          simp at hstored
      rw [hnone] at hcij
      exact (mIndN hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl cij hcij
  rec_rules_nested := fun c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij hcijk => by
    rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · cases hfind; simp [ctorInfo] at hkind
    · rw [S.envCtors_find? env hok.nodup_ctors] at hcij
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
          exact (List.nodup_cons.mp hok.nodup).1
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', h⟩)))
        · rw [← h, hok.fresh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨c', hc', rfl⟩))))] at hstored
          simp at hstored
      rw [hnone] at hcij
      exact (mIndN hs m hok).rec_rules_nested c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst
        hinst cij I nPc nf hcij hcijk

theorem mCtorsN_M : (mCtorsN hs m hok).M = S.M₃N m.M N := rfl

/-- The recursors' and rules' types are well-denoted at every valuation. -/
theorem wd_recTypeN (φ : Name → Nat) (ρ : Nat → V) : WellDenoted (S.M₃N m.M N) φ ρ (S.recTypeN N) := by
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := (infer_sound (m := mCtorsN hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtorsN_M] at this

theorem wd_rec1Type (φ : Name → Nat) (ρ : Nat → V) : WellDenoted (S.M₃N m.M N) φ ρ (S.rec1Type N) := by
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2.2.2.2.2.2.2.2
  have := (infer_sound (m := mCtorsN hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtorsN_M] at this

theorem wd_ruleTypeN {c : CtorSpec} (hc : c ∈ S.ctors) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted (S.M₃N m.M N) φ ρ (S.ruleTypeN N c) := by
  obtain ⟨T, hT⟩ := (hok.2.2.2.2.2.1 c hc).2.2.2
  have := (infer_sound (m := mCtorsN hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtorsN_M] at this

theorem wd_rule1Type {c : CtorSpec} (hc : c ∈ N.K.ctors) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted (S.M₃N m.M N) φ ρ (S.rule1Type N c) := by
  obtain ⟨T, hT⟩ := hok.2.2.2.2.2.2.2.2.2.2.2.1 c hc
  have := (infer_sound (m := mCtorsN hs m hok) (φ := φ) hT ρ (Sat_nil _ _ _)).1
  rwa [mCtorsN_M] at this

end IndSpec

/-- **Installing a nested block preserves having a block model.**
Every stored constant keeps its set; the new block, being nested,
stores no block law of its own. -/
theorem install_nest {env : Env} {S : IndSpec} {N : NestInfo} (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : S.OkN N env) :
    ∃ m' : BlockModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  sorry

/-- **Installing any accepted block preserves having a block model.** -/
theorem install_ind_any {env : Env} {S : IndSpec} (hs : Env.Scoped env) (m : BlockModel V env)
    (hok : IndOk env S) :
    ∃ m' : BlockModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  unfold IndOk at hok
  split at hok
  · exact install_ind' ‹_› hs m hok
  · exact install_nest hs m hok

/-- A closed environment stays closed under any accepted block. -/
theorem _root_.Fragment.Env.Scoped.install_any {env : Env} {S : IndSpec} (hs : Env.Scoped env)
    (hok : IndOk env S) : Env.Scoped (S.install env) := by
  unfold IndOk at hok
  split at hok
  · exact hs.install S ‹_› hok
  · exact hs.installN hok

end Fragment
