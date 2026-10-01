module

public import Fragment.BlockModel
public import Fragment.NestRead
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
    S.Reader (env := env) M φ (S.M₃N M N) φ := by
  sorry

/-! ## The container's facts -/

variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

/-- The container's block law, in the model. -/
theorem K_law : N.KS.Scoped env ∧ N.KS.NoCont ∧
    env.find? N.KS.name = some N.KS.indInfo ∧
    (∀ (j : Nat) (c : CtorSpec), N.KS.ctors[j]? = some c → env.find? c.name = some (N.KS.ctorInfo c)) ∧
    (∀ ls, m.M N.KS.name ls = N.KS.famSet m.M ls) ∧
    (∀ (j : Nat) (c : CtorSpec), N.KS.ctors[j]? = some c →
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
  sorry

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

/-- **The container's facts** at every valuation: from its block law,
the nested checks and the scope. -/
theorem nestFacts (φ : Name → Nat) : S.NestFacts m.M (S.lparams.map φ) N := by
  sorry

/-- The final assignment reads the former and the constructors, under
the class's guard. -/
theorem reader₃N (M : Name → List Nat → V) (φ : Name → Nat) :
    S.Reader₂ (env := env) M φ (S.M₃N M N) φ := by
  sorry

end IndSpec

end Fragment
