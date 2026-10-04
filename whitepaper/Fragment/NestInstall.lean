module

public import Fragment.NestIota

@[expose] public section

/-!
# Installing a nested block: the model

The model of the installed nested environment (`mInstallN`): the final
assignment with the two recursors' type laws and the ι laws of both
rule sets (`NestIota.lean`) on top of the model with the former and
the constructors (`InstallNest.lean`); the block laws survive
(`blocksN`); `install_nest`, and the one installation theorem for any
accepted block (`install_ind_any`).
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

namespace IndSpec

variable {env : Env} {S : IndSpec} {N : NestInfo}
variable (hs : Env.Scoped env) (m : BlockModel V env) (hok : S.OkN N env)
include hs m hok

/-! ## The installed nested environment's model -/

omit hs m in
/-- The installed nested environment, by its branch. -/
theorem install_eq_installN : S.install env = S.installN N env := by
  simp [IndSpec.install, hok.nest]

omit m in
/-- A stored rule's constructor is stored, hence none of the new
names. -/
theorem stored_ctor_of_envCtors {c : Name} {ci : ConstInfo} {nP nM nMin nI : Nat}
    {rules : List RecRule} (hfind : (S.envCtors env).find? c = some ci)
    (hkind : ci.kind = .recursor nP nM nMin nI rules) {rl : RecRule} (hrl : rl ∈ rules) :
    (env.find? rl.ctor).isSome := by
  rw [S.envCtors_find? env hok.nodup_ctors] at hfind
  split at hfind
  · cases hfind; simp [ctorInfo] at hkind
  · rw [S.envInd_find?] at hfind
    split at hfind
    · cases hfind; simp [indInfo] at hkind
    · exact ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2

/-- **The model of the installed nested block**: the final assignment
with the four laws — the two recursors' types, their rules' ι laws
(`T.rec`'s plain, `T.rec_1`'s nested; a `T.rec_1` rule never fires by
the plain ι step, a `T.rec` rule never by the nested one), and the
constants of the environment with the former and the constructors
(`mCtorsN`). -/
noncomputable def mInstallN : EnvModel V (S.install env) where
  M := S.M₃N m.M N
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [install_eq_installN hok, S.installN_find?] at hfind
    split at hfind
    · rename_i hc
      subst hc
      cases hfind
      exact type_ok_rec1 hs m hok φ ρ hls
    · split at hfind
      · rename_i hc
        subst hc
        cases hfind
        exact type_ok_recN hs m hok φ ρ hls
      · exact (mCtorsN hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [install_eq_installN hok, S.installN_find?] at hfind
    split at hfind
    · cases hfind; simp [rec1Info, ConstInfo.value?, ConstKind.value?] at hv
    · split at hfind
      · cases hfind; simp [recInfoN, ConstInfo.value?, ConstKind.value?] at hv
      · exact (mCtorsN hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij => by
    rw [install_eq_installN hok, S.installN_find?] at hfind
    split at hfind
    · -- `T.rec_1`: its rules carry an instantiation
      cases hfind
      simp only [rec1Info, ConstKind.recursor.injEq] at hkind
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
      obtain ⟨j, c', hc', rfl⟩ := S.mem_rules1 N hrl
      cases hinst
    · split at hfind
      · -- `T.rec`: one of the generated rules, at its constructor
        rename_i hc
        subst hc
        cases hfind
        simp only [recInfoN, ConstKind.recursor.injEq] at hkind
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
        obtain ⟨j, c', hc', rfl⟩ := S.mem_rulesN N hrl
        have hcij' : (S.install env).find? c'.name = some (S.ctorInfo c') := by
          rw [install_eq_installN hok, S.installN_find?, ite_eq_right (hok.ctor_ne_aux hc'),
            ite_eq_right (hok.ctor_ne_rec hc'), S.envCtors_find? env hok.nodup_ctors,
            S.ctorOf?_of_getElem? hok.nodup_ctors hc']
        rw [hcij'] at hcij
        cases hcij
        exact rec_rule_lawN hs m hok hc'
      · have hstored := stored_ctor_of_envCtors hs hok hfind hkind hrl
        have hne : rl.ctor ≠ S.recName := Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
        have hne' : rl.ctor ≠ N.aux := Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
        rw [install_eq_installN hok, S.installN_find?, ite_eq_right hne', ite_eq_right hne] at hcij
        exact (mCtorsN hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij
  rec_rules_nested := fun c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij hcijk => by
    rw [install_eq_installN hok, S.installN_find?] at hfind
    split at hfind
    · -- `T.rec_1`: one of the generated rules, at the container's constructor
      rename_i hc
      subst hc
      cases hfind
      simp only [rec1Info, ConstKind.recursor.injEq] at hkind
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
      obtain ⟨j, c', hc', rfl⟩ := S.mem_rules1 N hrl
      have hK := K_law m hok
      have hcij' : (S.install env).find? c'.name = some (N.KS.ctorInfo c') := by
        rw [install_eq_installN hok]
        exact S.find?_mono_installN N env hok.fresh (hK.2.2.2.1 j c' hc')
      rw [hcij'] at hcij
      cases hcij
      simp only [ctorInfo, ConstKind.ctor.injEq] at hcijk
      obtain ⟨-, rfl, -⟩ := hcijk
      exact rec_rule_law1N hs m hok hc'
    · split at hfind
      · -- `T.rec`: its rules carry no instantiation
        cases hfind
        simp only [recInfoN, ConstKind.recursor.injEq] at hkind
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
        obtain ⟨j, c', hc', rfl⟩ := S.mem_rulesN N hrl
        cases hinst
      · have hstored := stored_ctor_of_envCtors hs hok hfind hkind hrl
        have hne : rl.ctor ≠ S.recName := Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
        have hne' : rl.ctor ≠ N.aux := Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
        rw [install_eq_installN hok, S.installN_find?, ite_eq_right hne', ite_eq_right hne] at hcij
        exact (mCtorsN hs m hok).rec_rules_nested c ci nP nM nMin nI rules hfind hkind rl hrl lvs
          pinst hinst cij I nPc nf hcij hcijk

omit hs in
/-- **The block laws survive the nested installation**: the new
block stores none (it is nested); every old block's law is transported
to the final assignment and grown by the former, the constructors and
the two recursors. -/
theorem blocksN : ∀ (K : Name) (ci : ConstInfo) (nP nI : Nat) (cs : List Name) (spec : IndSpec),
    (S.install env).find? K = some ci → ci.kind = .induct nP nI cs spec →
    spec.BlockLaw (S.install env) (S.M₃N m.M N) := by
  intro K ci nP nI cs spec hfind hkind
  have hagree : AgreeOn env m.M (S.M₃N m.M N) := agree_M₃N hok m.M
  have hfreshC : ∀ c ∈ S.ctors, (S.envInd env).find? c.name = none := by
    intro c hc
    rw [S.envInd_find?, ite_eq_right (fun h => (List.nodup_cons.mp hok.nodup).1
      (by rw [← h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))))]
    exact hok.fresh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map_of_mem hc))))
  have hfreshR : (S.envCtors env).find? S.recName = none := by
    rw [S.envCtors_find? env hok.nodup_ctors, hok.ctorOf?_rec, S.envInd_find?,
      ite_eq_right hok.name_ne_rec.symm]
    exact hok.fresh _ (by simp)
  have hfreshA : ((S.envCtors env).add S.recName (S.recInfoN N)).find? N.aux = none := by
    rw [Env.find?_add_of_ne _ _ hok.rec_ne_aux.symm, S.envCtors_find? env hok.nodup_ctors,
      hok.ctorOf?_aux, S.envInd_find?, ite_eq_right hok.name_ne_aux.symm]
    exact hok.fresh _ (by simp)
  rw [install_eq_installN hok] at hfind ⊢
  rw [S.installN_find?] at hfind
  split at hfind
  · cases hfind; simp [rec1Info] at hkind
  · split at hfind
    · cases hfind; simp [recInfoN] at hkind
    · rw [S.envCtors_find? env hok.nodup_ctors] at hfind
      split at hfind
      · cases hfind; simp [ctorInfo] at hkind
      · rw [S.envInd_find?] at hfind
        split at hfind
        · -- the new block is nested: no law
          cases hfind
          simp only [indInfo, ConstKind.induct.injEq] at hkind
          obtain ⟨-, -, -, rfl⟩ := hkind
          intro hpl
          rw [hok.nest] at hpl
          cases hpl
        · have h₁ := spec.BlockLaw_transport hagree (m.blocks K ci nP nI cs spec hfind hkind)
          have h₂ := spec.BlockLaw_add h₁ S.name S.indInfo hok.freshI
          have h₃ := spec.BlockLaw_foldl S.ctorInfo h₂ hfreshC hok.nodup_ctors
          have h₄ := spec.BlockLaw_add h₃ S.recName (S.recInfoN N) hfreshR
          exact spec.BlockLaw_add h₄ N.aux (S.rec1Info N) hfreshA

end IndSpec

/-- **Installing a nested block preserves having a block model.**
Every stored constant keeps its set; the new block, being nested,
stores no block law of its own. -/
theorem install_nest {env : Env} {S : IndSpec} {N : NestInfo} (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : S.OkN N env) :
    ∃ m' : BlockModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  exact ⟨{ toEnvModel := IndSpec.mInstallN hs m hok, blocks := IndSpec.blocksN m hok },
    fun n hn ls => (IndSpec.agree_M₃N hok m.M n hn ls).symm⟩

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
