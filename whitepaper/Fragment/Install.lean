module

public import Fragment.InstallDef
public import Fragment.InstallIota

@[expose] public section

/-!
# Installing a declaration preserves having a model

The two environment steps and their models:

* **A definition** (`install_def`, `InstallDef.lean`): the new
  constant's set is its value's denotation; every stored constant
  keeps its set.
* **An inductive block** (`install_ind`, here): the former's set is
  the graph over the parameters and indices of the fibre — the least
  fixed point of the block's operator inside the set theory
  (`IndSem.lean`); each constructor's
  set is the graph of its tagged tuple, the recursor's the graph of
  the model's recursor (the recursion theorem over the fixed point);
  every stored constant keeps its set (`agree_M₃`).  The three laws:
  the types (`InstallInd.lean`), no definition among the new
  constants, and the ι law of every generated rule
  (`InstallIota.lean`).

Con-leche's counterparts: `ConLeche/Model/Install.lean` (definitions)
and `ConLeche/Model/Inductives/DeclNative.lean` (a block, by the
native route).
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

namespace IndSpec

variable {env : Env} {S : IndSpec}
variable (hpl : S.nest = none) (hs : Env.Scoped env) (m : EnvModel V env) (hok : S.Ok env)
include hpl hs m hok

/-- **The model of the installed block**: the final assignment `M₃`
with the three laws, by cases on where a name is found — the new
recursor (`type_ok_rec`, `rec_rule_law`), or a constant of the
environment with the former and the constructors (`mCtors`). -/
noncomputable def mInstall : EnvModel V (S.install env) where
  M := S.M₃ m.M
  type_ok := fun c ci hfind φ ρ ls hls => by
    rw [S.install_find? hpl] at hfind
    split at hfind
    · rename_i hc
      subst hc
      cases hfind
      exact type_ok_rec hpl hs m hok φ ρ hls
    · exact (mCtors hpl hs m hok).type_ok c ci hfind φ ρ ls hls
  unfold := fun c ci v hfind hv φ ρ ls hls => by
    rw [S.install_find? hpl] at hfind
    split at hfind
    · cases hfind
      simp [recInfo, ConstInfo.value?, ConstKind.value?] at hv
    · exact (mCtors hpl hs m hok).unfold c ci v hfind hv φ ρ ls hls
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij => by
    rw [S.install_find? hpl] at hfind
    split at hfind
    · -- the new recursor: one of the generated rules, at its constructor
      rename_i hc
      subst hc
      cases hfind
      simp only [recInfo, ConstKind.recursor.injEq] at hkind
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
      obtain ⟨j, c', hc', rfl⟩ := S.mem_rules hrl
      have hcij' : (S.install env).find? c'.name = some (S.ctorInfo c') := by
        rw [S.install_find? hpl, if_neg (hok.ctor_ne_rec hc'), S.envCtors_find? env hok.nodup_ctors,
          S.ctorOf?_of_getElem? hok.nodup_ctors hc']
      rw [hcij'] at hcij
      cases hcij
      exact rec_rule_law hpl hs m hok hc'
    · -- a stored recursor: its rule's constructor is stored, hence not the new recursor
      have hstored : (env.find? rl.ctor).isSome := by
        rw [S.envCtors_find? env hok.nodup_ctors] at hfind
        split at hfind
        · cases hfind; simp [ctorInfo] at hkind
        · rw [S.envInd_find?] at hfind
          split at hfind
          · cases hfind; simp [indInfo] at hkind
          · exact ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
      have hne : rl.ctor ≠ S.recName :=
        Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
      rw [S.install_find? hpl, if_neg hne] at hcij
      exact (mCtors hpl hs m hok).rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij
  rec_rules_nested := fun c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij hcijk => by
    rw [S.install_find? hpl] at hfind
    split at hfind
    · -- the new recursor's rules are plain
      rename_i hc
      subst hc
      cases hfind
      simp only [recInfo, ConstKind.recursor.injEq] at hkind
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hkind
      obtain ⟨j, c', hc', rfl⟩ := S.mem_rules hrl
      cases hinst
    · have hstored : (env.find? rl.ctor).isSome := by
        rw [S.envCtors_find? env hok.nodup_ctors] at hfind
        split at hfind
        · cases hfind; simp [ctorInfo] at hkind
        · rw [S.envInd_find?] at hfind
          split at hfind
          · cases hfind; simp [indInfo] at hkind
          · exact ((hs c ci hfind).2.2 nP nM nMin nI rules hkind rl hrl).2
      have hne : rl.ctor ≠ S.recName :=
        Env.ne_of_isSome_find? hstored (hok.fresh _ (by simp))
      rw [S.install_find? hpl, if_neg hne] at hcij
      exact (mCtors hpl hs m hok).rec_rules_nested c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst
        hinst cij I nPc nf hcij hcijk

theorem mInstall_M : (mInstall hpl hs m hok).M = S.M₃ m.M := rfl

end IndSpec

/-- **Installing a plain inductive block preserves having a model.**
Every stored constant keeps its set. -/
theorem install_ind {env : Env} {S : IndSpec} (hpl : S.nest = none) (hs : Env.Scoped env)
    (m : EnvModel V env) (hok : S.Ok env) :
    ∃ m' : EnvModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls :=
  ⟨S.mInstall hpl hs m hok, fun n hn ls => (S.agree_M₃ hok m.M n hn ls).symm⟩

end Fragment
