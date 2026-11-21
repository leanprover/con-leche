module

public import ConLeche.Model.CopyStmt
public import ConLeche.Verify.Cached.Cone
import ConLeche.Model.Modular.Read
import ConLeche.Verify.Cached.DeclNames

public section

/-!
# The solution at the input's level-parameter names

A justified input reads a solution statement at its own level-parameter names (`copyB`'s second
branch).  `renEnv Ef envS` is the solution's environment with each such statement renamed to the
input's names (read off the input's final environment `Ef`); `Model/CopyStmt.lean` carries the
solution's model across.  Every name the input shares with the solution (`Shared`, the union of the
justifications' cones read in `Ef`) then has its input copy refine the renamed solution's
(`Refines`, exactly as the context reading of `Model/Modular` asks).
-/

namespace ConLeche.Model.Solution

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify

/-- **A solution constant at the input's names**: a statement at a name no pin reserves, renamed
to the level parameters of the input's constant of its name where those are other names, as
many, neither list with a repeat. -/
@[expose] def renS (Ef : Env) (c : ConstantInfo) : ConstantInfo :=
  match Ef.find? c.name with
  | some ci =>
    if c.isStmtKind && !reservedBasisNames.contains c.name &&
        ci.toConstantVal.levelParams != c.toConstantVal.levelParams &&
        levelsRenaming c.toConstantVal.levelParams ci.toConstantVal.levelParams
    then c.atLps ci.toConstantVal.levelParams else c
  | none => c

/-- **The renamed solution environment.** -/
@[expose] def renEnv (Ef envS : Env) : Env := ⟨envS.consts.map (renS Ef), envS.tables⟩

theorem renS_name (Ef : Env) (c : ConstantInfo) : (renS Ef c).name = c.name := by
  unfold renS
  split
  · split
    · exact atLps_name c _
    · rfl
  · rfl

theorem renEnv_find (Ef envS : Env) (n : Name) :
    (renEnv Ef envS).find? n = (envS.find? n).map (renS Ef) := by
  unfold renEnv Env.find?
  rw [List.find?_map]
  congr 1
  apply congrArg (envS.consts.find? ·)
  funext c
  simp only [Function.comp_apply, renS_name]

theorem renEnv_findTable (Ef envS : Env) (n : Name) :
    (renEnv Ef envS).findTable? n = envS.findTable? n := by
  unfold Env.findTable?
  rw [renEnv_find]
  cases envS.find? n <;> rfl

theorem levelsRenaming_spec {ps ps' : List Name} (h : levelsRenaming ps ps' = true) :
    ps.length = ps'.length ∧ ps.Nodup ∧ ps'.Nodup := by
  simp only [levelsRenaming, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A renamed constant is a copy of the solution's, and only a statement at an unreserved name
moves. -/
theorem renS_copy (Ef : Env) (c : ConstantInfo) :
    ConstCopy c (renS Ef c) ∧
      (renS Ef c ≠ c → c.isStmtKind = true ∧ reservedBasisNames.contains c.name = false) := by
  unfold renS
  split
  · split
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hk, hr⟩, -⟩, hl⟩ := hc
      obtain ⟨hlen, -, hnd⟩ := levelsRenaming_spec hl
      refine ⟨.inr ⟨_, rfl, hnd, hlen, ?_⟩, fun _ => ⟨hk, hr⟩⟩
      cases c <;> simp_all [ConstantInfo.isStmtKind, RuleFree]
    · exact ⟨.inl rfl, fun h => absurd rfl h⟩
  · exact ⟨.inl rfl, fun h => absurd rfl h⟩

theorem constsCopy_map (Ef : Env) : ∀ l : List ConstantInfo, ConstsCopy l (l.map (renS Ef))
  | [] => .nil
  | c :: l => .cons (renS_copy Ef c).1 (constsCopy_map Ef l)

/-- **The renamed solution is a copy of the solution.** -/
theorem renEnv_copies {Ef envS : Env} (hnd : NodupNames envS) : CopiesEnv envS (renEnv Ef envS) :=
  ⟨constsCopy_map Ef envS.consts, rfl, hnd⟩

/-- **Only statements at unreserved names move.** -/
theorem renEnv_stmt (Ef envS : Env) : StmtCopies envS (renEnv Ef envS) := by
  intro n c c' hf hf' hne
  rw [renEnv_find, hf] at hf'
  obtain rfl := Option.some.inj hf'
  have hn : c.name = n := Env.find?_name hf
  rw [← hn]
  exact (renS_copy Ef c).2 hne

/-! ## The shared names -/

/-- **The names the input shares with the solution**: those of some shared cone read in the
input's final environment. -/
@[expose] def Shared (JS : Solution) (Ef : Env) (n : Name) : Prop :=
  ∃ T, ConeClosed JS Ef.find? Ef.findTable? T ∧ T n

theorem shared_closed (JS : Solution) (Ef : Env) :
    ConeClosed JS Ef.find? Ef.findTable? (Shared JS Ef) := by
  intro n ⟨T, hT, hn⟩
  obtain ⟨hg, hc⟩ := hT n hn
  exact ⟨hg, fun ci hci m hm => ⟨T, hT, hc ci hci m hm⟩⟩

theorem entryNeeds_congr {mates : Std.HashMap Name (Array Name)}
    {f g : Name → Option ProjTable} {ci : ConstantInfo}
    (h : f ci.toConstantVal.name = g ci.toConstantVal.name) :
    entryNeeds mates f ci = entryNeeds mates g ci := by
  simp only [entryNeeds, h]

/-- **A cone read at an earlier environment is one of the final environment**, whose entries and
tables at the earlier names are the earlier ones. -/
theorem coneClosed_lift {JS : Solution} {E Ef : Env} {T : Name → Prop}
    (hfind : ∀ x ci, E.find? x = some ci → Ef.find? x = some ci)
    (htab : ∀ x, (E.find? x).isSome = true → Ef.findTable? x = E.findTable? x)
    (h : ConeClosed JS E.find? E.findTable? T) : ConeClosed JS Ef.find? Ef.findTable? T := by
  intro n hn
  obtain ⟨⟨ci, ci', h1, h2, h3, h4⟩, hc⟩ := h n hn
  have hs : (E.find? n).isSome = true := by rw [h1]; rfl
  refine ⟨⟨ci, ci', hfind n ci h1, h2, h3, by rw [htab n hs]; exact h4⟩, fun c hc' m hm => ?_⟩
  rw [hfind n ci h1] at hc'
  obtain rfl := Option.some.inj hc'
  have hnm : ci.toConstantVal.name = n := Env.find?_name h1
  rw [entryNeeds_congr (g := E.findTable?) (by rw [hnm]; exact htab n hs)] at hm
  exact hc ci h1 m hm

theorem cone_shared {JS : Solution} {Ef : Env} {T : Name → Prop}
    (h : ConeClosed JS Ef.find? Ef.findTable? T) {n : Name} (hn : T n) : Shared JS Ef n :=
  ⟨T, h, hn⟩

/-! ## A shared name's copies -/

theorem copyB_spec {ci' ci : ConstantInfo} (h : copyB ci' ci = true) :
    (ci.toConstantVal.levelParams = ci'.toConstantVal.levelParams ∧ ci = ci') ∨
    (ci.toConstantVal.levelParams ≠ ci'.toConstantVal.levelParams ∧ ci'.isStmtKind = true ∧
      reservedBasisNames.contains ci'.name = false ∧
      levelsRenaming ci'.toConstantVal.levelParams ci.toConstantVal.levelParams = true ∧
      ci = ci'.atLps ci.toConstantVal.levelParams) := by
  unfold copyB at h
  dsimp only at h
  split at h
  · next he => exact .inl ⟨by simpa using he, ConstantInfo.eq_of_beqP h⟩
  · next he =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hk, hr⟩, hl⟩, hb⟩ := h
    refine .inr ⟨by simpa using he, hk, ?_, hl, ?_⟩
    · have : ci'.toConstantVal.name = ci'.name := by cases ci' <;> rfl
      rw [← this]; exact hr
    · rw [← ConLeche.Cached.ConstantInfo.atLps_eq_atLpsC] at hb
      exact (ConstantInfo.eq_of_beqP hb).symm

theorem cv_name_eq (c : ConstantInfo) : c.toConstantVal.name = c.name := by cases c <;> rfl

/-- **A shared name's input copy refines the renamed solution's.** -/
theorem refines_ren {JS : Solution} {Ef envS : Env} (hJ : JS.idx = mkFEnv envS) {n : Name}
    (hg : ConeGood JS Ef.find? Ef.findTable? n) :
    ∃ ci ci', Ef.find? n = some ci ∧ (renEnv Ef envS).find? n = some ci' ∧ Refines ci ci' ∧
      (reduceOpNames.contains n = true → ci' = ci) := by
  obtain ⟨ci, cS, h1, h2, h3, -⟩ := hg
  rw [hJ, mkFEnv_find?] at h2
  suffices hs : Refines ci (renS Ef cS) ∧ (reduceOpNames.contains n = true → renS Ef cS = ci) from
    ⟨ci, renS Ef cS, h1, by rw [renEnv_find, h2]; rfl, hs⟩
  have hnS : cS.name = n := Env.find?_name h2
  have hnC : ci.name = n := Env.find?_name h1
  have hrenS : renS Ef cS = (if cS.isStmtKind && !reservedBasisNames.contains cS.name &&
        ci.toConstantVal.levelParams != cS.toConstantVal.levelParams &&
        levelsRenaming cS.toConstantVal.levelParams ci.toConstantVal.levelParams
      then cS.atLps ci.toConstantVal.levelParams else cS) := by
    unfold renS; rw [hnS, h1]
  have hyes : ∀ (hk : cS.isStmtKind = true) (hr : reservedBasisNames.contains cS.name = false)
      (hl : ci.toConstantVal.levelParams ≠ cS.toConstantVal.levelParams)
      (hlr : levelsRenaming cS.toConstantVal.levelParams ci.toConstantVal.levelParams = true),
      renS Ef cS = cS.atLps ci.toConstantVal.levelParams := by
    intro hk hr hl hlr
    rw [hrenS]
    simp only [hk, hr, hlr, Bool.not_false, Bool.true_and, Bool.and_true, bne_iff_ne, ne_eq, hl,
      not_false_eq_true, ↓reduceIte]
  have hno : ci.toConstantVal.levelParams = cS.toConstantVal.levelParams → renS Ef cS = cS := by
    intro hl
    rw [hrenS]
    simp [hl]
  unfold refinesB at h3
  rcases Bool.or_eq_true_iff.mp h3 with h3 | h3
  · rcases copyB_spec h3 with ⟨hl, rfl⟩ | ⟨hl, hk, hr, hlr, he⟩
    · rw [hno hl]; exact ⟨.inl rfl, fun _ => rfl⟩
    · rw [hyes hk hr hl hlr]; exact ⟨.inl he, fun _ => he.symm⟩
  · cases ci with
    | axiomInfo cv =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3
      obtain ⟨⟨hk, hro⟩, hc⟩ := h3
      have hro' : reduceOpNames.contains n = true → False := fun h => by
        rw [cv_name_eq, hnS, h] at hro; exact nomatch hro
      rcases copyB_spec hc with ⟨hl, he⟩ | ⟨hl, -, hr, hlr, he⟩
      · rw [hno hl]; exact ⟨.inr ⟨he, hk⟩, fun h => (hro' h).elim⟩
      · rw [hyes hk hr hl hlr]
        refine ⟨.inr ⟨?_, by rw [atLps_isStmtKind]; exact hk⟩, fun h => (hro' h).elim⟩
        rw [he, atLps_cv]
        rfl
    | _ => simp at h3

end ConLeche.Model.Solution
