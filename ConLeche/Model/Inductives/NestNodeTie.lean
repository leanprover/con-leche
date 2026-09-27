module

public import ConLeche.Model.Inductives.ContSem
public import ConLeche.Verify.Inductives.RecNestKTie
import ConLeche.Model.Inductives.PosDerivMonoK
import ConLeche.Verify.Inductives.LayoutKSpec

public section

/-!
# The model side of the node lemma's determinism ties (PRIMREC / NESTKN-NL)

`groupsOkK_of_cover`: the canonical groups of a context reading a covered environment
are consistent (`GroupsOkK`, the hypothesis of `NestRouteRun.contLay_node`): a stored
container's group is its recorded block's names (`ContBlockOk.all`), and so is each
mate's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche (Env Name NestCtx IndCaps ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

omit [SetTheory V] in
theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.eraseDups_cons]
    have ha := (List.nodup_cons.mp h).1
    have hf : l.filter (fun b => !b == a) = l :=
      List.filter_eq_self.mpr fun b hb => by
        have : b ≠ a := fun e => ha (e ▸ hb)
        simpa using this
    rw [hf, eraseDups_of_nodup (List.nodup_cons.mp h).2]

/-- A stored inductive recorded in a block has that block's names as its group. -/
theorem groupOfK_of_block {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env} {ctx : NestCtx}
    (hcov : ContCover mp ctx) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) : ConLeche.groupOfK ctx (D.member mm) = D.names := by
  have hblk := hcov.block D hD
  obtain ⟨cv, caps, hf⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  have hall := hblk.all mm hmm cv caps hf
  have hb : ConLeche.nestBlockOf ctx (D.member mm) = D.names := by
    unfold ConLeche.nestBlockOf
    rw [hcov.find, hf]
    exact hall
  have hmem := LfpDatum.member_mem_names mp hD hmm
  unfold ConLeche.groupOfK
  simp only [hb, List.contains_eq_mem, List.mem_eraseDups, hmem, decide_true, if_true]
  exact eraseDups_of_nodup hblk.nodup

/-- **The canonical groups are consistent** at a context reading a covered environment. -/
theorem groupsOkK_of_cover {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env} {ctx : NestCtx}
    (hcov : ContCover mp ctx) : ConLeche.GroupsOkK ctx := by
  intro C hC hq n hn
  cases hf : env.find? C with
  | some ci =>
    cases ci with
    | indInfo cv caps =>
      obtain ⟨D, hD, mm, hmm, rfl⟩ := hcov.cover _ cv caps hf hC hq
      rw [groupOfK_of_block hcov hD hmm] at hn ⊢
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
      have hk := lfp_namesLen mp hD
      have hmi : D.member i = D.names[i] := by
        unfold LfpDatum.member
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      rw [← hmi, groupOfK_of_block hcov hD (by omega)]
    | _ =>
      have hb : ConLeche.nestBlockOf ctx C = [] := by
        unfold ConLeche.nestBlockOf; rw [hcov.find, hf]
      have hg : ConLeche.groupOfK ctx C = [C] := by
        unfold ConLeche.groupOfK; simp [hb]
      rw [hg] at hn; rw [List.mem_singleton.mp hn]
  | none =>
    have hb : ConLeche.nestBlockOf ctx C = [] := by
      unfold ConLeche.nestBlockOf; rw [hcov.find, hf]
    have hg : ConLeche.groupOfK ctx C = [C] := by
      unfold ConLeche.groupOfK; simp [hb]
    rw [hg] at hn; rw [List.mem_singleton.mp hn]

end ConLeche.Model
