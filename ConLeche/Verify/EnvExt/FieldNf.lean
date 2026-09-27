module

public import ConLeche.Verify.EnvExt.Base
public import ConLeche.Verify.EnvExt.Ok
public import ConLeche.Kernel.Inductives.FieldNf
import ConLeche.Verify.EnvExt.Knot
import ConLeche.Verify.EnvExt.ScOps

public section

/-!
# Env extension, part 12: the walk's field normal form

`nestNf`/`nestTeleNf` (`Kernel/Inductives/FieldNf.lean`) recompute the
positivity walk's field normal forms without its decisions — the
helper a rec check that re-reads an older home's constructor fields at
a later environment runs.  At the pure operations (`fueledOps`) they
are in the currency whenever their input is scoped (the
`Telescope.lean` pattern), so the member tie
(`Semantics/FoldScope.lean`, `memberTie_nestTeleNf`) holds of them.
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (mode : CheckMode) (F : Nat)
  (names : List Name) (nP hi : Nat)

theorem nestNf_ok (H : Agree N E₁ E₂) :
    ∀ (fuel dep : Nat) {e : Expr}, Sc N e →
      Ok (Sc N) (nestNf (fueledOps mode F) E₂ names nP hi fuel dep e)
        (nestNf (fueledOps mode F) E₁ names nP hi fuel dep e)
  | 0, _, _, _ => Ok.throw _
  | fuel + 1, dep, e, he => by
    simp only [nestNf]
    refine Ok.bind ((pureFns_ok mode H F).whnf dep e he) (fun w hw => ?_)
    unfold nestNfAt
    split
    · exact Ok.pure (by split <;> assumption)
    · split
      · rename_i a b bm
        have hpi := sc_forallE.mp hw
        refine Ok.bind (nestNf_ok H fuel (dep + 1)
          (sc_instantiate1' hpi.2 (sc_fvar.mpr hpi.1))) (fun nb hnb => ?_)
        exact Ok.pure (sc_forallE.mpr ⟨hpi.1, sc_abstract1 _ _ _ hnb⟩)
      · exact Ok.pure hw

theorem nestTeleNf_ok (H : Agree N E₁ E₂) (fuel base : Nat) :
    ∀ (nF j : Nat) {cur : Expr}, Sc N cur →
      Ok (fun r => (∀ x ∈ r.1, Sc N x.1) ∧ Sc N r.2)
        (nestTeleNf (fueledOps mode F) E₂ names nP hi fuel base nF j cur)
        (nestTeleNf (fueledOps mode F) E₁ names nP hi fuel base nF j cur)
  | 0, _, _, hc => by
    simp only [nestTeleNf]; exact Ok.pure ⟨fun _ h => (nomatch h), hc⟩
  | nF + 1, j, cur, hc => by
    simp only [nestTeleNf]
    split
    · rename_i a b bm
      have hpi := sc_forallE.mp hc
      refine Ok.bind (nestNf_ok mode F names nP hi H fuel (base + j) hpi.1) (fun nd hnd => ?_)
      refine Ok.bind (nestTeleNf_ok H fuel base nF (j + 1)
        (sc_instantiate1' hpi.2 (sc_fvar.mpr hpi.1))) (fun r hr => ?_)
      obtain ⟨nds, res⟩ := r
      refine Ok.pure ⟨fun x hx => ?_, hr.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hnd
      · exact hr.1 x hx
    · exact Ok.throw _

/-- **The field normal form at a base**: on a constructor type resolving
in `B`, a success of the helper at the later of two environments
extending `B` without new in-scope names is the earlier one's. -/
theorem nestTeleNf_base_agree {B : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
    (hnat : NatOpGuards B)
    (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
    (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) (h₁₂ : Extends E₁ E₂) (fuel base nF j : Nat)
    {cur : Expr} (hc : cur.constsResolve B = true) {r : List (Expr × BinderMeta) × Expr}
    (h : nestTeleNf (fueledOps mode F) E₂ names nP hi fuel base nF j cur = .ok r) :
    nestTeleNf (fueledOps mode F) E₁ names nP hi fuel base nF j cur = .ok r :=
  (nestTeleNf_ok mode F names nP hi (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂) fuel base
    nF j (sc_of_constsResolve hc) r h).1

end ConLeche.EnvExt
