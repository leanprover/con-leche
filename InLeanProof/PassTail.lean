module

public import InLeanProof.PassClasses
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-classes: the tail's stages (task #451, lane O7-classes)

The stages after the pass, each InLean's twin against master's pure stage on
the translated block:

* `checkBlockIdxSortsFI_run`: every member's index binders have sorts
  (`checkBlockIdxSortsC` against master's `checkBlockIdxSorts`, through
  `checkStructFieldSortsIFI_run`).
* `streamKCheckI_run`: the records' K flags against the generated family's
  (`recKExpected` on the translated majors, `trOut`).

The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## The index sorts -/

/-- **Every member's index binders have sorts** (`checkBlockIdxSortsC`):
InLean's check passing means master's passes on the translated members. -/
theorem checkBlockIdxSortsFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} (hsr : okL p.resSort = true) :
    ∀ {l : List InLean.MemberShape} {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ →
      (∀ ms ∈ l, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true) →
      InLean.checkBlockIdxSortsC (sharedOpsC .verified fe) fe p l s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        CRuns .verified (ConLeche.Cached.checkBlockIdxSortsC .verified (ConLeche.mkFEnv L) (trShape p)
            (l.map trMember))
          (ConLeche.checkBlockIdxSorts (ConLeche.fueledOpsM .verified) L (trShape p)
            (l.map trMember)) () ()
  | [], s₀, s', u, hs, _, h => by
    unfold InLean.checkBlockIdxSortsC at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by
      unfold ConLeche.Cached.checkBlockIdxSortsC ConLeche.checkBlockIdxSorts
      exact CRuns.pure' _ _⟩
  | ms :: rest, s₀, s', u, hs, hok, h => by
    unfold InLean.checkBlockIdxSortsC at h
    obtain ⟨hk1, hk2⟩ := hok ms List.mem_cons_self
    obtain ⟨o, s₁, h1, h⟩ := bind_run h
    obtain ⟨tq, s₂, h2, h⟩ := bind_run h
    cases o with
    | none => simp only [InLean.unwrapOr] at h2; exact (throw_run h2).elim
    | some q =>
    simp only [InLean.unwrapOr] at h2
    obtain ⟨rfl, rfl⟩ := pure_run h2
    obtain ⟨fvs, b⟩ := q
    obtain ⟨hs₁, ht₁, hokf, hopc, hfv⟩ := openClosedI_run hs hk1 hk2 h1 (TabLe.refl _)
    have hop := hopc
    rw [ConLeche.Cached.openPisAtFvarsC_eq] at hop
    obtain ⟨_, s₃, h3, h⟩ := bind_run h
    have hcf : ∀ (i : Nat) (x : ConLeche.Expr), ((TrSL s₁ fvs).drop p.nP)[i]? = some x →
        (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (p.nP + i) x.fvarTypeD ∧
          x.fvarTypeD.looseBVarsBounded 0 = true := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      exact hfv (p.nP + i) x hx
    obtain ⟨hs₃, ht₃, hR3⟩ := checkStructFieldSortsIFI_run hO hsr hcf ms.nIdx hs₁
      (by simp only [OkSL, List.all_eq_true] at hokf ⊢
          exact fun x hx => hokf x (List.mem_of_mem_drop hx)) rfl
      (by simp [TrSL, List.map_drop]) rfl h3
    obtain ⟨hs', ht', hR⟩ := checkBlockIdxSortsFI_run hO hsr hs₃
      (fun m hm => hok m (List.mem_cons_of_mem _ hm)) h
    refine ⟨hs', ht₁.trans (ht₃.trans ht'), ?_⟩
    simp only [List.map_cons]
    unfold ConLeche.Cached.checkBlockIdxSortsC ConLeche.checkBlockIdxSorts
    simp only [trMember_cvT, trCV_type, trMember_nIdx, trShape_nP, hop, hopc, ConLeche.unwrapOr]
    exact CRuns.bind (CRuns.pure' _ _) (CRuns.bind hR3 hR)

/-! ## The K flags -/

/-- A generated recursor with its major and its rules, read at a state. -/
@[expose] def trOut (s : InLean.CState) (g : Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr) :
    ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr :=
  (trCV g.1, trTM s g.2.1, TrSL s g.2.2)

theorem recKExpected_tr (s : InLean.CState) (p : InLean.BlockShape) (M : InLean.TargetMajor) :
    ConLeche.recKExpected (trShape p) (trTM s M) = InLean.recKExpected p M := by
  unfold ConLeche.recKExpected InLean.recKExpected
  simp only [trTM, trShape_k]
  cases M.member with
  | none => rfl
  | some _ =>
    cases hc : M.ctors with
    | nil => rfl
    | cons c cs =>
      cases cs with
      | nil => simp [trCtor, trShape]
      | cons _ _ => rfl

/-- **The records' K flags** (`streamKCheck`): InLean's check passing means
master's passes on the translated records and generated family. -/
theorem streamKCheckI_run (s : InLean.CState) (p : InLean.BlockShape) :
    ∀ {rcs : List InLean.RecShape} {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
      {s₀ s' : InLean.CState} {u : Unit},
      InLean.streamKCheck p rcs out s₀ = .ok (u, s') →
      s' = s₀ ∧ Runs (ConLeche.streamKCheck (m := ConLeche.FueledM) (trShape p) (rcs.map trRec)
        (out.map (trOut s))) ()
  | rc :: rcs, g :: gs, s₀, s', u, h => by
    unfold InLean.streamKCheck at h
    by_cases hk : (rc.isK == InLean.recKExpected p g.2.1) = true
    · simp only [hk, ↓reduceIte] at h
      obtain ⟨hs, hR⟩ := streamKCheckI_run s p h
      refine ⟨hs, ?_⟩
      simp only [List.map_cons]
      unfold ConLeche.streamKCheck
      have hkC : ((trRec rc).isK == ConLeche.recKExpected (trShape p) (trOut s g).2.1) = true := by
        simp only [trRec, trOut, recKExpected_tr]; exact hk
      simp only [hkC, ↓reduceIte]
      exact hR
    · simp only [hk] at h
      obtain ⟨_, _, h1, -⟩ := bind_run h
      exact (throw_run h1).elim
  | [], _, s₀, s', u, h | _ :: _, [], s₀, s', u, h => by
    unfold InLean.streamKCheck at h
    obtain ⟨-, rfl⟩ := pure_run h
    refine ⟨rfl, ?_⟩
    unfold ConLeche.streamKCheck
    first | exact Runs.pure _ | simp only [List.map_cons, List.map_nil]; exact Runs.pure _

end InLeanProof
