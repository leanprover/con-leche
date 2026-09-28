module

import ConLeche.Model.Inductives.ClassRunWF
public import ConLeche.Model.Inductives.ClassStage
public import ConLeche.Verify.Inductives.ClassInv
public import ConLeche.Model.Inductives.BlockRecRule
public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Cached.Erase

public section

/-!
# The defeq tier, read: `AliasKeySem` at the hole context (P2d, item 1)

The class check's coarser identification (`classAliases`) matched an
occurrence `I.{us} p⃗ …` with a container class `ci` per component: the
levels `isEquiv`, every parameter `pᵢ` either equal up to annotations to
the class's hole-form parameter `qᵢ`, or both inferred and `isDefEq` —
at the HOLE context (the canonical parameters, the members' holes, one
hole per container class).  `AliasKeySem` (`ClassStage.lean`) is that
match read: at every valuation of the hole context that satisfies it
(`WalkCtx`), the alias's key reads as the class's key in hole form.
The per-component defeq is `Rules.defeq_sound` at the hole context, the
readings exist by `acceptedReads_of`, the frame/context/grading of both
sides by `WalkCtx.subjOkL` — the same argument as the old route's
`param_read_eq`, over the class check's holes.

Premises: every fvar leaf of the defeq tier's candidates, of the
classes' member-abstracted parameters and of the classes' holes is an
entry of the hole context `L` (a syntactic fact of the crests, discharged
with the context's construction).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo ClassAlias ClassRun classCtxOf classHi FEnv BlockParts
  ConstantInfo ConstantVal TargetMajor ClassCtor classAge classMates)

universe u

/-- **The leaves of the class abstraction**: the term's, and the holes'. -/
theorem fvarLeaves_classAbsSpec {occ : Expr → Option (Expr × Nat)} {P : Nat × Expr → Prop}
    (hocc : ∀ x h n, occ x = some (h, n) → ∀ l ∈ h.fvarLeaves, P l) :
    ∀ (e : Expr) (hd : Option (Expr × Nat)),
      (∀ h n, hd = some (h, n) → ∀ l ∈ h.fvarLeaves, P l) →
      (∀ l ∈ e.fvarLeaves, P l) → ∀ l ∈ (ConLeche.classAbsSpec occ hd e).fvarLeaves, P l := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hd hhd he l hl
    simp only [Expr.fvarLeaves, List.mem_append] at he
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold ConLeche.classAbsSpec at hl
      split at hl
      · rename_i h hh
        exact hocc _ _ _ hh l hl
      · rename_i h n hh
        simp only [Expr.fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact ihf (some (h, n)) (fun h' n' e => by
            simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
            exact hocc _ _ _ hh) (fun l h => he l (Or.inl h)) l hl
        · exact iha none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
      · simp only [Expr.fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact ihf none (fun _ _ e => nomatch e) (fun l h => he l (Or.inl h)) l hl
        · exact iha none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
    · exact hhd h 0 rfl l hl
    · simp only [ConLeche.classAbsSpec, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact ihf (some (h, n)) (fun h' n' e => by
          simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact hhd h (n + 1) rfl) (fun l h => he l (Or.inl h)) l hl
      · exact iha none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
  | lam t b m iht ihb =>
    intro hd hhd he l hl
    simp only [Expr.fvarLeaves, List.mem_append] at he
    rcases hd with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact iht none (fun _ _ e => nomatch e) (fun l h => he l (Or.inl h)) l hl
      · exact ihb none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
    · exact hhd h 0 rfl l hl
    · simp only [ConLeche.classAbsSpec] at hl
      exact he l (by simpa [Expr.fvarLeaves] using hl)
  | forallE t b m iht ihb =>
    intro hd hhd he l hl
    simp only [Expr.fvarLeaves, List.mem_append] at he
    rcases hd with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact iht none (fun _ _ e => nomatch e) (fun l h => he l (Or.inl h)) l hl
      · exact ihb none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
    · exact hhd h 0 rfl l hl
    · simp only [ConLeche.classAbsSpec] at hl
      exact he l (by simpa [Expr.fvarLeaves] using hl)
  | letE t v b iht ihv ihb =>
    intro hd hhd he l hl
    simp only [Expr.fvarLeaves, List.mem_append] at he
    rcases hd with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact iht none (fun _ _ e => nomatch e) (fun l h => he l (Or.inl (Or.inl h))) l hl
      · exact ihv none (fun _ _ e => nomatch e) (fun l h => he l (Or.inl (Or.inr h))) l hl
      · exact ihb none (fun _ _ e => nomatch e) (fun l h => he l (Or.inr h)) l hl
    · exact hhd h 0 rfl l hl
    · simp only [ConLeche.classAbsSpec] at hl
      exact he l (by simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢; exact hl)
  | proj s i x ih =>
    intro hd hhd he l hl
    simp only [Expr.fvarLeaves] at he
    rcases hd with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, Expr.fvarLeaves] at hl
      exact ih none (fun _ _ e => nomatch e) he l hl
    · exact hhd h 0 rfl l hl
    · simp only [ConLeche.classAbsSpec] at hl
      exact he l (by simpa [Expr.fvarLeaves] using hl)
  | _ =>
    intro hd hhd he l hl
    rcases hd with _ | ⟨h, _ | n⟩
    · exact he l hl
    · exact hhd h 0 rfl l hl
    · exact he l hl

section Sem

variable {V : Type u} [SetTheory V]
  {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts} {block : List ConstantInfo}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {ctors : List (List ClassCtor)}

/-- **`AliasKeySem` at the run**: at every valuation satisfying the hole
context `L`, an alias's key reads as its class's key in hole form. -/
theorem classRun_aliasKeySem {F : Nat}
    (R : ClassRun (ConLeche.fueledOps .verified F) fe₁ env₁ fe p block cvTas ctorsAs out ctors)
    (m : EnvModel V env₁) (φ : Name → Nat)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (m.acval n ψ).liftN 1 k = m.acval n ψ)
    (hin : Rules.RulesInputs V m φ)
    (hwf : ClassOccWF R.cls (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls))
    {L : List Expr} (hL : FvarList (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls) L)
    (hLc : ∀ e ∈ R.cands, ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hLd : ∀ c ∈ R.cls, ∀ x ∈ c.dsA, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hLh : ∀ c ∈ R.cls, ∀ h, c.hole = some h → ∀ l ∈ h.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) :
    AliasKeySem V m.acval env₁ φ R.cls R.al (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls)
      (fun τ => ∃ Δ, WalkCtx V m φ (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls) τ Δ L) := by
  generalize hH : classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls = H at *
  intro a ha
  obtain ⟨e, he, us, hfn, hle, hps, hlv_eq, ci, hci, hI, hN, hh, hlv, hdef⟩ := R.halFrom a ha
  rw [hH] at hdef
  refine ⟨ci, hci, hh, fun τ hτ r r' hr hr' => ?_⟩
  obtain ⟨Δ0, hW0⟩ := hτ
  -- the candidate's guard: its parameters are bound-closed
  have hguard : ∀ x ∈ e.getAppArgs.take a.nPc, x.bvarB = 0 := by
    obtain ⟨I, us', nPc, hfn', hl, -, hx⟩ := R.hcand e he
    rw [hfn] at hfn'
    simp only [Expr.const.injEq] at hfn'
    obtain ⟨rfl, -⟩ := hfn'
    obtain ⟨c, hc, hcm⟩ := List.mem_filterMap.mp (lookup_mem hl)
    split at hcm
    · rename_i hcn
      simp only [Option.some.injEq, Prod.mk.injEq] at hcm
      obtain ⟨hcI, hcN⟩ := hcm
      have hcs : c.hole.isSome := by
        rw [classInfosD_hole_isSome R.hcls hc]; exact hcn
      have hcis : ci.hole.isSome := by rw [hh]; rfl
      have : c.nPc = ci.nPc := hwf.nPc c hc ci hci hcs hcis (by rw [hcI, hI])
      have hn : a.nPc = nPc := by rw [← hN, ← this, hcN]
      intro x hx'
      rw [hn] at hx'
      exact (hx x hx').1
    · exact nomatch hcm
  -- the hole-form parameters: scoped, bound-closed, their leaves in the context
  have hocc : ∀ x h n, ConLeche.classOcc? R.cls x = some (h, n) →
      Expr.fvarsBelow H h ∧ h.looseBVarsBounded 0 = true := by
    intro x h n hx
    obtain ⟨c', hc', hch, -⟩ := classOcc_spec hwf hx
    obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c' hc' h hch
    exact ⟨hi, rfl⟩
  have hsc : ci.hole.isSome := by rw [hh]; rfl
  obtain ⟨-, hk2⟩ := looseBVarsBounded_mkAppN_inv (hwf.keyScoped ci hci hsc).2
  have hqB : ∀ q ∈ ci.holeForm R.cls, q.looseBVarsBounded 0 = true := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    rw [ConLeche.classAbs_eq_spec]
    obtain ⟨-, hk1⟩ := fvarsBelow_mkAppN_inv (hwf.keyScoped ci hci hsc).1
    exact (classAbsSpec_scoped hocc y none 0 (fun _ _ e => nomatch e) (hk1 y hy) (hk2 y hy)).2
  have hqL : ∀ q ∈ ci.holeForm R.cls, ∀ l ∈ q.fvarLeaves, Expr.fvar l.1 l.2 ∈ L := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    rw [ConLeche.classAbs_eq_spec]
    refine fvarLeaves_classAbsSpec (P := fun l => Expr.fvar l.1 l.2 ∈ L) (fun x h n hx => ?_) y
      none (fun _ _ e => nomatch e) (hLd ci hci y hy)
    obtain ⟨c', hc', hch, -⟩ := classOcc_spec hwf hx
    exact hLh c' hc' h hch
  have hpL : ∀ x ∈ e.getAppArgs.take a.nPc, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ L :=
    fun x hx l hl => hLc e he l (ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_take hx) l hl)
  -- the per-component agreement
  have hagree : OptAgree (ValAgree V (fun τ => ∃ Δ, WalkCtx V m φ H τ Δ L) 0)
      (denoteMeta m.acval env₁ φ H (aliasKey a)) (denoteMeta m.acval env₁ φ H (holeKey R.cls ci)) := by
    unfold aliasKey holeKey
    obtain ⟨hlen, hpair⟩ := ConLeche.classParamsDefEq_true hdef
    refine optAgree_mkAppN _ _ (by rw [hps, List.length_map, hlen]) ?_ ?_
    · have hs : Expr.SemEq (.const a.ind a.lvls) (.const ci.key.ind ci.key.lvls) := by
        obtain ⟨hl1, hl2⟩ := Level.evalEqList_of_isEquivList hlv
        rw [hlv_eq]
        exact ⟨hI.symm, hl1, hl2⟩
      rw [denoteMeta_semEq hs]
      exact optAgree_refl' _
    · intro i a2 a1 ha2 ha1
      rw [hps, List.getElem?_map] at ha2
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ha2
      have hxe : Expr.SemEq x x.eraseFVarTys := Expr.SemEq.eraseR (Expr.SemEq.refl x)
      rw [← denoteMeta_semEq hxe]
      have hxm : x ∈ e.getAppArgs.take a.nPc := List.mem_of_getElem? hx
      have ha1m : a1 ∈ ci.holeForm R.cls := List.mem_of_getElem? ha1
      rcases hpair i x a1 hx ha1 with heq | ⟨⟨ta, hta⟩, ⟨tb, htb⟩, hd⟩
      · -- equal up to annotations
        have h1 : Expr.SemEq x x.eraseFVarTys := hxe
        have h2 : Expr.SemEq a1 a1.eraseFVarTys := Expr.SemEq.eraseR (Expr.SemEq.refl a1)
        rw [denoteMeta_semEq h1, heq, ← denoteMeta_semEq h2]
        exact optAgree_refl' _
      · change inferTypeCore .verified env₁ F H x = .ok ta at hta
        change inferTypeCore .verified env₁ F H a1 = .ok tb at htb
        change isDefEqCore .verified env₁ F H x a1 = .ok true at hd
        have hxB : x.looseBVarsBounded 0 = true := ConLeche.Expr.bvarB_le (by
          rw [hguard x hxm]; exact Nat.le_refl 0)
        have ha1B := hqB a1 ha1m
        obtain ⟨xa, hxa⟩ := acceptedReads_of m φ hta (wscoped_of_leaves_mem hL _ (hpL x hxm)) hxB
          (fun l hl => hW0.2.2.2.2.1 _ (hpL x hxm l hl))
        obtain ⟨qa, hqa⟩ := acceptedReads_of m φ htb (wscoped_of_leaves_mem hL _ (hqL a1 ha1m))
          ha1B (fun l hl => hW0.2.2.2.2.1 _ (hqL a1 ha1m l hl))
        rw [hxa, hqa]
        intro vals τ' hvl ⟨Δ', hW'⟩
        obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero hvl
        obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl hin hL hW' (hpL x hxm) hxB hxa
          ⟨_, Rules.inferTypeCore_bridge hta⟩
        obtain ⟨hFrB, hCB, hGB⟩ := WalkCtx.subjOkL hacl hin hL hW' (hqL a1 ha1m) ha1B hqa
          ⟨_, Rules.inferTypeCore_bridge htb⟩
        simpa [consList_nil] using Rules.defeq_sound hin (Rules.isDefEqCore_bridge hd) hFrA hFrB
          hCA hCB hxa hqa hGA hGB τ' hW'.2.1
  rw [hr, hr'] at hagree
  have := hagree [] τ rfl ⟨Δ0, hW0⟩
  simpa [consList_nil] using this

end Sem

end ConLeche.Model
