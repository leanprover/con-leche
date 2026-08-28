import Setlec.SetR.Bridge.InferStruct

/-!
# `DefEqSpineStepR`, discharged (task #148, T3, batch d — spine part)

`defeqSpine` is the lazy-delta step's attempt to avoid unfolding: if
both sides are the *same* stored constant applied to spines, compare the
levels and the arguments instead of unfolding either head.  Its bridge
is D7 `appCong` — the rule the design gives "two bridge entry points",
this being the second (the first is the stuck block's `.app`/`.app`
congruence, which reuses `defEqL_of_defEqListR` below).

The levels enter through `EnvR.val_params`: the checker compares them
with `Level.isEquiv`, which is sound for `eval` and nothing stronger,
and a constant's valuation reads nothing else — so the two
instantiations are *indistinguishable to the valuation* and the heads'
denotations are equal on the nose, not merely `DefEq`.  That is why D7's
head premise here is `DefEq.refl`.

Repair-independent: neither D7 nor `DefEqL` has an `Infer` premise, so
neither Finding 1's repair nor Finding 3 touches this batch.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- **A constant at level-equivalent instantiations denotes the same
term.**  `val_params` says a valuation reads only its own parameters;
`Level.substFn_of_evalEqList` says the two instantiations agree on all
of them. -/
theorem denote_const_congrR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {d : Nat} {n : Name} {us us' : List Level} {va vb : VExpr}
    (hlev : Level.isEquivList us us' = some true)
    (hva : denote m.cval env φ d (.const n us) = some va)
    (hvb : denote m.cval env φ d (.const n us') = some vb) : va = vb := by
  rw [denote_const] at hva hvb
  cases hf : env.find? n with
  | none => rw [hf] at hva; exact nomatch hva
  | some ci =>
    rw [hf] at hva hvb
    dsimp only at hva hvb
    split at hva
    · split at hvb
      · rw [← Option.some.inj hva, ← Option.some.inj hvb]
        refine m.val_params n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _ (Level.isEquivList_sound hlev φ) p
      · exact nomatch hvb
    · exact nomatch hva

/-- **A certified spine list is a `DefEqL`.**  The transpose of
`defEqList` (`Core.lean:754-761`), one `DefEqL.cons` per certificate, in
the checker's own order — the shape `Tele` and `DefEqL` were designed
for, so the induction is the list's and nothing else. -/
theorem defEqL_of_defEqListR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (ihd : DefEqClaimsR mode m φ fuel) {d : Nat}
    {Δ : List VExpr} :
    ∀ {as bs : List Expr} {vas vbs : List VExpr},
      defEqListP mode env fuel d as bs = .ok true →
      (∀ x ∈ as, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x) →
      (∀ x ∈ bs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x) →
      DenoteSpine m.cval env φ d as vas →
      DenoteSpine m.cval env φ d bs vbs →
      DefEqL mode env m.cval φ Δ vas vbs := by
  intro as
  induction as with
  | nil =>
    intro bs vas vbs h _ _ hsa hsb
    cases hsa
    cases bs with
    | nil => cases hsb; exact DefEqL.nil
    | cons _ _ => simp [defEqListP, defEqList, pure, Except.pure] at h
  | cons x xs ih =>
    intro bs vas vbs h hfa hfb hsa hsb
    cases bs with
    | nil => simp [defEqListP, defEqList, pure, Except.pure] at h
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := defEqList_step_inv h
      cases hsa with | cons hx hsa' => ?_
      cases hsb with | cons hy hsb' => ?_
      obtain ⟨hwx, hbx, hLx, hCx⟩ := hfa x (by simp)
      obtain ⟨hwy, hby, hLy, hCy⟩ := hfb y (by simp)
      exact DefEqL.cons (ihd hxy hwx hbx hLx hwy hby hLy hCx hCy hx hy)
        (ih htail (fun z hz => hfa z (by simp [hz]))
          (fun z hz => hfb z (by simp [hz])) hsa' hsb')

/-- The frame conditions of every argument of a spine. -/
theorem frame_spineR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {a : Expr}
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkR mode cval env φ d Δ a) :
    ∀ x ∈ a.getAppArgs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOkR mode cval env φ d Δ x := by
  intro x hx
  exact ⟨hws.getAppArgs x hx, looseBVarsBounded_getAppArgs hb x hx,
    fun l hl => hLb l (fvarLeaves_getAppArgs hx l hl),
    CtxOkR.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hC⟩

/-- **`DefEqSpineStepR`, proved.** -/
theorem defeqSpine_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (ihd : DefEqClaimsR mode m φ fuel) :
    DefEqSpineStepR (mode := mode) m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨n, us, us', hfa, hfb, hlenAB, hlev, hlist⟩ := defeqSpine_inv h
  -- both sides are the same constant applied to a spine
  have hea : a = Expr.mkAppN (.const n us) a.getAppArgs := by
    rw [← hfa, Expr.mkAppN_getApp]
  have heb : b = Expr.mkAppN (.const n us') b.getAppArgs := by
    rw [← hfb, Expr.mkAppN_getApp]
  rw [hea] at hva
  rw [heb] at hvb
  obtain ⟨vfa, vas, hvfa, hspa, rfl⟩ := denote_mkAppN_inv hva
  obtain ⟨vfb, vbs, hvfb, hspb, rfl⟩ := denote_mkAppN_inv hvb
  -- the two level instantiations are indistinguishable to the valuation
  obtain rfl : vfa = vfb := denote_const_congrR m φ hlev hvfa hvfb
  refine DefEq.appCong ?_ DefEq.refl
    (defEqL_of_defEqListR m φ ihd hlist (frame_spineR hwa hba hLa hCa)
      (frame_spineR hwb hbb hLb hCb) hspa hspb)
  rw [hspa.length, hspb.length, hlenAB]

end Setlec.SetR
