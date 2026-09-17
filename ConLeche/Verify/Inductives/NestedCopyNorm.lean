module

public import ConLeche.Verify.Inductives.NestedCopyTele
public import ConLeche.Verify.Inductives.MutualNormPres
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The constructors' normalisation keeps the residual (task #315 L-B)

`normCtorValM` (`Kernel/Inductives/MutualInstall.lean`) opens a
constructor's type at its `nP` parameters, normalises the `nF` field
DOMAINS positively (`normPosDomM`) and closes the telescope back up
around the residual it never touched.  `normCtorValM_resid`
(`NestedCopyRewrite`'s neighbour `NestedInv`) already says the stored
type is that re-closure; what a READER of the stored type needs on top
is that the re-closure can be opened again and gives the same residual
back.

That is a frame fact and this module is it: the positivity walk keeps
a term bound-variable closed (`normPosDomM_bounded` —
`normPosDomM_pres` without its scoping half, which the copy's binders
do not supply), hence so does the field telescope
(`normFieldDomsM_bounded`), hence the re-closure is a telescope over
CLOSED domains (`normCtorValM_frame`), which is exactly the hypothesis
of the round trip `openPisAtFvars_closeTelescope`.  The consumer
`normCtorValM_openResid` reads the stored type's two-stage opening and
lands on the residual of the GIVEN type, modulo annotations.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A member of a `zipWith` is its function at members of the two
lists. -/
private theorem mem_zipWithD {α β γ : Type} {g : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β} {c : γ}, c ∈ List.zipWith g l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, c = g a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWithD h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

/-- Two consecutive openings are one. -/
private theorem openPisAtFvars_addD :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr}
      {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, _m, _e, _d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, e, d, fvs, fvs', o, o', h, h' => by
    match e, h with
    | .forallE _dom _body _mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next _fvs₁ _e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h'' := openPisAtFvars_addD n h₁
          (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
        rw [show n + 1 + m = n + m + 1 from by omega]
        simp only [openPisAtFvars]
        rw [h'']
        rfl
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- **The positivity normalisation keeps a term bound-variable
closed**: `normPosDomM_pres` without the `WScoped` half.  Each `whnf`
step preserves the bound (`whnf_looseBVars`) and the Π step opens at a
fresh `fvar` and closes with `abstract1`, which is exactly the
`instantiate1`/`abstract1` round trip on the bound.  The scoping half
is dropped because a copy's stored binders carry no context depth to
state it at — the reader only ever needs closedness. -/
theorem normPosDomM_bounded {env : Env} (henv : EnvWF env) {memberNames : List Name} {F : Nat} :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr},
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok e' →
      e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro d e e' h hb
    rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
    · exact hb
    have hwb : w.looseBVarsBounded 0 = true := whnf_looseBVars henv F hw hb
    rcases hcase with rfl | ⟨dom, body, bm, body', fuel', rfl, rfl, -, hbody', rfl⟩
    · exact hwb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwb
    have hopenb : (body.instantiate1 (.fvar d dom)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hwb.2
    have hb' := ih fuel' (by omega) hbody' hopenb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hwb.1, looseBVarsBounded_abstract1 body' 0 hb'⟩

/-- **The field telescope's domains are bound-variable closed**: the
walk peels a `∀` whose domain is closed because the whole type is,
normalises it (`normPosDomM_bounded`) and recurses on the body OPENED
at a fresh variable, which is closed again.  This is the hypothesis
`openPisAtFvars_closeTelescope` asks of the binders the constructor's
normalisation re-closes. -/
theorem normFieldDomsM_bounded {env : Env} (henv : EnvWF env) {memberNames : List Name} {F : Nat} :
    ∀ {n i : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames i n e = .ok (bs, r) →
      e.looseBVarsBounded 0 = true →
      ∀ b ∈ bs, b.1.looseBVarsBounded 0 = true := by
  intro n
  induction n with
  | zero =>
    intro i e bs r h _hb
    obtain ⟨rfl, -⟩ := normFieldDomsM_zero_inv h
    intro b hbmem
    exact absurd hbmem (by simp)
  | succ n ih =>
    intro i e bs r h hb
    obtain ⟨dom, body, bm, dom', bs', rfl, hdom, hrec, rfl⟩ := normFieldDomsM_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hdom' : dom'.looseBVarsBounded 0 = true :=
      normPosDomM_bounded henv 1024 hdom hb.1
    have hopen : (body.instantiate1 (.fvar i dom)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    intro b hbmem
    rcases List.mem_cons.mp hbmem with rfl | hbmem
    · exact hdom'
    · exact ih hrec hopen b hbmem

/-- **THE STORED CONSTRUCTOR'S TYPE IS A CLOSED TELESCOPE OVER THE
GIVEN TYPE'S RESIDUAL** (`normCtorValM_resid` with the two facts its
reader needs): the re-closed telescope has exactly `nP + nF` binders —
one per opened parameter (`openPisAtFvars_length`, `stripPis_length`)
and one per normalised field (`normFieldDomsM_open`) — and every one of
their domains is bound-variable closed: the parameters' are the
openers' own types (`openPisAtFvars_bounded`), the fields' are
`normFieldDomsM_bounded`'s. -/
theorem normCtorValM_frame {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true) :
    cvCa' = cvCa ∨
      ∃ (bs : List (Expr × BinderMeta)) (fvs xFvs : List Expr) (crest xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvs, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        bs.length = nP + nF ∧
        (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) ∧
        cvCa'.type = closeTelescope bs 0 xrest := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cres⟩ := q
  try simp only at h
  obtain ⟨rr, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvs, crest⟩ := rr
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  try simp only at h
  obtain ⟨xFvs, hopX, hfbs⟩ := normFieldDomsM_open hu
  have hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest) := unwrapOr_ok hr
  have hcbs : cbs.length = nP := Expr.stripPis_length nP (unwrapOr_ok hq)
  have hfvs : fvs.length = nP := Verify.openPisAtFvars_length nP hop1
  obtain ⟨hcrest, hfvsb⟩ := Verify.openPisAtFvars_bounded nP hop1 hb
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  · refine Or.inr ⟨List.zipWith (fun (x : Expr) (bb : Expr × BinderMeta) => (x.fvarTypeD, bb.2))
        fvs cbs ++ fbs, fvs, xFvs, crest, resid, hop1, hopX, ?_, ?_, ?_⟩
    · simp [hfvs, hcbs, hfbs]
    · intro b hbmem
      rcases List.mem_append.mp hbmem with hbmem | hbmem
      · obtain ⟨x, hx, _bb, -, rfl⟩ := mem_zipWithD hbmem
        exact hfvsb x hx
      · exact normFieldDomsM_bounded henv hu hcrest b hbmem
    · rw [checkConstantValPre_ok h]

/-- **THE STORED TYPE READS BACK TO THE GIVEN TYPE'S RESIDUAL** (task
#315 L-B): open the constructor type the normalisation STORED at its
`nP` parameters and then at its `nF` fields, and what is left is the
residual the same two-stage opening of the type the normalisation was
GIVEN hands back — modulo annotations, which the re-closure's
`abstract1`/`instantiate1` round trip may move (`Expr.ErasedEq`).
Either the stage stored its input unchanged, or `normCtorValM_frame`'s
telescope is re-opened by `openPisAtFvars_closeTelescope`, at the very
length the two openings consume. -/
theorem normCtorValM_openResid {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true)
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    {fvs' xFvs' : List Expr} {crest' xrest' : Expr}
    (hop1' : openPisAtFvars nP cvCa'.type 0 = some (fvs', crest'))
    (hop2' : openPisAtFvars nF crest' nP = some (xFvs', xrest')) :
    Expr.ErasedEq xrest' xrest := by
  rcases normCtorValM_frame henv h hb with rfl |
    ⟨bs, fvs₀, xFvs₀, crest₀, xrest₀, hA, hB, hlen, hdoms, hty⟩
  · -- the stage stored its input: the two openings are the same calls
    rw [hop1] at hop1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
    obtain ⟨rfl, rfl⟩ := hop1'
    rw [hop2] at hop2'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop2'
    obtain ⟨rfl, rfl⟩ := hop2'
    exact Expr.ErasedEq.rfl _
  -- the given type's openings are the ones the frame hands back
  rw [hop1] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  obtain ⟨rfl, rfl⟩ := hA
  rw [hop2] at hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨rfl, rfl⟩ := hB
  have hxb : xrest.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop2 (Verify.openPisAtFvars_bounded nP hop1 hb).1).1
  obtain ⟨fvs₃, r₃, hop₃, -, her₃⟩ := openPisAtFvars_closeTelescope bs 0 xrest hdoms hxb
  rw [hlen] at hop₃
  have hadd : openPisAtFvars (nP + nF) cvCa'.type 0 = some (fvs' ++ xFvs', xrest') :=
    openPisAtFvars_addD nP hop1' (by simpa using hop2')
  rw [hty, hop₃] at hadd
  simp only [Option.some.injEq, Prod.mk.injEq] at hadd
  obtain ⟨-, rfl⟩ := hadd
  exact her₃

end ConLeche
