module

public import InLeanProof.PassCtors
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Denote.IndFrame

/-!
# O7-stages: the positivity context against master's (task #451, lane O7-stages)

`blockNestCtxI_run` (`blockNestCtxS_spec`'s twin): InLean's `blockNestCtx`
builds the context master's pure `blockNestCtx` builds at the translated
shape, its parameters and holes read at the final state.  InLean's context
holds the environment (`fe`), master's the lookup (`find?`); `blockNestCtx`
reads neither, so the lookup is any.

* `instPisWithI_tr`: InLean's `instPisWith` at arguments with a closed
  reading is master's at the readings (InLean's also skips `mdata`, which
  the reading drops).
* `nestHolesI_run`: the holes loop (`for` with an early `return none`) reads
  as master's `mapM` over the member indices.
* `nestOccI_tr`, `piDomsOccI_tr`: the occurrence tests (`EO.any`) are
  master's on the reading (a variable through its interned depth).
* `replaceAppsI_tr`: InLean's whole-application replacement (`EO.replace`
  with `phApp?`) is master's `replaceApps` on the reading, given related
  substitutions (`SubRel`); the building block of the canonical crest
  (`nestCanonCrest`), which the uniformity check and the walk read.

The proofs are functional (`bindI_ok`, `pureI_ok`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Instantiating a telescope's leading binders -/

/-- **InLean's `instPisWith`, read**: at arguments with a closed reading, the
result has a reading, and it is master's `instPisWith` at the readings. -/
theorem instPisWithI_tr {s : InLean.CState} :
    ∀ (as : List Lean.Expr) (e : Lean.Expr) {r : Lean.Expr}, OkS s e = true → OkSL s as = true →
      (∀ a ∈ as, (TrS s a).looseBVarsBounded 0 = true) →
      InLean.instPisWith as e = some r →
      OkS s r = true ∧ ConLeche.instPisWith (TrSL s as) (TrS s e) = some (TrS s r)
  | [], e, r, he, _, _, h => by
    simp only [InLean.instPisWith, Option.some.injEq] at h
    subst h
    exact ⟨he, rfl⟩
  | a :: as, .forallE n t b bi, r, he, ha, hc, h => by
    simp only [InLean.instPisWith] at h
    simp only [OkS_forallE, Bool.and_eq_true] at he
    simp only [OkSL_cons, Bool.and_eq_true] at ha
    have hca := hc a List.mem_cons_self
    have hb' := OkS_inst1 he.2 ha.1 hca
    rw [inst1I_eq] at h
    obtain ⟨h1, h2⟩ := instPisWithI_tr as _ hb' ha.2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h
    refine ⟨h1, ?_⟩
    rw [TrS_forallE, TrSL_cons, ConLeche.instPisWith, ← TrS_inst1_eq he.2 ha.1 hca]
    exact h2
  | a :: as, .mdata m e, r, he, ha, hc, h => by
    simp only [InLean.instPisWith] at h
    rw [OkS_mdata] at he
    rw [TrS_mdata]
    exact instPisWithI_tr (a :: as) e he ha hc h
  | _ :: _, .bvar _, _, _, _, _, h | _ :: _, .fvar _, _, _, _, _, h
  | _ :: _, .mvar _, _, _, _, _, h | _ :: _, .sort _, _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, _, h | _ :: _, .app _ _, _, _, _, _, h
  | _ :: _, .lam _ _ _ _, _, _, _, _, h | _ :: _, .letE _ _ _ _ _, _, _, _, _, h
  | _ :: _, .lit _, _, _, _, _, h | _ :: _, .proj _ _ _, _, _, _, _, h => by
    simp [InLean.instPisWith] at h

/-! ## Occurrences of a member or a hole -/

/-- `EO.any` at a predicate that picks a member's constant or a variable of
depth in `lo ..< hi` is master's `nestOcc` on the reading. -/
theorem anySpec_nestOcc (s : InLean.CState) (names : List Lean.Name) (lo hi : Nat)
    (p : Lean.Expr → Bool)
    (hc : ∀ n us, p (.const n us) = names.contains n)
    (hf : ∀ id, p (.fvar id) = match EO.fvDepth? id with
      | some i => lo ≤ i && i < hi
      | none => false)
    (ho : ∀ x, (∀ n us, x ≠ .const n us) → (∀ id, x ≠ .fvar id) → p x = false) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      anySpec (fun x _ => if p x then some true else none) e k =
        ConLeche.Expr.nestOcc (names.map toName) lo hi (TrS s e) := by
  intro e
  induction e with
  | const n us =>
    intro k _
    simp only [anySpec, hc, TrS_const, ConLeche.Expr.nestOcc, contains_map_toName]
    cases names.contains n <;> rfl
  | fvar id =>
    intro k hok
    have hok' := hok
    simp only [OkS, okE, Option.isSome_iff_exists] at hok'
    obtain ⟨c, hcid⟩ := hok'
    obtain ⟨d, ty, rfl, hd⟩ := FVarTable.trans_depthOK _ id c hcid
    have hT : TrS s (.fvar id) = .fvar d ty := by
      simp only [TrS, trE, hcid, Option.getD_some]
    simp only [anySpec, hf, hd, hT, ConLeche.Expr.nestOcc]
    by_cases h1 : lo ≤ d <;> by_cases h2 : d < hi <;> simp [h1, h2]
  | proj sn i x ih =>
    intro k hok
    rw [OkS_proj] at hok
    simp only [anySpec, ho (.proj sn i x) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, ih k hok, TrS_proj, ConLeche.Expr.nestOcc]
  | app f a ihf iha =>
    intro k hok
    simp only [OkS_app, Bool.and_eq_true] at hok
    simp only [anySpec, ho (.app f a) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, ihf k hok.1, iha k hok.2, TrS_app, ConLeche.Expr.nestOcc]
  | lam _ t b _ iht ihb =>
    intro k hok
    simp only [OkS_lam, Bool.and_eq_true] at hok
    simp only [anySpec, ho (.lam _ t b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht k hok.1, ihb (k + 1) hok.2, TrS_lam, ConLeche.Expr.nestOcc]
  | forallE _ t b _ iht ihb =>
    intro k hok
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    simp only [anySpec, ho (.forallE _ t b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht k hok.1, ihb (k + 1) hok.2, TrS_forallE, ConLeche.Expr.nestOcc]
  | letE _ t v b _ iht ihv ihb =>
    intro k hok
    simp only [OkS_letE, Bool.and_eq_true] at hok
    simp only [anySpec, ho (.letE _ t v b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht k hok.1.1, ihv k hok.1.2, ihb (k + 1) hok.2, TrS_letE,
      ConLeche.Expr.nestOcc]
  | mdata m x ih =>
    intro k hok
    rw [OkS_mdata] at hok
    simp only [anySpec, ho (.mdata m x) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, ih k hok, TrS_mdata]
  | bvar i => intro k _; simp [anySpec, ho (.bvar i), TrS_bvar, ConLeche.Expr.nestOcc]
  | mvar i => intro k hok; simp [OkS, okE] at hok
  | sort u => intro k _; simp [anySpec, ho (.sort u), TrS_sort, ConLeche.Expr.nestOcc]
  | lit l => intro k _; simp [anySpec, ho (.lit l), TrS_lit, ConLeche.Expr.nestOcc]

/-- **InLean's `nestOcc`, read**: master's on the reading. -/
theorem nestOccI_tr {s : InLean.CState} (names : List Lean.Name) (lo hi : Nat) {e : Lean.Expr}
    (h : OkS s e = true) :
    InLean.nestOcc names lo hi e = ConLeche.Expr.nestOcc (names.map toName) lo hi (TrS s e) := by
  simp only [InLean.nestOcc, EO.any, anyNode_spec]
  exact anySpec_nestOcc s names lo hi _ (fun _ _ => rfl) (fun _ => rfl)
    (fun x h1 h2 => by cases x <;> simp_all) e 0 h

/-- **InLean's `piDomsOcc`, read.** -/
theorem piDomsOccI_tr {s : InLean.CState} (names : List Lean.Name) (lo hi : Nat) :
    ∀ (n : Nat) (e : Lean.Expr), OkS s e = true →
      InLean.piDomsOcc names lo hi n e =
        ConLeche.Expr.piDomsOcc (names.map toName) lo hi n (TrS s e)
  | 0, _, _ => by simp [InLean.piDomsOcc, ConLeche.Expr.piDomsOcc]
  | n + 1, .forallE _ d b _, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [InLean.piDomsOcc, TrS_forallE, ConLeche.Expr.piDomsOcc, nestOccI_tr names lo hi h.1,
      piDomsOccI_tr names lo hi n b h.2]
  | n + 1, .mdata _ e, h => by
    rw [OkS_mdata] at h
    simp only [InLean.piDomsOcc, TrS_mdata]
    exact piDomsOccI_tr names lo hi (n + 1) e h
  | _ + 1, .fvar _, h => by
    rw [TrS_fvar h]; simp only [InLean.piDomsOcc]; rfl
  | _ + 1, .bvar _, _ | _ + 1, .mvar _, _ | _ + 1, .sort _, _
  | _ + 1, .const _ _, _ | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _ _, _
  | _ + 1, .letE _ _ _ _ _, _ | _ + 1, .lit _, _ | _ + 1, .proj _ _ _, _ => by
    simp only [InLean.piDomsOcc]; rfl

/-! ## Whole-application replacement -/

/-- A term whose top is not a variable does not read as one. -/
theorem TrS_not_fvar {s : InLean.CState} :
    ∀ {x : Lean.Expr}, OkS s x = true → (∀ id, EO.stripTop x ≠ .fvar id) →
      ∀ j ty, TrS s x ≠ .fvar j ty
  | .mdata m x, h, hn => by
    rw [OkS_mdata] at h
    rw [TrS_mdata]
    exact TrS_not_fvar h (fun id hid => hn id (by simpa [EO.stripTop] using hid))
  | .fvar id, _, hn => absurd rfl (hn id)
  | .mvar _, h, _ => by simp [OkS, okE] at h
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .app _ _, _, _ | .lam _ _ _ _, _, _
  | .forallE _ _ _ _, _, _ | .letE _ _ _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by
    intro j ty h; simp [TrS, trE] at h

/-- A term whose top is a variable reads as one at the variable's depth. -/
theorem TrS_stripTop_fvar {s : InLean.CState} {x : Lean.Expr} {id : FVarId} (h : OkS s x = true)
    (hst : EO.stripTop x = .fvar id) :
    ∃ d ty, TrS s x = .fvar d ty ∧ EO.fvDepth? id = some d := by
  have h' : OkS s (.fvar id) = true := by rw [← hst, OkS_stripTop]; exact h
  simp only [OkS, okE, Option.isSome_iff_exists] at h'
  obtain ⟨c, hc⟩ := h'
  obtain ⟨d, ty, rfl, hd⟩ := FVarTable.trans_depthOK _ id c hc
  refine ⟨d, ty, ?_, hd⟩
  rw [← TrS_stripTop, hst]
  simp only [TrS, trE, hc, Option.getD_some]

/-- The placeholder application's head, translated. -/
@[expose] def phTr (p : Lean.Name × List Lean.Level) : ConLeche.Name × List ConLeche.Level :=
  (toName p.1, p.2.map trL)

/-- **InLean's `phApp?`, read**: master's on the reading, its levels with a
reading. -/
theorem phAppI_tr {s : InLean.CState} (b : Nat) :
    ∀ (e : Lean.Expr) (n : Nat), OkS s e = true →
      (InLean.phApp? b e n).map phTr = ConLeche.Expr.phApp? b (TrS s e) n ∧
        ∀ p, InLean.phApp? b e n = some p → p.2.all okLv = true
  | .const c us, 0, h => by
    rw [OkS_const] at h
    refine ⟨rfl, ?_⟩
    intro p hp; simp only [InLean.phApp?, Option.some.injEq] at hp; subst hp; exact h
  | .const c us, _ + 1, _ => by simp [InLean.phApp?, TrS_const, ConLeche.Expr.phApp?]
  | .mdata m e, n, h => by
    rw [OkS_mdata] at h
    simp only [InLean.phApp?, TrS_mdata]
    exact phAppI_tr b e n h
  | .app f x, 0, _ => by simp [InLean.phApp?, TrS_app, ConLeche.Expr.phApp?]
  | .app f x, n + 1, h => by
    simp only [OkS_app, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := phAppI_tr b f n h.1
    simp only [InLean.phApp?, TrS_app]
    cases hst : EO.stripTop x with
    | fvar id =>
      obtain ⟨d, ty, hT, hd⟩ := TrS_stripTop_fvar h.2 hst
      simp only [hT, hd, ConLeche.Expr.phApp?]
      by_cases hj : d = b + n
      · simp only [hj, beq_self_eq_true, ↓reduceIte]; exact ⟨ih1, ih2⟩
      · have : (some d == some (b + n)) = false := by simp [hj]
        simp only [this, hj, Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, fun _ h => nomatch h⟩
    | _ =>
      have hn : ∀ id, EO.stripTop x ≠ .fvar id := by intro id; rw [hst]; simp
      have hnf := TrS_not_fvar h.2 hn
      refine ⟨?_, fun _ h => nomatch h⟩
      simp only [Option.map_none]
      generalize TrS s x = tx at hnf
      cases tx <;> first | rfl | exact (hnf _ _ rfl).elim
  | .bvar _, _, _ | .sort _, _, _ | .lam _ _ _ _, _, _ | .forallE _ _ _ _, _, _
  | .letE _ _ _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by
    simp [InLean.phApp?, TrS, trE, ConLeche.Expr.phApp?]
  | .fvar id, _, h => by
    rw [TrS_fvar h]; simp [InLean.phApp?, ConLeche.Expr.phApp?]
  | .mvar _, _, h => by simp [OkS, okE] at h

/-- What the replacement needs of a pair of substitutions: InLean's images
have a reading, which is master's image at the translated head. -/
@[expose] def SubRel (s : InLean.CState) (fI : Lean.Name → List Lean.Level → Option Lean.Expr)
    (fC : ConLeche.Name → List ConLeche.Level → Option ConLeche.Expr) : Prop :=
  ∀ c us, us.all okLv = true →
    (fI c us).map (TrS s) = fC (toName c) (us.map trL) ∧ ∀ y, fI c us = some y → OkS s y = true

/-- The callback of InLean's `replaceApps`. -/
@[expose] def raF (fI : Lean.Name → List Lean.Level → Option Lean.Expr) (b n : Nat)
    (x : Lean.Expr) : Option Lean.Expr :=
  match EO.stripTop x with
  | .app .. | .const .. => (InLean.phApp? b x n).bind fun p => fI p.1 p.2
  | _ => none

theorem replaceApps_eq (fI : Lean.Name → List Lean.Level → Option Lean.Expr) (b n : Nat)
    (e : Lean.Expr) : InLean.replaceApps fI b n e = mapSpec (fun x _ => raF fI b n x) e 0 := by
  unfold InLean.replaceApps EO.replace
  rw [mapOff_spec]; rfl

theorem raF_hole {s : InLean.CState} {fI fC} (hR : SubRel s fI fC) (b n : Nat) {x : Lean.Expr}
    (h : OkS s x = true) :
    Option.map (TrS s) ((InLean.phApp? b x n).bind fun p => fI p.1 p.2) =
      ConLeche.Expr.appHole? fC b n (TrS s x) ∧
      ∀ y, (InLean.phApp? b x n).bind (fun p => fI p.1 p.2) = some y → OkS s y = true := by
  obtain ⟨h1, h2⟩ := phAppI_tr (s := s) b x n h
  unfold ConLeche.Expr.appHole?
  rw [← h1]
  cases hp : InLean.phApp? b x n with
  | none => exact ⟨rfl, fun _ h => nomatch h⟩
  | some p =>
    obtain ⟨r1, r2⟩ := hR p.1 p.2 (h2 p hp)
    simp only [Option.bind_some, Option.map_some, phTr]
    exact ⟨r1, r2⟩

/-- **InLean's `replaceApps`, read**: master's on the reading, given related
substitutions. -/
theorem replaceAppsI_tr {s : InLean.CState} {fI fC} (hR : SubRel s fI fC) (b n : Nat) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      OkS s (mapSpec (fun x _ => raF fI b n x) e k) = true ∧
        TrS s (mapSpec (fun x _ => raF fI b n x) e k) = ConLeche.Expr.replaceApps fC b n (TrS s e) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro k h
    have h' := h
    simp only [OkS_app, Bool.and_eq_true] at h'
    obtain ⟨hm, hok⟩ := raF_hole hR b n (x := .app f a) h
    have hF : raF fI b n (.app f a) = (InLean.phApp? b (.app f a) n).bind (fun p => fI p.1 p.2) := rfl
    simp only [mapSpec, hF, TrS_app, ConLeche.Expr.replaceApps]
    rw [TrS_app] at hm
    cases hb : (InLean.phApp? b (.app f a) n).bind (fun p => fI p.1 p.2) with
    | none =>
      rw [hb, Option.map_none] at hm
      rw [← hm]
      simp only [Option.getD_none, OkS_app, TrS_app, (ihf k h'.1).1, (iha k h'.2).1,
        (ihf k h'.1).2, (iha k h'.2).2, Bool.and_self, true_and]
    | some y =>
      rw [hb, Option.map_some] at hm
      rw [← hm]
      exact ⟨hok y hb, rfl⟩
  | const c us =>
    intro k h
    obtain ⟨hm, hok⟩ := raF_hole hR b n (x := .const c us) h
    have hF : raF fI b n (.const c us) = (InLean.phApp? b (.const c us) n).bind (fun p => fI p.1 p.2) := rfl
    rw [TrS_const] at hm ⊢
    simp only [mapSpec, hF, ConLeche.Expr.replaceApps]
    cases hb : (InLean.phApp? b (.const c us) n).bind (fun p => fI p.1 p.2) with
    | none =>
      rw [hb, Option.map_none] at hm
      rw [← hm]
      exact ⟨h, rfl⟩
    | some y =>
      rw [hb, Option.map_some] at hm
      rw [← hm]
      exact ⟨hok y hb, rfl⟩
  | lam nm t bd bi iht ihb =>
    intro k h
    simp only [OkS_lam, Bool.and_eq_true] at h
    have hF : raF fI b n (.lam nm t bd bi) = none := rfl
    simp only [mapSpec, hF, Option.getD_none, OkS_lam, TrS_lam,
      ConLeche.Expr.replaceApps, (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2,
      (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | forallE nm t bd bi iht ihb =>
    intro k h
    simp only [OkS_forallE, Bool.and_eq_true] at h
    have hF : raF fI b n (.forallE nm t bd bi) = none := rfl
    simp only [mapSpec, hF, Option.getD_none, OkS_forallE, TrS_forallE,
      ConLeche.Expr.replaceApps, (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2,
      (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | letE nm t v bd nd iht ihv ihb =>
    intro k h
    simp only [OkS_letE, Bool.and_eq_true] at h
    have hF : raF fI b n (.letE nm t v bd nd) = none := rfl
    simp only [mapSpec, hF, Option.getD_none, OkS_letE, TrS_letE,
      ConLeche.Expr.replaceApps, (iht k h.1.1).1, (ihv k h.1.2).1, (ihb (k + 1) h.2).1,
      (iht k h.1.1).2, (ihv k h.1.2).2, (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | proj sn i x ih =>
    intro k h
    rw [OkS_proj] at h
    have hF : raF fI b n (.proj sn i x) = none := rfl
    simp only [mapSpec, hF, Option.getD_none, OkS_proj, TrS_proj,
      ConLeche.Expr.replaceApps, (ih k h).1, (ih k h).2, true_and]
  | mdata m x ih =>
    intro k h
    rw [OkS_mdata] at h
    have hF : raF fI b n (.mdata m x) = raF fI b n x := by
      simp only [raF, EO.stripTop]
      split <;> simp_all [InLean.phApp?]
    simp only [mapSpec, hF, TrS_mdata]
    cases hx : raF fI b n x with
    | none =>
      simp only [Option.getD_none, OkS_mdata, TrS_mdata]
      exact ih k h
    | some y =>
      have := mapSpec_eq_of_some (f := fun x _ => raF fI b n x) (k := k) hx
      rw [← this]
      exact ih k h
  | fvar id =>
    intro k h
    have hF : raF fI b n (.fvar id) = none := rfl
    simp only [mapSpec, hF, Option.getD_none]
    refine ⟨h, ?_⟩
    rw [TrS_fvar h]; rfl
  | bvar i => intro k h; exact ⟨h, rfl⟩
  | sort u => intro k h; exact ⟨h, rfl⟩
  | lit l => intro k h; exact ⟨h, rfl⟩
  | mvar i => intro k h; simp [OkS, okE] at h

/-! ## The holes -/

/-- Master's hole at member index `mm` (`nestHoles`' body). -/
@[expose] def cHoleAt (cctx : ConLeche.NestCtx) (mm : Nat) : Option ConLeche.Expr :=
  match cctx.formers[mm]? with
  | some cv => (ConLeche.instPisWith cctx.params cv.type).map (.fvar (cctx.nP + mm) ·)
  | none => none

theorem cNestHoles_eq (cctx : ConLeche.NestCtx) :
    ConLeche.nestHoles cctx = (List.range cctx.names.length).mapM (cHoleAt cctx) := rfl

/-- What the holes loop needs of the two contexts: the same formers (read),
parameter count and member count, the parameters read at the loop's first
state `sI`, closed. -/
structure HolesPre (sI : InLean.CState) (ctx : InLean.NestCtx) (cctx : ConLeche.NestCtx) : Prop where
  formers : cctx.formers = ctx.formers.map trCV
  nP : cctx.nP = ctx.nP
  params : cctx.params = TrSL sI ctx.params
  okParams : OkSL sI ctx.params = true
  clParams : ∀ a ∈ ctx.params, (TrS sI a).looseBVarsBounded 0 = true
  okFormers : ∀ cv ∈ ctx.formers, okC cv.type = true ∧ (trC cv.type).looseBVarsBounded 0 = true

/-- **The holes loop**: from the first state `sI`, every iteration that
continues pushes master's hole at its index. -/
theorem nestHolesLoopI_run {sI : InLean.CState} {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx}
    (hP : HolesPre sI ctx cctx) :
    ∀ (l : List Nat) (out : Array Lean.Expr) {s₀ s' : InLean.CState}
      {r : Option (Option (List Lean.Expr)) × Array Lean.Expr},
      CSOKI mode eager env s₀ → TabLe sI s₀ → OkSL s₀ out.toList = true →
      (forIn l ((none, out) : Option (Option (List Lean.Expr)) × Array Lean.Expr)
        fun (mm : Nat) (r : Option (Option (List Lean.Expr)) × Array Lean.Expr) =>
          match ctx.formers[mm]? with
          | some cv =>
            match InLean.instPisWith ctx.params cv.type with
            | some ty => do
              let x ← InLean.mkFVarM (ctx.nP + mm) ty
              pure (ForInStep.yield (none, r.snd.push x))
            | none => pure (ForInStep.done (some none, r.snd))
          | none => pure (ForInStep.done (some none, r.snd))) s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' r.snd.toList = true ∧
        (∀ x, r.fst ≠ some (some x)) ∧
        (r.fst = none → ∃ rest, l.mapM (cHoleAt cctx) = some rest ∧
          TrSL s' r.snd.toList = TrSL s' out.toList ++ rest)
  | [], out, s₀, s', r, hs, _, hout, h => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun _ => ⟨[], rfl, by simp⟩⟩
  | mm :: l, out, s₀, s', r, hs, hI, hout, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, s₁, h1, h2⟩ := bindI_ok h
    cases hf : ctx.formers[mm]? with
    | none =>
      simp only [hf] at h1
      obtain ⟨rfl, rfl⟩ := pureI_ok h1
      obtain ⟨rfl, rfl⟩ := pureI_ok h2
      exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun h => by simp at h⟩
    | some cv =>
      simp only [hf] at h1
      cases hi : InLean.instPisWith ctx.params cv.type with
      | none =>
        simp only [hi] at h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h2
        exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun h => by simp at h⟩
      | some ty =>
        simp only [hi] at h1
        obtain ⟨x, s₂, hx, h1⟩ := bindI_ok h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h1
        simp only at h2
        obtain ⟨hokcv, hclcv⟩ := hP.okFormers cv (List.mem_of_getElem? hf)
        obtain ⟨hokty, hty⟩ := instPisWithI_tr ctx.params cv.type (OkS_of_okC _ hokcv) hP.okParams
          hP.clParams hi
        rw [TrS_of_okC _ hokcv] at hty
        have hclty : (TrS sI ty).looseBVarsBounded 0 = true :=
          ConLeche.looseBVarsBounded_instPisWith (fun a ha => by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
            exact hP.clParams b hb) hclcv hty
        have hokty₀ := okS_of_tabLe hI hokty
        have htr₀ := TrS_of_tabLe hI hokty
        obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1
          (mkFVarM_specI hs (ctx.nP + mm) hokty₀ (by rw [htr₀]; exact hclty)) x s₂ hx
        have hout₂ : OkSL s₂ (out.push x).toList = true := by
          simp only [Array.toList_push, OkSL, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true]
          exact ⟨okSL_of_tabLe ht₂ hout, hokx⟩
        obtain ⟨hs', ht', hok', hns, hR⟩ := nestHolesLoopI_run hP l (out.push x) hs₂ (hI.trans ht₂)
          hout₂ h2
        refine ⟨hs', ht₂.trans ht', hok', hns, fun hn => ?_⟩
        obtain ⟨rest, hrest, htr⟩ := hR hn
        have hhole : cHoleAt cctx mm = some (.fvar (ctx.nP + mm) (TrS sI ty)) := by
          unfold cHoleAt
          rw [hP.formers, List.getElem?_map, hf]
          simp only [Option.map_some, trCV_type, hP.params, hP.nP, hty, Option.map_some]
        refine ⟨.fvar (ctx.nP + mm) (TrS sI ty) :: rest, ?_, ?_⟩
        · rw [List.mapM_cons, hhole, hrest]; rfl
        · rw [htr]
          have hx' : TrS s' x = .fvar (ctx.nP + mm) (TrS sI ty) := by
            rw [TrS_of_tabLe ht' hokx, htx, htr₀]
          simp only [Array.toList_push, TrSL, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append]
          rw [show TrS s' x = _ from hx']

/-- **The holes** (`nestHoles`): InLean's answer `some holes` is master's, read
at the final state. -/
theorem nestHolesI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} {s₀ s' : InLean.CState}
    {holes : List Lean.Expr} (hP : HolesPre s₀ ctx cctx) (hn : cctx.names.length = ctx.names.length)
    (hs : CSOKI mode eager env s₀) (h : InLean.nestHoles ctx s₀ = .ok (some holes, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' holes = true ∧
      ConLeche.nestHoles cctx = some (TrSL s' holes) := by
  unfold InLean.nestHoles at h
  obtain ⟨r, s₁, h1, h2⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok₁, hns, hR⟩ := nestHolesLoopI_run (mode := mode) (eager := eager) (env := env) hP
    (List.range ctx.names.length) #[] hs (TabLe.refl _) rfl h1
  obtain ⟨r1, r2⟩ := r
  cases r1 with
  | some x =>
    cases x with
    | some y => exact (hns y rfl).elim
    | none =>
      obtain ⟨hx, rfl⟩ := pureI_ok h2
      cases hx
  | none =>
    obtain ⟨hx, rfl⟩ := pureI_ok h2
    cases hx
    obtain ⟨rest, hrest, htr⟩ := hR rfl
    refine ⟨hs₁, ht₁, hok₁, ?_⟩
    rw [cNestHoles_eq, hn, hrest]
    simpa [TrSL] using htr.symm

/-! ## The context -/

theorem trShape_formers (p : InLean.BlockShape) :
    (trShape p).formers = p.formers.map trCV := by
  simp [ConLeche.BlockShape.formers, InLean.BlockShape.formers, trShape, trMember]

theorem trShape_nP (p : InLean.BlockShape) : (trShape p).nP = p.nP := rfl

/-- **The positivity context** (`blockNestCtxS_spec`'s twin): InLean's
`blockNestCtx` builds `p.nestCtx fvs fe` and holes whose readings at the final
state are master's context at the translated shape (at any lookup) and its
holes; the parameters are variables, closed, one per parameter. -/
theorem blockNestCtxI_run {p : InLean.BlockShape} {fe : InLean.FEnv} {s₀ s' : InLean.CState}
    {ctx : InLean.NestCtx} {holes : List Lean.Expr} (find? : ConLeche.Name → Option ConLeche.ConstantInfo)
    (hs : CSOKI mode eager env s₀)
    (hok : ∀ ms ∈ p.members, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true)
    (h : InLean.blockNestCtx p fe s₀ = .ok ((ctx, holes), s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∃ fvs, ctx = p.nestCtx fvs fe ∧
      OkSL s' fvs = true ∧ OkSL s' holes = true ∧
      (∀ a ∈ fvs, (TrS s' a).looseBVarsBounded 0 = true) ∧
      (∀ a ∈ fvs, ConLeche.Expr.WScoped p.nP (TrS s' a)) ∧
      ConLeche.nestHoles ((trShape p).nestCtx (TrSL s' fvs) find?) = some (TrSL s' holes) ∧
      Runs (ConLeche.blockNestCtx (m := ConLeche.FueledM) (trShape p) find?)
        ((trShape p).nestCtx (TrSL s' fvs) find?, TrSL s' holes) := by
  unfold InLean.blockNestCtx at h
  obtain ⟨c0, s₁, h1, h⟩ := bindI_ok h
  cases h0 : p.formers.head? with
  | none => simp only [h0, InLean.unwrapOr] at h1; exact (throwI_ok h1).elim
  | some cv0 =>
  simp only [h0, InLean.unwrapOr] at h1
  obtain ⟨hc0, rfl⟩ := pureI_ok h1
  subst hc0
  have hcv0 : cv0 ∈ p.formers := List.mem_of_mem_head? h0
  obtain ⟨ms0, hms0, hcvT⟩ := List.mem_map.1 hcv0
  obtain ⟨hok0, hcl0⟩ := hok ms0 hms0
  rw [hcvT] at hok0 hcl0
  obtain ⟨o, s₂, h2, h⟩ := bindI_ok h
  obtain ⟨q0, s₃, h3, h⟩ := bindI_ok h
  cases o with
  | none => simp only [InLean.unwrapOr] at h3; exact (throwI_ok h3).elim
  | some pq =>
  simp only [InLean.unwrapOr] at h3
  obtain ⟨hpq, rfl⟩ := pureI_ok h3
  subst hpq
  obtain ⟨fvs, b⟩ := pq
  obtain ⟨o2, s₄, h4, h⟩ := bindI_ok h
  obtain ⟨hl, s₅, h5, h⟩ := bindI_ok h
  cases o2 with
  | none => simp only [InLean.unwrapOr] at h5; exact (throwI_ok h5).elim
  | some hl' =>
  simp only [InLean.unwrapOr] at h5
  obtain ⟨hhl, rfl⟩ := pureI_ok h5
  subst hhl
  obtain ⟨hctx, rfl⟩ := pureI_ok h
  simp only [Prod.mk.injEq] at hctx
  obtain ⟨rfl, rfl⟩ := hctx
  -- the opener, read at the opener's own state
  obtain ⟨hs₂, ht₂, hokf, hop, hfv⟩ := openClosedI_run hs hok0 hcl0 h2 (TabLe.refl _)
  have hclf : ∀ a ∈ fvs, (TrS s₂ a).looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
    have hx : (TrSL s₂ fvs)[i]? = some (TrS s₂ a) := by
      simp [TrSL, hi]
    obtain ⟨⟨k, ty, hk⟩, -, -⟩ := hfv i _ hx
    rw [hk]
    simp [ConLeche.Expr.looseBVarsBounded]
  -- the holes
  have hP : HolesPre s₂ (p.nestCtx fvs fe) ((trShape p).nestCtx (TrSL s₂ fvs) find?) := by
    refine ⟨?_, rfl, rfl, hokf, hclf, ?_⟩
    · show (trShape p).formers = p.formers.map trCV
      exact trShape_formers p
    · intro cv hcv
      obtain ⟨ms, hms, rfl⟩ := List.mem_map.1 hcv
      exact hok ms hms
  obtain ⟨hs₄, ht₄, hokh, hholes⟩ := nestHolesI_run hP
    (by simp [ConLeche.BlockShape.nestCtx, InLean.BlockShape.nestCtx, trShape_memberNames]) hs₂ h4
  refine ⟨hs₄, ht₂.trans ht₄, fvs, rfl, okSL_of_tabLe ht₄ hokf, hokh, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [TrS_of_tabLe ht₄ (by simp only [OkSL, List.all_eq_true] at hokf; exact hokf a ha)]
    exact hclf a ha
  · intro a ha
    rw [TrS_of_tabLe ht₄ (by simp only [OkSL, List.all_eq_true] at hokf; exact hokf a ha)]
    have := (ConLeche.openPisAtFvars_WScoped p.nP _ 0 hop (trC_wscoped 0 _)).1 (TrS s₂ a)
      (List.mem_map_of_mem ha)
    rwa [Nat.zero_add] at this
  · rw [TrSL_of_tabLe ht₄ hokf]; exact hholes
  · rw [TrSL_of_tabLe ht₄ hokf]
    have hc0 : (trShape p).formers.head? = some (trCV cv0) := by
      rw [trShape_formers, List.head?_map, h0]; rfl
    unfold ConLeche.blockNestCtx
    simp only [hc0, ConLeche.unwrapOr]
    refine Runs.bind (Runs.pure _) ?_
    simp only [trCV_type] at hop ⊢
    rw [trShape_nP, hop]
    refine Runs.bind (Runs.pure _) ?_
    simp only [hholes]
    refine Runs.bind (Runs.pure _) ?_
    exact Runs.pure _

end InLeanProof
