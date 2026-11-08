module

public import ConLeche.Modular
public import ConLeche.Driver.Reach
public import ConLeche.Verify.EnvExt
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.Cached.StreamIndex
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Driver.Reach

/-!
# A statement inferred a proposition at the context is one at the part below it

The worker infers the statements of its proof pairs at its whole sorted context
(`inferFlags` at `mkFEnv (streamEnv ctx)`, `ConLeche/Driver/Reach.lean`).  The specification's
proof route (`ProofSide`, `ConLeche/Modular.lean`) asks the inference at the part of the context
below the name (`Module.part`: the records before the name's).  This file carries the verdict:

* `inferFlags_typeIsProp`: the cached inference's accept is the pure `TypeIsProp`, with the
  statement's syntactic clauses and its resolution at the context;
* `typeIsProp_restrict`: the kernel's run on a type resolving in an environment `E₁` that `E₂`
  extends is the same run at both (`knot_ext`), so `TypeIsProp` at `E₂` is `TypeIsProp` at `E₁`;
* `prefix_envExt`: a context in read order with distinct names extends each of its prefixes, given
  what the knot reads past the term (`StoredFacts`) of which a context's validation says nothing:
  that the recursors' rules name stored constructors (`RecCtorsStored` of the context) and that a
  record storing `Nat` stores its two constructors;
* `typeIsProp_part`: the three together at a context record's statement, whose type does not read
  the record's own name, at `Module.part`.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Verify ConLeche.Cached
open Std.WP

/-! ## The cached inference is `TypeIsProp` -/

private theorem csok_empty (env : Env) : CSOK .verified false env ({} : CState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ModeMemosOK.empty⟩ <;>
    (intros; simp_all)

/-- **An accepted inference is `TypeIsProp`**: `typeIsPropC` answering `true` from the empty
state at `mkFEnv E`, for a type with no free variable. -/
theorem typeIsPropC_sound {E : Env} (henv : EnvWF E) {cv : ConstantVal}
    (hfv : cv.type.hasFvar = false) {s' : CState}
    (h : typeIsPropC (mkFEnv E) cv {} = .ok (true, s')) : TypeIsProp .verified E cv.type := by
  have hs := csok_empty E
  have hw : Expr.WScoped 0 cv.type := wscoped_of_hasFvar_false hfv
  unfold typeIsPropC at h
  simp only [bind, StateT.bind] at h
  cases hi : (coreKnotI .verified false (mkFEnv E) checkFuel).infer 0 cv.type {} with
  | error e => rw [hi] at h; exact nomatch h
  | ok r =>
  obtain ⟨jsty, s₁⟩ := r
  rw [hi] at h
  simp only [Except.bind] at h
  obtain ⟨hs₁, ⟨F₁, hF₁⟩, hw₁⟩ := triple_iff_run.mp (inferK_spec henv hs hw) jsty s₁ hi
  cases ho : opSIxC .verified (mkFEnv E) 0 jsty s₁ with
  | error e => rw [ho] at h; exact nomatch h
  | ok r =>
  obtain ⟨u, s₂⟩ := r
  rw [ho] at h
  simp only at h
  obtain ⟨-, ⟨F₂, hF₂⟩⟩ := triple_iff_run.mp (opSIxC_spec henv hs₁ hw₁) u s₂ ho
  have hq : Level.isEquiv u .zero = some true := by
    cases hq : Level.isEquiv u .zero with
    | none => rw [hq] at h; exact nomatch h
    | some b =>
      rw [hq] at h
      cases h
      rfl
  refine ⟨max F₁ F₂, jsty, u, ?_, ?_, hq⟩
  · exact ((fueledOpsM .verified).inferType E 0 cv.type).property (Nat.le_max_left F₁ F₂) hF₁
  · exact ((fueledOpsM .verified).ensureSort E 0 jsty).property (Nat.le_max_right F₁ F₂) hF₂

/-- The head of the inferred flags: an accept there is the statement's clauses and its
inference. -/
private theorem inferFlags_head {E : Env} (henv : EnvWF E) {w : String} {y : Name}
    {cv : ConstantVal} {rest : List (String × Name × ConstantVal)}
    (h : inferFlags (mkFEnv E) ((w, y, cv) :: rest) = .ok ()) :
    (exprOk cv.levelParams 0 cv.type = true ∧ cv.type.constsResolve E = true ∧
      TypeIsProp .verified E cv.type) ∧ inferFlags (mkFEnv E) rest = .ok () := by
  unfold inferFlags at h
  split at h
  · exact nomatch h
  · next hok =>
    have hok' : (exprOk cv.levelParams 0 cv.type && cv.type.constsResolveF (mkFEnv E)) = true := by
      simpa using hok
    rw [Bool.and_eq_true] at hok'
    cases hrun : typeIsPropC (mkFEnv E) cv {} with
    | error e =>
      simp only [StateT.run', hrun] at h
      exact nomatch h
    | ok r =>
      obtain ⟨b, s'⟩ := r
      simp only [StateT.run', hrun] at h
      cases b with
      | false => exact nomatch h
      | true =>
        have hfv : cv.type.hasFvar = false := by
          have := hok'.1
          simp only [exprOk, Bool.and_eq_true, Bool.not_eq_true'] at this
          exact this.1.1
        exact ⟨⟨hok'.1, by rw [← constsResolveF_eq]; exact hok'.2,
          typeIsPropC_sound henv hfv hrun⟩, h⟩

/-- **The inferred flags' accept**: every recorded statement is syntactically closed, resolves at
the context and is `TypeIsProp` there. -/
theorem inferFlags_typeIsProp {E : Env} (henv : EnvWF E) :
    ∀ {ps : List (String × Name × ConstantVal)}, inferFlags (mkFEnv E) ps = .ok () →
      ∀ {w : String} {y : Name} {cv : ConstantVal}, (w, y, cv) ∈ ps →
        exprOk cv.levelParams 0 cv.type = true ∧ cv.type.constsResolve E = true ∧
          TypeIsProp .verified E cv.type
  | [], _, _, _, _, hm => nomatch hm
  | (w', y', cv') :: rest, h, w, y, cv, hm => by
    obtain ⟨hhd, htl⟩ := inferFlags_head henv h
    rcases List.mem_cons.mp hm with he | hm'
    · simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      exact hhd
    · exact inferFlags_typeIsProp henv htl hm'

/-! ## The verdict at an environment the context extends -/

/-- **`TypeIsProp` at a sub-environment**: a type resolving in `E₁`, which `E₂` extends, is
inferred and sorted alike at both (`knot_ext`), so its verdict is the same. -/
theorem typeIsProp_restrict {mode : CheckMode} {E₁ E₂ : Env} (hx : EnvExt E₁ E₂) {ty : Expr}
    (hr : ty.constsResolve E₁ = true) (h : TypeIsProp mode E₂ ty) : TypeIsProp mode E₁ ty := by
  obtain ⟨F, stype, u, hi, hs, hu⟩ := h
  have K := knot_ext mode hx F false
  obtain ⟨hie, hres⟩ := K.infer 0 hr
  have hi' : inferTypeCore mode false E₁ F 0 ty = .ok stype := by
    rw [← hi]; exact hie.symm
  have hst : stype.constsResolve E₁ = true := hres stype hi'
  obtain ⟨hse, -⟩ := ensureSort_rel (env₂ := E₂) K 0 hst
  refine ⟨F, stype, u, hi', ?_, hu⟩
  rw [← hs]; exact hse.symm

/-! ## A prefix of a context in read order -/

/-- Two members of a list with one image under a map whose images are distinct are one. -/
theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy', he.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx', he⟩) h.1
    · exact eq_of_map_nodup h.2 hx' hy' he

/-- Where names are distinct, a stored constant is what its name finds. -/
theorem find_of_mem_nodup {E : Env} (hnd : (E.consts.map (·.name)).Nodup) {ci : ConstantInfo}
    (h : ci ∈ E.consts) : E.find? ci.name = some ci := by
  have hs : (E.find? ci.name).isSome = true := by
    simp only [Env.find?, List.find?_isSome]
    exact ⟨ci, h, by simp⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  rw [hc, eq_of_map_nodup (f := fun x : ConstantInfo => x.name) hnd (Env.find?_mem hc) h
    (Env.find?_name hc)]

section Prefix

variable {ctx : List Declaration}

/-- The context's names, distinct, as the context's environment says. -/
theorem nodupNames_of_ctx (hnd : (ctx.flatMap declNames).Nodup) :
    ((streamEnv ctx).consts.map (·.name)).Nodup :=
  nodupNames_streamEnv hnd

/-- A constant of a prefix is one of the context's. -/
theorem mem_prefix_consts {r : Nat} {ci : ConstantInfo}
    (h : ci ∈ (streamEnv (ctx.take r)).consts) : ci ∈ (streamEnv ctx).consts := by
  rcases (mem_streamEnv_consts _ _).1 h with ⟨d, hd, hc⟩ | h'
  · exact (mem_streamEnv_consts _ _).2 (.inl ⟨d, List.mem_of_mem_take hd, hc⟩)
  · simp [Env.empty] at h'

/-- A constant of a prefix is one of a longer prefix's. -/
theorem mem_prefix_mono {j r : Nat} (hjr : j ≤ r) {ci : ConstantInfo}
    (h : ci ∈ (streamEnv (ctx.take j)).consts) : ci ∈ (streamEnv (ctx.take r)).consts := by
  rcases (mem_streamEnv_consts _ _).1 h with ⟨d, hd, hc⟩ | h'
  · refine (mem_streamEnv_consts _ _).2 (.inl ⟨d, ?_, hc⟩)
    exact (List.take_sublist_take_left hjr).subset hd
  · simp [Env.empty] at h'

/-- What a prefix stores, a longer one stores. -/
theorem isSome_prefix_mono {j r : Nat} (hjr : j ≤ r) {n : Name}
    (h : ((streamEnv (ctx.take j)).find? n).isSome = true) :
    ((streamEnv (ctx.take r)).find? n).isSome = true := by
  simp only [Env.find?, List.find?_isSome] at h ⊢
  obtain ⟨c, hc, hn⟩ := h
  exact ⟨c, mem_prefix_mono hjr hc, hn⟩

theorem resolve_prefix_mono {j r : Nat} (hjr : j ≤ r) {e : Expr}
    (h : e.constsResolve (streamEnv (ctx.take j)) = true) :
    e.constsResolve (streamEnv (ctx.take r)) = true :=
  Expr.constsResolve_of_find (fun _ => isSome_prefix_mono hjr) h

/-- **A prefix's lookup is the context's**, the names being distinct. -/
theorem find_prefix (hnd : (ctx.flatMap declNames).Nodup) {r : Nat} {n : Name}
    {ci : ConstantInfo} (h : (streamEnv (ctx.take r)).find? n = some ci) :
    (streamEnv ctx).find? n = some ci := by
  have hm := mem_prefix_consts (Env.find?_mem h)
  rw [← Env.find?_name h]
  exact find_of_mem_nodup (nodupNames_of_ctx hnd) hm

/-- A constant of a prefix comes from a record before the prefix's end. -/
theorem prefix_record {r : Nat} {ci : ConstantInfo}
    (h : ci ∈ (streamEnv (ctx.take r)).consts) :
    ∃ k, ∃ hk : k < ctx.length, k < r ∧ ci ∈ declConstants ctx[k] := by
  rcases (mem_streamEnv_consts _ _).1 h with ⟨d, hd, hc⟩ | h'
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hk' : k < r ∧ k < ctx.length := by simpa [Nat.lt_min] using hk
    exact ⟨k, hk'.2, hk'.1, by simpa using hc⟩
  · simp [Env.empty] at h'

/-- A table of a prefix comes from a record before the prefix's end. -/
theorem prefix_record_table {r : Nat} {t : ProjTable}
    (h : t ∈ (streamEnv (ctx.take r)).tables) :
    ∃ k, ∃ hk : k < ctx.length, k < r ∧ t ∈ declTables ctx[k] := by
  rcases (mem_streamEnv_tables _ _).1 h with ⟨d, hd, hc⟩ | h'
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hk' : k < r ∧ k < ctx.length := by simpa [Nat.lt_min] using hk
    exact ⟨k, hk'.2, hk'.1, by simpa using hc⟩
  · simp [Env.empty] at h'

end Prefix

/-- **A record's tables are at its constants' names.** -/
theorem declTables_names {d : Declaration} {t : ProjTable} (h : t ∈ declTables d) :
    t.structName ∈ declNames d := by
  cases d with
  | indDecl block nP =>
    simp only [declTables] at h
    split at h
    · next p hp =>
      obtain ⟨ms, hms, hn⟩ := blockTables_names p p.members t h
      simp only [declNames, declConstants, hp]
      have := blockConstants_names p
      simp only [ConstantInfo.name] at this
      rw [this, hn]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hms))
    · exact nomatch h
  | _ => simp [declTables] at h

theorem nestedRead_mono {p q : Expr → Bool} {lps : List Name} {tyA : Expr} {mI rP cnP : Nat}
    {lvls : List Level} {pins : List Expr} (h : NestedRead p lps tyA mI rP cnP lvls pins)
    (hq : ∀ pin ∈ pins, q pin = true) : NestedRead q lps tyA mI rP cnP lvls pins := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun pin hp => ⟨(h3 pin hp).1, (h3 pin hp).2.1, hq pin hp, (h3 pin hp).2.2.2⟩, h4⟩

section PrefixFacts

variable {ctx : List Declaration} {r : Nat}
  (hnd : (ctx.flatMap declNames).Nodup)
  (hord : ∀ k (hk : k < ctx.length), RecordScoped (streamEnv (ctx.take (k + 1))) ctx[k])

include hnd in
/-- **A prefix's tables are the context's** at the structures the prefix stores: a table is at a
name of its record, and no later record stores that name. -/
theorem findTable_prefix {T : Name} (hT : ((streamEnv (ctx.take r)).find? T).isSome = true) :
    (streamEnv ctx).findTable? T = (streamEnv (ctx.take r)).findTable? T := by
  have hTC : ((streamEnv ctx).find? T).isSome = true := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
    rw [find_prefix hnd hci]; rfl
  obtain ⟨d', hd', hTd'⟩ := streamEnv_find_mem hT
  unfold Env.findTable?
  simp only [hTC, hT, ↓reduceIte]
  rw [streamEnv_tables, streamEnv_tables]
  conv => lhs; rw [← List.take_append_drop r ctx]
  rw [List.flatMap_append, List.reverse_append, List.append_assoc, List.find?_append]
  have hnone : ((ctx.drop r).flatMap declTables).reverse.find? (fun t => t.structName == T) =
      none := by
    refine List.find?_eq_none.mpr fun t ht he => ?_
    rw [List.mem_reverse, List.mem_flatMap] at ht
    obtain ⟨d, hd, htd⟩ := ht
    have hn := declTables_names htd
    rw [beq_iff_eq.mp he] at hn
    rw [← List.take_append_drop r ctx, List.flatMap_append, List.nodup_append] at hnd
    exact hnd.2.2 T (List.mem_flatMap.2 ⟨d', hd', hTd'⟩) T (List.mem_flatMap.2 ⟨d, hd, hn⟩) rfl
  rw [hnone, Option.none_or]

include hord in
/-- **A prefix is well formed**: each record is scoped in the prefix ending with it, and its
syntactic clauses are the context's. -/
theorem envWF_prefix (hwf : EnvWF (streamEnv ctx)) : EnvWF (streamEnv (ctx.take r)) := by
  refine ⟨fun c hc => ?_, fun c hc => hwf.shapes c (mem_prefix_consts hc), fun t ht => ?_⟩
  · obtain ⟨k, hk, hkr, hck⟩ := prefix_record hc
    obtain ⟨e1, e2, e3, -, -⟩ := (hord k hk).1 c hck
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := hwf.consts c (mem_prefix_consts hc)
    have hm : ∀ {e : Expr}, e.constsResolve (streamEnv (ctx.take (k + 1))) = true →
        e.constsResolve (streamEnv (ctx.take r)) = true := resolve_prefix_mono (by omega)
    refine ⟨h1, h2, hm e1, h4, fun cv v hint he => ?_, fun cv mI rP isK rules he rl hrl => ?_⟩
    · obtain ⟨a, b, -, d⟩ := h5 cv v hint he
      exact ⟨a, b, hm (e2 cv v hint he), d⟩
    · obtain ⟨a, b, -, d, f⟩ := h6 cv mI rP isK rules he rl hrl
      obtain ⟨g1, -, g3⟩ := e3 cv mI rP isK rules he rl hrl
      exact ⟨a, b, hm g1, d, fun lvls pins hf =>
        nestedRead_mono (f lvls pins hf) fun pin hp => hm (g3 lvls pins hf pin hp)⟩
  · obtain ⟨k, hk, hkr, htk⟩ := prefix_record_table ht
    have htC : t ∈ (streamEnv ctx).tables :=
      (mem_streamEnv_tables _ _).2 (.inl ⟨_, List.getElem_mem hk, htk⟩)
    obtain ⟨-, h2, h3⟩ := hwf.tables t htC
    obtain ⟨-, hb⟩ := (hord k hk).2 t htk
    refine ⟨streamEnv_find_of_mem (List.mem_take_iff_getElem.2 ⟨k, Nat.lt_min.2 ⟨hkr, hk⟩, rfl⟩)
      (declTables_names htk), h2, fun i b hib => ?_⟩
    obtain ⟨a, b', -, d⟩ := h3 i b hib
    exact ⟨a, b', resolve_prefix_mono (by omega)
      (hb b (Array.mem_toList_iff.2 (Array.mem_of_getElem? hib))), d⟩

theorem bool_of_beq : boolTrueName ∈ pinFootprint natBeqName ∧
    boolFalseName ∈ pinFootprint natBeqName := by decide

theorem bool_of_ble : boolTrueName ∈ pinFootprint natBleName ∧
    boolFalseName ∈ pinFootprint natBleName := by decide

include hord in
/-- What a constant of a prefix reads is stored in the prefix (its record's scope). -/
theorem prefix_scoped {ci : ConstantInfo} (hc : ci ∈ (streamEnv (ctx.take r)).consts) :
    ∃ k, k + 1 ≤ r ∧ EntryScoped (streamEnv (ctx.take (k + 1))) ci := by
  obtain ⟨k, hk, hkr, hck⟩ := prefix_record hc
  exact ⟨k, hkr, (hord k hk).1 ci hck⟩

include hord in
/-- The footprint of a stored pinned name is stored in a prefix. -/
theorem prefix_footprint {n m : Name} (hn : ((streamEnv (ctx.take r)).find? n).isSome = true)
    (hm : m ∈ pinFootprint n) : ((streamEnv (ctx.take r)).find? m).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨k, hkr, hsc⟩ := prefix_scoped hord (Env.find?_mem hci)
  have hname : ci.toConstantVal.name = n := Env.find?_name hci
  exact isSome_prefix_mono hkr (hsc.2.2.2.2 m (by rw [hname]; exact hm))

include hnd hord in
/-- **What the knot reads past the term, at a prefix**: given that the context's recursors' rules
name stored constructors and that a record storing `Nat` stores its constructors. -/
theorem storedFacts_prefix (hwf : EnvWF (streamEnv ctx))
    (hrec : RecCtorsStored (streamEnv ctx))
    (hnat : ∀ d ∈ ctx, natName ∈ declNames d →
      natZeroName ∈ declNames d ∧ natSuccName ∈ declNames d) :
    StoredFacts (streamEnv (ctx.take r)) := by
  have hwfP := envWF_prefix (r := r) hord hwf
  -- `Nat` stored: its record stores its constructors
  have hN : ((streamEnv (ctx.take r)).find? natName).isSome = true →
      ((streamEnv (ctx.take r)).find? natZeroName).isSome = true ∧
        ((streamEnv (ctx.take r)).find? natSuccName).isSome = true := by
    intro h
    obtain ⟨d, hd, hnd'⟩ := streamEnv_find_mem h
    obtain ⟨h0, h1⟩ := hnat d (List.mem_of_mem_take hd) hnd'
    exact ⟨streamEnv_find_of_mem hd h0, streamEnv_find_of_mem hd h1⟩
  refine ⟨hwfP, fun h => ?_, fun n cv mI rP isK rules hf rl hrl => ?_, fun T i e hf => ?_,
    fun h => ?_⟩
  · -- the `Nat` trio
    have hNat : ((streamEnv (ctx.take r)).find? natName).isSome = true := by
      rcases h with h | h | h
      · exact h
      · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
        have hs := hwfP.shapes ci (Env.find?_mem hci)
        obtain ⟨k, hkr, hsc⟩ := prefix_scoped hord (Env.find?_mem hci)
        have hty := hsc.1
        unfold litShapeOk at hs
        rw [Env.find?_name hci] at hs
        simp (decide := true) only [↓reduceIte, natZeroOk, Bool.and_eq_true, beq_iff_eq] at hs
        rw [hs.2] at hty
        exact isSome_prefix_mono hkr (by simpa [Expr.constsResolve] using hty)
      · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
        have hs := hwfP.shapes ci (Env.find?_mem hci)
        obtain ⟨k, hkr, hsc⟩ := prefix_scoped hord (Env.find?_mem hci)
        have hty := hsc.1
        unfold litShapeOk at hs
        rw [Env.find?_name hci] at hs
        simp (decide := true) only [↓reduceIte, natSuccOk, Bool.and_eq_true] at hs
        obtain ⟨-, hm⟩ := hs
        split at hm
        · next c1 c2 heq =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          rw [heq] at hty
          simp only [Expr.constsResolve, Bool.and_eq_true] at hty
          rw [← hm.1]
          exact isSome_prefix_mono hkr hty.1
        · exact nomatch hm
    exact ⟨hNat, hN hNat⟩
  · -- the rules' constructors
    obtain ⟨cvj, cnP, cnF, hc⟩ := hrec n cv mI rP isK rules (find_prefix hnd hf) rl hrl
    obtain ⟨k, hkr, hsc⟩ := prefix_scoped hord (Env.find?_mem hf)
    have hcs := isSome_prefix_mono hkr ((hsc.2.2.1 cv mI rP isK rules rfl rl hrl).2.1)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hcs
    rw [find_prefix hnd hx] at hc
    exact ⟨cvj, cnP, cnF, hx.trans hc⟩
  · -- a table's constructor
    unfold Env.findProj? at hf
    split at hf
    · next tbl htb =>
      split at hf
      · obtain rfl := Option.some.inj hf
        obtain ⟨htm, -, -⟩ := Env.findTable?_mem htb
        obtain ⟨k, hk, hkr, htk⟩ := prefix_record_table htm
        exact isSome_prefix_mono hkr ((hord k hk).2 tbl htk).1
      · exact nomatch hf
    · exact nomatch hf
  · -- the `Bool` constructors below the comparisons
    rcases h with h | h
    · exact ⟨prefix_footprint hord h bool_of_beq.1, prefix_footprint hord h bool_of_beq.2⟩
    · exact ⟨prefix_footprint hord h bool_of_ble.1, prefix_footprint hord h bool_of_ble.2⟩

include hnd hord in
/-- **A context in read order with distinct names extends each of its prefixes.** -/
theorem prefix_envExt (hwf : EnvWF (streamEnv ctx)) (hrec : RecCtorsStored (streamEnv ctx))
    (hnat : ∀ d ∈ ctx, natName ∈ declNames d →
      natZeroName ∈ declNames d ∧ natSuccName ∈ declNames d) :
    EnvExt (streamEnv (ctx.take r)) (streamEnv ctx) :=
  ⟨fun _ _ h => find_prefix hnd h, fun _ hT => findTable_prefix hnd hT,
    storedFacts_prefix hnd hord hwf hrec hnat⟩

end PrefixFacts

/-! ## The statement's names at the part below its record -/

/-- **Resolution read off the names an expression reads**: where every name `e` reads that `E₂`
stores is stored in `E₁`, what resolves in `E₂` resolves in `E₁`. -/
theorem constsResolve_of_readNames {E₁ E₂ : Env} :
    ∀ {e : Expr}, (∀ n ∈ e.readNames, (E₂.find? n).isSome = true → (E₁.find? n).isSome = true) →
      e.constsResolve E₂ = true → e.constsResolve E₁ = true
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .lit (.natVal _), hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    simp only [Expr.readNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hf
    exact ⟨⟨hf.1 h.1.1, hf.2.1 h.1.2⟩, hf.2.2 h.2⟩
  | .lit (.strVal _), hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    simp only [Expr.readNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hf
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := h
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hf
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨b1 a1, b2 a2⟩, b3 a3⟩, b4 a4⟩, b5 a5⟩, b6 a6⟩, b7 a7⟩, b8 a8⟩, b9 a9⟩,
      b10 a10⟩
  | .const n _, hf, h => hf n (by simp [Expr.readNames]) h
  | .fvar _ ty, hf, h => constsResolve_of_readNames (e := ty) hf h
  | .app f a, hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_of_readNames (fun n hn => hf n (List.mem_append_left _ hn)) h.1,
      constsResolve_of_readNames (fun n hn => hf n (List.mem_append_right _ hn)) h.2⟩
  | .lam ty b, hf, h | .forallE ty b, hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_of_readNames (fun n hn => hf n (List.mem_append_left _ hn)) h.1,
      constsResolve_of_readNames (fun n hn => hf n (List.mem_append_right _ hn)) h.2⟩
  | .letE ty v b, hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨constsResolve_of_readNames (fun n hn => hf n
        (List.mem_append_left _ (List.mem_append_left _ hn))) h.1.1,
      constsResolve_of_readNames (fun n hn => hf n
        (List.mem_append_left _ (List.mem_append_right _ hn))) h.1.2⟩,
      constsResolve_of_readNames (fun n hn => hf n (List.mem_append_right _ hn)) h.2⟩
  | .proj s _ e, hf, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf s (by simp [Expr.readNames]) h.1,
      constsResolve_of_readNames (fun n hn => hf n (List.mem_cons_of_mem _ hn)) h.2⟩

section Part

variable {ctx : List Declaration} {r : Nat} (hr : r < ctx.length)
  (hnd : (ctx.flatMap declNames).Nodup)

include hr hnd in
/-- **The record at position `r` is the first to install its names**: the rank of each is `r`. -/
theorem findIdx_record {y : Name} (hy : y ∈ declNames ctx[r]) :
    ctx.findIdx (fun d => (declNames d).contains y) = r := by
  refine (List.findIdx_eq hr).2 ⟨by simpa using hy, fun j hj => ?_⟩
  cases hc' : (declNames ctx[j]).contains y with
  | false => rfl
  | true =>
  have hc : y ∈ declNames ctx[j] := by simpa using hc'
  exfalso
  rw [← List.take_append_drop r ctx, List.flatMap_append, List.nodup_append] at hnd
  refine hnd.2.2 y (List.mem_flatMap.2 ⟨ctx[j], ?_, hc⟩) y (List.mem_flatMap.2 ⟨ctx[r], ?_, hy⟩) rfl
  · exact List.mem_take_iff_getElem.2 ⟨j, Nat.lt_min.2 ⟨hj, by omega⟩, rfl⟩
  · exact List.mem_iff_getElem.2 ⟨0, by simp; omega, by simp⟩

include hr in
/-- **A statement's names at the part below its record**: the record at position `r`, scoped in
the prefix ending with it, installing a constant `ci` and only the name `y`, which `ci`'s type
does not read, has `ci`'s type resolve in the prefix before it. -/
theorem constsResolve_part
    (hord : RecordScoped (streamEnv (ctx.take (r + 1))) ctx[r]) {y : Name} {ci : ConstantInfo}
    (hci : ci ∈ declConstants ctx[r]) (honly : ∀ n ∈ declNames ctx[r], n = y)
    (hny : y ∉ ci.toConstantVal.type.readNames) :
    ci.toConstantVal.type.constsResolve (streamEnv (ctx.take r)) = true := by
  refine constsResolve_of_readNames (fun n hn hs => ?_) ((hord.1 ci hci).1)
  obtain ⟨d, hd, hnd'⟩ := streamEnv_find_mem hs
  rw [List.take_add_one, List.getElem?_eq_getElem hr] at hd
  rcases List.mem_append.mp hd with hd | hd
  · exact streamEnv_find_of_mem hd hnd'
  · simp only [Option.toList_some, List.mem_singleton] at hd
    subst hd
    exact absurd (honly n hnd' ▸ hn) hny

end Part

/-- **The proof route's inference at the part** (`ProofSide`, `ConLeche/Modular.lean`): at a
module whose context has distinct names, is in read order and well formed, whose recursors'
rules name stored constructors and whose record storing `Nat` stores its constructors, an accept of
the inferred flags at the whole context holding `(w, y, cv)`, where the context record of `y`
installs only `y` with a constant of `cv`'s type, which does not read `y`, gives `cv`'s type
resolving in the part of the context below `y` and `TypeIsProp` there. -/
theorem typeIsProp_part {m : Module} (hnd : (m.ctx.flatMap declNames).Nodup)
    (hord : ∀ k (hk : k < m.ctx.length), RecordScoped (streamEnv (m.ctx.take (k + 1))) m.ctx[k])
    (hwf : EnvWF m.context) (hrec : RecCtorsStored m.context)
    (hnat : ∀ d ∈ m.ctx, natName ∈ declNames d →
      natZeroName ∈ declNames d ∧ natSuccName ∈ declNames d)
    {ps : List (String × Name × ConstantVal)} (hfl : inferFlags (mkFEnv m.context) ps = .ok ())
    {w : String} {y : Name} {cv : ConstantVal} (hmem : (w, y, cv) ∈ ps)
    {r : Nat} (hr : r < m.ctx.length) {ci : ConstantInfo} (hci : ci ∈ declConstants m.ctx[r])
    (hty : ci.toConstantVal.type = cv.type) (hy : y ∈ declNames m.ctx[r])
    (honly : ∀ n ∈ declNames m.ctx[r], n = y) (hny : y ∉ cv.type.readNames) :
    cv.type.constsResolve (m.part y) = true ∧ TypeIsProp .verified (m.part y) cv.type := by
  have hpart : m.part y = streamEnv (m.ctx.take r) := by
    simp only [Module.part, Module.rank]
    rw [findIdx_record hr hnd hy]
  obtain ⟨-, -, hP⟩ := inferFlags_typeIsProp hwf hfl hmem
  have hres : cv.type.constsResolve (streamEnv (m.ctx.take r)) = true := by
    rw [← hty]
    exact constsResolve_part hr (hord r hr) hci honly (by rw [hty]; exact hny)
  rw [hpart]
  exact ⟨hres, typeIsProp_restrict (prefix_envExt hnd hord hwf hrec hnat) hres hP⟩

end ConLeche.Driver
