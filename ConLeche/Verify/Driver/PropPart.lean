module

import ConLeche.Modular
public import ConLeche.Driver.Reach
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.Cached.StreamIndex
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.PinRen
public import ConLeche.Verify.EnvWF

/-!
# A statement the worker inferred a proposition is one over the part below it

The worker infers the statements of its proof pairs over the part of its sorted context below
each name (`inferFlags`, `ctxPart`, `ConLeche/Driver/Reach.lean`), which is the specification's
`Module.part` (`ConLeche/Modular.lean`), where its proof route (`ProofSide`) asks the inference.

* `inferFlags_typeIsProp`: the cached inference's accept is the pure `TypeIsProp`, with the
  statement's syntactic clauses and its resolution at the part;
* `envWF_prefix`: a prefix of a well-formed context in read order is well formed;
* `typeIsProp_part`: the two together, at `Module.part`.
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
inference over the part below its name. -/
private theorem inferFlags_head {ctx : List Declaration} {w : String} {y : Name}
    {cv : ConstantVal} {rest : List (String × Name × ConstantVal)}
    (henv : EnvWF (streamEnv (ctxPart ctx y)))
    (h : inferFlags ctx ((w, y, cv) :: rest) = .ok ()) :
    (exprOk cv.levelParams 0 cv.type = true ∧ cv.type.constsResolve (streamEnv (ctxPart ctx y)) = true ∧
      TypeIsProp .verified (streamEnv (ctxPart ctx y)) cv.type) ∧ inferFlags ctx rest = .ok () := by
  unfold inferFlags at h
  simp only at h
  generalize streamEnv (ctxPart ctx y) = E at henv h ⊢
  split at h
  · exact nomatch h
  · next hok =>
    have hok' : (exprOk cv.levelParams 0 cv.type && cv.type.constsResolveF (mkFEnv E)) = true := by
      simpa [constsResolveFC_spec] using hok
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

/-- **The inferred flags' accept**: every recorded statement is syntactically closed, resolves
over the part of the context below its name and is `TypeIsProp` there. -/
theorem inferFlags_typeIsProp {ctx : List Declaration}
    (henv : ∀ y, EnvWF (streamEnv (ctxPart ctx y))) :
    ∀ {ps : List (String × Name × ConstantVal)}, inferFlags ctx ps = .ok () →
      ∀ {w : String} {y : Name} {cv : ConstantVal}, (w, y, cv) ∈ ps →
        exprOk cv.levelParams 0 cv.type = true ∧
          cv.type.constsResolve (streamEnv (ctxPart ctx y)) = true ∧
          TypeIsProp .verified (streamEnv (ctxPart ctx y)) cv.type
  | [], _, _, _, _, hm => nomatch hm
  | (w', y', cv') :: rest, h, w, y, cv, hm => by
    obtain ⟨hhd, htl⟩ := inferFlags_head (henv y') h
    rcases List.mem_cons.mp hm with he | hm'
    · simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      exact hhd
    · exact inferFlags_typeIsProp henv htl hm'

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
      obtain ⟨ms, hms, hn⟩ := blockTables_getD_names p h
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

end PrefixFacts

/-- **A statement record installs at most its own name** (the tolerated axiom nothing,
`Quot.sound` its pin under that name). -/
theorem declNames_stmt {d : Declaration} {cv : ConstantVal}
    (hd : d = .axiomDecl cv ∨ ∃ v h, d = .defnDecl cv v h) : ∀ n ∈ declNames d, n = cv.name := by
  intro n hn
  rcases hd with rfl | ⟨v, h, rfl⟩
  · simp only [declNames, declConstants] at hn
    split at hn
    · next hq =>
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
      rw [hn, hq]
      have := atLps_name (quotPin .sound) cv.levelParams
      simp only [quotAt, ConstantInfo.name] at this ⊢
      rw [this]
      decide
    · split at hn
      · exact nomatch hn
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
        exact hn
  · simp only [declNames, declConstants, List.map_cons, List.map_nil, List.mem_singleton] at hn
    exact hn

/-! ## At the specification's part -/

/-- **A recorded statement is a proposition over the part below its name** (`Module.part`), for a
module whose context is the worker's: name-distinct, in read order, well formed. -/
theorem typeIsProp_part {m : Module}
    (hord : ∀ k (hk : k < m.ctx.length), RecordScoped (streamEnv (m.ctx.take (k + 1))) m.ctx[k])
    (hwf : EnvWF m.context)
    {ps : List (String × Name × ConstantVal)} (hfl : inferFlags m.ctx ps = .ok ())
    {w : String} {y : Name} {cv : ConstantVal} (hmem : (w, y, cv) ∈ ps) :
    cv.type.constsResolve (m.part y) = true ∧ TypeIsProp .verified (m.part y) cv.type := by
  obtain ⟨-, h1, h2⟩ := inferFlags_typeIsProp (fun y => envWF_prefix hord hwf) hfl hmem
  exact ⟨h1, h2⟩

end ConLeche.Driver
