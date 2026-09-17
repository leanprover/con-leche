module

public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas

public section

/-!
# The closed spine under an opened telescope (task #315)

The reading side of a nested block sees a constructor's residual
*opened*: `openPisAtFvars L x d` returns one fresh variable per binder
and the residual with those variables substituted.  What the pins and
the restore table describe is the *unopened* residual — `stripPis`'
body, still carrying `L` loose `bvar`s.  When the opened residual is a
constant spine whose first arguments are variables of the ambient
prefix (indices `< d`, so *below* every opener), the two descriptions
line up argument by argument:

* the head constant and the prefix arguments are already there before
  the opening, unchanged;
* the remaining arguments are the unopened ones with the openers
  substituted.

The reason the prefix survives verbatim is one clause of
`Expr.instantiate1`: it maps `.fvar idx ty` to itself (it never
descends into the annotation, and never rewrites a variable).  So an
opener — itself an `fvar` — can only *produce* a variable of its own
index, and an argument that comes out as a variable *below* `d` must
have been that variable all along (`os_instSeq_eq_fvar_inv`).
-/

namespace ConLeche

/-- **The substitution cannot manufacture a foreign variable.**  If a
sequence of `fvar` arguments, none of them the variable `k`, turns `e`
into `.fvar k ty`, then `e` was `.fvar k ty` already. -/
theorem os_instSeq_eq_fvar_inv :
    ∀ (vs : List Expr) (t : Nat) {e : Expr} {k : Nat} {ty : Expr},
      (∀ v ∈ vs, ∃ j tj, v = Expr.fvar j tj ∧ j ≠ k) →
      Expr.instSeq vs t e = .fvar k ty → e = .fvar k ty := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ h; exact h
  | cons v vs ih =>
    intro t e k ty hall h
    obtain ⟨j, tj, hv, hjk⟩ := hall v List.mem_cons_self
    subst hv
    have hstep : e.instantiate1 (.fvar j tj) t = .fvar k ty :=
      ih (t - 1) (fun x hx => hall x (List.mem_cons_of_mem _ hx)) h
    cases e with
    | bvar i =>
      rw [show (Expr.bvar i).instantiate1 (.fvar j tj) t =
          (if i = t then .fvar j tj else if i > t then .bvar (i - 1) else .bvar i) from rfl]
        at hstep
      split at hstep
      · injection hstep with hjeq _
        exact absurd hjeq hjk
      · split at hstep <;> exact absurd hstep (by simp)
    | fvar idx ty' => exact hstep
    | _ => exact absurd hstep (by simp [Expr.instantiate1])

/-- **A prefix of ambient variables is read off unchanged.**  Every
substituted argument is a variable at or above `d`, every expected one
a variable below `d`, so the substitution was the identity on the
prefix and the two lists are equal. -/
theorem os_map_instSeq_fvars_eq (vs : List Expr) (t d : Nat)
    (hvs : ∀ v ∈ vs, ∃ j tj, v = Expr.fvar j tj ∧ d ≤ j) :
    ∀ (A P : List Expr), (∀ p ∈ P, ∃ k ty, p = Expr.fvar k ty ∧ k < d) →
      A.map (Expr.instSeq vs t ·) = P → A = P := by
  intro A
  induction A with
  | nil => intro _ _ h; exact h
  | cons a A ih =>
    intro P hP h
    cases P with
    | nil => simp at h
    | cons p P =>
      rw [List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨k, ty, hpk, hkd⟩ := hP p List.mem_cons_self
      subst hpk
      have ha : a = Expr.fvar k ty := by
        refine os_instSeq_eq_fvar_inv vs t (fun w hw => ?_) h1
        obtain ⟨j, tj, hw', hdj⟩ := hvs w hw
        exact ⟨j, tj, hw', by omega⟩
      rw [ha, ih P (fun q hq => hP q (List.mem_cons_of_mem _ hq)) h2]

/-- `instSeq_getAppFn_const_inv` with the opener hypothesis spelled
out: `AllFvarsL` is sealed outside its own module, so the `∀`-form is
what a caller can actually build. -/
theorem os_instSeq_getAppFn_const_inv : ∀ (vs : List Expr),
    (∀ v ∈ vs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty) →
    ∀ (t : Nat) (e : Expr) {n : Name} {us : List Level},
      (Expr.instSeq vs t e).getAppFn = .const n us → e.getAppFn = .const n us := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ h; exact h
  | cons v vs ih =>
    intro hall t e n us h
    obtain ⟨idx, ty, hv⟩ := hall v List.mem_cons_self
    subst hv
    exact Expr.getAppFn_const_of_instantiate1
      (ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _ h)

/-- `instSeq_getAppArgs` with the opener hypothesis spelled out. -/
theorem os_instSeq_getAppArgs : ∀ (vs : List Expr),
    (∀ v ∈ vs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty) →
    ∀ (t : Nat) (e : Expr),
      (Expr.instSeq vs t e).getAppArgs = e.getAppArgs.map (Expr.instSeq vs t ·) := by
  intro vs
  induction vs with
  | nil => intro _ t e; simp [Expr.instSeq]
  | cons v vs ih =>
    intro hall t e
    obtain ⟨idx, ty, hv⟩ := hall v List.mem_cons_self
    subst hv
    show (Expr.instSeq vs (t - 1) (e.instantiate1 _ t)).getAppArgs = _
    rw [ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _,
      Expr.getAppArgs_instantiate1_var, List.map_map]
    rfl

/-- **The goal.**  An opened residual that is a constant spine with an
ambient-variable prefix comes from an unopened residual with the SAME
head, the SAME prefix, and the remaining arguments substituted. -/
theorem os_openPisAtFvars_constSpine_stripPis {L d : Nat} {x : Expr} {afvs : List Expr}
    {n : Name} {us : List Level} {fvsP is : List Expr}
    (hop : openPisAtFvars L x d = some (afvs, Expr.mkAppN (.const n us) (fvsP ++ is)))
    (hP : ∀ v ∈ fvsP, ∃ (k : Nat) (ty : Expr), v = .fvar k ty ∧ k < d) :
    ∃ (tbs : List (Expr × BinderMeta)) (is₀ : List Expr),
      x.stripPis L = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is₀)) ∧
      is = is₀.map (Expr.instSeq afvs (L - 1)) := by
  obtain ⟨bs, body₀, hstrip, hlen, hIdx, -⟩ := Verify.openPisAtFvars_stripPis L hop
  have hfv : ∀ v ∈ afvs, ∃ j tj, v = Expr.fvar j tj ∧ d ≤ j := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
    have hiL : i < L := by rw [← hlen]; exact hi
    obtain ⟨ty, hj⟩ := hIdx i hiL
    rw [List.getElem?_eq_getElem hi] at hj
    exact ⟨d + i, ty, by rw [← hvi]; exact Option.some.inj hj, Nat.le_add_right d i⟩
  have hall : ∀ v ∈ afvs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    intro v hv
    obtain ⟨j, tj, hv', -⟩ := hfv v hv
    exact ⟨j, tj, hv'⟩
  have hbody := Verify.openPisAtFvars_instSeq L hop hstrip
  have hfn : body₀.getAppFn = .const n us := by
    refine os_instSeq_getAppFn_const_inv afvs hall (L - 1) body₀ ?_
    rw [← hbody, Expr.getAppFn_mkAppN]
    rfl
  have hargs : body₀.getAppArgs.map (Expr.instSeq afvs (L - 1) ·) = fvsP ++ is := by
    rw [← os_instSeq_getAppArgs afvs hall (L - 1) body₀, ← hbody, Expr.getAppArgs_mkAppN]
    rfl
  obtain ⟨A, B, hAB, hA, hB⟩ := List.map_eq_append_iff.mp hargs
  have hAeq : A = fvsP := os_map_instSeq_fvars_eq afvs (L - 1) d hfv A fvsP hP hA
  have hb0 : body₀ = Expr.mkAppN (.const n us) (fvsP ++ B) := by
    rw [← hAeq, ← hAB, ← hfn, Expr.mkAppN_getApp]
  rw [hb0] at hstrip
  exact ⟨bs, B, hstrip, hB.symm⟩

/-! ## B1 at a constructor's FIELD domain (task #315 L-B)

`openPisAtFvars_domain` (`ConLeche/Verify/Denote/TeleOpen.lean`) is
stated at one opening.  A constructor's telescope is opened in TWO
stages — the block's parameters at depth `0`, then the constructor's
fields at depth `nP` — and that is the frame `BlockOpened` states its
field facts at (`xFvs[l].fvarTypeD`, with the parameter openers `fvsP`
appearing in the spine).  What the copy's arms consume is the CLOSED
domain, `fcs[l].1`, with `bvar`s for the parameters and the earlier
fields (`NestedPinsRun.copyFields`, DESIGN §U.34 (c)).

This section is the bridge between the two, and its head, spine and
mention corollaries.  The hypotheses are the COMPOSED opening and
strip — a caller builds them with `openPisAtFvars_add` and
`stripPis_append` — so nothing here needs the model tier. -/

/-- Every variable of a telescope opened at depth `0` is an `fvar`. -/
private theorem os_openers_fvar {n : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (hop : openPisAtFvars n e 0 = some (fvs, body)) :
    ∀ v ∈ fvs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
  obtain ⟨-, -, -, hlen, hIdx, -⟩ := Verify.openPisAtFvars_stripPis n hop
  intro v hv
  obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
  obtain ⟨ty, hj⟩ := hIdx i (by rw [← hlen]; exact hi)
  rw [List.getElem?_eq_getElem hi] at hj
  exact ⟨0 + i, ty, by rw [← hvi]; exact Option.some.inj hj⟩

/-- **B1 at a constructor's field.**  The `l`-th field's OPENED domain
— what `BlockOpened` describes — is the `l`-th CLOSED domain
instantiated at the parameter openers followed by the earlier field
openers, exactly.  This is the identity every arm of the copy's shape
crosses: `BlockOpened.recF`/`.nestF`/`.ord` speak of the left side,
`NestedPinsRun.copyFields` hands over the right. -/
theorem os_field_domain (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta}
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b) :
    x.fvarTypeD = Expr.instSeq (fvsP ++ xFvs.take l) (nP + l - 1) b.1 := by
  have hx' : (fvsP ++ xFvs)[nP + l]? = some x := by
    rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
    exact hx
  have hb' : (pcs ++ fcs)[nP + l]? = some b := by
    rw [List.getElem?_append_right (by omega), hlenC, Nat.add_sub_cancel_left]
    exact hb
  have hcore := Verify.openPisAtFvars_domain (nP + k) hop hstrip (nP + l) x b hx' hb'
  have htake : (fvsP ++ xFvs).take (nP + l) = fvsP ++ xFvs.take l := by
    rw [List.take_append, hlenP, Nat.add_sub_cancel_left,
      List.take_of_length_le (by omega)]
  rw [hcore, htake]

/-- The same, at the `nP - 1 + l` spelling `copyFields` uses (a
container has at least the parameter it is nested in). -/
theorem os_field_domain_pos (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta}
    (hnP : 0 < nP)
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b) :
    x.fvarTypeD = Expr.instSeq (fvsP ++ xFvs.take l) (nP - 1 + l) b.1 := by
  rw [os_field_domain nP k l hop hstrip hlenP hlenC hx hb,
    show nP - 1 + l = nP + l - 1 from by omega]

/-- **Head transfer, opened to closed.**  A field whose OPENED domain
is a constant spine had that constant at its head before the opening:
the substitution puts `fvar`s where the `bvar`s stood and can never
manufacture a `const` head.  This is the direction `recF` and `pinF`
need — `BlockOpened` gives the opened head, the rewrite kit
(`replaceAllNested_occurrence`, `instSeq_mkAppN_const`) consumes the
closed one. -/
theorem os_field_domain_head (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta} {n : Name} {us : List Level}
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b)
    (hhead : x.fvarTypeD.getAppFn = Expr.const n us) :
    b.1.getAppFn = Expr.const n us := by
  have hall : ∀ v ∈ fvsP ++ xFvs.take l, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    intro v hv
    refine os_openers_fvar hop v ?_
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_of_mem_take h)
  refine os_instSeq_getAppFn_const_inv _ hall (nP + l - 1) b.1 ?_
  rw [← os_field_domain nP k l hop hstrip hlenP hlenC hx hb]
  exact hhead

/-- **Spine transfer.**  The opened domain's arguments are the closed
domain's, instantiated one for one — so the argument COUNT is the same
and the arguments correspond positionally. -/
theorem os_field_domain_args (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta}
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b) :
    x.fvarTypeD.getAppArgs
      = b.1.getAppArgs.map (Expr.instSeq (fvsP ++ xFvs.take l) (nP + l - 1) ·) := by
  have hall : ∀ v ∈ fvsP ++ xFvs.take l, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    intro v hv
    refine os_openers_fvar hop v ?_
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_of_mem_take h)
  rw [os_field_domain nP k l hop hstrip hlenP hlenC hx hb]
  exact os_instSeq_getAppArgs _ hall (nP + l - 1) b.1

/-- **Mention transfer, closed to opened**: a constant the closed
domain mentions is mentioned by the opened one.  (`ContainerModeled`'s
`ordFree` is stated the other way; see the twin below.) -/
theorem os_field_domain_mentions (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta} {m : Name}
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b)
    (hm : b.1.mentionsConst m = true) :
    x.fvarTypeD.mentionsConst m = true := by
  rw [os_field_domain nP k l hop hstrip hlenP hlenC hx hb]
  cases hc : (Expr.instSeq (fvsP ++ xFvs.take l) (nP + l - 1) b.1).mentionsConst m with
  | true => rfl
  | false => rw [mentionsConst_instSeq_false _ _ hc] at hm; exact nomatch hm

/-- **Mention transfer, the consumer's direction**: an opened domain
free of a constant has a closed domain free of it.  This is the form
`ContainerModeled.ordFree` (a container-ORDINARY field mentions no
member of the container's block, stated opened) is read at, and it is
what tells `ordF`'s left arm that `replaceAllNested` leaves the closed
domain alone (`replaceAllNested_of_no_mention`). -/
theorem os_field_domain_free (nP k l : Nat) {e : Expr} {fvsP xFvs : List Expr} {body : Expr}
    {pcs fcs : List (Expr × BinderMeta)} {body₀ : Expr}
    {x : Expr} {b : Expr × BinderMeta} {m : Name}
    (hop : openPisAtFvars (nP + k) e 0 = some (fvsP ++ xFvs, body))
    (hstrip : e.stripPis (nP + k) = some (pcs ++ fcs, body₀))
    (hlenP : fvsP.length = nP) (hlenC : pcs.length = nP)
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some b)
    (hm : x.fvarTypeD.mentionsConst m = false) :
    b.1.mentionsConst m = false := by
  cases hc : b.1.mentionsConst m with
  | false => rfl
  | true =>
    rw [os_field_domain_mentions nP k l hop hstrip hlenP hlenC hx hb hc] at hm
    exact nomatch hm

end ConLeche

