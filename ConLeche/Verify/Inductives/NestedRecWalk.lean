module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.StructRec

public section

/-!
# The restore walk at the auxiliary applications (task #315 M7)

The nested route's read-back runs `restoreNested` over every member the
scratch install stored, and the reading law has to say what that walk
DID.  `NestedInv.lean` has the Π node and a type pin's fire; this
module adds what a *rule* and a *constructor* need:

* the spine identity and its two step lemmas, so a node can be cut into
  head and arguments (`Expr.getAppFn_app`, `Expr.getAppArgs_app`);
* the shape the restore relies on — `RestoreTbl.IsKey` and the
  inductive `AuxAppsOk`, the model's face of the K.34 record: every
  application headed by a table key carries the block's parameters in
  its first `R.nP` arguments;
* the walk's remaining inversions: the λ node (`restoreWalk_lam_inv`),
  an application whose spine head is no key (`restoreWalk_app_inv`),
  and the two bare-constant cases (`restoreWalk_const_rec`,
  `restoreWalk_const_free`);
* a constructor pin's fire (`restoreWalk_ctorPin`), `restoreWalk_pin`'s
  `ctorPins` twin;
* the rebuild on a λ-prefix (`restoreNested_lams`), `restoreNested_pis`'
  twin;
* and the two facts the reading law consumes about the shape:
  `AuxAppsOk.key_inv` (a key-headed node's walk result) and
  `map_instSeq_structPsAt_prefix` (the parameter variables, opened at a
  sequence whose prefix is the parameter openers).
-/

namespace ConLeche

open Expr

/-! ## The spine, in one step

`Expr.mkAppN_getApp` (`ConLeche/Verify/InferLemmas.lean`) is already the
spine identity; these are its two node steps, which the cuts below use
to read a `.app` node as a spine. -/

/-- The spine head of an application is its function's. -/
theorem Expr.getAppFn_app (f a : Expr) : (Expr.app f a).getAppFn = f.getAppFn := rfl

/-- The spine arguments of an application extend its function's. -/
theorem Expr.getAppArgs_app (f a : Expr) :
    (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl

/-- A λ mentions a constant exactly when one of its two parts does. -/
theorem Expr.mentionsConst_lam_false {n : Name} {ty b : Expr} {bm : BinderMeta}
    (h : (Expr.lam ty b bm).mentionsConst n = false) :
    ty.mentionsConst n = false ∧ b.mentionsConst n = false := by
  simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using h

/-- A `let` mentions a constant exactly when one of its three parts
does. -/
theorem Expr.mentionsConst_letE_false {n : Name} {ty v b : Expr}
    (h : (Expr.letE ty v b).mentionsConst n = false) :
    ty.mentionsConst n = false ∧ v.mentionsConst n = false ∧ b.mentionsConst n = false := by
  simpa only [Expr.mentionsConst, Bool.or_eq_false_iff, and_assoc] using h

/-- A projection mentions a constant exactly when its subject does (the
structure name is not a constant occurrence the walk follows). -/
theorem Expr.mentionsConst_proj_false {n : Name} {sn : Name} {i : Nat} {x : Expr}
    (h : (Expr.proj sn i x).mentionsConst n = false) : x.mentionsConst n = false :=
  (by simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using h :
    _ = false ∧ x.mentionsConst n = false).2

/-- An application mentions a constant exactly when one of its two
parts does. -/
theorem Expr.mentionsConst_app_false {n : Name} {f a : Expr}
    (h : (Expr.app f a).mentionsConst n = false) :
    f.mentionsConst n = false ∧ a.mentionsConst n = false := by
  simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using h

/-! ## The shape the restore relies on -/

/-- A restore-table key: an auxiliary type (`pins`) or an auxiliary
constructor (`ctorPins`). -/
@[expose] def RestoreTbl.IsKey (R : RestoreTbl) (n : Name) : Prop :=
  (R.pins.lookup n).isSome = true ∨ (R.ctorPins.find? (fun q => q.1 == n)).isSome = true

/-- **The auxiliary applications sit at the parameters** (DESIGN §U.29,
PLAN-M7 §1a — the precondition `restoreNode` relies on when it drops the
first `nP` arguments of a key-headed application): at depth `d` below the
parameter prefix, every application headed by a key `n` has exactly
`R.nP + ar` arguments (`arityOf n = some ar`), its first `R.nP` the
parameter variables `structPsAt d R.nP`, its level arguments
`lps.map .param`, and the remaining arguments satisfy the shape; every
other node is structural (`d + 1` under a binder, and `letE`/`proj`
descend exactly as the walk does), a constant is not a key unless
applied, and a literal is inert.

**Weakened to the kernel's own Bool** (task #315, DESIGN §U.29 (q)):
`nestedAuxAppsOk`'s `auxAppsOk` descends into a `.letE`/`.proj` and
passes a `.lit`, and imposes nothing at a non-key constant, so those
three cases are HERE and the `const` case carries the key test alone —
otherwise the record could not discharge its own model face.  The
readings' congruences pay for them with `RestoreAgree.projEq`/`.litEq`
(the two environments answer alike at a projection table entry and at a
literal) and with `denoteMeta`'s own `none` at a `letE`. -/
inductive AuxAppsOk (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat) :
    Nat → Expr → Prop
  | key {d : Nat} {n : Name} {args : List Expr} {ar : Nat} :
      R.IsKey n → arityOf n = some ar → args.length = R.nP + ar →
      args.take R.nP = structPsAt d R.nP →
      (∀ a ∈ args.drop R.nP, AuxAppsOk R lps arityOf d a) →
      AuxAppsOk R lps arityOf d (Expr.mkAppN (.const n (lps.map .param)) args)
  | app {d : Nat} {f a : Expr} :
      (∀ n us, f.getAppFn = .const n us → ¬ R.IsKey n) →
      AuxAppsOk R lps arityOf d f → AuxAppsOk R lps arityOf d a →
      AuxAppsOk R lps arityOf d (.app f a)
  | lam {d : Nat} {ty b : Expr} {bm : BinderMeta} :
      AuxAppsOk R lps arityOf d ty → AuxAppsOk R lps arityOf (d + 1) b →
      AuxAppsOk R lps arityOf d (.lam ty b bm)
  | forallE {d : Nat} {ty b : Expr} {bm : BinderMeta} :
      AuxAppsOk R lps arityOf d ty → AuxAppsOk R lps arityOf (d + 1) b →
      AuxAppsOk R lps arityOf d (.forallE ty b bm)
  | letE {d : Nat} {ty v b : Expr} :
      AuxAppsOk R lps arityOf d ty → AuxAppsOk R lps arityOf d v →
      AuxAppsOk R lps arityOf (d + 1) b →
      AuxAppsOk R lps arityOf d (.letE ty v b)
  | proj {d : Nat} {sn : Name} {i : Nat} {x : Expr} :
      AuxAppsOk R lps arityOf d x → AuxAppsOk R lps arityOf d (.proj sn i x)
  | const {d : Nat} {n : Name} {us : List Level} :
      ¬ R.IsKey n → AuxAppsOk R lps arityOf d (.const n us)
  | bvar {d i : Nat} : AuxAppsOk R lps arityOf d (.bvar i)
  | sort {d : Nat} {u : Level} : AuxAppsOk R lps arityOf d (.sort u)
  | lit {d : Nat} {l : Literal} : AuxAppsOk R lps arityOf d (.lit l)
  | fvar {d i : Nat} {ty : Expr} : AuxAppsOk R lps arityOf d (.fvar i ty)

/-! ## The Bool decides the shape (task #315, K.38 landed) -/

/-- `find?`'s definedness is `any`. -/
theorem List.isSome_find?_eq_any {α : Type} (q : α → Bool) :
    ∀ l : List α, (l.find? q).isSome = l.any q
  | [] => rfl
  | a :: l => by
    rw [List.find?_cons, List.any_cons]
    cases hp : q a with
    | false => simpa using List.isSome_find?_eq_any q l
    | true => simp

/-- **`isAuxAppKey` DECIDES `RestoreTbl.IsKey`** — the kernel's Bool and
the model's Prop are the same key test. -/
theorem isAuxAppKey_iff {R : RestoreTbl} {n : Name} :
    isAuxAppKey R n = true ↔ R.IsKey n := by
  unfold isAuxAppKey RestoreTbl.IsKey
  rw [Bool.or_eq_true, List.isSome_find?_eq_any (fun q => q.1 == n) R.ctorPins]

/-- **THE REFLECTION** (task #315, DESIGN §U.29 (w)): the kernel's walk
`auxAppsOk` — K.35's Bool with K.38's level conjunct — DECIDES the
model's shape `AuxAppsOk`.  The recursion is `auxAppsOk`'s own, on
`sizeOf`: a key-headed spine is presented by the spine identity
(`Expr.mkAppN_getApp`) and its head's level arguments are K.38's
conjunct; every other node is structural, and the `attach` of the
children is bookkeeping (`auxAppsOk_attach_all`). -/
theorem auxAppsOk_reflect {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat} :
    ∀ (e : Expr) (d : Nat), auxAppsOk R lps arityOf d e = true → AuxAppsOk R lps arityOf d e
  | .bvar _, _, _ => .bvar
  | .sort _, _, _ => .sort
  | .lit _, _, _ => .lit
  | .fvar _ _, _, _ => .fvar
  | .const n us, d, h => by
    rw [auxAppsOk] at h
    by_cases hk : isAuxAppKey R n = true
    · rw [if_pos hk] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hus, har⟩ := h
      obtain rfl : us = lps.map Level.param := by simpa using hus
      cases hA : arityOf n with
      | none => rw [hA] at har; exact nomatch har
      | some ar =>
        rw [hA] at har
        have h0 : R.nP + ar = 0 := by simpa using har
        refine AuxAppsOk.key (args := []) (ar := ar) (isAuxAppKey_iff.mp hk) hA
          (by simp only [List.length_nil]; omega) ?_ (fun a ha => absurd ha (by simp))
        have hnP : R.nP = 0 := by omega
        rw [hnP]
        rfl
    · exact AuxAppsOk.const (fun hc => hk (isAuxAppKey_iff.mpr hc))
  | .lam ty b bm, d, h => by
    rw [auxAppsOk] at h
    simp only [Bool.and_eq_true] at h
    exact .lam (auxAppsOk_reflect ty d h.1) (auxAppsOk_reflect b (d + 1) h.2)
  | .forallE ty b bm, d, h => by
    rw [auxAppsOk] at h
    simp only [Bool.and_eq_true] at h
    exact .forallE (auxAppsOk_reflect ty d h.1) (auxAppsOk_reflect b (d + 1) h.2)
  | .letE ty v b, d, h => by
    rw [auxAppsOk] at h
    simp only [Bool.and_eq_true] at h
    exact .letE (auxAppsOk_reflect ty d h.1.1) (auxAppsOk_reflect v d h.1.2)
      (auxAppsOk_reflect b (d + 1) h.2)
  | .proj sn i x, d, h => by
    rw [auxAppsOk] at h
    exact .proj (auxAppsOk_reflect x d h)
  | .app f a, d, h => by
    rw [auxAppsOk] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hnode, hkids⟩ := h
    rw [auxAppsOk_attach_all] at hkids
    rw [List.all_eq_true] at hkids
    unfold auxAppsNodeKids at hkids
    by_cases hhead : auxAppsHeadIsKey R (Expr.app f a) = true
    · -- a key-headed spine: the shape is the node's own test
      rw [if_pos hhead] at hkids
      unfold auxAppsHeadIsKey at hhead
      unfold auxAppsNodeOk at hnode
      cases hfn : (Expr.app f a).getAppFn with
      | const n us =>
        rw [hfn] at hhead hnode
        simp only at hhead hnode
        rw [if_pos hhead] at hnode
        simp only [Bool.and_eq_true] at hnode
        obtain ⟨hus, har⟩ := hnode
        obtain rfl : us = lps.map Level.param := by simpa using hus
        cases hA : arityOf n with
        | none => rw [hA] at har; exact nomatch har
        | some ar =>
          rw [hA] at har
          simp only [Bool.and_eq_true, beq_iff_eq] at har
          have hsp := Expr.mkAppN_getApp (Expr.app f a)
          rw [hfn] at hsp
          rw [← hsp]
          refine AuxAppsOk.key (isAuxAppKey_iff.mp hhead) hA har.1 har.2 (fun x hx => ?_)
          have hlt : sizeOf x < sizeOf (Expr.app f a) :=
            sizeOf_mem_getAppArgs (List.mem_of_mem_drop hx)
          exact auxAppsOk_reflect x d (hkids x hx)
      | _ => rw [hfn] at hhead; exact nomatch hhead
    · -- no key at the head: the two halves
      rw [if_neg hhead] at hkids
      have hf : f ∈ auxAppsKids (Expr.app f a) := by
        show f ∈ [f, a]
        simp
      have ha : a ∈ auxAppsKids (Expr.app f a) := by
        show a ∈ [f, a]
        simp
      refine AuxAppsOk.app (fun n us hfn hkey => ?_)
        (auxAppsOk_reflect f d (hkids f hf)) (auxAppsOk_reflect a d (hkids a ha))
      refine hhead ?_
      unfold auxAppsHeadIsKey
      rw [Expr.getAppFn_app, hfn]
      exact isAuxAppKey_iff.mpr hkey
  termination_by e => sizeOf e
  decreasing_by
    all_goals
      first
        | exact hlt
        | (simp only [Expr.app.sizeOf_spec]; omega)
        | (simp only [Expr.lam.sizeOf_spec]; omega)
        | (simp only [Expr.forallE.sizeOf_spec]; omega)
        | (simp only [Expr.letE.sizeOf_spec]; omega)
        | (simp only [Expr.proj.sizeOf_spec]; omega)

/-! ## The walk's inversions -/

/-- **The λ node, inverted** (`restoreWalk_forallE_inv`'s twin). -/
theorem restoreWalk_lam_inv {R : RestoreTbl} {d : Nat} {ty b e' : Expr} {bm : BinderMeta}
    (h : restoreWalk R d (.lam ty b bm) = .ok e') :
    ∃ ty' b', restoreWalk R d ty = .ok ty' ∧ restoreWalk R (d + 1) b = .ok b' ∧
      e' = .lam ty' b' bm := by
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.lam ty b bm).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false,
      restoreNode_lam] at h
    cases hty : restoreWalk R d ty with
    | error err => rw [hty] at h; simp at h
    | ok ty' =>
      rw [hty] at h
      cases hb : restoreWalk R (d + 1) b with
      | error err => rw [hb] at h; simp at h
      | ok b' =>
        rw [hb] at h
        exact ⟨ty', b', rfl, rfl, (Except.ok.inj h).symm⟩
  · simp only [restoreWalk, hp, Bool.not_false, if_pos] at h
    have hp' := fun n hn => Expr.mentionsConst_lam_false (auxNames_mention_false hp n hn)
    exact ⟨ty, b, restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).1),
      restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).2), (Except.ok.inj h).symm⟩

/-- **The application node, inverted, when the spine head is no key**:
the walk is componentwise.  (The head half `restoreHead` declines when
neither pin map answers at the head — `restoreHead_none`;
`restoreNode_eq_head` at a non-`const` node; then `restoreWalk`'s `.app`
branch, or the prune, which is componentwise by `restoreWalk_of_no_aux`
on both parts.) -/
theorem restoreWalk_app_inv {R : RestoreTbl} {d : Nat} {f a e' : Expr}
    (hkey : ∀ n us, (Expr.app f a).getAppFn = .const n us → ¬ R.IsKey n)
    (h : restoreWalk R d (.app f a) = .ok e') :
    ∃ f' a', restoreWalk R d f = .ok f' ∧ restoreWalk R d a = .ok a' ∧ e' = .app f' a' := by
  have hnode : restoreNode R d (.app f a) = .ok none := by
    rw [restoreNode_eq_head (by intro n us hq; exact Expr.noConfusion hq)]
    refine restoreHead_none ?_ ?_
    · intro n us hfn
      cases hl : R.pins.lookup n with
      | none => rfl
      | some pin => exact absurd (Or.inl (by rw [hl]; rfl)) (hkey n us hfn)
    · intro n us hfn
      cases hl : R.ctorPins.find? (fun p => p.1 == n) with
      | none => rfl
      | some q => exact absurd (Or.inr (by rw [hl]; rfl)) (hkey n us hfn)
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.app f a).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode] at h
    cases hf : restoreWalk R d f with
    | error err => rw [hf] at h; simp at h
    | ok f' =>
      rw [hf] at h
      cases ha : restoreWalk R d a with
      | error err => rw [ha] at h; simp at h
      | ok a' =>
        rw [ha] at h
        exact ⟨f', a', rfl, rfl, (Except.ok.inj h).symm⟩
  · simp only [restoreWalk, hp, Bool.not_false, if_pos] at h
    have hp' := fun n hn => Expr.mentionsConst_app_false (auxNames_mention_false hp n hn)
    exact ⟨f, a, restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).1),
      restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).2), (Except.ok.inj h).symm⟩

/-- **The walk at an auxiliary recursor's name**: a `recMap` key is
renamed (the recursor map is consulted first, `restoreNode_const`). -/
theorem restoreWalk_const_rec {R : RestoreTbl} {d : Nat} {n n' : Name} {us : List Level}
    (hr : R.recMap.lookup n = some n') (haux : n ∈ R.auxNames) :
    restoreWalk R d (.const n us) = .ok (.const n' us) := by
  have hment : (R.auxNames.any fun m => (Expr.const n us).mentionsConst m) = true := by
    simp only [List.any_eq_true]
    exact ⟨n, haux, by simp [Expr.mentionsConst]⟩
  have hnode : restoreNode R d (.const n us) = .ok (some (.const n' us)) := by
    rw [restoreNode_const, hr]
  rw [restoreWalk.eq_def]
  simp only [hment, Bool.not_true, Bool.false_eq_true, if_false, hnode]

/-- **The walk at a name outside `auxNames`**: it is its own
restoration (the prune). -/
theorem restoreWalk_const_free {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level}
    (hn : n ∉ R.auxNames) : restoreWalk R d (.const n us) = .ok (.const n us) := by
  refine restoreWalk_of_no_aux _ _ (fun m hm => ?_)
  simp only [Expr.mentionsConst, beq_eq_false_iff_ne, ne_eq]
  exact fun hq => hn (hq ▸ hm)

/-- **A constructor pin's fire** (`restoreWalk_pin`'s `ctorPins` twin):
at `auxJ.c p⃗ f⃗` with `auxJ.c` a `ctorPins` key (no `pins` answer, an
`auxNames` entry, no `recMap` answer for the bare case) and
`R.nP ≤ args.length`, when the lifted pin is headed by a constant
`J ilvls`, the walk replaces the node by `J.c ilvls` at the lifted pin's
arguments and the arguments past the parameters; the arguments are NOT
visited. -/
theorem restoreWalk_ctorPin {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level}
    {args : List Expr} {pin : Expr} {newName J : Name} {ilvls : List Level}
    (hp : R.pins.lookup n = none)
    (hc : R.ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName))
    (hrec : R.recMap.lookup n = none) (haux : n ∈ R.auxNames) (hlen : R.nP ≤ args.length)
    (hhead : (pin.liftLooseBVars d 0).getAppFn = .const J ilvls) :
    restoreWalk R d (Expr.mkAppN (.const n us) args) =
      .ok (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) (pin.liftLooseBVars d 0).getAppArgs)
        (args.drop R.nP)) := by
  have hment : (R.auxNames.any fun m =>
      (Expr.mkAppN (.const n us) args).mentionsConst m) = true := by
    simp only [List.any_eq_true]
    exact ⟨n, haux, Expr.mentionsConst_mkAppN_head args _ (by simp [Expr.mentionsConst])⟩
  have hnode : restoreNode R d (Expr.mkAppN (.const n us) args) =
      .ok (some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls)
        (pin.liftLooseBVars d 0).getAppArgs) (args.drop R.nP))) := by
    rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
    · have h0 : R.nP = 0 := Nat.le_zero.mp hlen
      simp only [Expr.mkAppN, restoreNode, hrec, hp, hc, Expr.getAppFn, Expr.getAppArgs, h0,
        hhead]
      simp
    · rw [List.concat_eq_append, Expr.mkAppN_append_one]
      have hfn : (Expr.app (Expr.mkAppN (.const n us) as) a).getAppFn = .const n us := by
        show (Expr.mkAppN (.const n us) as).getAppFn = _
        rw [Expr.getAppFn_mkAppN]
        rfl
      have hargs : (Expr.app (Expr.mkAppN (.const n us) as) a).getAppArgs = as ++ [a] := by
        show (Expr.mkAppN (.const n us) as).getAppArgs ++ [a] = _
        rw [Expr.getAppArgs_mkAppN]
        rfl
      rw [List.concat_eq_append] at hlen
      simp only [restoreNode, hfn, hargs, hp, hc, if_neg (Nat.not_lt.mpr hlen), hhead]
  rw [restoreWalk.eq_def]
  simp only [hment, Bool.not_true, Bool.false_eq_true, if_false, hnode]

/-! ## The walk at the three nodes the shape now admits -/

/-- The node step declines at a `let`. -/
theorem restoreNode_letE {R : RestoreTbl} {d : Nat} {ty v b : Expr} :
    restoreNode R d (.letE ty v b) = .ok none := rfl

/-- The node step declines at a projection. -/
theorem restoreNode_proj {R : RestoreTbl} {d : Nat} {sn : Name} {i : Nat} {x : Expr} :
    restoreNode R d (.proj sn i x) = .ok none := rfl

/-- **The walk at a bare constant that is no key and no `recMap`
entry**: it is its own restoration.  (`restoreWalk_const_free` is the
case outside `auxNames`; this is the remaining one, where the node step
declines at both pin maps and the recursor map and the fallthrough
returns the term.) -/
theorem restoreWalk_const_nonkey {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level}
    (hkey : ¬ R.IsKey n) (hrec : R.recMap.lookup n = none) :
    restoreWalk R d (.const n us) = .ok (.const n us) := by
  have hp : R.pins.lookup n = none := by
    cases hl : R.pins.lookup n with
    | none => rfl
    | some pin => exact absurd (Or.inl (by rw [hl]; rfl)) hkey
  have hc : R.ctorPins.find? (fun q => q.1 == n) = none := by
    cases hl : R.ctorPins.find? (fun q => q.1 == n) with
    | none => rfl
    | some q => exact absurd (Or.inr (by rw [hl]; rfl)) hkey
  have hnode : restoreNode R d (.const n us) = .ok none := by
    simp only [restoreNode, hrec, Expr.getAppFn, hp, hc]
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun m => (Expr.const n us).mentionsConst m) with hm | hm
  · rw [restoreWalk.eq_def]
    simp only [hm, Bool.not_true, Bool.false_eq_true, if_false, hnode]
  · exact restoreWalk_of_no_aux _ _ (fun m hmm => auxNames_mention_false hm m hmm)

/-- **The `let` node, inverted**: the walk is componentwise, the body at
`d + 1` (`restoreWalk_lam_inv`'s twin). -/
theorem restoreWalk_letE_inv {R : RestoreTbl} {d : Nat} {ty v b e' : Expr}
    (h : restoreWalk R d (.letE ty v b) = .ok e') :
    ∃ ty' v' b', restoreWalk R d ty = .ok ty' ∧ restoreWalk R d v = .ok v' ∧
      restoreWalk R (d + 1) b = .ok b' ∧ e' = .letE ty' v' b' := by
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.letE ty v b).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false,
      restoreNode_letE] at h
    cases hty : restoreWalk R d ty with
    | error err => rw [hty] at h; simp at h
    | ok ty' =>
      rw [hty] at h
      cases hv : restoreWalk R d v with
      | error err => rw [hv] at h; simp at h
      | ok v' =>
        rw [hv] at h
        cases hb : restoreWalk R (d + 1) b with
        | error err => rw [hb] at h; simp at h
        | ok b' =>
          rw [hb] at h
          exact ⟨ty', v', b', rfl, rfl, rfl, (Except.ok.inj h).symm⟩
  · simp only [restoreWalk, hp, Bool.not_false, if_pos] at h
    have hp' := fun n hn => Expr.mentionsConst_letE_false (auxNames_mention_false hp n hn)
    exact ⟨ty, v, b, restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).1),
      restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).2.1),
      restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).2.2), (Except.ok.inj h).symm⟩

/-- **The projection node, inverted**: the walk descends into the
subject at the same depth. -/
theorem restoreWalk_proj_inv {R : RestoreTbl} {d : Nat} {sn : Name} {i : Nat} {x e' : Expr}
    (h : restoreWalk R d (.proj sn i x) = .ok e') :
    ∃ x', restoreWalk R d x = .ok x' ∧ e' = .proj sn i x' := by
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.proj sn i x).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false,
      restoreNode_proj] at h
    cases hx : restoreWalk R d x with
    | error err => rw [hx] at h; simp at h
    | ok x' => rw [hx] at h; exact ⟨x', rfl, (Except.ok.inj h).symm⟩
  · simp only [restoreWalk, hp, Bool.not_false, if_pos] at h
    have hp' := fun n hn => Expr.mentionsConst_proj_false (auxNames_mention_false hp n hn)
    exact ⟨x, restoreWalk_of_no_aux _ _ hp', (Except.ok.inj h).symm⟩

/-! ## The rebuild for a λ-prefix -/

/-- **The prologue**: `stripPisOrLams` peels the λs a `stripLams`
peels. -/
theorem stripPisOrLams_of_stripLams {k : Nat} {e : Expr} {bs : List (Expr × BinderMeta)}
    {body : Expr} (h : e.stripLams k = some (bs, body)) :
    stripPisOrLams k e = some (bs, body) := by
  induction k generalizing e bs body with
  | zero => simpa only [Expr.stripLams, stripPisOrLams] using h
  | succ k ih =>
    cases e with
    | lam ty b bm =>
      rw [Expr.stripLams] at h
      cases hb : b.stripLams k with
      | none => rw [hb] at h; simp at h
      | some q =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [stripPisOrLams, ih hb, Option.map_some]
    | _ => simp [Expr.stripLams] at h

/-- **The rebuild, for a rule**: on a λ-prefix `restoreNested` walks the
body at depth 0 and puts the λs back (`restoreNested_pis`'s twin;
`stripLams` peels what `stripPisOrLams` peels at a λ-headed term).
`hlam` is what decides the rebuild's binder; at `R.nP = 0` the telescope
is empty and the flag does not matter. -/
theorem restoreNested_lams {R : RestoreTbl} {e e' : Expr} {bs : List (Expr × BinderMeta)}
    {body : Expr} (hs : e.stripLams R.nP = some (bs, body))
    (hlam : 0 < R.nP → ∃ ty b bm, e = .lam ty b bm)
    (h : restoreNested R e = .ok e') :
    ∃ body', restoreWalk R 0 body = .ok body' ∧
      e' = bs.foldr (fun (b : Expr × BinderMeta) acc => Expr.lam b.1 acc b.2) body' := by
  have hso := stripPisOrLams_of_stripLams hs
  simp only [restoreNested, hso] at h
  cases hw : restoreWalk R 0 body with
  | error err => rw [hw] at h; simp at h
  | ok body' =>
    rw [hw] at h
    refine ⟨body', rfl, ?_⟩
    cases hnP : R.nP with
    | zero =>
      rw [hnP] at hs
      simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simpa using h.symm
    | succ k =>
      obtain ⟨ty, b, bm, rfl⟩ := hlam (by omega)
      simpa using h.symm

/-! ## Two facts about the shape -/

/-- A key-headed application's walk, under the shape: the head is a
`pins` key or a `ctorPins` key, and the walk fires by
`restoreWalk_pin`/`restoreWalk_ctorPin` — packaged as the shape's
inversion for the reading law: the walk's result at a key node. -/
theorem AuxAppsOk.key_inv {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat}
    {d : Nat} {n : Name} {args : List Expr} {ar : Nat} (hk : R.KeysInAux)
    (hkey : R.IsKey n) (har : arityOf n = some ar) (hlen : args.length = R.nP + ar)
    (hrec : R.recMap.lookup n = none) :
    (∃ pin, R.pins.lookup n = some pin ∧
      restoreWalk R d (Expr.mkAppN (.const n (lps.map .param)) args)
        = .ok (Expr.mkAppN (pin.liftLooseBVars d 0) (args.drop R.nP))) ∨
    (R.pins.lookup n = none ∧ ∃ pin newName,
      R.ctorPins.find? (fun q => q.1 == n) = some (n, pin, newName) ∧
      ∀ J ilvls, (pin.liftLooseBVars d 0).getAppFn = .const J ilvls →
        restoreWalk R d (Expr.mkAppN (.const n (lps.map .param)) args)
          = .ok (Expr.mkAppN (Expr.mkAppN (.const newName ilvls)
              (pin.liftLooseBVars d 0).getAppArgs) (args.drop R.nP))) := by
  have hnP : R.nP ≤ args.length := by omega
  cases hpin : R.pins.lookup n with
  | some pin =>
    exact Or.inl ⟨pin, rfl, restoreWalk_pin hpin hrec (hk.1 n pin hpin) hnP⟩
  | none =>
    have hsome : (R.ctorPins.find? (fun q => q.1 == n)).isSome = true := by
      rcases hkey with h1 | h1
      · rw [hpin] at h1; exact absurd h1 (by simp)
      · exact h1
    cases hc : R.ctorPins.find? (fun q => q.1 == n) with
    | none => rw [hc] at hsome; exact absurd hsome (by simp)
    | some q =>
      obtain ⟨cn, pin, newName⟩ := q
      obtain rfl : cn = n := by
        have := List.find?_some hc
        simpa using this
      refine Or.inr ⟨rfl, pin, newName, rfl, fun J ilvls hhead => ?_⟩
      exact restoreWalk_ctorPin hpin hc hrec (hk.2.1 _ _ hc) hnP hhead

/-- The parameter variables at depth `d`, instantiated by a sequence
whose first `nP` entries are the parameter openers, are those
openers. -/
theorem map_instSeq_structPsAt_prefix (fvsP fvs : List Expr) (nP d : Nat)
    (hcl : ∀ a ∈ fvsP ++ fvs, a.looseBVarsBounded 0 = true) (hlenP : fvsP.length = nP)
    (hlen : fvs.length = d) :
    (structPsAt d nP).map (Expr.instSeq (fvsP ++ fvs) (nP + d - 1)) = fvsP := by
  have hle : nP ≤ (fvsP ++ fvs).length := by
    simp only [List.length_append, hlenP, hlen]
    omega
  have := map_instSeq_structPsAt (fvsP ++ fvs) d nP hcl hle
  rw [Nat.add_comm nP d]
  rw [this, List.take_left' hlenP]

end ConLeche
