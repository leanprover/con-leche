module

public import ConLeche.Frontend.Scan.Equiv.Kit
import ConLeche.Frontend.Scan.Equiv.Scalars
import ConLeche.Frontend.Scan.Equiv.Keys
import ConLeche.Frontend.Scan.Equiv.Objects

public section

/-!
# The recogniser is its naive reference (task #261)

`scanLineSpec` is the naive recogniser (`ConLeche/Frontend/Scan/Naive.lean`)
read at a `USize` position of a `ByteArray`, and
`scanLineSpec_eq_scanLineFwd` says it IS the fast recogniser
(`ConLeche/Frontend/Scan/Fast.lean`): the same record on every line,
the same tag at the same byte on every malformed one, over every array
and every position — no well-formedness hypothesis, both sides define
the language.  The theorem is `@[csimp]`: the driver
(`ConLeche/Frontend/ExportC.lean`) reads lines with `scanLineSpec`, and
the compiler substitutes `scanLineFwd` on the strength of the equality,
the way the tree installs every fast twin (`canonEqFast`,
`beqMemo`, `constsResolveFFast`).  Nothing is `implemented_by`.

The proof is the chain of twins below it: the scalars
(`Equiv/Scalars.lean`), the keys and lists (`Equiv/Keys.lean`), the
object slot loops (`Equiv/Objects.lean`), then the line loop and the
line here.  Every twin has the one shape
`fastX b i = liftRes b i (naiveX (tailAt b i))` of `Equiv/Kit.lean`.

What the equality does NOT cover, and where that lives: the escape
decoder and `String.fromUTF8?` are shared leaves (both sides run the
same function on the same bytes); the semantic layer `applyLine` —
index resolution, smart constructors, packed fields, taint, prelude
dedupe, the modeller — is shared code, differentially tested; the
stream-index tables have their own laws (`IdTable.get?_insert` and its siblings,
beside the structure in `ConLeche/Frontend/Scan/Types.lean`).
-/

namespace ConLeche.Frontend

/-- One line of the stream from `i`, by the naive reference: the record
and the position after its newline, or `0` when the buffer ended
before a newline did (the fast recogniser's encoding of an incomplete
tail), or the tag at the offending byte.  The driver calls this; the
compiler runs `scanLineFwd`. -/
def scanLineSpec (b : ByteArray) (i : USize) : ScanRes LineRec :=
  match naiveLine (tailAt b i) with
  | .ok (r, some _) rest => .ok r (posAt i.toNat (tailAt b i) rest).toUSize
  | .ok (r, none) _ => .ok r 0
  | .err t rest => .err ⟨posAt i.toNat (tailAt b i) rest, t⟩

/-! ## The line -/

/-- The fast line loop's index state, from the naive one's: `0` none,
`1` `in`, `2` `il`, `3` `ie`. -/
def idxCode : Option (IdxKey × Nat) → UInt8
  | none => 0
  | some (.«in», _) => 1
  | some (.il, _) => 2
  | some (.ie, _) => 3

def idxVal : Option (IdxKey × Nat) → Nat
  | none => 0
  | some (_, n) => n

theorem NRes.suffix_of_err {r : NRes α} {t : ErrTag} {rest l : List UInt8}
    (h : r = .err t rest) (hs : r.rest <:+ l) : rest <:+ l := by subst h; exact hs
theorem NRes.suffix_of_ok {r : NRes α} {x : α} {rest l : List UInt8}
    (h : r = .ok x rest) (hs : r.rest <:+ l) : rest <:+ l := by subst h; exact hs

-- The rest of any sub-scanner of the line loop is a suffix of its input.
macro "line_sub_suffix1" : tactic => `(tactic| first
  | exact naiveNatList_rest_suffix _ | exact naiveStrName_rest_suffix _
  | exact naiveNumName_rest_suffix _ | exact naiveAppExpr_rest_suffix _
  | exact naiveLamExpr_rest_suffix _ | exact naiveForallExpr_rest_suffix _
  | exact naiveLetExpr_rest_suffix _ | exact naiveConstExpr_rest_suffix _
  | exact naiveProjExpr_rest_suffix _ | exact naiveQuotedNat_rest_suffix _
  | exact naiveStr_rest_suffix _ | exact naiveAxiomDecl_rest_suffix _
  | exact naiveDefDecl_rest_suffix _ | exact naiveThmDecl_rest_suffix _
  | exact naiveOpaqueDecl_rest_suffix _ | exact naiveQuotDecl_rest_suffix _
  | exact naiveIndDecl_rest_suffix _)

/-- … also through the key dispatch `match k with | .kStr => … | _ => …`. -/
-- The line loop's inner dispatches are on a `let`-bound key; the case
-- hypothesis names it, and rewriting with it reduces the dispatch.
macro "line_key_case" : tactic => `(tactic| first
  | (have hk : _ = Key.kIn := ‹_›; rw [hk]) | (have hk : _ = Key.kIl := ‹_›; rw [hk]) | (have hk : _ = Key.kIe := ‹_›; rw [hk])
  | (have hk : _ = Key.kBvar := ‹_›; rw [hk]) | (have hk : _ = Key.kSort := ‹_›; rw [hk]) | (have hk : _ = Key.kSucc := ‹_›; rw [hk]) | (have hk : _ = Key.kParam := ‹_›; rw [hk])
  | (have hk : _ = Key.kMax := ‹_›; rw [hk]) | (have hk : _ = Key.kImax := ‹_›; rw [hk]) | (have hk : _ = Key.kStr := ‹_›; rw [hk]) | (have hk : _ = Key.kNum := ‹_›; rw [hk])
  | (have hk : _ = Key.kApp := ‹_›; rw [hk]) | (have hk : _ = Key.kLam := ‹_›; rw [hk]) | (have hk : _ = Key.kForallE := ‹_›; rw [hk]) | (have hk : _ = Key.kLetE := ‹_›; rw [hk])
  | (have hk : _ = Key.kConst := ‹_›; rw [hk]) | (have hk : _ = Key.kProj := ‹_›; rw [hk])
  | (have hk : _ = Key.kAxiom := ‹_›; rw [hk]) | (have hk : _ = Key.kDef := ‹_›; rw [hk]) | (have hk : _ = Key.kThm := ‹_›; rw [hk]) | (have hk : _ = Key.kOpaque := ‹_›; rw [hk])
  | (have hk : _ = Key.kQuot := ‹_›; rw [hk]) | (have hk : _ = Key.kInductive := ‹_›; rw [hk]))

macro "line_sub_suffix" : tactic =>
  `(tactic| first | line_sub_suffix1 | (line_key_case; line_sub_suffix1))

theorem naiveLineLoop_rest_suffix (l : List UInt8) (w : Bool) (idx : Option (IdxKey × Nat))
    (pl : LinePayload) : (naiveLineLoop l w idx pl).rest <:+ l := by
  fun_induction naiveLineLoop l w idx pl
  all_goals first
    | exact List.suffix_rfl
    | exact List.suffix_cons _ _
    | (rename_i ih; exact ih.trans (List.suffix_cons _ _))
    | skip
  all_goals
    have hlv := (naiveValue_rest_suffix ‹naiveValue _ = some _›).trans
      ((naiveKeyBody_rest_suffix ‹naiveKeyBody _ = some _›).trans (List.suffix_cons ‹UInt8› _))
  all_goals first
    | exact hlv
    | exact (naiveNum_rest_suffix ‹naiveNum _ = some _›).trans hlv
    | exact (NRes.suffix_of_err ‹_ = NRes.err _ _› (by line_sub_suffix)).trans hlv
    | (rename_i ih; exact ih.trans ((naiveNum_rest_suffix ‹naiveNum _ = some _›).trans hlv))
    | (rename_i ih; exact ih.trans ((NRes.suffix_of_ok ‹_ = NRes.ok _ _› (by line_sub_suffix)).trans hlv))
    | (rename_i ih; exact ih.trans ((naiveSkipBraced_rest_suffix ‹naiveSkipBraced _ _ = some _›).trans
        ((List.suffix_cons _ _).trans hlv)))
    | skip

/-! ### The line loop, case by case

The line loop is the object loops' skeleton with an index state
(`idxKind`, `idx`) in place of the seen-mask and a payload in place of
the record state, so the proof is `Equiv/Objects.lean`'s: the fast
loop's own `fun_induction`, one tactic macro per case shape, and the
member step's arithmetic taken whole from there (`memberFacts`,
`subSlotFacts`, `restFacts`).  Two things are new.  The index state is
encoded, so the induction runs on the fast loop's OWN variables
(`scanLineLoop_aux`) and every case carries `idxKind = idxCode idx` and
`idx = idxVal idx` to the induction hypothesis; the four `idx_*` lemmas
read a code back into the naive state, and `brace_cond`/`idx_isSome`
translate the two guards that read it.  And the naive dispatch is a
`match` on 23 keys rather than a table lookup: each case reduces it
with `keyOf key = .kXxx`, which `memberFacts`' `keyAt_eq` hands over
from the fast side's own `keyAt … = .kXxx`.

`fun_induction` opens 124 cases: fourteen before the key dispatch (the
whitespace step, the eight arms of the closing brace, the two of the
comma, the quote where a comma was due, and the two key guards), four
or five per key, then the unknown key, the byte that starts no member,
and the end of the array.
-/

/-! ### The index state -/

theorem idxCode_ne_zero (idx : Option (IdxKey × Nat)) : (idxCode idx != 0) = idx.isSome := by
  rcases idx with _ | ⟨kk, n⟩
  · rfl
  · cases kk <;> rfl

theorem idx_zero {idx : Option (IdxKey × Nat)} (hk : (0 : UInt8) = idxCode idx) : idx = none := by
  rcases idx with _ | ⟨kk, n⟩
  · rfl
  · cases kk <;> simp [idxCode] at hk

theorem idx_one {idx : Option (IdxKey × Nat)} {n : Nat} (hk : (1 : UInt8) = idxCode idx)
    (hv : n = idxVal idx) : idx = some (.«in», n) := by
  rcases idx with _ | ⟨kk, m⟩
  · simp [idxCode] at hk
  · cases kk
    · simp only [idxVal] at hv; rw [hv]
    · simp [idxCode] at hk
    · simp [idxCode] at hk

theorem idx_two {idx : Option (IdxKey × Nat)} {n : Nat} (hk : (2 : UInt8) = idxCode idx)
    (hv : n = idxVal idx) : idx = some (.il, n) := by
  rcases idx with _ | ⟨kk, m⟩
  · simp [idxCode] at hk
  · cases kk
    · simp [idxCode] at hk
    · simp only [idxVal] at hv; rw [hv]
    · simp [idxCode] at hk

theorem idx_three {idx : Option (IdxKey × Nat)} {n : Nat} (hk : (3 : UInt8) = idxCode idx)
    (hv : n = idxVal idx) : idx = some (.ie, n) := by
  rcases idx with _ | ⟨kk, m⟩
  · simp [idxCode] at hk
  · cases kk
    · simp [idxCode] at hk
    · simp [idxCode] at hk
    · simp only [idxVal] at hv; rw [hv]

/-- The index guard `idxKind != 0`, in the naive vocabulary. -/
theorem idx_isSome {idxKind : UInt8} {idx : Option (IdxKey × Nat)} (hk : idxKind = idxCode idx) :
    idx.isSome = (idxKind != 0) := by rw [hk, idxCode_ne_zero]

/-- The closing brace's guard, in the naive vocabulary. -/
theorem brace_cond {w : Bool} {idxKind : UInt8} {idx : Option (IdxKey × Nat)} {pl : LinePayload}
    (hk : idxKind = idxCode idx) :
    (w && (idx.isSome || !pl.isAbsent)) = (w && (idxKind != 0 || !pl.isAbsent)) := by
  rw [hk, idxCode_ne_zero]

/-! ### The line loop's case scripts -/

macro "ln_end" : tactic => `(tactic|
  (rename_i h
   intro idx hk hv2
   rw [tailAt_of_not_lt h, naiveLineLoop.eq_def]
   simp only []
   rw [← tailAt_of_not_lt h, liftRes_err_self]))

macro "ln_ws" : tactic => `(tactic|
  (rename_i h c hws ih
   intro idx hk hv2
   simp only [c] at hws
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, ↓reduceIte]
   rw [ih idx hk hv2]
   exact (liftRes_step _ h (naiveLineLoop_rest_suffix _ _ _ _)).symm))

macro "ln_brace_key" : tactic => `(tactic|
  (rename_i h c hws h125 hbr
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

/-- An accepting arm of the closing brace, with the index key its code names. -/
macro "ln_brace_ok" idxlem:ident : tactic => `(tactic|
  (rename_i h c hws h125 r hbr
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [$idxlem:ident hk hv2]
   exact (liftRes_ok_step h).symm))

/-- The two arms with no index key: `decl` (a payload variable) and `header`. -/
macro "ln_brace_decl" : tactic => `(tactic|
  (rename_i h c hws h125 r hbr
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [idx_zero hk]
   exact (liftRes_ok_step h).symm))

macro "ln_brace_header" : tactic => `(tactic|
  (rename_i h c hws h125 hbr
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [idx_zero hk]
   exact (liftRes_ok_step h).symm))

macro "ln_brace_absent" : tactic => `(tactic|
  (rename_i h c hws h125 hbr
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

/-- The brace where the payload and the index key disagree: every
combination is either the fast loop's own `mixedKeys` or excluded by
one of the arms above it. -/
macro "ln_brace_mixed" : tactic => `(tactic|
  (rename_i pl h c hws h125 hbr x5 x4 x3 x2 x1 x0
   intro idx hk hv2
   simp only [c] at hws h125
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, brace_cond hk, hbr, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   rcases idx with _ | ⟨kk, n⟩ <;> (try cases kk) <;> cases pl <;>
     first
       | exact (x5 rfl).elim
       | exact (x4 _ rfl hk).elim
       | exact (x3 _ rfl hk).elim
       | exact (x2 _ rfl hk).elim
       | exact (x1 _ rfl hk).elim
       | exact (x0 rfl hk).elim
       | exact (liftRes_err_self _ _ ErrTag.mixedKeys).symm))

macro "ln_comma_key" : tactic => `(tactic|
  (rename_i h c hws h125 h44
   intro idx hk hv2
   simp only [c] at hws h125 h44
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_comma" : tactic => `(tactic|
  (rename_i h c hws h125 h44 hw ih
   intro idx hk hv2
   simp only [c] at hws h125 h44
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, hw, ↓reduceIte, Bool.false_eq_true]
   rw [ih idx hk hv2]
   exact (liftRes_step _ h (naiveLineLoop_rest_suffix _ _ _ _)).symm))

macro "ln_notwant" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hnw
   intro idx hk hv2
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hnw, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_nokey" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke hke
   intro idx hk hv2
   have hkb := (keyEnd_eq_zero_iff h).mp (by simpa using hke)
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_nocolon" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi
   intro idx hk hv2
   obtain ⟨key, r1, hkb, hnv⟩ := colonFacts h rfl rfl hke hvi
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_other" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34
   intro idx hk hv2
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))


/-! ### The number slots -/

theorem lineNumNone {b : ByteArray} {v e : USize} {lv : List UInt8} (htv : tailAt b v = lv)
    (he0 : e = numEnd b v) (he : (e == v) = true) : naiveNum lv = none := by
  subst he0
  rw [← htv]
  exact (numEnd_eq_self_iff b v).mp (by simpa using he)

theorem lineNumFacts {b : ByteArray} {i v e : USize} {lv : List UInt8}
    (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlt : lv.length < (tailAt b i).length)
    (he0 : e = numEnd b v) (he : ¬ (e == v) = true) :
    naiveNum lv = some (readNatAt b v e, tailAt b e) ∧
      i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  subst he0
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  have he' : ¬ numEnd b v = v := by simpa using he
  obtain ⟨n, r, hnum⟩ : ∃ n r, naiveNum (tailAt b v) = some (n, r) := by
    cases hx : naiveNum (tailAt b v) with
    | none => exact absurd ((numEnd_eq_self_iff b v).mpr hx) he'
    | some p => obtain ⟨n, r⟩ := p; exact ⟨n, r, rfl⟩
  obtain ⟨hpos, hval⟩ := numEnd_of_some hnum
  have hrs : r <:+ tailAt b v := naiveNum_rest_suffix hnum
  have hen : (numEnd b v).toNat = posAt v.toNat (tailAt b v) r := by
    rw [hpos]; exact toNat_toUSize_posAt hvl hrs
  have hten : tailAt b (numEnd b v) = r := by rw [hpos]; exact tailAt_posAt hvl hrs
  obtain ⟨h1, h2, h3, h4⟩ :=
    restFacts h htv hvn hiv hsuf hlt (by rw [← htv]; exact hrs) hen hten
  exact ⟨by rw [hten, hval, ← htv]; exact hnum, h1, h2, h3, h4⟩

/-! ### The index keys -/

macro "ln_idx_dup" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   have hs : idx.isSome = true := by rw [idx_isSome hk]; exact hdup
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hs, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_idx_none" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   have hs : idx.isSome = false := by rw [idx_isSome hk]; simpa using hdup
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hs, lineNumNone htv rfl he,
     ↓reduceIte, Bool.false_eq_true]
   simp only [liftRes]
   exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedNat⟩) hvn))

macro "ln_idx_step" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he hj ih
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   have hs : idx.isSome = false := by rw [idx_isSome hk]; simpa using hdup
   obtain ⟨hnum, hile, heb, hrlt, hie⟩ := lineNumFacts h htv hvn hiv hlvs hlvlt rfl he
   simp only [hkey] at ih ⊢
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hs, hnum, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   simp only [hrlt, ↓reduceDIte]
   rw [liftRes_jump _ hile heb (naiveLineLoop_rest_suffix _ _ _ _)]
   exact ih _ rfl rfl))

macro "ln_idx_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he hj
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   exact absurd (lineNumFacts h htv hvn hiv hlvs hlvlt rfl he).2.2.2.2 hj))


/-! ### The payload keys -/

/-- A payload key on a line that already has one. -/
macro "ln_dup" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h, liftRes_err_self]))

macro "ln_num_none" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, lineNumNone htv rfl he,
     ↓reduceIte, Bool.false_eq_true]
   simp only [liftRes]
   exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedNat⟩) hvn))

macro "ln_num_step" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he hj n ih
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   obtain ⟨hnum, hile, heb, hrlt, hie⟩ := lineNumFacts h htv hvn hiv hlvs hlvlt rfl he
   simp only [hkey] at ih ⊢
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hnum, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   simp only [hrlt, ↓reduceDIte]
   rw [liftRes_jump _ hile heb (naiveLineLoop_rest_suffix _ _ _ _)]
   exact ih _ hk hv2))

macro "ln_num_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup e he hj
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   exact absurd (lineNumFacts h htv hvn hiv hlvs hlvlt rfl he).2.2.2.2 hj))


/-! ### The list keys and the sub-scanner keys -/

/-- The twin of the sub-scanner the key selected, in the case's hypothesis. -/
syntax "ln_twin" ident ident : tactic
macro_rules
  | `(tactic| ln_twin $hs:ident $ht:ident) => `(tactic|
      first
      | rw [scanNatList_eq, $ht:ident] at $hs:ident
      | rw [scanStrName_eq, $ht:ident] at $hs:ident
      | rw [scanNumName_eq, $ht:ident] at $hs:ident
      | rw [scanAppExpr_eq, $ht:ident] at $hs:ident
      | rw [scanLamExpr_eq, $ht:ident] at $hs:ident
      | rw [scanForallExpr_eq, $ht:ident] at $hs:ident
      | rw [scanLetExpr_eq, $ht:ident] at $hs:ident
      | rw [scanConstExpr_eq, $ht:ident] at $hs:ident
      | rw [scanProjExpr_eq, $ht:ident] at $hs:ident
      | rw [scanQuotedNat_eq, $ht:ident] at $hs:ident
      | rw [scanString_eq, $ht:ident] at $hs:ident
      | rw [scanAxiomDecl_eq, $ht:ident] at $hs:ident
      | rw [scanDefDecl_eq, $ht:ident] at $hs:ident
      | rw [scanThmDecl_eq, $ht:ident] at $hs:ident
      | rw [scanOpaqueDecl_eq, $ht:ident] at $hs:ident
      | rw [scanQuotDecl_eq, $ht:ident] at $hs:ident
      | rw [scanIndDecl_eq, $ht:ident] at $hs:ident)

macro "ln_sub_err" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup err hsc
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   try simp only [hkey] at hsc
   ln_twin hsc htv
   obtain ⟨t, r, hr, hlift⟩ := subSlotErr h htv hvn hlvs (by line_sub_suffix1) hsc
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hr, ↓reduceIte, Bool.false_eq_true]
   rw [liftRes_err_pos, hlift]))

macro "ln_sub_step" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup r e hsc hj ih
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   try simp only [hkey] at hsc
   ln_twin hsc htv
   obtain ⟨hread, hile, heb, hrlt, hie⟩ :=
     subSlotFacts h htv hvn hiv hlvs hlvlt (by line_sub_suffix1) hsc
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hread, ↓reduceIte,
     Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   simp only [hrlt, ↓reduceDIte]
   rw [liftRes_jump _ hile heb (naiveLineLoop_rest_suffix _ _ _ _)]
   exact ih _ hk hv2))

macro "ln_sub_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup r e hsc hj
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   try simp only [hkey] at hsc
   ln_twin hsc htv
   exact absurd
     (subSlotFacts h htv hvn hiv hlvs hlvlt (by line_sub_suffix1) hsc).2.2.2.2 hj))

macro "ln_list_step" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup j a d hj hsc ih
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   ln_twin hsc htv
   obtain ⟨hread, hile, heb, hrlt, hie⟩ :=
     subSlotFacts h htv hvn hiv hlvs hlvlt (by line_sub_suffix1) hsc
   simp only [hkey] at ih ⊢
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hread, ↓reduceIte,
     Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   simp only [hrlt, ↓reduceDIte]
   rw [liftRes_jump _ hile heb (naiveLineLoop_rest_suffix _ _ _ _)]
   exact ih _ hk hv2))

macro "ln_list_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup j a d hj hsc
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   ln_twin hsc htv
   exact absurd
     (subSlotFacts h htv hvn hiv hlvs hlvlt (by line_sub_suffix1) hsc).2.2.2.2 hj))

/-- A level list that is not a pair: the fast loop's `expectedList` is
the naive one's. -/
macro "ln_list_bad" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup ns j hsc hbad
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   ln_twin hsc htv
   obtain ⟨hread, hile, heb, hrlt, hie⟩ :=
     subSlotFacts h htv hvn hiv hlvs hlvlt (by line_sub_suffix1) hsc
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hread, ↓reduceIte,
     Bool.false_eq_true]
   rcases ns with _ | ⟨a, _ | ⟨d, _ | ⟨x, t⟩⟩⟩ <;>
     first
       | exact (hbad _ _ rfl).elim
       | exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedList⟩) hvn))


/-! ### The `meta` key -/

/-- The `meta` value's object brace, on both sides. -/
theorem lineMetaHead {b : ByteArray} {v : USize} {lv : List UInt8}
    (htv : tailAt b v = lv) (hb : ¬ (byteAt b v != 123) = true) :
    v < b.usize ∧ lv = 123 :: tailAt b (v + 1) := by
  have hb' : byteAt b v = 123 := by simpa using hb
  have hlt : v < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hb']; decide)
  refine ⟨hlt, ?_⟩
  have h1 := tailAt_of_lt hlt
  have h2 : b.uget v (usizeInBounds b v hlt) = 123 := by rw [← hb', byteAt_eq, h1]; rfl
  rw [← htv, h1, h2]

theorem lineMetaNone {b : ByteArray} {v e : USize} (hlt : v < b.usize)
    (he0 : e = skipBraced b (v + 1) 0) (he : (e == 0) = true) :
    naiveSkipBraced (tailAt b (v + 1)) 0 = none := by
  subst he0
  have hstep := usizeStep b v hlt
  have hvb := USize.lt_iff_toNat_lt.mp hlt
  have hv1l : (v + 1).toNat ≤ (bytes b).length := by simp only [length_bytes]; omega
  have hsb := skipBraced_eq b (v + 1) 0
  cases hx : naiveSkipBraced (tailAt b (v + 1)) 0 with
  | none => rfl
  | some r =>
    exfalso
    rw [hx] at hsb
    have h0 : skipBraced b (v + 1) 0 = 0 := by simpa using he
    rw [h0] at hsb
    have := congrArg USize.toNat hsb.symm
    rw [toNat_toUSize_posAt hv1l (naiveSkipBraced_rest_suffix hx)] at this
    simp only [posAt, USize.toNat_ofNat, Nat.zero_mod] at this
    omega

theorem lineMetaFacts {b : ByteArray} {i v e : USize} {lv : List UInt8}
    (h : i < b.usize) (hlt : v < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlvlt : lv.length < (tailAt b i).length)
    (he0 : e = skipBraced b (v + 1) 0) (he : ¬ (e == 0) = true) :
    naiveSkipBraced (tailAt b (v + 1)) 0 = some (tailAt b e) ∧
      i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  subst he0
  have hstep := usizeStep b v hlt
  have hvb := USize.lt_iff_toNat_lt.mp hlt
  have hv1l : (v + 1).toNat ≤ (bytes b).length := by simp only [length_bytes]; omega
  have hsb := skipBraced_eq b (v + 1) 0
  cases hx : naiveSkipBraced (tailAt b (v + 1)) 0 with
  | none =>
    exfalso
    rw [hx] at hsb
    exact he (by simp [hsb])
  | some r =>
    rw [hx] at hsb
    have hrs : r <:+ tailAt b (v + 1) := naiveSkipBraced_rest_suffix hx
    have hrlv : r <:+ lv := by
      rw [← htv]; exact hrs.trans (tailAt_suffix (by omega))
    have hen : (skipBraced b (v + 1) 0).toNat = posAt (v + 1).toNat (tailAt b (v + 1)) r := by
      rw [hsb]; exact toNat_toUSize_posAt hv1l hrs
    have hten : tailAt b (skipBraced b (v + 1) 0) = r := by
      rw [hsb]; exact tailAt_posAt hv1l hrs
    have hen' : (skipBraced b (v + 1) 0).toNat = posAt v.toNat (tailAt b v) r := by
      rw [hen, ← posAt_transfer (b := b) (i := v) (j := v + 1) (by omega)
        (by omega) (by omega) hrs]
    obtain ⟨h1, h2, h3, h4⟩ := restFacts h htv hvn hiv hsuf hlvlt hrlv hen' hten
    exact ⟨by rw [hten], h1, h2, h3, h4⟩

macro "ln_meta_nobrace" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup hb
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   have hbb : ¬ lv.headD 0 = 123 := by rw [← htv, ← byteAt_eq]; simpa using hb
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, ↓reduceIte, Bool.false_eq_true]
   split
   · exact absurd rfl hbb
   · exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedObject⟩) hvn))

macro "ln_meta_none" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup hb e he
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   obtain ⟨hvlt, hlv⟩ := lineMetaHead htv hb
   rw [hlv] at hvn
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hlv,
     lineMetaNone hvlt rfl he, ↓reduceIte, Bool.false_eq_true]
   simp only [liftRes]
   exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedObject⟩) hvn))

macro "ln_meta_step" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup hb e he hj ih
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   obtain ⟨hvlt, hlv⟩ := lineMetaHead htv hb
   obtain ⟨hread, hile, heb, hrlt, hie⟩ :=
     lineMetaFacts h hvlt htv hvn hiv hlvs hlvlt rfl he
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, hkey', hdup, hlv, hread, ↓reduceIte,
     Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   simp only [hrlt, ↓reduceDIte]
   rw [liftRes_jump _ hile heb (naiveLineLoop_rest_suffix _ _ _ _)]
   exact ih _ hk hv2))

macro "ln_meta_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k hkey hdup hb e he hj
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   obtain ⟨hvlt, hlv⟩ := lineMetaHead htv hb
   exact absurd (lineMetaFacts h hvlt htv hvn hiv hlvs hlvlt rfl he).2.2.2.2 hj))


/-- A key the line loop knows nothing about: the fast dispatch left one
`k ≠ .kXxx` per key it does know, and the naive dispatch falls through
to the same `unknownKey`. -/
macro "ln_unknown" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi k
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   intro idx hk hv2
   obtain ⟨key, r1, lv, hkb, hnv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   simp only [c] at hws h125 h44 h34
   rw [tailAt_of_lt h, naiveLineLoop.eq_def]
   simp only [hws, h125, h44, h34, hw, hkb, hnv, ↓reduceIte, Bool.false_eq_true]
   rw [← tailAt_of_lt h]
   cases hx : keyOf key <;>
     first
       | exact (liftRes_err_self _ _ ErrTag.unknownKey).symm
       | exact absurd (hka.trans hx) ‹_›))

theorem scanLineLoop_aux (b : ByteArray) (i : USize) (wantMember : Bool)
    (idxKind : UInt8) (idxN : Nat) (pl : LinePayload) :
    ∀ idx : Option (IdxKey × Nat), idxKind = idxCode idx → idxN = idxVal idx →
      scanLineLoop b i wantMember idxKind idxN pl =
        liftRes b i (naiveLineLoop (tailAt b i) wantMember idx pl) := by
  fun_induction scanLineLoop b i wantMember idxKind idxN pl
  case case1 => ln_ws
  case case2 => ln_brace_key
  case case3 => ln_brace_ok idx_one
  case case4 => ln_brace_ok idx_two
  case case5 => ln_brace_ok idx_three
  case case6 => ln_brace_decl
  case case7 => ln_brace_header
  case case8 => ln_brace_absent
  case case9 => ln_brace_mixed
  case case10 => ln_comma_key
  case case11 => ln_comma
  case case12 => ln_notwant
  case case13 => ln_nokey
  case case14 => ln_nocolon
  case case15 => ln_idx_dup
  case case16 => ln_idx_none
  case case17 => ln_idx_step
  case case18 => ln_idx_stuck
  case case19 => ln_idx_dup
  case case20 => ln_idx_none
  case case21 => ln_idx_step
  case case22 => ln_idx_stuck
  case case23 => ln_idx_dup
  case case24 => ln_idx_none
  case case25 => ln_idx_step
  case case26 => ln_idx_stuck
  case case27 => ln_dup
  case case28 => ln_num_none
  case case29 => ln_num_step
  case case30 => ln_num_stuck
  case case31 => ln_dup
  case case32 => ln_num_none
  case case33 => ln_num_step
  case case34 => ln_num_stuck
  case case35 => ln_dup
  case case36 => ln_num_none
  case case37 => ln_num_step
  case case38 => ln_num_stuck
  case case39 => ln_dup
  case case40 => ln_num_none
  case case41 => ln_num_step
  case case42 => ln_num_stuck
  case case43 => ln_dup
  case case44 => ln_sub_err
  case case45 => ln_list_step
  case case46 => ln_list_stuck
  case case47 => ln_list_bad
  case case48 => ln_dup
  case case49 => ln_sub_err
  case case50 => ln_list_step
  case case51 => ln_list_stuck
  case case52 => ln_list_bad
  case case53 => ln_dup
  case case54 => ln_sub_err
  case case55 => ln_sub_step
  case case56 => ln_sub_stuck
  case case57 => ln_dup
  case case58 => ln_sub_err
  case case59 => ln_sub_step
  case case60 => ln_sub_stuck
  case case61 => ln_dup
  case case62 => ln_sub_err
  case case63 => ln_sub_step
  case case64 => ln_sub_stuck
  case case65 => ln_dup
  case case66 => ln_sub_err
  case case67 => ln_sub_step
  case case68 => ln_sub_stuck
  case case69 => ln_dup
  case case70 => ln_sub_err
  case case71 => ln_sub_step
  case case72 => ln_sub_stuck
  case case73 => ln_dup
  case case74 => ln_sub_err
  case case75 => ln_sub_step
  case case76 => ln_sub_stuck
  case case77 => ln_dup
  case case78 => ln_sub_err
  case case79 => ln_sub_step
  case case80 => ln_sub_stuck
  case case81 => ln_dup
  case case82 => ln_sub_err
  case case83 => ln_sub_step
  case case84 => ln_sub_stuck
  case case85 => ln_dup
  case case86 => ln_sub_err
  case case87 => ln_sub_step
  case case88 => ln_sub_stuck
  case case89 => ln_dup
  case case90 => ln_sub_err
  case case91 => ln_sub_step
  case case92 => ln_sub_stuck
  case case93 => ln_dup
  case case94 => ln_sub_err
  case case95 => ln_sub_step
  case case96 => ln_sub_stuck
  case case97 => ln_dup
  case case98 => ln_sub_err
  case case99 => ln_sub_step
  case case100 => ln_sub_stuck
  case case101 => ln_dup
  case case102 => ln_sub_err
  case case103 => ln_sub_step
  case case104 => ln_sub_stuck
  case case105 => ln_dup
  case case106 => ln_sub_err
  case case107 => ln_sub_step
  case case108 => ln_sub_stuck
  case case109 => ln_dup
  case case110 => ln_sub_err
  case case111 => ln_sub_step
  case case112 => ln_sub_stuck
  case case113 => ln_dup
  case case114 => ln_sub_err
  case case115 => ln_sub_step
  case case116 => ln_sub_stuck
  case case117 => ln_dup
  case case118 => ln_meta_nobrace
  case case119 => ln_meta_none
  case case120 => ln_meta_step
  case case121 => ln_meta_stuck
  case case122 => ln_unknown
  case case123 => ln_other
  case case124 => ln_end

theorem scanLineLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool)
    (idx : Option (IdxKey × Nat)) (pl : LinePayload) :
    scanLineLoop b i wantMember (idxCode idx) (idxVal idx) pl =
      liftRes b i (naiveLineLoop (tailAt b i) wantMember idx pl) :=
  scanLineLoop_aux b i wantMember (idxCode idx) (idxVal idx) pl idx rfl rfl

/-- Positions compose: the rest `r` of a suffix `d` at `s` is at the
same place seen from `i`. -/
theorem posAt_trans {b : ByteArray} {i : USize} {d r : List UInt8}
    (hi : i.toNat ≤ (bytes b).length) (hd : d <:+ tailAt b i) (hr : r <:+ d) :
    posAt i.toNat (tailAt b i) r = posAt (posAt i.toNat (tailAt b i) d) d r := by
  have := hd.length_le; have := hr.length_le
  simp only [posAt, length_tailAt, length_bytes] at *
  omega

/-- What `skipWs` does, in the naive vocabulary: its tail is the
`dropWhile`, its position the lift's, and it is at the end exactly when
the `dropWhile` is empty. -/
theorem skipWs_facts {b : ByteArray} {j : USize} (hj : j.toNat ≤ (bytes b).length) :
    tailAt b (skipWs b j) = (tailAt b j).dropWhile isWs ∧
      (skipWs b j).toNat = posAt j.toNat (tailAt b j) ((tailAt b j).dropWhile isWs) ∧
      (b.usize ≤ skipWs b j ↔ ((tailAt b j).dropWhile isWs).length = 0) := by
  have hd := List.dropWhile_suffix (l := tailAt b j) isWs
  have hts : tailAt b (skipWs b j) = (tailAt b j).dropWhile isWs := by
    rw [skipWs_eq, tailAt_posAt hj hd]
  refine ⟨hts, by rw [skipWs_eq, toNat_toUSize_posAt hj hd], ?_⟩
  rw [USize.le_iff_toNat_le, ← hts, length_tailAt]; omega

/-- The bytes after a record: a newline, the end, or trailing garbage —
the same three answers on both sides. -/
theorem lineEnd_eq {b : ByteArray} {i j : USize} (r : LineRec) (l2 : List UInt8)
    (hi : i.toNat ≤ (bytes b).length) (hl2 : l2 <:+ tailAt b i)
    (hj : tailAt b j = l2) (hjn : j.toNat = posAt i.toNat (tailAt b i) l2) :
    (let p := skipWs b j
     if byteAt b p == 10 then ScanRes.ok r (p + 1)
     else if b.usize ≤ p then ScanRes.ok r 0
     else ScanRes.err ⟨p.toNat, .trailing⟩) =
    (match (match l2.dropWhile isWs with
            | 10 :: rest => NRes.ok (r, some rest) rest
            | [] => NRes.ok (r, none) []
            | l3 => NRes.err .trailing l3) with
     | NRes.ok (r, some _) rest => ScanRes.ok r (posAt i.toNat (tailAt b i) rest).toUSize
     | NRes.ok (r, none) _ => ScanRes.ok r 0
     | NRes.err t rest => ScanRes.err ⟨posAt i.toNat (tailAt b i) rest, t⟩) := by
  have hjle : j.toNat ≤ (bytes b).length := by
    rw [hjn]; exact posAt_le hi hl2
  obtain ⟨hts, hsn, hsize⟩ := skipWs_facts hjle
  rw [hj] at hts hsn hsize
  have hd : l2.dropWhile isWs <:+ l2 := List.dropWhile_suffix _
  simp only []
  generalize skipWs b j = s at hts hsn hsize
  rw [byteAt_eq, hts]
  generalize l2.dropWhile isWs = d at hd hts hsn hsize
  rcases d with _ | ⟨c, l'⟩
  · simp only [show ((0 : UInt8) == 10) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      hsize.mpr rfl, List.headD_nil]
  · have hlt : s < b.usize := by
      rw [USize.lt_iff_toNat_lt]; have := congrArg List.length hts
      simp only [length_tailAt, List.length_cons] at this; omega
    have hnotend : ¬ b.usize ≤ s := fun h => by have := hsize.mp h; simp at this
    have hpos : posAt i.toNat (tailAt b i) (c :: l') = s.toNat := by
      rw [hsn, hjn, ← posAt_trans hi hl2 hd]
    have hpos' : posAt i.toNat (tailAt b i) l' = s.toNat + 1 := by
      rw [posAt_trans hi (hd.trans hl2) (List.suffix_cons c l'), hpos]
      simp [posAt]
    by_cases hc : c = 10
    · subst hc
      simp only [List.headD_cons, BEq.rfl, ↓reduceIte, hpos']
      congr 1
      rw [← toUSize_toNat_add s 1 (by have := USize.toNat_lt_size b.usize; have := USize.lt_iff_toNat_lt.mp hlt; omega)]
      rfl
    · have hc' : (c == 10) = false := by simp [hc]
      simp only [List.headD_cons, hc', Bool.false_eq_true, ↓reduceIte, hnotend]
      split <;> rename_i h <;> split at h <;> simp_all

theorem scanLineFwd_eq (b : ByteArray) (i : USize) : scanLineFwd b i = scanLineSpec b i := by
  simp only [scanLineFwd, scanLineSpec, naiveLine]
  have hd := List.dropWhile_suffix (l := tailAt b i) isWs
  by_cases hi : i.toNat ≤ (bytes b).length
  · obtain ⟨hts, hsn, hsize⟩ := skipWs_facts hi
    generalize skipWs b i = s at hts hsn hsize
    rw [byteAt_eq, hts]
    generalize (tailAt b i).dropWhile isWs = d at hd hts hsn hsize
    rcases d with _ | ⟨c, l'⟩
    · simp only [show ((0 : UInt8) == 10) = false from rfl, Bool.false_eq_true, ↓reduceIte,
        hsize.mpr rfl, List.headD_nil]
    · have hlt : s < b.usize := by
        rw [USize.lt_iff_toNat_lt]; have := congrArg List.length hts
        simp only [length_tailAt, List.length_cons] at this; omega
      have hnotend : ¬ b.usize ≤ s := fun h => by have := hsize.mp h; simp at this
      have hpos' : posAt i.toNat (tailAt b i) l' = s.toNat + 1 := by
        rw [posAt_trans hi hd (List.suffix_cons c l'), ← hsn]
        simp [posAt]
      have hbig : s.toNat + 1 < USize.size := by
        have := USize.toNat_lt_size b.usize; have := USize.lt_iff_toNat_lt.mp hlt; omega
      have hl' : tailAt b (s + 1) = l' := by
        have := tailAt_of_lt hlt; rw [hts] at this; exact (List.cons.inj this).2.symm
      by_cases hc : c = 10
      · subst hc
        simp only [List.headD_cons, BEq.rfl, ↓reduceIte, hpos']
        congr 1
        rw [← toUSize_toNat_add s 1 hbig]; rfl
      · have hc' : (c == 10) = false := by simp [hc]
        by_cases hb : c = 123
        · subst hb
          simp only [List.headD_cons, hc', Bool.false_eq_true, ↓reduceIte, hnotend, bne_self_eq_false]
          have hloop := scanLineLoop_eq b (s + 1) true none .absent
          simp only [idxCode, idxVal, hl'] at hloop
          rw [hloop]
          have hsuf := naiveLineLoop_rest_suffix l' true none .absent
          have hs1 : (s + 1).toNat = s.toNat + 1 := usizeStep b s hlt
          have hs1le : (s + 1).toNat ≤ (bytes b).length := by
            rw [hs1, ← hpos']; exact posAt_le hi ((List.suffix_cons (123 : UInt8) l').trans hd)
          cases hL : naiveLineLoop l' true none .absent with
          | err t r =>
            rw [hL] at hsuf
            simp only [liftRes, NRes.rest] at hsuf ⊢
            congr 2
            rw [posAt_trans hi ((List.suffix_cons _ _).trans hd) hsuf, hpos']
            simp only [posAt, hs1, hl']
          | ok r l2 =>
            rw [hL] at hsuf
            simp only [NRes.rest] at hsuf
            simp only [liftRes]
            have hj : tailAt b (posAt (s + 1).toNat (tailAt b (s + 1)) l2).toUSize = l2 := by
              rw [tailAt_posAt hs1le (hl' ▸ hsuf)]
            have hjn : (posAt (s + 1).toNat (tailAt b (s + 1)) l2).toUSize.toNat =
                posAt i.toNat (tailAt b i) l2 := by
              rw [toNat_toUSize_posAt hs1le (hl' ▸ hsuf), hl',
                posAt_trans hi ((List.suffix_cons _ _).trans hd) hsuf, hpos', hs1]
            exact lineEnd_eq r l2 hi (hsuf.trans ((List.suffix_cons _ _).trans hd)) hj hjn
        · have hb' : (c != 123) = true := by simp [hb]
          simp only [List.headD_cons, hc', Bool.false_eq_true, ↓reduceIte, hnotend, hb']
          split <;> rename_i h <;> split at h <;> simp_all
  · have hi' : ¬ i < b.usize := fun h => hi (Nat.le_of_lt (toNat_tailAt_lt h))
    have ht : tailAt b i = [] := tailAt_of_not_lt hi'
    have hs : skipWs b i = i := by
      rw [skipWs_eq, ht]; simp [posAt]
    rw [hs, byteAt_eq, ht]
    simp only [List.dropWhile_nil, List.headD_nil]
    have : b.usize ≤ i := USize.le_iff_toNat_le.mpr (Nat.le_of_not_lt (by simpa [USize.lt_iff_toNat_lt] using hi'))
    simp only [show ((0 : UInt8) == 10) = false from rfl, Bool.false_eq_true, ↓reduceIte, this]

/-- THE theorem: the driver's line reader is its naive reference, on
every array at every position. -/
@[csimp] theorem scanLineSpec_eq_scanLineFwd : @scanLineSpec = @scanLineFwd := by
  funext b i
  exact (scanLineFwd_eq b i).symm

end ConLeche.Frontend
