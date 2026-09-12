module

public import ConLeche.Verify.Frontend.Digits
public import ConLeche.Verify.Frontend.Local

public section

/-!
# The three lines of the template, read (task #290)

The naive recogniser on the three lines `hasProofOfFalse`
(`ConLeche/Accepts.lean`) writes with `s!`:

* `{"in":i,"str":{"pre":0,"str":"False"}}` reads as the name entry
  `i ↦ str 0 "False"`;
* `{"ie":j,"const":{"name":i,"us":[]}}` as the expression entry
  `j ↦ const i []`;
* `{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}`
  as the theorem record `thm ⟨k, [], j⟩ v`;

each followed by a newline and anything, with the rest after the
newline — by computing the recogniser on the line's bytes, the four
interpolated indices kept symbolic as decimal runs (`IsDec`,
`ConLeche/Verify/Frontend/Digits.lean`).
-/

namespace ConLeche.Frontend

/-! ## Bytes of templates -/

theorem lit_append (a b : String) : lit (a ++ b) = lit a ++ lit b := by
  simp only [lit, String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.data_append,
    Array.toList_append]

-- the literal pieces of the three templates, as bytes
theorem lit_in : lit (toString "{\"in\":") = [123, 34, 105, 110, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_strFalse : lit (toString ",\"str\":{\"pre\":0,\"str\":\"False\"}}") =
    [44, 34, 115, 116, 114, 34, 58, 123, 34, 112, 114, 101, 34, 58, 48, 44, 34, 115, 116, 114,
     34, 58, 34, 70, 97, 108, 115, 101, 34, 125, 125] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_ie : lit (toString "{\"ie\":") = [123, 34, 105, 101, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_constName : lit (toString ",\"const\":{\"name\":") =
    [44, 34, 99, 111, 110, 115, 116, 34, 58, 123, 34, 110, 97, 109, 101, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_usNil : lit (toString ",\"us\":[]}}") = [44, 34, 117, 115, 34, 58, 91, 93, 125, 125] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_thmAll : lit (toString "{\"thm\":{\"all\":[") =
    [123, 34, 116, 104, 109, 34, 58, 123, 34, 97, 108, 108, 34, 58, 91] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_lpsName : lit (toString "],\"levelParams\":[],\"name\":") =
    [93, 44, 34, 108, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115, 34, 58, 91, 93, 44, 34, 110,
     97, 109, 101, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_type : lit (toString ",\"type\":") = [44, 34, 116, 121, 112, 101, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_value : lit (toString ",\"value\":") = [44, 34, 118, 97, 108, 117, 101, 34, 58] := by
  rw [lit_eq_toByteArray]; decide
theorem lit_close : lit (toString "}}") = [125, 125] := by
  rw [lit_eq_toByteArray]; decide

/-! ## The leaves -/

theorem keyOf_in : keyOf [105, 110] = .kIn := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_ie : keyOf [105, 101] = .kIe := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_str : keyOf [115, 116, 114] = .kStr := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_pre : keyOf [112, 114, 101] = .kPre := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_const : keyOf [99, 111, 110, 115, 116] = .kConst := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_name : keyOf [110, 97, 109, 101] = .kName := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_us : keyOf [117, 115] = .kUs := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_thm : keyOf [116, 104, 109] = .kThm := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_all : keyOf [97, 108, 108] = .kAll := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_levelParams : keyOf [108, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115] =
    .kLevelParams := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_type : keyOf [116, 121, 112, 101] = .kType := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide
theorem keyOf_value : keyOf [118, 97, 108, 117, 101] = .kValue := by
  unfold keyOf keyTable; simp only [lit_eq_toByteArray]; decide

/-- A literal byte that is no whitespace. -/
theorem isWs_lit (c : UInt8) (h : (c == 32 || c == 9 || c == 13) = false) : isWs c = false := by
  simpa [isWs] using h

theorem isWs_of_isDigit {c : UInt8} (h : isDigit c = true) : isWs c = false := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> simp at h

/-- A decimal is no whitespace at its front. -/
theorem dropWhile_isWs_isDec {d : List UInt8} {n : Nat} (hd : IsDec d n) (r : List UInt8) :
    (d ++ r).dropWhile isWs = d ++ r := by
  cases d with
  | nil => exact absurd rfl hd.ne_nil
  | cons c d' =>
    rw [List.cons_append, List.dropWhile_cons, isWs_of_isDigit (hd.digits c (List.mem_cons_self ..))]
    rfl

theorem naiveValue_isDec {d : List UInt8} {n : Nat} (hd : IsDec d n) (r : List UInt8) :
    naiveValue (58 :: (d ++ r)) = some (d ++ r) := by
  unfold naiveValue
  rw [List.dropWhile_cons, isWs_lit 58 (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte, dropWhile_isWs_isDec hd]

theorem naiveValue_lit (c : UInt8) (hc : isWs c = false) (r : List UInt8) :
    naiveValue (58 :: c :: r) = some (c :: r) := by
  unfold naiveValue
  rw [List.dropWhile_cons, isWs_lit 58 (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte, List.dropWhile_cons, hc]

theorem naiveStrBody_False (r : List UInt8) :
    naiveStrBody (70 :: 97 :: 108 :: 115 :: 101 :: 34 :: r) = some ([70, 97, 108, 115, 101], r) := by
  simp [naiveStrBody]
  rw [naiveStrBody.eq_def]; simp

theorem naiveStr_False (r : List UInt8) :
    naiveStr (34 :: 70 :: 97 :: 108 :: 115 :: 101 :: 34 :: r) = .ok "False" r := by
  unfold naiveStr
  simp only [naiveStrBody_False]
  have : String.fromUTF8? (⟨⟨[70, 97, 108, 115, 101]⟩⟩ : ByteArray) = some "False" := by decide
  simp [this]

theorem naiveNat_zero (r : List UInt8) : naiveNat (48 :: 44 :: r) = .ok 0 (44 :: r) := by
  simp [naiveNat, naiveNum, digitsVal, isDigit]

/-- `[]`: the empty index list. -/
theorem naiveNatList_nil (r : List UInt8) : naiveNatList (91 :: 93 :: r) = .ok [] r := by
  unfold naiveNatList naiveList
  show naiveListLoop isDigit naiveNat (93 :: r) [] true = _
  rw [naiveListLoop.eq_def]
  simp [isWs_lit 93 (by decide)]

/-- `[k]`: a one-element index list. -/
theorem naiveNatList_single {d : List UInt8} {k : Nat} (hd : IsDec d k) (r : List UInt8) :
    naiveNatList (91 :: (d ++ 93 :: r)) = .ok [k] r := by
  unfold naiveNatList naiveList
  obtain ⟨c, d', rfl⟩ : ∃ c d', d = c :: d' := by
    cases d with
    | nil => exact absurd rfl hd.ne_nil
    | cons c d' => exact ⟨c, d', rfl⟩
  have hdig : isDigit c = true := hd.digits c (List.mem_cons_self ..)
  have hws : isWs c = false := isWs_of_isDigit hdig
  have h93 : (c == 93) = false := by
    apply beq_eq_false_iff_ne.mpr; intro h; subst h; simp [isDigit] at hdig
  have h44 : (c == 44) = false := by
    apply beq_eq_false_iff_ne.mpr; intro h; subst h; simp [isDigit] at hdig
  have hnat := naiveNat_isDec hd (c := 93) (by decide) r
  show naiveListLoop isDigit naiveNat (c :: (d' ++ 93 :: r)) [] true = _
  rw [naiveListLoop.eq_def]
  simp only [hws, Bool.false_eq_true, ↓reduceIte, h93, h44, hdig, Bool.not_true,
    ← List.cons_append, hnat, dite_eq_ite]
  rw [if_pos (by simp only [List.length_cons, List.length_append]; omega), naiveListLoop.eq_def]
  simp [isWs_lit 93 (by decide)]

/-! ## The name entry `{"in":i,"str":{"pre":0,"str":"False"}}` -/

/-- The inner object `{"pre":0,"str":"False"}` followed by anything. -/
theorem naiveStrName_False (r : List UInt8) :
    naiveStrName (123 :: 34 :: 112 :: 114 :: 101 :: 34 :: 58 :: 48 :: 44 :: 34 :: 115 :: 116 ::
      114 :: 34 :: 58 :: 34 :: 70 :: 97 :: 108 :: 115 :: 101 :: 34 :: 125 :: r) =
      .ok (.str 0 "False") r := by
  unfold naiveStrName naiveObject
  simp only
  rw [naiveObjLoop.eq_def]
  simp +decide [naiveKeyBody, naiveValue_lit 48 (isWs_lit 48 (by decide)), keyOf_pre,
    strNameFields, Slot.of, naiveNat_zero]
  rw [naiveObjLoop.eq_def]
  simp +decide
  rw [naiveObjLoop.eq_def]
  simp +decide [naiveKeyBody, naiveValue_lit 34 (isWs_lit 34 (by decide)), keyOf_str,
    strNameFields, Slot.of, naiveStr_False]
  rw [naiveObjLoop.eq_def]
  simp +decide [NRes.map]

/-- The leaves every step may need, and every hypothesis in scope (the
digit runs' readings).  The steps are computations, so the linter that
flags an unused simp argument is off for them. -/
macro "eval_leaves" : tactic => `(tactic| simp +decide [isWs_lit 34 (by decide),
  isWs_lit 44 (by decide), isWs_lit 125 (by decide), isWs_lit 123 (by decide),
  isWs_lit 91 (by decide), isWs_lit 48 (by decide), naiveKeyBody,
  naiveValue_lit 123 (isWs_lit 123 (by decide)), naiveValue_lit 91 (isWs_lit 91 (by decide)),
  naiveValue_lit 48 (isWs_lit 48 (by decide)), naiveValue_lit 34 (isWs_lit 34 (by decide)),
  keyOf_in, keyOf_ie, keyOf_str, keyOf_pre, keyOf_const, keyOf_name, keyOf_us, keyOf_thm,
  keyOf_all, keyOf_levelParams, keyOf_type, keyOf_value, strNameFields, constFields, thmFields,
  cvSlots, Slot.of, Slot.drop, naiveNat_zero, naiveStr_False, naiveNatList_nil,
  naiveStrName_False, LinePayload.isAbsent, dite_eq_ite, NRes.map, *])

/-- One step of the object loop. -/
macro "obj_step" : tactic => `(tactic| (
  rw [naiveObjLoop.eq_def]
  eval_leaves
  try (rw [if_pos (by (try simp only [List.length_cons, List.length_append]); omega)])))

/-- One step of the line loop. -/
macro "line_step" : tactic => `(tactic| (
  rw [naiveLineLoop.eq_def]
  eval_leaves
  try (rw [if_pos (by (try simp only [List.length_cons, List.length_append]); omega)])))

set_option linter.unusedSimpArgs false

theorem naiveLine_nameFalse (i : Nat) (x : List UInt8) :
    naiveLine (lit s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}" ++ 10 :: x) =
      .ok (.name i (.str 0 "False"), some x) x := by
  have hd := repr_isDec i
  rw [lit_append, lit_append, lit_in, lit_strFalse]
  generalize lit (toString i) = d at hd ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hval := naiveValue_isDec hd
  have hnum := naiveNum_isDec hd (c := 44) (by decide)
  unfold naiveLine
  rw [List.dropWhile_cons, isWs_lit 123 (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  line_step
  line_step
  line_step
  line_step

/-! ## The expression entry `{"ie":j,"const":{"name":i,"us":[]}}` -/

/-- The inner object `{"name":i,"us":[]}` followed by anything. -/
theorem naiveConstExpr_ofDec {d : List UInt8} {i : Nat} (hd : IsDec d i) (r : List UInt8) :
    naiveConstExpr (123 :: 34 :: 110 :: 97 :: 109 :: 101 :: 34 :: 58 ::
      (d ++ 44 :: 34 :: 117 :: 115 :: 34 :: 58 :: 91 :: 93 :: 125 :: r)) =
      .ok (.const i []) r := by
  unfold naiveConstExpr naiveObject
  simp only
  have hval := naiveValue_isDec hd
  have hnat := naiveNat_isDec hd (c := 44) (by decide)
  obj_step
  obj_step
  obj_step
  obj_step

theorem naiveLine_constFalse (j i : Nat) (x : List UInt8) :
    naiveLine (lit s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}" ++ 10 :: x) =
      .ok (.expr j (.const i []), some x) x := by
  have hdj := repr_isDec j
  have hdi := repr_isDec i
  rw [lit_append, lit_append, lit_append, lit_append, lit_ie, lit_constName, lit_usNil]
  generalize lit (toString j) = dj at hdj ⊢
  generalize lit (toString i) = di at hdi ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hval := naiveValue_isDec hdj
  have hnum := naiveNum_isDec hdj (c := 44) (by decide)
  have hobj := naiveConstExpr_ofDec hdi
  unfold naiveLine
  rw [List.dropWhile_cons, isWs_lit 123 (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  line_step
  line_step
  line_step
  line_step

/-! ## The theorem record -/

/-- The object `{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}`
followed by anything. -/
theorem naiveThmDecl_ofDec {dk dj dv : List UInt8} {k j v : Nat} (hk : IsDec dk k)
    (hj : IsDec dj j) (hv : IsDec dv v) (r : List UInt8) :
    naiveThmDecl (123 :: 34 :: 97 :: 108 :: 108 :: 34 :: 58 :: 91 ::
      (dk ++ 93 :: 44 :: 34 :: 108 :: 101 :: 118 :: 101 :: 108 :: 80 :: 97 :: 114 :: 97 :: 109 ::
        115 :: 34 :: 58 :: 91 :: 93 :: 44 :: 34 :: 110 :: 97 :: 109 :: 101 :: 34 :: 58 ::
        (dk ++ 44 :: 34 :: 116 :: 121 :: 112 :: 101 :: 34 :: 58 ::
          (dj ++ 44 :: 34 :: 118 :: 97 :: 108 :: 117 :: 101 :: 34 :: 58 ::
            (dv ++ 125 :: r))))) =
      .ok (.thm ⟨k, [], j⟩ v) r := by
  unfold naiveThmDecl naiveObject
  simp only
  have hlist := naiveNatList_single hk
  have hvalk := naiveValue_isDec hk
  have hnatk := naiveNat_isDec hk (c := 44) (by decide)
  have hvalj := naiveValue_isDec hj
  have hnatj := naiveNat_isDec hj (c := 44) (by decide)
  have hvalv := naiveValue_isDec hv
  have hnatv := naiveNat_isDec hv (c := 125) (by decide)
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step
  obj_step

theorem naiveLine_thm (k j v : Nat) (x : List UInt8) :
    naiveLine (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
        ++ 10 :: x) =
      .ok (.decl (.thm ⟨k, [], j⟩ v), some x) x := by
  have hdk := repr_isDec k
  have hdj := repr_isDec j
  have hdv := repr_isDec v
  rw [lit_append, lit_append, lit_append, lit_append, lit_append, lit_append, lit_append,
    lit_append, lit_thmAll, lit_lpsName, lit_type, lit_value, lit_close]
  generalize lit (toString k) = dk at hdk ⊢
  generalize lit (toString j) = dj at hdj ⊢
  generalize lit (toString v) = dv at hdv ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hobj := naiveThmDecl_ofDec hdk hdj hdv
  unfold naiveLine
  rw [List.dropWhile_cons, isWs_lit 123 (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  line_step
  line_step

end ConLeche.Frontend
