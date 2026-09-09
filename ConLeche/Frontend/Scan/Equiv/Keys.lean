module

public import ConLeche.Frontend.Scan.Equiv.Kit
import ConLeche.Frontend.Scan.Equiv.Scalars

public section

/-!
# The key, list and variant-field twins (task #261)

The member step every slot loop takes — `keyEnd`, `keyAt`, `valueAt` —
against `naiveKeyBody`, `keyOf`, `naiveValue`; the generic list loop
against `scanNatListLoop`; the two variant-valued fields; the header's
bracket skipper; and the suffix lemmas of the generic naive loops,
which are what lets `liftRes_shift` chain a loop's continuation.
-/

namespace ConLeche.Frontend

/-! ## Keys -/

theorem naiveKeyBody_append {l k r : List UInt8} (h : naiveKeyBody l = some (k, r)) :
    l = k ++ 34 :: r := by
  induction l using naiveKeyBody.induct generalizing k r with
  | case1 => simp [naiveKeyBody] at h
  | case2 c l' hc =>
    simp only [naiveKeyBody, hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    have hc34 : c = 34 := by simpa using hc
    rw [← h.1, ← h.2, hc34]
    rfl
  | case3 c l' hc hb => simp [naiveKeyBody, hc, hb] at h
  | case4 c l' hc hb ih =>
    simp only [naiveKeyBody, hc, hb, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveKeyBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨k', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      simp only [List.cons_append]
      rw [← ih hs]

theorem keyEnd_eq (b : ByteArray) (j : USize) :
    keyEnd b j = match naiveKeyBody (tailAt b j) with
      | none => 0
      | some (k, _) => (j.toNat + k.length).toUSize := by
  fun_induction keyEnd b j with
  | case1 j h c hc =>
    have hc' : (b.uget j (usizeInBounds b j h) == 34) = true := hc
    rw [tailAt_of_lt h, naiveKeyBody.eq_def]
    simp only [hc', ↓reduceIte, List.length_nil, Nat.add_zero]
    exact USize.ofNat_toNat.symm
  | case2 j h c hc hb =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : (b.uget j (usizeInBounds b j h) < 32 || b.uget j (usizeInBounds b j h) == 92)
        = true := hb
    rw [tailAt_of_lt h, naiveKeyBody.eq_def]
    simp only [hc', hb', ↓reduceIte, Bool.false_eq_true]
  | case3 j h c hc hb ih =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : ¬ (b.uget j (usizeInBounds b j h) < 32 || b.uget j (usizeInBounds b j h) == 92)
        = true := hb
    have hstep := usizeStep b j h
    rw [tailAt_of_lt h, naiveKeyBody.eq_def]
    simp only [hc', hb', ↓reduceIte, Bool.false_eq_true]
    cases hs : naiveKeyBody (tailAt b (j + 1)) with
    | none => rw [ih, hs]; simp only [Option.map_none]
    | some p =>
      obtain ⟨k, r⟩ := p
      rw [ih, hs]
      simp only [Option.map_some, List.length_cons]
      congr 1
      omega
  | case4 j h =>
    rw [tailAt_of_not_lt h, naiveKeyBody.eq_def]

/-- The arithmetic a key inside the array leaves: the step past its
opening quote does not wrap, and the key, its closing quote and the
rest fill the array. -/
theorem keyEnd_facts {b : ByteArray} {i : USize} {k r : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r)) :
    (i + 1).toNat = i.toNat + 1 ∧
      i.toNat + 1 + k.length + 1 + r.length = b.usize.toNat := by
  have hstep := usizeStep b i h
  have hlen := congrArg List.length (naiveKeyBody_append hk)
  simp only [length_tailAt, List.length_append, List.length_cons, hstep] at hlen
  have hle : i.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp h
  exact ⟨hstep, by omega⟩

/-- At a quote inside the array, `keyEnd == 0` is exactly "no key". -/
theorem keyEnd_eq_zero_iff {b : ByteArray} {i : USize} (h : i < b.usize) :
    keyEnd b (i + 1) = 0 ↔ naiveKeyBody (tailAt b (i + 1)) = none := by
  rw [keyEnd_eq]
  cases hk : naiveKeyBody (tailAt b (i + 1)) with
  | none => simp
  | some p =>
    obtain ⟨k, r⟩ := p
    obtain ⟨hstep, hsum⟩ := keyEnd_facts h hk
    have hsz := USize.toNat_lt_size b.usize
    simp only [hstep, reduceCtorEq, iff_false]
    intro hx
    have hx' := congrArg USize.toNat hx
    rw [toNat_toUSize (by omega)] at hx'
    simp only [USize.toNat_ofNat, Nat.zero_mod] at hx'
    omega

theorem keyEnd_of_some {b : ByteArray} {i : USize} {k r : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r)) :
    keyEnd b (i + 1) ≠ 0 ∧ (keyEnd b (i + 1)).toNat = i.toNat + 1 + k.length ∧
      tailAt b (keyEnd b (i + 1) + 1) = r := by
  obtain ⟨hstep, hsum⟩ := keyEnd_facts h hk
  have hsz := USize.toNat_lt_size b.usize
  have hke : keyEnd b (i + 1) = (i.toNat + 1 + k.length).toUSize := by
    rw [keyEnd_eq, hk, hstep]
  have hken : (keyEnd b (i + 1)).toNat = i.toNat + 1 + k.length := by
    rw [hke, toNat_toUSize (by omega)]
  refine ⟨fun hx => ?_, hken, ?_⟩
  · rw [hx] at hken
    simp only [USize.toNat_ofNat, Nat.zero_mod] at hken
    omega
  · have hstep2 : (keyEnd b (i + 1) + 1).toNat = i.toNat + 1 + k.length + 1 := by
      rw [usize_step_of_lt (by omega), hken]
    have happ := naiveKeyBody_append hk
    show (bytes b).drop _ = r
    rw [hstep2]
    have : (bytes b).drop (i.toNat + 1 + k.length + 1)
        = ((bytes b).drop (i.toNat + 1)).drop (k.length + 1) := by
      rw [List.drop_drop, Nat.add_assoc]
    rw [this, ← hstep, ← tailAt, happ]
    simp

section KeyTable

/- The key table is 66 entries long, and the classifier is proved
against it by unfolding `List.find?` over all of them. -/
set_option maxRecDepth 4000

/-! ### The key table's literals -/

theorem lit_all : lit "all" = [97, 108, 108] := by rw [lit_eq_toByteArray]; rfl
theorem lit_app : lit "app" = [97, 112, 112] := by rw [lit_eq_toByteArray]; rfl
theorem lit_arg : lit "arg" = [97, 114, 103] := by rw [lit_eq_toByteArray]; rfl
theorem lit_axiom : lit "axiom" = [97, 120, 105, 111, 109] := by rw [lit_eq_toByteArray]; rfl
theorem lit_binderInfo :
    lit "binderInfo" = [98, 105, 110, 100, 101, 114, 73, 110, 102, 111] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_body : lit "body" = [98, 111, 100, 121] := by rw [lit_eq_toByteArray]; rfl
theorem lit_bvar : lit "bvar" = [98, 118, 97, 114] := by rw [lit_eq_toByteArray]; rfl
theorem lit_cidx : lit "cidx" = [99, 105, 100, 120] := by rw [lit_eq_toByteArray]; rfl
theorem lit_const : lit "const" = [99, 111, 110, 115, 116] := by rw [lit_eq_toByteArray]; rfl
theorem lit_ctor : lit "ctor" = [99, 116, 111, 114] := by rw [lit_eq_toByteArray]; rfl
theorem lit_ctors : lit "ctors" = [99, 116, 111, 114, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_def : lit "def" = [100, 101, 102] := by rw [lit_eq_toByteArray]; rfl
theorem lit_fn : lit "fn" = [102, 110] := by rw [lit_eq_toByteArray]; rfl
theorem lit_forallE :
    lit "forallE" = [102, 111, 114, 97, 108, 108, 69] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_hints : lit "hints" = [104, 105, 110, 116, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_i : lit "i" = [105] := by rw [lit_eq_toByteArray]; rfl
theorem lit_idx : lit "idx" = [105, 100, 120] := by rw [lit_eq_toByteArray]; rfl
theorem lit_ie : lit "ie" = [105, 101] := by rw [lit_eq_toByteArray]; rfl
theorem lit_il : lit "il" = [105, 108] := by rw [lit_eq_toByteArray]; rfl
theorem lit_imax : lit "imax" = [105, 109, 97, 120] := by rw [lit_eq_toByteArray]; rfl
theorem lit_in : lit "in" = [105, 110] := by rw [lit_eq_toByteArray]; rfl
theorem lit_induct :
    lit "induct" = [105, 110, 100, 117, 99, 116] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_inductive :
    lit "inductive" = [105, 110, 100, 117, 99, 116, 105, 118, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_isRec : lit "isRec" = [105, 115, 82, 101, 99] := by rw [lit_eq_toByteArray]; rfl
theorem lit_isReflexive :
    lit "isReflexive" = [105, 115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_isUnsafe :
    lit "isUnsafe" = [105, 115, 85, 110, 115, 97, 102, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_k : lit "k" = [107] := by rw [lit_eq_toByteArray]; rfl
theorem lit_kind : lit "kind" = [107, 105, 110, 100] := by rw [lit_eq_toByteArray]; rfl
theorem lit_lam : lit "lam" = [108, 97, 109] := by rw [lit_eq_toByteArray]; rfl
theorem lit_letE : lit "letE" = [108, 101, 116, 69] := by rw [lit_eq_toByteArray]; rfl
theorem lit_levelParams :
    lit "levelParams" = [108, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_max : lit "max" = [109, 97, 120] := by rw [lit_eq_toByteArray]; rfl
theorem lit_meta : lit "meta" = [109, 101, 116, 97] := by rw [lit_eq_toByteArray]; rfl
theorem lit_name : lit "name" = [110, 97, 109, 101] := by rw [lit_eq_toByteArray]; rfl
theorem lit_natVal : lit "natVal" = [110, 97, 116, 86, 97, 108] := by rw [lit_eq_toByteArray]; rfl
theorem lit_nfields :
    lit "nfields" = [110, 102, 105, 101, 108, 100, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_nondep :
    lit "nondep" = [110, 111, 110, 100, 101, 112] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_num : lit "num" = [110, 117, 109] := by rw [lit_eq_toByteArray]; rfl
theorem lit_numFields :
    lit "numFields" = [110, 117, 109, 70, 105, 101, 108, 100, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_numIndices :
    lit "numIndices" = [110, 117, 109, 73, 110, 100, 105, 99, 101, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_numMinors :
    lit "numMinors" = [110, 117, 109, 77, 105, 110, 111, 114, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_numMotives :
    lit "numMotives" = [110, 117, 109, 77, 111, 116, 105, 118, 101, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_numNested :
    lit "numNested" = [110, 117, 109, 78, 101, 115, 116, 101, 100] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_numParams :
    lit "numParams" = [110, 117, 109, 80, 97, 114, 97, 109, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_opaque :
    lit "opaque" = [111, 112, 97, 113, 117, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_param : lit "param" = [112, 97, 114, 97, 109] := by rw [lit_eq_toByteArray]; rfl
theorem lit_pre : lit "pre" = [112, 114, 101] := by rw [lit_eq_toByteArray]; rfl
theorem lit_proj : lit "proj" = [112, 114, 111, 106] := by rw [lit_eq_toByteArray]; rfl
theorem lit_pw : lit "pw" = [112, 119] := by rw [lit_eq_toByteArray]; rfl
theorem lit_quot : lit "quot" = [113, 117, 111, 116] := by rw [lit_eq_toByteArray]; rfl
theorem lit_recs : lit "recs" = [114, 101, 99, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_regular :
    lit "regular" = [114, 101, 103, 117, 108, 97, 114] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_rhs : lit "rhs" = [114, 104, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_rules : lit "rules" = [114, 117, 108, 101, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_safety :
    lit "safety" = [115, 97, 102, 101, 116, 121] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_sort : lit "sort" = [115, 111, 114, 116] := by rw [lit_eq_toByteArray]; rfl
theorem lit_str : lit "str" = [115, 116, 114] := by rw [lit_eq_toByteArray]; rfl
theorem lit_strVal :
    lit "strVal" = [115, 116, 114, 86, 97, 108] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_struct :
    lit "struct" = [115, 116, 114, 117, 99, 116] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_succ : lit "succ" = [115, 117, 99, 99] := by rw [lit_eq_toByteArray]; rfl
theorem lit_thm : lit "thm" = [116, 104, 109] := by rw [lit_eq_toByteArray]; rfl
theorem lit_type : lit "type" = [116, 121, 112, 101] := by rw [lit_eq_toByteArray]; rfl
theorem lit_typeName :
    lit "typeName" = [116, 121, 112, 101, 78, 97, 109, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_types : lit "types" = [116, 121, 112, 101, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_us : lit "us" = [117, 115] := by rw [lit_eq_toByteArray]; rfl
theorem lit_value : lit "value" = [118, 97, 108, 117, 101] := by rw [lit_eq_toByteArray]; rfl

/-! ### The literals the fast classifier compares against -/

theorem slit_binderInfo :
    lit "inderInfo" = [105, 110, 100, 101, 114, 73, 110, 102, 111] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_forallE :
    lit "orallE" = [111, 114, 97, 108, 108, 69] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_inductive :
    lit "nductive" = [110, 100, 117, 99, 116, 105, 118, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_isReflexive :
    lit "sReflexive" = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_isUnsafe :
    lit "sUnsafe" = [115, 85, 110, 115, 97, 102, 101] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_levelParams :
    lit "evelParams" = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_nfields :
    lit "fields" = [102, 105, 101, 108, 100, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numParams :
    lit "umParams" = [117, 109, 80, 97, 114, 97, 109, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numFields :
    lit "umFields" = [117, 109, 70, 105, 101, 108, 100, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numMinors :
    lit "umMinors" = [117, 109, 77, 105, 110, 111, 114, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numNested :
    lit "umNested" = [117, 109, 78, 101, 115, 116, 101, 100] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numIndices :
    lit "umIndices" = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_numMotives :
    lit "umMotives" = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_regular :
    lit "egular" = [101, 103, 117, 108, 97, 114] := by
  rw [lit_eq_toByteArray]; rfl
theorem slit_typeName :
    lit "ypeName" = [121, 112, 101, 78, 97, 109, 101] := by
  rw [lit_eq_toByteArray]; rfl

/-! ### `keyOf`, first byte by first byte -/

theorem keyOf_97 (k' : List UInt8) : keyOf (97 :: k') =
    if k' = [108, 108] then Key.kAll
    else if k' = [112, 112] then Key.kApp
    else if k' = [114, 103] then Key.kArg
    else if k' = [120, 105, 111, 109] then Key.kAxiom
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [108, 108]
  case pos => subst h0; simp
  by_cases h1 : k' = [112, 112]
  case pos => subst h1; simp
  by_cases h2 : k' = [114, 103]
  case pos => subst h2; simp
  by_cases h3 : k' = [120, 105, 111, 109]
  case pos => subst h3; simp
  have b0 : (([108, 108] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([112, 112] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([114, 103] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([120, 105, 111, 109] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  simp only [b0, b1, b2, b3]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem keyOf_98 (k' : List UInt8) : keyOf (98 :: k') =
    if k' = [105, 110, 100, 101, 114, 73, 110, 102, 111] then Key.kBinderInfo
    else if k' = [111, 100, 121] then Key.kBody
    else if k' = [118, 97, 114] then Key.kBvar
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [105, 110, 100, 101, 114, 73, 110, 102, 111]
  case pos => subst h0; simp
  by_cases h1 : k' = [111, 100, 121]
  case pos => subst h1; simp
  by_cases h2 : k' = [118, 97, 114]
  case pos => subst h2; simp
  have b0 : (([105, 110, 100, 101, 114, 73, 110, 102, 111] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([111, 100, 121] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([118, 97, 114] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  simp only [b0, b1, b2]
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem keyOf_99 (k' : List UInt8) : keyOf (99 :: k') =
    if k' = [105, 100, 120] then Key.kCidx
    else if k' = [111, 110, 115, 116] then Key.kConst
    else if k' = [116, 111, 114] then Key.kCtor
    else if k' = [116, 111, 114, 115] then Key.kCtors
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [105, 100, 120]
  case pos => subst h0; simp
  by_cases h1 : k' = [111, 110, 115, 116]
  case pos => subst h1; simp
  by_cases h2 : k' = [116, 111, 114]
  case pos => subst h2; simp
  by_cases h3 : k' = [116, 111, 114, 115]
  case pos => subst h3; simp
  have b0 : (([105, 100, 120] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([111, 110, 115, 116] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([116, 111, 114] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([116, 111, 114, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  simp only [b0, b1, b2, b3]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem keyOf_100 (k' : List UInt8) : keyOf (100 :: k') =
    if k' = [101, 102] then Key.kDef
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [101, 102]
  case pos => subst h0; simp
  have b0 : (([101, 102] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]

theorem keyOf_102 (k' : List UInt8) : keyOf (102 :: k') =
    if k' = [110] then Key.kFn
    else if k' = [111, 114, 97, 108, 108, 69] then Key.kForallE
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [110]
  case pos => subst h0; simp
  by_cases h1 : k' = [111, 114, 97, 108, 108, 69]
  case pos => subst h1; simp
  have b0 : (([110] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([111, 114, 97, 108, 108, 69] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  simp only [b0, b1]
  rw [if_neg h0, if_neg h1]

theorem keyOf_104 (k' : List UInt8) : keyOf (104 :: k') =
    if k' = [105, 110, 116, 115] then Key.kHints
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [105, 110, 116, 115]
  case pos => subst h0; simp
  have b0 : (([105, 110, 116, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]

theorem keyOf_105 (k' : List UInt8) : keyOf (105 :: k') =
    if k' = [] then Key.kI
    else if k' = [100, 120] then Key.kIdx
    else if k' = [101] then Key.kIe
    else if k' = [108] then Key.kIl
    else if k' = [109, 97, 120] then Key.kImax
    else if k' = [110] then Key.kIn
    else if k' = [110, 100, 117, 99, 116] then Key.kInduct
    else if k' = [110, 100, 117, 99, 116, 105, 118, 101] then Key.kInductive
    else if k' = [115, 82, 101, 99] then Key.kIsRec
    else if k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] then Key.kIsReflexive
    else if k' = [115, 85, 110, 115, 97, 102, 101] then Key.kIsUnsafe
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = []
  case pos => subst h0; simp
  by_cases h1 : k' = [100, 120]
  case pos => subst h1; simp
  by_cases h2 : k' = [101]
  case pos => subst h2; simp
  by_cases h3 : k' = [108]
  case pos => subst h3; simp
  by_cases h4 : k' = [109, 97, 120]
  case pos => subst h4; simp
  by_cases h5 : k' = [110]
  case pos => subst h5; simp
  by_cases h6 : k' = [110, 100, 117, 99, 116]
  case pos => subst h6; simp
  by_cases h7 : k' = [110, 100, 117, 99, 116, 105, 118, 101]
  case pos => subst h7; simp
  by_cases h8 : k' = [115, 82, 101, 99]
  case pos => subst h8; simp
  by_cases h9 : k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101]
  case pos => subst h9; simp
  by_cases h10 : k' = [115, 85, 110, 115, 97, 102, 101]
  case pos => subst h10; simp
  have b0 : k'.isEmpty = false := by
    cases k' with
    | nil => exact absurd rfl h0
    | cons _ _ => rfl
  have b1 : (([100, 120] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([108] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  have b4 : (([109, 97, 120] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h4
  have b5 : (([110] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h5
  have b6 : (([110, 100, 117, 99, 116] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h6
  have b7 : (([110, 100, 117, 99, 116, 105, 118, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h7
  have b8 : (([115, 82, 101, 99] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h8
  have b9 : (([115, 82, 101, 102, 108, 101, 120, 105, 118, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h9
  have b10 : (([115, 85, 110, 115, 97, 102, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h10
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7,
    if_neg h8, if_neg h9, if_neg h10]

theorem keyOf_107 (k' : List UInt8) : keyOf (107 :: k') =
    if k' = [] then Key.kK
    else if k' = [105, 110, 100] then Key.kKind
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = []
  case pos => subst h0; simp
  by_cases h1 : k' = [105, 110, 100]
  case pos => subst h1; simp
  have b0 : k'.isEmpty = false := by
    cases k' with
    | nil => exact absurd rfl h0
    | cons _ _ => rfl
  have b1 : (([105, 110, 100] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  simp only [b0, b1]
  rw [if_neg h0, if_neg h1]

theorem keyOf_108 (k' : List UInt8) : keyOf (108 :: k') =
    if k' = [97, 109] then Key.kLam
    else if k' = [101, 116, 69] then Key.kLetE
    else if k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] then Key.kLevelParams
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 109]
  case pos => subst h0; simp
  by_cases h1 : k' = [101, 116, 69]
  case pos => subst h1; simp
  by_cases h2 : k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115]
  case pos => subst h2; simp
  have b0 : (([97, 109] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([101, 116, 69] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([101, 118, 101, 108, 80, 97, 114, 97, 109, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  simp only [b0, b1, b2]
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem keyOf_109 (k' : List UInt8) : keyOf (109 :: k') =
    if k' = [97, 120] then Key.kMax
    else if k' = [101, 116, 97] then Key.kMeta
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 120]
  case pos => subst h0; simp
  by_cases h1 : k' = [101, 116, 97]
  case pos => subst h1; simp
  have b0 : (([97, 120] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([101, 116, 97] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  simp only [b0, b1]
  rw [if_neg h0, if_neg h1]

theorem keyOf_110 (k' : List UInt8) : keyOf (110 :: k') =
    if k' = [97, 109, 101] then Key.kName
    else if k' = [97, 116, 86, 97, 108] then Key.kNatVal
    else if k' = [102, 105, 101, 108, 100, 115] then Key.kNfields
    else if k' = [111, 110, 100, 101, 112] then Key.kNondep
    else if k' = [117, 109] then Key.kNum
    else if k' = [117, 109, 70, 105, 101, 108, 100, 115] then Key.kNumFields
    else if k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] then Key.kNumIndices
    else if k' = [117, 109, 77, 105, 110, 111, 114, 115] then Key.kNumMinors
    else if k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] then Key.kNumMotives
    else if k' = [117, 109, 78, 101, 115, 116, 101, 100] then Key.kNumNested
    else if k' = [117, 109, 80, 97, 114, 97, 109, 115] then Key.kNumParams
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 109, 101]
  case pos => subst h0; simp
  by_cases h1 : k' = [97, 116, 86, 97, 108]
  case pos => subst h1; simp
  by_cases h2 : k' = [102, 105, 101, 108, 100, 115]
  case pos => subst h2; simp
  by_cases h3 : k' = [111, 110, 100, 101, 112]
  case pos => subst h3; simp
  by_cases h4 : k' = [117, 109]
  case pos => subst h4; simp
  by_cases h5 : k' = [117, 109, 70, 105, 101, 108, 100, 115]
  case pos => subst h5; simp
  by_cases h6 : k' = [117, 109, 73, 110, 100, 105, 99, 101, 115]
  case pos => subst h6; simp
  by_cases h7 : k' = [117, 109, 77, 105, 110, 111, 114, 115]
  case pos => subst h7; simp
  by_cases h8 : k' = [117, 109, 77, 111, 116, 105, 118, 101, 115]
  case pos => subst h8; simp
  by_cases h9 : k' = [117, 109, 78, 101, 115, 116, 101, 100]
  case pos => subst h9; simp
  by_cases h10 : k' = [117, 109, 80, 97, 114, 97, 109, 115]
  case pos => subst h10; simp
  have b0 : (([97, 109, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([97, 116, 86, 97, 108] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([102, 105, 101, 108, 100, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([111, 110, 100, 101, 112] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  have b4 : (([117, 109] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h4
  have b5 : (([117, 109, 70, 105, 101, 108, 100, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h5
  have b6 : (([117, 109, 73, 110, 100, 105, 99, 101, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h6
  have b7 : (([117, 109, 77, 105, 110, 111, 114, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h7
  have b8 : (([117, 109, 77, 111, 116, 105, 118, 101, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h8
  have b9 : (([117, 109, 78, 101, 115, 116, 101, 100] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h9
  have b10 : (([117, 109, 80, 97, 114, 97, 109, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h10
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7,
    if_neg h8, if_neg h9, if_neg h10]

theorem keyOf_111 (k' : List UInt8) : keyOf (111 :: k') =
    if k' = [112, 97, 113, 117, 101] then Key.kOpaque
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [112, 97, 113, 117, 101]
  case pos => subst h0; simp
  have b0 : (([112, 97, 113, 117, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]

theorem keyOf_112 (k' : List UInt8) : keyOf (112 :: k') =
    if k' = [97, 114, 97, 109] then Key.kParam
    else if k' = [114, 101] then Key.kPre
    else if k' = [114, 111, 106] then Key.kProj
    else if k' = [119] then Key.kPw
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 114, 97, 109]
  case pos => subst h0; simp
  by_cases h1 : k' = [114, 101]
  case pos => subst h1; simp
  by_cases h2 : k' = [114, 111, 106]
  case pos => subst h2; simp
  by_cases h3 : k' = [119]
  case pos => subst h3; simp
  have b0 : (([97, 114, 97, 109] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([114, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([114, 111, 106] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([119] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  simp only [b0, b1, b2, b3]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem keyOf_113 (k' : List UInt8) : keyOf (113 :: k') =
    if k' = [117, 111, 116] then Key.kQuot
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [117, 111, 116]
  case pos => subst h0; simp
  have b0 : (([117, 111, 116] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]

theorem keyOf_114 (k' : List UInt8) : keyOf (114 :: k') =
    if k' = [101, 99, 115] then Key.kRecs
    else if k' = [101, 103, 117, 108, 97, 114] then Key.kRegular
    else if k' = [104, 115] then Key.kRhs
    else if k' = [117, 108, 101, 115] then Key.kRules
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [101, 99, 115]
  case pos => subst h0; simp
  by_cases h1 : k' = [101, 103, 117, 108, 97, 114]
  case pos => subst h1; simp
  by_cases h2 : k' = [104, 115]
  case pos => subst h2; simp
  by_cases h3 : k' = [117, 108, 101, 115]
  case pos => subst h3; simp
  have b0 : (([101, 99, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([101, 103, 117, 108, 97, 114] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([104, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([117, 108, 101, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  simp only [b0, b1, b2, b3]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem keyOf_115 (k' : List UInt8) : keyOf (115 :: k') =
    if k' = [97, 102, 101, 116, 121] then Key.kSafety
    else if k' = [111, 114, 116] then Key.kSort
    else if k' = [116, 114] then Key.kStr
    else if k' = [116, 114, 86, 97, 108] then Key.kStrVal
    else if k' = [116, 114, 117, 99, 116] then Key.kStruct
    else if k' = [117, 99, 99] then Key.kSucc
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 102, 101, 116, 121]
  case pos => subst h0; simp
  by_cases h1 : k' = [111, 114, 116]
  case pos => subst h1; simp
  by_cases h2 : k' = [116, 114]
  case pos => subst h2; simp
  by_cases h3 : k' = [116, 114, 86, 97, 108]
  case pos => subst h3; simp
  by_cases h4 : k' = [116, 114, 117, 99, 116]
  case pos => subst h4; simp
  by_cases h5 : k' = [117, 99, 99]
  case pos => subst h5; simp
  have b0 : (([97, 102, 101, 116, 121] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([111, 114, 116] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([116, 114] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([116, 114, 86, 97, 108] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  have b4 : (([116, 114, 117, 99, 116] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h4
  have b5 : (([117, 99, 99] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h5
  simp only [b0, b1, b2, b3, b4, b5]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

theorem keyOf_116 (k' : List UInt8) : keyOf (116 :: k') =
    if k' = [104, 109] then Key.kThm
    else if k' = [121, 112, 101] then Key.kType
    else if k' = [121, 112, 101, 78, 97, 109, 101] then Key.kTypeName
    else if k' = [121, 112, 101, 115] then Key.kTypes
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [104, 109]
  case pos => subst h0; simp
  by_cases h1 : k' = [121, 112, 101]
  case pos => subst h1; simp
  by_cases h2 : k' = [121, 112, 101, 78, 97, 109, 101]
  case pos => subst h2; simp
  by_cases h3 : k' = [121, 112, 101, 115]
  case pos => subst h3; simp
  have b0 : (([104, 109] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  have b1 : (([121, 112, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h1
  have b2 : (([121, 112, 101, 78, 97, 109, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h2
  have b3 : (([121, 112, 101, 115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h3
  simp only [b0, b1, b2, b3]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem keyOf_117 (k' : List UInt8) : keyOf (117 :: k') =
    if k' = [115] then Key.kUs
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [115]
  case pos => subst h0; simp
  have b0 : (([115] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]

theorem keyOf_118 (k' : List UInt8) : keyOf (118 :: k') =
    if k' = [97, 108, 117, 101] then Key.kValue
    else Key.kUnknown := by
  unfold keyOf keyTable
  simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo, lit_body,
    lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn, lit_forallE, lit_hints,
    lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct, lit_inductive, lit_isRec,
    lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam, lit_letE, lit_levelParams, lit_max,
    lit_meta, lit_name, lit_natVal, lit_nfields, lit_nondep, lit_num, lit_numFields,
    lit_numIndices, lit_numMinors, lit_numMotives, lit_numNested, lit_numParams, lit_opaque,
    lit_param, lit_pre, lit_proj, lit_pw, lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules,
    lit_safety, lit_sort, lit_str, lit_strVal, lit_struct, lit_succ, lit_thm, lit_type,
    lit_typeName, lit_types, lit_us, lit_value]
  simp
  by_cases h0 : k' = [97, 108, 117, 101]
  case pos => subst h0; simp
  have b0 : (([97, 108, 117, 101] : List UInt8) == k') = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact Ne.symm h0
  simp only [b0]
  rw [if_neg h0]


/-! ### The classifier's arithmetic -/

theorem usz1 : ((1 : USize)).toNat = 1 := by simp
theorem usz2 : ((2 : USize)).toNat = 2 := by simp
theorem usz3 : ((3 : USize)).toNat = 3 := by simp
theorem usz4 : ((4 : USize)).toNat = 4 := by simp
theorem usz5 : ((5 : USize)).toNat = 5 := by simp
theorem usz6 : ((6 : USize)).toNat = 6 := by simp
theorem usz7 : ((7 : USize)).toNat = 7 := by simp
theorem usz8 : ((8 : USize)).toNat = 8 := by simp
theorem usz9 : ((9 : USize)).toNat = 9 := by simp
theorem usz10 : ((10 : USize)).toNat = 10 := by simp
theorem usz11 : ((11 : USize)).toNat = 11 := by simp

theorem kl_beq {kl c : USize} (h : kl.toNat = c.toNat) : (kl == c) = true := by
  simp only [beq_iff_eq]
  exact USize.toNat_inj.mp h

theorem kl_beq_ne {kl c : USize} (h : ¬ kl.toNat = c.toNat) : ¬ (kl == c) = true := by
  simp only [beq_iff_eq]
  intro hx
  exact h (by rw [hx])

/-- Under the classifier's length test its literal compare is a list
equality: the key's closing quote stops any longer match. -/
theorem isPrefixOf_key {lst k' r : List UInt8} (hl : k'.length = lst.length) :
    lst.isPrefixOf (k' ++ 34 :: r) = (k' == lst) := by
  induction lst generalizing k' with
  | nil =>
    cases k' with
    | nil => simp
    | cons a as => simp at hl
  | cons x xs ih =>
    cases k' with
    | nil => simp at hl
    | cons a as =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.cons_append, List.isPrefixOf_cons_cons, ih hl]
      simp
      rw [BEq.comm]

theorem keyOf_nil : keyOf [] = Key.kUnknown := by
  unfold keyOf keyTable
  simp only [lit_eq_toByteArray]
  rfl


/-! ### The unrolled literal compares (task #264)

`keyAt` compares a key's tail by `litN b j c₀ … c_{n-1}`, an unrolled
chain of `byteAt` equalities; when the key has exactly `n` more bytes,
every read is inside the key and the chain is the list equality. -/

/-- One byte of a key: the tail at `j` starts with `c`, so `byteAt b j = c`
and the tail at `j + 1` is the rest. -/
theorem key_byte_step {b : ByteArray} {j : USize} {c : UInt8} {t : List UInt8}
    (h : tailAt b j = c :: t) : byteAt b j = c ∧ tailAt b (j + 1) = t := by
  have hlt : j < b.usize := by
    by_cases hlt : j < b.usize
    · exact hlt
    · rw [tailAt_of_not_lt hlt] at h; exact absurd h (by simp)
  have hx := tailAt_of_lt hlt
  rw [h] at hx
  injection hx with h1 h2
  exact ⟨by rw [byteAt_eq, h]; rfl, h2.symm⟩

/-- A small `USize` literal step, `j + (m + 1) = j + m + 1`. -/
theorem usize_lit_step (j : USize) (m : Nat) (hm : m + 1 < 2 ^ 32) :
    j + (m + 1).toUSize = j + m.toUSize + 1 := by
  rw [USize.add_assoc]; congr 1
  apply USize.toNat_inj.mp
  have h1 : m + 1 < USize.size := Nat.lt_of_lt_of_le hm USize.le_size
  have h2 : m < USize.size := by omega
  have h3 : (1 : Nat) < USize.size := by omega
  simp only [USize.toNat_add, Nat.toUSize, USize.toNat_ofNat', USize.size] at *
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  have : (1 : USize).toNat = 1 := by
    simp only [USize.toNat_ofNat] at *; exact Nat.mod_eq_of_lt h3
  rw [this, Nat.mod_eq_of_lt h1]
theorem usize_add_2 (j : USize) : j + 2 = j + 1 + 1 := usize_lit_step j 1 (by decide)
theorem usize_add_3 (j : USize) : j + 3 = j + 2 + 1 := usize_lit_step j 2 (by decide)
theorem usize_add_4 (j : USize) : j + 4 = j + 3 + 1 := usize_lit_step j 3 (by decide)
theorem usize_add_5 (j : USize) : j + 5 = j + 4 + 1 := usize_lit_step j 4 (by decide)
theorem usize_add_6 (j : USize) : j + 6 = j + 5 + 1 := usize_lit_step j 5 (by decide)
theorem usize_add_7 (j : USize) : j + 7 = j + 6 + 1 := usize_lit_step j 6 (by decide)
theorem usize_add_8 (j : USize) : j + 8 = j + 7 + 1 := usize_lit_step j 7 (by decide)
theorem usize_add_9 (j : USize) : j + 9 = j + 8 + 1 := usize_lit_step j 8 (by decide)

theorem lit1_key (b : ByteArray) (j : USize) (c0 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 1) :
    (lit1 b j c0 = true) = (k' = [c0]) := by
  rcases k' with _ | ⟨a0, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit1
  obtain ⟨e0, t0⟩ := key_byte_step hT
  simp only [e0, beq_iff_eq, List.cons.injEq, and_true]

theorem lit2_key (b : ByteArray) (j : USize) (c0 c1 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 2) :
    (lit2 b j c0 c1 = true) = (k' = [c0, c1]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨_, _⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit2
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  simp only [e0, e1, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]

theorem lit3_key (b : ByteArray) (j : USize) (c0 c1 c2 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 3) :
    (lit3 b j c0 c1 c2 = true) = (k' = [c0, c1, c2]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨_, _⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit3
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  simp only [usize_add_2, e0, e1, e2, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit4_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 4) :
    (lit4 b j c0 c1 c2 c3 = true) = (k' = [c0, c1, c2, c3]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit4
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  simp only [usize_add_3, usize_add_2, e0, e1, e2, e3, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit5_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 5) :
    (lit5 b j c0 c1 c2 c3 c4 = true) = (k' = [c0, c1, c2, c3, c4]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit5
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  simp only [usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit6_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 6) :
    (lit6 b j c0 c1 c2 c3 c4 c5 = true) = (k' = [c0, c1, c2, c3, c4, c5]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit6
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  obtain ⟨e5, t5⟩ := key_byte_step t4
  simp only [usize_add_5, usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, e5, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit7_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 7) :
    (lit7 b j c0 c1 c2 c3 c4 c5 c6 = true) = (k' = [c0, c1, c2, c3, c4, c5, c6]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit7
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  obtain ⟨e5, t5⟩ := key_byte_step t4
  obtain ⟨e6, t6⟩ := key_byte_step t5
  simp only [usize_add_6, usize_add_5, usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, e5, e6, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit8_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 8) :
    (lit8 b j c0 c1 c2 c3 c4 c5 c6 c7 = true) = (k' = [c0, c1, c2, c3, c4, c5, c6, c7]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit8
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  obtain ⟨e5, t5⟩ := key_byte_step t4
  obtain ⟨e6, t6⟩ := key_byte_step t5
  obtain ⟨e7, t7⟩ := key_byte_step t6
  simp only [usize_add_7, usize_add_6, usize_add_5, usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, e5, e6, e7, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit9_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 9) :
    (lit9 b j c0 c1 c2 c3 c4 c5 c6 c7 c8 = true) = (k' = [c0, c1, c2, c3, c4, c5, c6, c7, c8]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit9
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  obtain ⟨e5, t5⟩ := key_byte_step t4
  obtain ⟨e6, t6⟩ := key_byte_step t5
  obtain ⟨e7, t7⟩ := key_byte_step t6
  obtain ⟨e8, t8⟩ := key_byte_step t7
  simp only [usize_add_8, usize_add_7, usize_add_6, usize_add_5, usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, e5, e6, e7, e8, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

theorem lit10_key (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : UInt8) (k' r : List UInt8)
    (hT : tailAt b j = k' ++ 34 :: r) (hl : k'.length = 10) :
    (lit10 b j c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 = true) = (k' = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]) := by
  rcases k' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.cons_append, List.nil_append] at hT
  unfold lit10
  obtain ⟨e0, t0⟩ := key_byte_step hT
  obtain ⟨e1, t1⟩ := key_byte_step t0
  obtain ⟨e2, t2⟩ := key_byte_step t1
  obtain ⟨e3, t3⟩ := key_byte_step t2
  obtain ⟨e4, t4⟩ := key_byte_step t3
  obtain ⟨e5, t5⟩ := key_byte_step t4
  obtain ⟨e6, t6⟩ := key_byte_step t5
  obtain ⟨e7, t7⟩ := key_byte_step t6
  obtain ⟨e8, t8⟩ := key_byte_step t7
  obtain ⟨e9, t9⟩ := key_byte_step t8
  simp only [usize_add_9, usize_add_8, usize_add_7, usize_add_6, usize_add_5, usize_add_4, usize_add_3, usize_add_2, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, beq_iff_eq, Bool.and_eq_true, List.cons.injEq, and_true]
  simp only [and_assoc]

/-- The classifier — first byte, length, one unrolled compare — is the
table lookup. -/
theorem keyAt_eq {b : ByteArray} {i : USize} {k r : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r)) :
    keyAt b i (keyEnd b (i + 1) - (i + 1)) = keyOf k := by
  obtain ⟨hstep, hsum⟩ := keyEnd_facts h hk
  obtain ⟨hne0, hkeN, hT1⟩ := keyEnd_of_some h hk
  have hsz := USize.toNat_lt_size b.usize
  have hltN := USize.lt_iff_toNat_lt.mp h
  have happ := naiveKeyBody_append hk
  have hle : (i + 1).toNat ≤ (keyEnd b (i + 1)).toNat := by omega
  have hkl : (keyEnd b (i + 1) - (i + 1)).toNat = k.length := by
    rw [USize.toNat_sub_of_le _ _ hle, hkeN, hstep]
    omega
  cases k with
  | nil =>
    have hb : byteAt b (i + 1) = 34 := by rw [byteAt_eq, happ]; rfl
    unfold keyAt
    rw [hb]
    exact keyOf_nil.symm
  | cons c k' =>
    have hb : byteAt b (i + 1) = c := by rw [byteAt_eq, happ]; rfl
    have hi1lt : i + 1 < b.usize := by
      refine USize.lt_iff_toNat_lt.mpr ?_
      simp only [List.length_cons] at hsum
      omega
    have hT2 : tailAt b (i + 1 + 1) = k' ++ 34 :: r := by
      have hx := tailAt_of_lt hi1lt
      rw [happ] at hx
      injection hx with _ hx2
      exact hx2.symm
    simp only [List.length_cons] at hkl
    unfold keyAt
    rw [hb]
    split
    · -- 'a'
      rw [keyOf_97]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 112 112 k' r hT2 (by simp [hL0]),
          lit2_key b (i + 1 + 1) 114 103 k' r hT2 (by simp [hL0]),
          lit2_key b (i + 1 + 1) 108 108 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [112, 112]
        case pos => subst e0; simp
        by_cases e1 : k' = [114, 103]
        case pos => subst e1; simp
        by_cases e2 : k' = [108, 108]
        case pos => subst e2; simp
        have n3 : ¬ k' = [120, 105, 111, 109] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e2, if_neg e0, if_neg e1, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL1 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 120 105 111 109 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [120, 105, 111, 109]
        case pos => subst e0; simp
        have n0 : ¬ k' = [108, 108] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n1 : ¬ k' = [112, 112] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [114, 103] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      have m0 : ¬ k' = [108, 108] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [112, 112] := by
        intro hx
        exact hL0 (by simp [hx])
      have m2 : ¬ k' = [114, 103] := by
        intro hx
        exact hL0 (by simp [hx])
      have m3 : ¬ k' = [120, 105, 111, 109] := by
        intro hx
        exact hL1 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3]
    · -- 'b'
      rw [keyOf_98]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 111 100 121 k' r hT2 (by simp [hL0]),
          lit3_key b (i + 1 + 1) 118 97 114 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [111, 100, 121]
        case pos => subst e0; simp
        by_cases e1 : k' = [118, 97, 114]
        case pos => subst e1; simp
        have n0 : ¬ k' = [105, 110, 100, 101, 114, 73, 110, 102, 111] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg e0, if_neg e1]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL1 : k'.length = 9
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz10]))]
        simp only [lit9_key b (i + 1 + 1) 105 110 100 101 114 73 110 102 111 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [105, 110, 100, 101, 114, 73, 110, 102, 111]
        case pos => subst e0; simp
        have n1 : ¬ k' = [111, 100, 121] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [118, 97, 114] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg e0, if_neg n1, if_neg n2]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz10]; omega))]
      have m0 : ¬ k' = [105, 110, 100, 101, 114, 73, 110, 102, 111] := by
        intro hx
        exact hL1 (by simp [hx])
      have m1 : ¬ k' = [111, 100, 121] := by
        intro hx
        exact hL0 (by simp [hx])
      have m2 : ¬ k' = [118, 97, 114] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2]
    · -- 'c'
      rw [keyOf_99]
      by_cases hL0 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 111 110 115 116 k' r hT2 (by simp [hL0]),
          lit4_key b (i + 1 + 1) 116 111 114 115 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [111, 110, 115, 116]
        case pos => subst e0; simp
        by_cases e1 : k' = [116, 111, 114, 115]
        case pos => subst e1; simp
        have n0 : ¬ k' = [105, 100, 120] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [116, 111, 114] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg e1]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      by_cases hL1 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 116 111 114 k' r hT2 (by simp [hL1]),
          lit3_key b (i + 1 + 1) 105 100 120 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [116, 111, 114]
        case pos => subst e0; simp
        by_cases e1 : k' = [105, 100, 120]
        case pos => subst e1; simp
        have n1 : ¬ k' = [111, 110, 115, 116] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n3 : ¬ k' = [116, 111, 114, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg e1, if_neg n1, if_neg e0, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      have m0 : ¬ k' = [105, 100, 120] := by
        intro hx
        exact hL1 (by simp [hx])
      have m1 : ¬ k' = [111, 110, 115, 116] := by
        intro hx
        exact hL0 (by simp [hx])
      have m2 : ¬ k' = [116, 111, 114] := by
        intro hx
        exact hL1 (by simp [hx])
      have m3 : ¬ k' = [116, 111, 114, 115] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3]
    · -- 'd'
      rw [keyOf_100]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 101 102 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      have m0 : ¬ k' = [101, 102] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · -- 'f'
      rw [keyOf_102]
      by_cases hL0 : k'.length = 1
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz2]))]
        simp only [lit1_key b (i + 1 + 1) 110 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [110]
        case pos => subst e0; simp
        have n1 : ¬ k' = [111, 114, 97, 108, 108, 69] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e0, if_neg n1]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz2]; omega))]
      by_cases hL1 : k'.length = 6
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz7]))]
        simp only [lit6_key b (i + 1 + 1) 111 114 97 108 108 69 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [111, 114, 97, 108, 108, 69]
        case pos => subst e0; simp
        have n0 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz7]; omega))]
      have m0 : ¬ k' = [110] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [111, 114, 97, 108, 108, 69] := by
        intro hx
        exact hL1 (by simp [hx])
      simp only [if_neg m0, if_neg m1]
    · -- 'h'
      rw [keyOf_104]
      by_cases hL0 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 105 110 116 115 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      have m0 : ¬ k' = [105, 110, 116, 115] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · -- 'i'
      rw [keyOf_105]
      by_cases hL0 : k'.length = 1
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz2]))]
        simp only [lit1_key b (i + 1 + 1) 101 k' r hT2 (by simp [hL0]),
          lit1_key b (i + 1 + 1) 110 k' r hT2 (by simp [hL0]),
          lit1_key b (i + 1 + 1) 108 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [101]
        case pos => subst e0; simp
        by_cases e1 : k' = [110]
        case pos => subst e1; simp
        by_cases e2 : k' = [108]
        case pos => subst e2; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg e2, if_neg n4, if_neg e1, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz2]; omega))]
      by_cases hL1 : k'.length = 0
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz1]))]
        have hnil : k' = [] := List.eq_nil_of_length_eq_zero hL1
        subst hnil
        simp
      rw [if_neg (kl_beq_ne (by rw [hkl, usz1]; omega))]
      by_cases hL2 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 100 120 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [100, 120]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL3 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL3, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 109 97 120 k' r hT2 (by simp [hL3])]
        by_cases e0 : k' = [109, 97, 120]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg e0, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL4 : k'.length = 8
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL4, usz9]))]
        simp only [lit8_key b (i + 1 + 1) 110 100 117 99 116 105 118 101 k' r hT2 (by simp [hL4])]
        by_cases e0 : k' = [110, 100, 117, 99, 116, 105, 118, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg e0, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz9]; omega))]
      by_cases hL5 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL5, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 115 82 101 99 k' r hT2 (by simp [hL5])]
        by_cases e0 : k' = [115, 82, 101, 99]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg e0, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      by_cases hL6 : k'.length = 10
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL6, usz11]))]
        simp only [lit10_key b (i + 1 + 1) 115 82 101 102 108 101 120 105 118 101 k' r hT2 (by simp [hL6])]
        by_cases e0 : k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL6
          simp at hL6
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg e0, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz11]; omega))]
      by_cases hL7 : k'.length = 7
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL7, usz8]))]
        simp only [lit7_key b (i + 1 + 1) 115 85 110 115 97 102 101 k' r hT2 (by simp [hL7])]
        by_cases e0 : k' = [115, 85, 110, 115, 97, 102, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n6 : ¬ k' = [110, 100, 117, 99, 116] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL7
          simp at hL7
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz8]; omega))]
      by_cases hL8 : k'.length = 5
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL8, usz6]))]
        simp only [lit5_key b (i + 1 + 1) 110 100 117 99 116 k' r hT2 (by simp [hL8])]
        by_cases e0 : k' = [110, 100, 117, 99, 116]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n1 : ¬ k' = [100, 120] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n2 : ¬ k' = [101] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n3 : ¬ k' = [108] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n4 : ¬ k' = [109, 97, 120] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n5 : ¬ k' = [110] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n8 : ¬ k' = [115, 82, 101, 99] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        have n10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
          intro hx
          rw [hx] at hL8
          simp at hL8
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg e0,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz6]; omega))]
      have m0 : ¬ k' = [] := by
        intro hx
        exact hL1 (by simp [hx])
      have m1 : ¬ k' = [100, 120] := by
        intro hx
        exact hL2 (by simp [hx])
      have m2 : ¬ k' = [101] := by
        intro hx
        exact hL0 (by simp [hx])
      have m3 : ¬ k' = [108] := by
        intro hx
        exact hL0 (by simp [hx])
      have m4 : ¬ k' = [109, 97, 120] := by
        intro hx
        exact hL3 (by simp [hx])
      have m5 : ¬ k' = [110] := by
        intro hx
        exact hL0 (by simp [hx])
      have m6 : ¬ k' = [110, 100, 117, 99, 116] := by
        intro hx
        exact hL8 (by simp [hx])
      have m7 : ¬ k' = [110, 100, 117, 99, 116, 105, 118, 101] := by
        intro hx
        exact hL4 (by simp [hx])
      have m8 : ¬ k' = [115, 82, 101, 99] := by
        intro hx
        exact hL5 (by simp [hx])
      have m9 : ¬ k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] := by
        intro hx
        exact hL6 (by simp [hx])
      have m10 : ¬ k' = [115, 85, 110, 115, 97, 102, 101] := by
        intro hx
        exact hL7 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3, if_neg m4, if_neg m5, if_neg m6,
        if_neg m7, if_neg m8, if_neg m9, if_neg m10]
    · -- 'k'
      rw [keyOf_107]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 105 110 100 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [105, 110, 100]
        case pos => subst e0; simp
        have n0 : ¬ k' = [] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL1 : k'.length = 0
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz1]))]
        have hnil : k' = [] := List.eq_nil_of_length_eq_zero hL1
        subst hnil
        simp
      rw [if_neg (kl_beq_ne (by rw [hkl, usz1]; omega))]
      have m0 : ¬ k' = [] := by
        intro hx
        exact hL1 (by simp [hx])
      have m1 : ¬ k' = [105, 110, 100] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0, if_neg m1]
    · -- 'l'
      rw [keyOf_108]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 97 109 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [97, 109]
        case pos => subst e0; simp
        have n1 : ¬ k' = [101, 116, 69] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e0, if_neg n1, if_neg n2]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL1 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 101 116 69 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [101, 116, 69]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 109] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg e0, if_neg n2]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL2 : k'.length = 10
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz11]))]
        simp only [lit10_key b (i + 1 + 1) 101 118 101 108 80 97 114 97 109 115 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 109] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n1 : ¬ k' = [101, 116, 69] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg n0, if_neg n1, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz11]; omega))]
      have m0 : ¬ k' = [97, 109] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [101, 116, 69] := by
        intro hx
        exact hL1 (by simp [hx])
      have m2 : ¬ k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] := by
        intro hx
        exact hL2 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2]
    · -- 'm'
      rw [keyOf_109]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 97 120 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [97, 120]
        case pos => subst e0; simp
        have n1 : ¬ k' = [101, 116, 97] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e0, if_neg n1]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL1 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 101 116 97 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [101, 116, 97]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 120] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      have m0 : ¬ k' = [97, 120] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [101, 116, 97] := by
        intro hx
        exact hL1 (by simp [hx])
      simp only [if_neg m0, if_neg m1]
    · -- 'n'
      rw [keyOf_110]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 97 109 101 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [97, 109, 101]
        case pos => subst e0; simp
        have n1 : ¬ k' = [97, 116, 86, 97, 108] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n3 : ¬ k' = [111, 110, 100, 101, 112] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n4 : ¬ k' = [117, 109] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL1 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 117 109 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [117, 109]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 109, 101] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n1 : ¬ k' = [97, 116, 86, 97, 108] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n3 : ¬ k' = [111, 110, 100, 101, 112] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg e0, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL2 : k'.length = 5
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz6]))]
        simp only [lit5_key b (i + 1 + 1) 97 116 86 97 108 k' r hT2 (by simp [hL2]),
          lit5_key b (i + 1 + 1) 111 110 100 101 112 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [97, 116, 86, 97, 108]
        case pos => subst e0; simp
        by_cases e1 : k' = [111, 110, 100, 101, 112]
        case pos => subst e1; simp
        have n0 : ¬ k' = [97, 109, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n4 : ¬ k' = [117, 109] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg e1, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz6]; omega))]
      by_cases hL3 : k'.length = 6
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL3, usz7]))]
        simp only [lit6_key b (i + 1 + 1) 102 105 101 108 100 115 k' r hT2 (by simp [hL3])]
        by_cases e0 : k' = [102, 105, 101, 108, 100, 115]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 109, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n1 : ¬ k' = [97, 116, 86, 97, 108] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n3 : ¬ k' = [111, 110, 100, 101, 112] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n4 : ¬ k' = [117, 109] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
          if_neg n7, if_neg n8, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz7]; omega))]
      by_cases hL4 : k'.length = 8
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL4, usz9]))]
        simp only [lit8_key b (i + 1 + 1) 117 109 80 97 114 97 109 115 k' r hT2 (by simp [hL4]),
          lit8_key b (i + 1 + 1) 117 109 70 105 101 108 100 115 k' r hT2 (by simp [hL4]),
          lit8_key b (i + 1 + 1) 117 109 77 105 110 111 114 115 k' r hT2 (by simp [hL4]),
          lit8_key b (i + 1 + 1) 117 109 78 101 115 116 101 100 k' r hT2 (by simp [hL4])]
        by_cases e0 : k' = [117, 109, 80, 97, 114, 97, 109, 115]
        case pos => subst e0; simp
        by_cases e1 : k' = [117, 109, 70, 105, 101, 108, 100, 115]
        case pos => subst e1; simp
        by_cases e2 : k' = [117, 109, 77, 105, 110, 111, 114, 115]
        case pos => subst e2; simp
        by_cases e3 : k' = [117, 109, 78, 101, 115, 116, 101, 100]
        case pos => subst e3; simp
        have n0 : ¬ k' = [97, 109, 101] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n1 : ¬ k' = [97, 116, 86, 97, 108] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n3 : ¬ k' = [111, 110, 100, 101, 112] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n4 : ¬ k' = [117, 109] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        have n8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
          intro hx
          rw [hx] at hL4
          simp at hL4
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg e1, if_neg n6,
          if_neg e2, if_neg n8, if_neg e3, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz9]; omega))]
      by_cases hL5 : k'.length = 9
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL5, usz10]))]
        simp only [lit9_key b (i + 1 + 1) 117 109 73 110 100 105 99 101 115 k' r hT2 (by simp [hL5]),
          lit9_key b (i + 1 + 1) 117 109 77 111 116 105 118 101 115 k' r hT2 (by simp [hL5])]
        by_cases e0 : k' = [117, 109, 73, 110, 100, 105, 99, 101, 115]
        case pos => subst e0; simp
        by_cases e1 : k' = [117, 109, 77, 111, 116, 105, 118, 101, 115]
        case pos => subst e1; simp
        have n0 : ¬ k' = [97, 109, 101] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n1 : ¬ k' = [97, 116, 86, 97, 108] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n3 : ¬ k' = [111, 110, 100, 101, 112] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n4 : ¬ k' = [117, 109] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        have n10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
          intro hx
          rw [hx] at hL5
          simp at hL5
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg e0,
          if_neg n7, if_neg e1, if_neg n9, if_neg n10]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz10]; omega))]
      have m0 : ¬ k' = [97, 109, 101] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [97, 116, 86, 97, 108] := by
        intro hx
        exact hL2 (by simp [hx])
      have m2 : ¬ k' = [102, 105, 101, 108, 100, 115] := by
        intro hx
        exact hL3 (by simp [hx])
      have m3 : ¬ k' = [111, 110, 100, 101, 112] := by
        intro hx
        exact hL2 (by simp [hx])
      have m4 : ¬ k' = [117, 109] := by
        intro hx
        exact hL1 (by simp [hx])
      have m5 : ¬ k' = [117, 109, 70, 105, 101, 108, 100, 115] := by
        intro hx
        exact hL4 (by simp [hx])
      have m6 : ¬ k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] := by
        intro hx
        exact hL5 (by simp [hx])
      have m7 : ¬ k' = [117, 109, 77, 105, 110, 111, 114, 115] := by
        intro hx
        exact hL4 (by simp [hx])
      have m8 : ¬ k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] := by
        intro hx
        exact hL5 (by simp [hx])
      have m9 : ¬ k' = [117, 109, 78, 101, 115, 116, 101, 100] := by
        intro hx
        exact hL4 (by simp [hx])
      have m10 : ¬ k' = [117, 109, 80, 97, 114, 97, 109, 115] := by
        intro hx
        exact hL4 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3, if_neg m4, if_neg m5, if_neg m6,
        if_neg m7, if_neg m8, if_neg m9, if_neg m10]
    · -- 'o'
      rw [keyOf_111]
      by_cases hL0 : k'.length = 5
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz6]))]
        simp only [lit5_key b (i + 1 + 1) 112 97 113 117 101 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz6]; omega))]
      have m0 : ¬ k' = [112, 97, 113, 117, 101] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · -- 'p'
      rw [keyOf_112]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 114 101 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [114, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 114, 97, 109] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [114, 111, 106] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n3 : ¬ k' = [119] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL1 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 97 114 97 109 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [97, 114, 97, 109]
        case pos => subst e0; simp
        have n1 : ¬ k' = [114, 101] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [114, 111, 106] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n3 : ¬ k' = [119] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg e0, if_neg n1, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      by_cases hL2 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 114 111 106 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [114, 111, 106]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 114, 97, 109] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n1 : ¬ k' = [114, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n3 : ¬ k' = [119] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL3 : k'.length = 1
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL3, usz2]))]
        simp only [lit1_key b (i + 1 + 1) 119 k' r hT2 (by simp [hL3])]
        by_cases e0 : k' = [119]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 114, 97, 109] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n1 : ¬ k' = [114, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n2 : ¬ k' = [114, 111, 106] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz2]; omega))]
      have m0 : ¬ k' = [97, 114, 97, 109] := by
        intro hx
        exact hL1 (by simp [hx])
      have m1 : ¬ k' = [114, 101] := by
        intro hx
        exact hL0 (by simp [hx])
      have m2 : ¬ k' = [114, 111, 106] := by
        intro hx
        exact hL2 (by simp [hx])
      have m3 : ¬ k' = [119] := by
        intro hx
        exact hL3 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3]
    · -- 'q'
      rw [keyOf_113]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 117 111 116 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      have m0 : ¬ k' = [117, 111, 116] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · -- 'r'
      rw [keyOf_114]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 101 99 115 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [101, 99, 115]
        case pos => subst e0; simp
        have n1 : ¬ k' = [101, 103, 117, 108, 97, 114] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [104, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n3 : ¬ k' = [117, 108, 101, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg e0, if_neg n1, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL1 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 117 108 101 115 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [117, 108, 101, 115]
        case pos => subst e0; simp
        have n0 : ¬ k' = [101, 99, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n1 : ¬ k' = [101, 103, 117, 108, 97, 114] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [104, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      by_cases hL2 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 104 115 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [104, 115]
        case pos => subst e0; simp
        have n0 : ¬ k' = [101, 99, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n1 : ¬ k' = [101, 103, 117, 108, 97, 114] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n3 : ¬ k' = [117, 108, 101, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL3 : k'.length = 6
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL3, usz7]))]
        simp only [lit6_key b (i + 1 + 1) 101 103 117 108 97 114 k' r hT2 (by simp [hL3])]
        by_cases e0 : k' = [101, 103, 117, 108, 97, 114]
        case pos => subst e0; simp
        have n0 : ¬ k' = [101, 99, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n2 : ¬ k' = [104, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n3 : ¬ k' = [117, 108, 101, 115] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz7]; omega))]
      have m0 : ¬ k' = [101, 99, 115] := by
        intro hx
        exact hL0 (by simp [hx])
      have m1 : ¬ k' = [101, 103, 117, 108, 97, 114] := by
        intro hx
        exact hL3 (by simp [hx])
      have m2 : ¬ k' = [104, 115] := by
        intro hx
        exact hL2 (by simp [hx])
      have m3 : ¬ k' = [117, 108, 101, 115] := by
        intro hx
        exact hL1 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3]
    · -- 's'
      rw [keyOf_115]
      by_cases hL0 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 116 114 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [116, 114]
        case pos => subst e0; simp
        have n0 : ¬ k' = [97, 102, 101, 116, 121] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n1 : ¬ k' = [111, 114, 116] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n3 : ¬ k' = [116, 114, 86, 97, 108] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n4 : ¬ k' = [116, 114, 117, 99, 116] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n5 : ¬ k' = [117, 99, 99] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg n3, if_neg n4, if_neg n5]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL1 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 111 114 116 k' r hT2 (by simp [hL1]),
          lit3_key b (i + 1 + 1) 117 99 99 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [111, 114, 116]
        case pos => subst e0; simp
        by_cases e1 : k' = [117, 99, 99]
        case pos => subst e1; simp
        have n0 : ¬ k' = [97, 102, 101, 116, 121] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n2 : ¬ k' = [116, 114] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n3 : ¬ k' = [116, 114, 86, 97, 108] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n4 : ¬ k' = [116, 114, 117, 99, 116] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg n3, if_neg n4, if_neg e1]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL2 : k'.length = 5
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz6]))]
        simp only [lit5_key b (i + 1 + 1) 116 114 117 99 116 k' r hT2 (by simp [hL2]),
          lit5_key b (i + 1 + 1) 116 114 86 97 108 k' r hT2 (by simp [hL2]),
          lit5_key b (i + 1 + 1) 97 102 101 116 121 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [116, 114, 117, 99, 116]
        case pos => subst e0; simp
        by_cases e1 : k' = [116, 114, 86, 97, 108]
        case pos => subst e1; simp
        by_cases e2 : k' = [97, 102, 101, 116, 121]
        case pos => subst e2; simp
        have n1 : ¬ k' = [111, 114, 116] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n2 : ¬ k' = [116, 114] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n5 : ¬ k' = [117, 99, 99] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg e2, if_neg n1, if_neg n2, if_neg e1, if_neg e0, if_neg n5]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz6]; omega))]
      have m0 : ¬ k' = [97, 102, 101, 116, 121] := by
        intro hx
        exact hL2 (by simp [hx])
      have m1 : ¬ k' = [111, 114, 116] := by
        intro hx
        exact hL1 (by simp [hx])
      have m2 : ¬ k' = [116, 114] := by
        intro hx
        exact hL0 (by simp [hx])
      have m3 : ¬ k' = [116, 114, 86, 97, 108] := by
        intro hx
        exact hL2 (by simp [hx])
      have m4 : ¬ k' = [116, 114, 117, 99, 116] := by
        intro hx
        exact hL2 (by simp [hx])
      have m5 : ¬ k' = [117, 99, 99] := by
        intro hx
        exact hL1 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3, if_neg m4, if_neg m5]
    · -- 't'
      rw [keyOf_116]
      by_cases hL0 : k'.length = 3
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz4]))]
        simp only [lit3_key b (i + 1 + 1) 121 112 101 k' r hT2 (by simp [hL0])]
        by_cases e0 : k' = [121, 112, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [104, 109] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n2 : ¬ k' = [121, 112, 101, 78, 97, 109, 101] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        have n3 : ¬ k' = [121, 112, 101, 115] := by
          intro hx
          rw [hx] at hL0
          simp at hL0
        simp only [if_neg n0, if_neg e0, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz4]; omega))]
      by_cases hL1 : k'.length = 7
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL1, usz8]))]
        simp only [lit7_key b (i + 1 + 1) 121 112 101 78 97 109 101 k' r hT2 (by simp [hL1])]
        by_cases e0 : k' = [121, 112, 101, 78, 97, 109, 101]
        case pos => subst e0; simp
        have n0 : ¬ k' = [104, 109] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n1 : ¬ k' = [121, 112, 101] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        have n3 : ¬ k' = [121, 112, 101, 115] := by
          intro hx
          rw [hx] at hL1
          simp at hL1
        simp only [if_neg n0, if_neg n1, if_neg e0, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz8]; omega))]
      by_cases hL2 : k'.length = 2
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL2, usz3]))]
        simp only [lit2_key b (i + 1 + 1) 104 109 k' r hT2 (by simp [hL2])]
        by_cases e0 : k' = [104, 109]
        case pos => subst e0; simp
        have n1 : ¬ k' = [121, 112, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n2 : ¬ k' = [121, 112, 101, 78, 97, 109, 101] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        have n3 : ¬ k' = [121, 112, 101, 115] := by
          intro hx
          rw [hx] at hL2
          simp at hL2
        simp only [if_neg e0, if_neg n1, if_neg n2, if_neg n3]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz3]; omega))]
      by_cases hL3 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL3, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 121 112 101 115 k' r hT2 (by simp [hL3])]
        by_cases e0 : k' = [121, 112, 101, 115]
        case pos => subst e0; simp
        have n0 : ¬ k' = [104, 109] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n1 : ¬ k' = [121, 112, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        have n2 : ¬ k' = [121, 112, 101, 78, 97, 109, 101] := by
          intro hx
          rw [hx] at hL3
          simp at hL3
        simp only [if_neg n0, if_neg n1, if_neg n2, if_neg e0]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      have m0 : ¬ k' = [104, 109] := by
        intro hx
        exact hL2 (by simp [hx])
      have m1 : ¬ k' = [121, 112, 101] := by
        intro hx
        exact hL0 (by simp [hx])
      have m2 : ¬ k' = [121, 112, 101, 78, 97, 109, 101] := by
        intro hx
        exact hL1 (by simp [hx])
      have m3 : ¬ k' = [121, 112, 101, 115] := by
        intro hx
        exact hL3 (by simp [hx])
      simp only [if_neg m0, if_neg m1, if_neg m2, if_neg m3]
    · -- 'u'
      rw [keyOf_117]
      by_cases hL0 : k'.length = 1
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz2]))]
        simp only [lit1_key b (i + 1 + 1) 115 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz2]; omega))]
      have m0 : ¬ k' = [115] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · -- 'v'
      rw [keyOf_118]
      by_cases hL0 : k'.length = 4
      case pos =>
        rw [if_pos (kl_beq (by rw [hkl, hL0, usz5]))]
        simp only [lit4_key b (i + 1 + 1) 97 108 117 101 k' r hT2 (by simp [hL0])]
      rw [if_neg (kl_beq_ne (by rw [hkl, usz5]; omega))]
      have m0 : ¬ k' = [97, 108, 117, 101] := by
        intro hx
        exact hL0 (by simp [hx])
      simp only [if_neg m0]
    · rename_i _ e97 e98 e99 e100 e102 e104 e105 e107 e108 e109 e110 e111 e112 e113 e114 e115
         e116 e117 e118
      have f97 : ((97 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e97 hx.symm
      have f98 : ((98 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e98 hx.symm
      have f99 : ((99 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e99 hx.symm
      have f100 : ((100 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e100 hx.symm
      have f102 : ((102 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e102 hx.symm
      have f104 : ((104 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e104 hx.symm
      have f105 : ((105 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e105 hx.symm
      have f107 : ((107 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e107 hx.symm
      have f108 : ((108 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e108 hx.symm
      have f109 : ((109 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e109 hx.symm
      have f110 : ((110 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e110 hx.symm
      have f111 : ((111 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e111 hx.symm
      have f112 : ((112 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e112 hx.symm
      have f113 : ((113 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e113 hx.symm
      have f114 : ((114 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e114 hx.symm
      have f115 : ((115 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e115 hx.symm
      have f116 : ((116 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e116 hx.symm
      have f117 : ((117 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e117 hx.symm
      have f118 : ((118 : UInt8) == c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => e118 hx.symm
      have hu : keyOf (c :: k') = Key.kUnknown := by
        unfold keyOf keyTable
        simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo,
          lit_body, lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn,
          lit_forallE, lit_hints, lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct,
          lit_inductive, lit_isRec, lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam,
          lit_letE, lit_levelParams, lit_max, lit_meta, lit_name, lit_natVal, lit_nfields,
          lit_nondep, lit_num, lit_numFields, lit_numIndices, lit_numMinors, lit_numMotives,
          lit_numNested, lit_numParams, lit_opaque, lit_param, lit_pre, lit_proj, lit_pw,
          lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules, lit_safety, lit_sort, lit_str,
          lit_strVal, lit_struct, lit_succ, lit_thm, lit_type, lit_typeName, lit_types, lit_us,
          lit_value]
        simp [f97, f98, f99, f100, f102, f104, f105, f107, f108, f109, f110, f111, f112, f113,
          f114, f115, f116, f117, f118]
      rw [hu]

end KeyTable

/-- A later tail is a suffix of an earlier one. -/
theorem tailAt_suffix {b : ByteArray} {i j : USize} (h : i.toNat ≤ j.toNat) :
    tailAt b j <:+ tailAt b i := by
  have hd : tailAt b j = (tailAt b i).drop (j.toNat - i.toNat) := by
    simp only [tailAt, List.drop_drop]
    congr 1
    omega
  rw [hd]
  exact List.drop_suffix _ _

/-- The position of a suffix of the tail, counted from the end. -/
theorem posAt_tailAt {b : ByteArray} {j : USize} {rest : List UInt8}
    (hj : j.toNat ≤ b.usize.toNat) (hr : rest <:+ tailAt b j) :
    posAt j.toNat (tailAt b j) rest = b.usize.toNat - rest.length := by
  have := hr.length_le
  simp only [posAt, length_tailAt] at *
  omega

theorem le_posAt (j : Nat) (l rest : List UInt8) : j ≤ posAt j l rest := Nat.le_add_right _ _

/-- The step past the key's closing quote: the rest after it is `r1`,
which sits at a position past `i`. -/
theorem keyEnd_succ_facts {b : ByteArray} {i : USize} {k r1 : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r1)) :
    (keyEnd b (i + 1) + 1).toNat = i.toNat + 1 + k.length + 1 ∧
      i.toNat ≤ (keyEnd b (i + 1) + 1).toNat ∧
      (keyEnd b (i + 1) + 1).toNat ≤ b.usize.toNat := by
  obtain ⟨_, hsum⟩ := keyEnd_facts h hk
  obtain ⟨_, hken, _⟩ := keyEnd_of_some h hk
  have hsz := USize.toNat_lt_size b.usize
  have hstep2 : (keyEnd b (i + 1) + 1).toNat = i.toNat + 1 + k.length + 1 := by
    rw [usize_step_of_lt (by omega), hken]
  exact ⟨hstep2, by omega, by omega⟩

theorem naiveValue_eq (l : List UInt8) :
    naiveValue l = match l.dropWhile isWs with
      | 58 :: r => some (r.dropWhile isWs)
      | _ => none := rfl

theorem valueAt_eq {b : ByteArray} {i : USize} {k r1 : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r1)) :
    valueAt b i (keyEnd b (i + 1)) = match naiveValue r1 with
      | none => i
      | some lv => (posAt i.toNat (tailAt b i) lv).toUSize := by
  obtain ⟨_, _, hT1⟩ := keyEnd_of_some h hk
  obtain ⟨_, hij, hjb⟩ := keyEnd_succ_facts h hk
  have hiu : i.toNat ≤ b.usize.toNat := Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
  have hwsuf : (r1.dropWhile isWs) <:+ tailAt b (keyEnd b (i + 1) + 1) := by
    rw [hT1]; exact List.dropWhile_suffix _
  have hp : skipWs b (keyEnd b (i + 1) + 1)
      = (posAt (keyEnd b (i + 1) + 1).toNat (tailAt b (keyEnd b (i + 1) + 1))
          (r1.dropWhile isWs)).toUSize := by
    rw [skipWs_eq, hT1]
  have hpT : tailAt b (skipWs b (keyEnd b (i + 1) + 1)) = r1.dropWhile isWs := by
    rw [hp]
    exact tailAt_posAt (by simp only [length_bytes]; exact hjb) hwsuf
  have hpN : (skipWs b (keyEnd b (i + 1) + 1)).toNat
      = posAt (keyEnd b (i + 1) + 1).toNat (tailAt b (keyEnd b (i + 1) + 1))
          (r1.dropWhile isWs) := by
    rw [hp]
    exact toNat_toUSize_posAt (by simp only [length_bytes]; exact hjb) hwsuf
  have hpge : (keyEnd b (i + 1) + 1).toNat ≤ (skipWs b (keyEnd b (i + 1) + 1)).toNat := by
    rw [hpN]; simp only [posAt]; omega
  simp only [valueAt]
  rw [byteAt_eq, hpT]
  cases hws : r1.dropWhile isWs with
  | nil =>
    have hnv : naiveValue r1 = none := by rw [naiveValue_eq, hws]
    rw [hnv]
    simp only [List.headD_nil, beq_iff_eq]
    rw [if_neg (by decide)]
  | cons c r' =>
    by_cases hc : c = 58
    · subst hc
      have hnv : naiveValue r1 = some (r'.dropWhile isWs) := by
        rw [naiveValue_eq, hws]
        rfl
      have hplt : skipWs b (keyEnd b (i + 1) + 1) < b.usize := by
        refine lt_usize_of_byteAt_ne_zero (b := b) (p := skipWs b (keyEnd b (i + 1) + 1)) ?_
        rw [byteAt_eq, hpT, hws]
        simp
      have hT2 : tailAt b (skipWs b (keyEnd b (i + 1) + 1) + 1) = r' := by
        have hx := tailAt_of_lt hplt
        rw [hpT, hws] at hx
        simp only [List.cons.injEq] at hx
        exact hx.2.symm
      have hpltN := USize.lt_iff_toNat_lt.mp hplt
      have hstep1 : (skipWs b (keyEnd b (i + 1) + 1) + 1).toNat
          = (skipWs b (keyEnd b (i + 1) + 1)).toNat + 1 :=
        usize_step_of_lt (by have := USize.toNat_lt_size b.usize; omega)
      have hsuf' : (r'.dropWhile isWs) <:+ tailAt b (skipWs b (keyEnd b (i + 1) + 1) + 1) := by
        rw [hT2]; exact List.dropWhile_suffix _
      have hb1 : (skipWs b (keyEnd b (i + 1) + 1) + 1).toNat ≤ b.usize.toNat := by
        rw [hstep1]; omega
      have hcalc := posAt_tailAt hb1 hsuf'
      rw [hT2] at hcalc
      have hlvi : (r'.dropWhile isWs) <:+ tailAt b i := by
        refine (List.dropWhile_suffix (l := r') isWs).trans ?_
        rw [← hT2]
        exact tailAt_suffix (by rw [hstep1]; omega)
      rw [hnv]
      simp only [List.headD_cons, beq_iff_eq, ↓reduceIte]
      rw [skipWs_eq, hT2, hcalc, posAt_tailAt hiu hlvi]
    · have hnv : naiveValue r1 = none := by
        rw [naiveValue_eq, hws]
        split
        · next r heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 hc
        · rfl
      rw [hnv]
      simp only [List.headD_cons, beq_iff_eq, hc, ↓reduceIte]

/-- A value's input is a proper suffix of the member's: the key's quote
and the colon were consumed. -/
theorem naiveValue_of_key {b : ByteArray} {i : USize} {k r1 lv : List UInt8} (h : i < b.usize)
    (hk : naiveKeyBody (tailAt b (i + 1)) = some (k, r1)) (hv : naiveValue r1 = some lv) :
    lv <:+ tailAt b i ∧ lv.length < (tailAt b i).length := by
  obtain ⟨_, _, hT1⟩ := keyEnd_of_some h hk
  obtain ⟨hjN, hij, hjb⟩ := keyEnd_succ_facts h hk
  have hlt := USize.lt_iff_toNat_lt.mp h
  have hsuf : lv <:+ tailAt b i := by
    refine ((naiveValue_rest_suffix hv).trans ?_).trans (tailAt_suffix hij)
    rw [hT1]
    exact List.suffix_rfl
  refine ⟨hsuf, ?_⟩
  have hlen : lv.length ≤ r1.length := (naiveValue_rest_suffix hv).length_le
  have hr1 : r1.length = b.usize.toNat - (i.toNat + 1 + k.length + 1) := by
    rw [← hT1, length_tailAt, hjN]
  simp only [length_tailAt]
  omega

/-! ## Suffix lemmas of the generic loops -/

theorem Slot.of_read_rest (mask : UInt32) (scan : List UInt8 → NRes α) (set : α → σ → σ)
    (l : List UInt8) (st : σ) : ((Slot.of mask scan set).read l st).rest = (scan l).rest := by
  simp only [Slot.of]
  cases scan l <;> rfl

theorem naiveListLoop_rest_suffix (start : UInt8 → Bool) (item : List UInt8 → NRes α)
    (hitem : ∀ l, (item l).rest <:+ l) (l : List UInt8) (acc : List α) (w : Bool) :
    (naiveListLoop start item l acc w).rest <:+ l := by
  induction l, acc, w using naiveListLoop.induct start item with
  | case1 acc w => rw [naiveListLoop.eq_1]; exact List.suffix_rfl
  | case2 c l' acc w hws ih =>
    rw [naiveListLoop.eq_2]
    simp only [hws, ↓reduceIte]
    exact ih.trans (List.suffix_cons _ _)
  | case3 c l' acc w hws h93 hwa =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, hwa, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case4 c l' acc w hws h93 hwa =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, hwa, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_cons _ _
  | case5 c l' acc hws h93 h44 =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case6 c l' acc w hws h93 h44 hw ih =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hw, ↓reduceIte, Bool.false_eq_true]
    exact ih.trans (List.suffix_cons _ _)
  | case7 c l' acc w hws h93 h44 hst hw =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hst, hw, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case8 c l' acc w hws h93 h44 hst hw t r hi =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hst, hw, hi, ↓reduceIte, Bool.false_eq_true]
    have := hitem (c :: l')
    rw [hi] at this
    exact this
  | case9 c l' acc w hws h93 h44 hst hw x rest hi hlt ih =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hst, hw, hi, hlt, ↓reduceIte, Bool.false_eq_true, dif_pos]
    have hr := hitem (c :: l')
    rw [hi] at hr
    exact ih.trans hr
  | case10 c l' acc w hws h93 h44 hst hw x rest hi hlt =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hst, hw, hi, hlt, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case11 c l' acc w hws h93 h44 hst =>
    rw [naiveListLoop.eq_2]
    simp only [hws, h93, h44, hst, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl

theorem naiveList_rest_suffix (start : UInt8 → Bool) (item : List UInt8 → NRes α)
    (hitem : ∀ l, (item l).rest <:+ l) (l : List UInt8) :
    (naiveList start item l).rest <:+ l := by
  unfold naiveList
  split
  · next l' =>
    exact (naiveListLoop_rest_suffix start item hitem l' [] true).trans (List.suffix_cons _ _)
  · exact List.suffix_rfl

theorem naiveNatList_rest_suffix (l : List UInt8) : (naiveNatList l).rest <:+ l :=
  naiveList_rest_suffix isDigit naiveNat naiveNat_rest_suffix l

theorem naivePw_rest_suffix (l : List UInt8) : (naivePw l).rest <:+ l := by
  unfold naivePw
  split
  · next l' =>
    rw [NRes.rest_map]
    exact (naiveListLoop_rest_suffix isDigit naiveNat naiveNat_rest_suffix l' [] true).trans
      (List.suffix_cons _ _)
  · next l' =>
    split
    · next r hr => exact (naiveLit_rest_suffix hr).trans (List.suffix_cons _ _)
    · exact List.suffix_rfl
  · exact List.suffix_rfl

theorem naiveHints_rest_suffix (l : List UInt8) : (naiveHints l).rest <:+ l := by
  unfold naiveHints
  split
  · next l' =>
    split
    · next r hr => exact (naiveLit_rest_suffix hr).trans (List.suffix_cons _ _)
    · split
      · next r hr => exact (naiveLit_rest_suffix hr).trans (List.suffix_cons _ _)
      · exact List.suffix_rfl
  · next l' =>
    have hp : l'.dropWhile isWs <:+ (123 : UInt8) :: l' :=
      (List.dropWhile_suffix _).trans (List.suffix_cons _ _)
    split
    · next p' hd =>
      rw [hd] at hp
      split
      · exact hp
      · next key r1 hkb =>
        split
        · split
          · exact hp
          · next lv hlv =>
            have hlv' : lv <:+ (123 : UInt8) :: l' :=
              ((naiveValue_rest_suffix hlv).trans
                ((naiveKeyBody_rest_suffix hkb).trans (List.suffix_cons _ _))).trans hp
            split
            · exact hlv'
            · next n r2 hnum =>
              have hr2 : r2 <:+ (123 : UInt8) :: l' := (naiveNum_rest_suffix hnum).trans hlv'
              split
              · next rest hq =>
                have := (List.dropWhile_suffix (l := r2) isWs).trans hr2
                rw [hq] at this
                exact (List.suffix_cons _ _).trans this
              · exact (List.dropWhile_suffix (l := r2) isWs).trans hr2
        · exact hp
    · exact List.suffix_rfl
  · exact List.suffix_rfl

theorem naiveSkipBraced_rest_suffix {l r : List UInt8} {d : Nat}
    (h : naiveSkipBraced l d = some r) : r <:+ l := by
  induction l, d using naiveSkipBraced.induct generalizing r with
  | case1 d => rw [naiveSkipBraced.eq_def] at h; simp at h
  | case2 c l' d hc hsb =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, ↓reduceIte, hsb, reduceCtorEq] at h
  | case3 c l' d hc body rest hsb hlt ih =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, ↓reduceIte, hsb, hlt, dif_pos] at h
    exact (ih h).trans ((naiveStrBody_rest_suffix hsb).trans (List.suffix_cons _ _))
  | case4 c l' d hc body rest hsb hlt =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, ↓reduceIte, hsb, dif_neg hlt, reduceCtorEq] at h
  | case5 c l' d hc hbr ih =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, hbr, ↓reduceIte, Bool.false_eq_true] at h
    exact (ih h).trans (List.suffix_cons _ _)
  | case6 c l' hc hbr hcl =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, hbr, hcl, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at h
    rw [← h]
    exact List.suffix_cons _ _
  | case7 c l' hc hbr hcl d ih =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, hbr, hcl, ↓reduceIte, Bool.false_eq_true] at h
    exact (ih h).trans (List.suffix_cons _ _)
  | case8 c l' d hc hbr hcl ih =>
    rw [naiveSkipBraced.eq_def] at h
    simp only [hc, hbr, hcl, ↓reduceIte, Bool.false_eq_true] at h
    exact (ih h).trans (List.suffix_cons _ _)

theorem naiveObjLoop_rest_suffix (fields : Key → Option (Slot σ)) (required : UInt32)
    (hf : ∀ k slot, fields k = some slot → ∀ l st, (slot.read l st).rest <:+ l)
    (l : List UInt8) (w : Bool) (seen : UInt32) (st : σ) :
    (naiveObjLoop fields required l w seen st).rest <:+ l := by
  induction l, w, seen, st using naiveObjLoop.induct fields required with
  | case1 w seen st => rw [naiveObjLoop.eq_1]; exact List.suffix_rfl
  | case2 c l' w seen st hws ih =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, ↓reduceIte]
    exact ih.trans (List.suffix_cons _ _)
  | case3 c l' w seen st hws h125 hc =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, hc, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case4 c l' w seen st hws h125 hc hreq =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, hc, hreq, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case5 c l' w seen st hws h125 hc hreq =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, hc, hreq, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_cons _ _
  | case6 c l' seen st hws h125 h44 =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case7 c l' w seen st hws h125 h44 hw ih =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, hw, ↓reduceIte, Bool.false_eq_true]
    exact ih.trans (List.suffix_cons _ _)
  | case8 c l' w seen st hws h125 h44 h34 hw =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case9 c l' w seen st hws h125 h44 h34 hw hkb =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case10 c l' w seen st hws h125 h44 h34 hw key r1 hkb hv =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case11 c l' w seen st hws h125 h44 h34 hw key r1 hkb lv hv hfk =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, hfk, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case12 c l' w seen st hws h125 h44 h34 hw key r1 hkb lv hv slot hfk hdup =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, hfk, hdup, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl
  | case13 c l' w seen st hws h125 h44 h34 hw key r1 hkb lv hv slot hfk hdup t rr hread =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, hfk, hdup, hread, ↓reduceIte,
      Bool.false_eq_true]
    have hlv : lv <:+ c :: l' :=
      (naiveValue_rest_suffix hv).trans
        ((naiveKeyBody_rest_suffix hkb).trans (List.suffix_cons _ _))
    have hr := hf _ _ hfk lv st
    rw [hread] at hr
    exact hr.trans hlv
  | case14 c l' w seen st hws h125 h44 h34 hw key r1 hkb lv hv slot hfk hdup x rest hread hlt ih =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, hfk, hdup, hread, hlt, ↓reduceIte,
      Bool.false_eq_true, dif_pos]
    have hlv : lv <:+ c :: l' :=
      (naiveValue_rest_suffix hv).trans
        ((naiveKeyBody_rest_suffix hkb).trans (List.suffix_cons _ _))
    have hr := hf _ _ hfk lv st
    rw [hread] at hr
    exact ih.trans (hr.trans hlv)
  | case15 c l' w seen st hws h125 h44 h34 hw key r1 hkb lv hv slot hfk hdup x rest hread hlt =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, hw, hkb, hv, hfk, hdup, hread, dif_neg hlt, ↓reduceIte,
      Bool.false_eq_true]
    exact List.suffix_rfl
  | case16 c l' w seen st hws h125 h44 h34 =>
    rw [naiveObjLoop.eq_2]
    simp only [hws, h125, h44, h34, ↓reduceIte, Bool.false_eq_true]
    exact List.suffix_rfl

theorem naiveObject_rest_suffix (fields : Key → Option (Slot σ)) (required : UInt32)
    (hf : ∀ k slot, fields k = some slot → ∀ l st, (slot.read l st).rest <:+ l)
    (init : σ) (finish : σ → α) (l : List UInt8) :
    (naiveObject fields required init finish l).rest <:+ l := by
  unfold naiveObject
  split
  · next l' =>
    rw [NRes.rest_map]
    exact (naiveObjLoop_rest_suffix fields required hf l' true 0 init).trans
      (List.suffix_cons _ _)
  · exact List.suffix_rfl

/-! ## Lists -/

/-- One step of a loop: a result whose rest lies at or after `i + 1`
lifts the same at `i`. -/
theorem liftRes_step {b : ByteArray} {i : USize} (r : NRes α) (h : i < b.usize)
    (hr : r.rest <:+ tailAt b (i + 1)) : liftRes b i r = liftRes b (i + 1) r := by
  have hstep := usizeStep b i h
  have hlt := USize.lt_iff_toNat_lt.mp h
  exact liftRes_shift r (by omega) (by simp only [length_bytes]; omega) hr

/-- A jump to a later position inside the array. -/
theorem liftRes_jump {b : ByteArray} {i e : USize} (r : NRes α) (hie : i.toNat ≤ e.toNat)
    (he : e.toNat ≤ b.usize.toNat) (hr : r.rest <:+ tailAt b e) :
    liftRes b i r = liftRes b e r :=
  liftRes_shift r hie (by simp only [length_bytes]; exact he) hr

/-- The `.ok` that consumed exactly the byte at `i`. -/
theorem liftRes_ok_step {b : ByteArray} {i : USize} {v : α} (h : i < b.usize) :
    liftRes b i (.ok v (tailAt b (i + 1))) = .ok v (i + 1) := by
  have hT := tailAt_of_lt h
  have h1 : tailAt b (i + 1) = (tailAt b i).drop 1 := by rw [hT]; rfl
  have hlen : 1 ≤ (tailAt b i).length := by rw [hT]; simp
  rw [h1, liftRes_ok_drop hlen]
  rfl

theorem naiveNat_of_none {l : List UInt8} (h : naiveNum l = none) :
    naiveNat l = .err .expectedNat l := by
  unfold naiveNat; rw [h]

theorem naiveNat_of_some {l : List UInt8} {n : Nat} {r : List UInt8}
    (h : naiveNum l = some (n, r)) : naiveNat l = .ok n r := by
  unfold naiveNat; rw [h]

theorem scanNatListLoop_eq (b : ByteArray) (i : USize) (acc : List Nat) (w : Bool) :
    scanNatListLoop b i acc w = liftRes b i (naiveListLoop isDigit naiveNat (tailAt b i) acc w) := by
  fun_induction scanNatListLoop b i acc w with
  | case1 i acc w h c hws ih =>
    have hws' : isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = naiveListLoop isDigit naiveNat (tailAt b (i + 1)) acc w := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', ↓reduceIte]
    rw [hnl, ih, liftRes_step _ h (naiveListLoop_rest_suffix _ _ naiveNat_rest_suffix _ _ _)]
  | case2 i acc w h c hws h93 hwa =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .expectedList (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', hwa, ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h]
    rw [hnl, liftRes_err_self]
  | case3 i acc w h c hws h93 hwa =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .ok acc.reverse (tailAt b (i + 1)) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', hwa, ↓reduceIte, Bool.false_eq_true]
    rw [hnl, liftRes_ok_step h]
  | case4 i acc h c hws h93 h44 =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc true
        = .err .expectedList (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h]
    rw [hnl, liftRes_err_self]
  | case5 i acc w h c hws h93 h44 hw ih =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = naiveListLoop isDigit naiveNat (tailAt b (i + 1)) acc true := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hw, ↓reduceIte, Bool.false_eq_true]
    rw [hnl, ih, liftRes_step _ h (naiveListLoop_rest_suffix _ _ naiveNat_rest_suffix _ _ _)]
  | case6 i acc w h c hws h93 h44 hdig hw =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : ¬ (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hdig' : isDigit (b.uget i (usizeInBounds b i h)) = true := hdig
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .expectedList (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hdig', hw, ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h]
    rw [hnl, liftRes_err_self]
  | case7 i acc w h c hws h93 h44 hdig hw e he =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : ¬ (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hdig' : isDigit (b.uget i (usizeInBounds b i h)) = true := hdig
    have he' : numEnd b i = i := by
      have : (numEnd b i == i) = true := he
      simpa using this
    have hnum : naiveNum (tailAt b i) = none := (numEnd_eq_self_iff b i).mp he'
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .expectedNat (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hdig', hw, ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h, naiveNat_of_none hnum]
    rw [hnl, liftRes_err_self]
  | case8 i acc w h c hws h93 h44 hdig hw e he hlt ih =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : ¬ (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hdig' : isDigit (b.uget i (usizeInBounds b i h)) = true := hdig
    have he' : ¬ numEnd b i = i := by
      have : ¬ (numEnd b i == i) = true := he
      simpa using this
    obtain ⟨n, r, hnum⟩ : ∃ n r, naiveNum (tailAt b i) = some (n, r) := by
      cases hx : naiveNum (tailAt b i) with
      | none => exact absurd ((numEnd_eq_self_iff b i).mpr hx) he'
      | some p => obtain ⟨n, r⟩ := p; exact ⟨n, r, rfl⟩
    obtain ⟨hpos, hval⟩ := numEnd_of_some hnum
    have hsuf : r <:+ tailAt b i := naiveNum_rest_suffix hnum
    have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
    have hguard : r.length < (tailAt b i).length := by
      rw [← lt_posAt_iff hi hsuf, ← hpos]; exact hlt
    have hte : tailAt b e = r := by
      show tailAt b (numEnd b i) = r
      rw [hpos]; exact tailAt_posAt (Nat.le_of_lt hi) hsuf
    have hen : e.toNat ≤ b.usize.toNat := by
      show (numEnd b i).toNat ≤ b.usize.toNat
      rw [hpos, toNat_toUSize_posAt (Nat.le_of_lt hi) hsuf]
      have := posAt_le (Nat.le_of_lt hi) hsuf
      simpa only [length_bytes] using this
    have hie : i.toNat ≤ e.toNat :=
      Nat.le_of_lt (USize.lt_iff_toNat_lt.mp (show i < numEnd b i from hlt))
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = naiveListLoop isDigit naiveNat r (n :: acc) false := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hdig', hw, ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h, naiveNat_of_some hnum]
      simp only [hguard, ↓reduceDIte]
    have hval' : readNatAt b i e = n := hval
    have hr : (naiveListLoop isDigit naiveNat r (n :: acc) false).rest <:+ tailAt b e := by
      rw [hte]; exact naiveListLoop_rest_suffix _ _ naiveNat_rest_suffix _ _ _
    rw [hnl, ih, hte, hval']
    exact (liftRes_jump _ hie hen hr).symm
  | case9 i acc w h c hws h93 h44 hdig hw e he hlt =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : ¬ (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hdig' : isDigit (b.uget i (usizeInBounds b i h)) = true := hdig
    have he' : ¬ numEnd b i = i := by
      have : ¬ (numEnd b i == i) = true := he
      simpa using this
    obtain ⟨n, r, hnum⟩ : ∃ n r, naiveNum (tailAt b i) = some (n, r) := by
      cases hx : naiveNum (tailAt b i) with
      | none => exact absurd ((numEnd_eq_self_iff b i).mpr hx) he'
      | some p => obtain ⟨n, r⟩ := p; exact ⟨n, r, rfl⟩
    obtain ⟨hpos, _⟩ := numEnd_of_some hnum
    have hsuf : r <:+ tailAt b i := naiveNum_rest_suffix hnum
    have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
    have hguard : ¬ r.length < (tailAt b i).length := by
      rw [← lt_posAt_iff hi hsuf, ← hpos]; exact hlt
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .noProgress (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hdig', hw, ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h, naiveNat_of_some hnum]
      simp only [hguard, ↓reduceDIte]
    rw [hnl, liftRes_err_self]
  | case10 i acc w h c hws h93 h44 hdig =>
    have hws' : ¬ isWs (b.uget i (usizeInBounds b i h)) = true := hws
    have h93' : ¬ (b.uget i (usizeInBounds b i h) == 93) = true := h93
    have h44' : ¬ (b.uget i (usizeInBounds b i h) == 44) = true := h44
    have hdig' : ¬ isDigit (b.uget i (usizeInBounds b i h)) = true := hdig
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .expectedList (tailAt b i) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveListLoop.eq_2]
      simp only [hws', h93', h44', hdig', ↓reduceIte, Bool.false_eq_true]
      rw [← tailAt_of_lt h]
    rw [hnl, liftRes_err_self]
  | case11 i acc w h =>
    have hnl : naiveListLoop isDigit naiveNat (tailAt b i) acc w
        = .err .expectedList (tailAt b i) := by
      rw [tailAt_of_not_lt h, naiveListLoop.eq_1]
    rw [hnl, liftRes_err_self]

theorem naiveList_cons_91 (start : UInt8 → Bool) (item : List UInt8 → NRes α)
    (l' : List UInt8) : naiveList start item (91 :: l') = naiveListLoop start item l' [] true :=
  rfl

theorem naiveList_of_ne (start : UInt8 → Bool) (item : List UInt8 → NRes α) {l : List UInt8}
    (h : ¬ l.headD 0 = 91) : naiveList start item l = .err .expectedList l := by
  unfold naiveList
  split
  · next l' => exact absurd rfl h
  · rfl

theorem scanNatList_eq (b : ByteArray) (i : USize) :
    scanNatList b i = liftRes b i (naiveNatList (tailAt b i)) := by
  unfold scanNatList naiveNatList
  rw [byteAt_eq]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    by_cases hc : b.uget i (usizeInBounds b i hlt) = 91
    · have hT91 : tailAt b i = 91 :: tailAt b (i + 1) := by rw [hT, hc]
      rw [hT91, naiveList_cons_91, scanNatListLoop_eq,
        liftRes_step _ hlt (naiveListLoop_rest_suffix _ _ naiveNat_rest_suffix _ _ _)]
      simp only [List.headD_cons, beq_self_eq_true, ↓reduceIte]
    · have hhd : ¬ (tailAt b i).headD 0 = 91 := by rw [hT]; exact hc
      rw [naiveList_of_ne _ _ hhd, liftRes_err_self]
      simp only [hhd, ↓reduceIte, beq_iff_eq]
  · have hhd : ¬ (tailAt b i).headD 0 = 91 := by rw [tailAt_of_not_lt hlt]; simp
    rw [naiveList_of_ne _ _ hhd, liftRes_err_self]
    simp only [hhd, ↓reduceIte, beq_iff_eq]

/-! ## The two variant-valued fields -/

/-- The position a tail stands at, seen from an earlier index. -/
theorem posAt_tailAt_self {b : ByteArray} {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ b.usize.toNat) : posAt i.toNat (tailAt b i) (tailAt b j) = j.toNat := by
  simp only [posAt, length_tailAt]
  omega

theorem liftRes_err_at {α : Type} {b : ByteArray} {i j : USize} {t : ErrTag}
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ b.usize.toNat) :
    liftRes b i (.err t (tailAt b j) : NRes α) = .err ⟨j.toNat, t⟩ := by
  simp only [liftRes]
  rw [posAt_tailAt_self hij hj]

theorem liftRes_ok_at {b : ByteArray} {i j : USize} {v : α}
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ b.usize.toNat) :
    liftRes b i (.ok v (tailAt b j)) = .ok v j := by
  simp only [liftRes]
  rw [posAt_tailAt_self hij hj]
  exact congrArg (ScanRes.ok v) USize.ofNat_toNat

theorem length_lit_never : (lit "never\"").length = 6 := by rw [lit_eq_toByteArray]; rfl
theorem length_lit_abbrev : (lit "abbrev\"").length = 7 := by rw [lit_eq_toByteArray]; rfl
theorem length_lit_opaque : (lit "opaque\"").length = 7 := by rw [lit_eq_toByteArray]; rfl

theorem naivePw_of_ne {l : List UInt8} (h1 : ¬ l.headD 0 = 91) (h2 : ¬ l.headD 0 = 34) :
    naivePw l = .err .badPw l := by
  unfold naivePw
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl

theorem naivePw_cons_91 (l' : List UInt8) :
    naivePw (91 :: l') = (naiveListLoop isDigit naiveNat l' [] true).map .ifAllZero := rfl

theorem naivePw_cons_34 (l' : List UInt8) :
    naivePw (34 :: l') = match naiveLit "never\"" l' with
      | some r => .ok .never r
      | none => .err .badPw (34 :: l') := rfl

theorem scanPw_eq (b : ByteArray) (i : USize) :
    scanPw b i = liftRes b i (naivePw (tailAt b i)) := by
  unfold scanPw
  rw [byteAt_eq]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    have hhead : (tailAt b i).headD 0 = b.uget i (usizeInBounds b i hlt) := by rw [hT]; rfl
    rw [hhead]
    by_cases h91 : b.uget i (usizeInBounds b i hlt) = 91
    · have hT91 : tailAt b i = 91 :: tailAt b (i + 1) := by rw [hT, h91]
      have hsuf : ((naiveListLoop isDigit naiveNat (tailAt b (i + 1)) [] true).map
          PwRec.ifAllZero).rest <:+ tailAt b (i + 1) := by
        rw [NRes.rest_map]
        exact naiveListLoop_rest_suffix _ _ naiveNat_rest_suffix _ _ _
      rw [hT91, naivePw_cons_91, liftRes_step _ hlt hsuf, scanNatListLoop_eq]
      simp only [h91, beq_self_eq_true, ↓reduceIte]
      cases naiveListLoop isDigit naiveNat (tailAt b (i + 1)) [] true <;> rfl
    · by_cases h34 : b.uget i (usizeInBounds b i hlt) = 34
      · have hT34 : tailAt b i = 34 :: tailAt b (i + 1) := by rw [hT, h34]
        rw [hT34, naivePw_cons_34, ← hT34,
          matchLit_lit b (i + 1) "never\"" (size_toUTF8_lt "never\"" 6 rfl (by decide))]
        unfold naiveLit
        rw [if_neg (by simpa using h91), if_pos (by simpa using h34)]
        by_cases hpre : (lit "never\"").isPrefixOf (tailAt b (i + 1)) = true
        · have hlen6 : 6 ≤ (tailAt b (i + 1)).length := by
            have hp := (List.isPrefixOf_iff_prefix.mp hpre).length_le
            rwa [length_lit_never] at hp
          have hdrop : (tailAt b (i + 1)).drop (lit "never\"").length = (tailAt b i).drop 7 := by
            rw [hT34, length_lit_never]; rfl
          have hlen7 : 7 ≤ (tailAt b i).length := by
            rw [hT34]; simp only [List.length_cons]; omega
          simp only [hpre, ↓reduceIte]
          rw [hdrop, liftRes_ok_drop hlen7]
          rfl
        · simp only [hpre, Bool.false_eq_true, ↓reduceIte, liftRes_err_self]
      · have hh1 : ¬ (tailAt b i).headD 0 = 91 := by rw [hhead]; exact h91
        have hh2 : ¬ (tailAt b i).headD 0 = 34 := by rw [hhead]; exact h34
        rw [naivePw_of_ne hh1 hh2, liftRes_err_self]
        simp only [beq_iff_eq, h91, h34, ↓reduceIte]
  · have hnil := tailAt_of_not_lt hlt
    have hh1 : ¬ (tailAt b i).headD 0 = 91 := by rw [hnil]; simp
    have hh2 : ¬ (tailAt b i).headD 0 = 34 := by rw [hnil]; simp
    rw [naivePw_of_ne hh1 hh2, liftRes_err_self]
    simp only [beq_iff_eq, hh1, hh2, ↓reduceIte]

/-! ## Hints -/

theorem naiveHints_cons_34 (l' : List UInt8) :
    naiveHints (34 :: l') = match naiveLit "abbrev\"" l' with
      | some r => .ok .«abbrev» r
      | none => match naiveLit "opaque\"" l' with
        | some r => .ok .«opaque» r
        | none => .err .badHints (34 :: l') := rfl

theorem naiveHints_of_ne {l : List UInt8} (h1 : ¬ l.headD 0 = 34) (h2 : ¬ l.headD 0 = 123) :
    naiveHints l = .err .badHints l := by
  unfold naiveHints
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl

theorem naiveHints_cons_123 {l' p' : List UInt8} (h : l'.dropWhile isWs = 34 :: p') :
    naiveHints (123 :: l') = (match naiveKeyBody p' with
      | none => .err .badHints (34 :: p')
      | some (key, r1) => match keyOf key with
        | .kRegular => (match naiveValue r1 with
          | none => .err .expectedColon (34 :: p')
          | some lv => match naiveNum lv with
            | none => .err .expectedNat lv
            | some (n, r2) => match r2.dropWhile isWs with
              | 125 :: rest => .ok (.regular n) rest
              | q => .err .expectedComma q)
        | _ => .err .badHints (34 :: p')) := by
  unfold naiveHints
  simp only [h]
  rfl

theorem naiveHints_cons_123_bad {l' : List UInt8} (h : ¬ (l'.dropWhile isWs).headD 0 = 34) :
    naiveHints (123 :: l') = .err .badHints (123 :: l') := by
  unfold naiveHints
  simp only []
  split
  · next p p' heq => rw [heq] at h; exact absurd rfl h
  · rfl

theorem scanHints_eq (b : ByteArray) (i : USize) :
    scanHints b i = liftRes b i (naiveHints (tailAt b i)) := by
  simp only [scanHints]
  rw [byteAt_eq]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    have hhead : (tailAt b i).headD 0 = b.uget i (usizeInBounds b i hlt) := by rw [hT]; rfl
    rw [hhead]
    by_cases h34 : b.uget i (usizeInBounds b i hlt) = 34
    · have hT34 : tailAt b i = 34 :: tailAt b (i + 1) := by rw [hT, h34]
      rw [hT34, naiveHints_cons_34, ← hT34, if_pos (by simpa using h34),
        matchLit_lit b (i + 1) "abbrev\"" (size_toUTF8_lt "abbrev\"" 7 rfl (by decide)),
        matchLit_lit b (i + 1) "opaque\"" (size_toUTF8_lt "opaque\"" 7 rfl (by decide))]
      unfold naiveLit
      have hdrop : ∀ n : Nat, n = 7 → (tailAt b (i + 1)).drop n = (tailAt b i).drop 8 := by
        intro n hn; rw [hn, hT34]; rfl
      by_cases hA : (lit "abbrev\"").isPrefixOf (tailAt b (i + 1)) = true
      · have hlen : 8 ≤ (tailAt b i).length := by
          have hp := (List.isPrefixOf_iff_prefix.mp hA).length_le
          rw [length_lit_abbrev] at hp
          rw [hT34]; simp only [List.length_cons]; omega
        simp only [hA, ↓reduceIte]
        rw [hdrop _ length_lit_abbrev, liftRes_ok_drop hlen]
        rfl
      · by_cases hO : (lit "opaque\"").isPrefixOf (tailAt b (i + 1)) = true
        · have hlen : 8 ≤ (tailAt b i).length := by
            have hp := (List.isPrefixOf_iff_prefix.mp hO).length_le
            rw [length_lit_opaque] at hp
            rw [hT34]; simp only [List.length_cons]; omega
          simp only [hA, hO, Bool.false_eq_true, ↓reduceIte]
          rw [hdrop _ length_lit_opaque, liftRes_ok_drop hlen]
          rfl
        · simp only [hA, hO, Bool.false_eq_true, ↓reduceIte, liftRes_err_self]
    · by_cases h123 : b.uget i (usizeInBounds b i hlt) = 123
      · have hT123 : tailAt b i = 123 :: tailAt b (i + 1) := by rw [hT, h123]
        have hltN := USize.lt_iff_toNat_lt.mp hlt
        have hsz := USize.toNat_lt_size b.usize
        have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hlt
        have hi1b : (i + 1).toNat ≤ b.usize.toNat := by omega
        have hsufW : (tailAt b (i + 1)).dropWhile isWs <:+ tailAt b (i + 1) :=
          List.dropWhile_suffix _
        have hPeq : skipWs b (i + 1)
            = (posAt (i + 1).toNat (tailAt b (i + 1))
                ((tailAt b (i + 1)).dropWhile isWs)).toUSize := skipWs_eq b (i + 1)
        have hPT : tailAt b (skipWs b (i + 1)) = (tailAt b (i + 1)).dropWhile isWs := by
          rw [hPeq]; exact tailAt_posAt (by simp only [length_bytes]; exact hi1b) hsufW
        have hPN : (skipWs b (i + 1)).toNat
            = posAt (i + 1).toNat (tailAt b (i + 1)) ((tailAt b (i + 1)).dropWhile isWs) := by
          rw [hPeq]; exact toNat_toUSize_posAt (by simp only [length_bytes]; exact hi1b) hsufW
        have hPle : (skipWs b (i + 1)).toNat ≤ b.usize.toNat := by
          rw [hPN, posAt_tailAt hi1b hsufW]; omega
        have hiP : i.toNat ≤ (skipWs b (i + 1)).toNat := by
          rw [hPN]; simp only [posAt]; omega
        rw [if_neg (by simpa using h34), if_pos (by simpa using h123)]
        by_cases hq : byteAt b (skipWs b (i + 1)) = 34
        · have hPlt : skipWs b (i + 1) < b.usize :=
            lt_usize_of_byteAt_ne_zero (by rw [hq]; decide)
          have hP1T : tailAt b (skipWs b (i + 1))
              = 34 :: tailAt b (skipWs b (i + 1) + 1) := by
            rw [tailAt_of_lt hPlt, uget_eq_byteAt hPlt, hq]
          have hdw : (tailAt b (i + 1)).dropWhile isWs
              = 34 :: tailAt b (skipWs b (i + 1) + 1) := by rw [← hPT]; exact hP1T
          rw [hT123, naiveHints_cons_123 hdw, if_neg (by simp [hq])]
          cases hkb : naiveKeyBody (tailAt b (skipWs b (i + 1) + 1)) with
          | none =>
            rw [(keyEnd_eq_zero_iff hPlt).mpr hkb]
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [← hP1T, liftRes_err_at hiP hPle]
          | some pr =>
            obtain ⟨key, r1⟩ := pr
            obtain ⟨hne0, hkeN, hT1⟩ := keyEnd_of_some hPlt hkb
            have hErr : ScanRes.err (α := HintsRec)
                ⟨(skipWs b (i + 1)).toNat, ErrTag.badHints⟩
                = liftRes b i (.err ErrTag.badHints
                    (34 :: tailAt b (skipWs b (i + 1) + 1)) : NRes HintsRec) := by
              rw [← hP1T, liftRes_err_at hiP hPle]
            rw [if_neg (by simpa using hne0), keyAt_eq hPlt hkb]
            cases hko : keyOf key <;> simp only [hko] <;> try exact hErr
            -- the `kRegular` slot
            rw [valueAt_eq hPlt hkb]
            cases hvv : naiveValue r1 with
            | none =>
              simp only [beq_self_eq_true, ↓reduceIte]
              rw [← hP1T, liftRes_err_at hiP hPle]
            | some lv =>
              simp only []
              obtain ⟨hlvsuf, hlvlt⟩ := naiveValue_of_key hPlt hkb hvv
              have hVn : (posAt (skipWs b (i + 1)).toNat
                  (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat
                  = posAt (skipWs b (i + 1)).toNat (tailAt b (skipWs b (i + 1))) lv :=
                toNat_toUSize_posAt (by simp only [length_bytes]; exact hPle) hlvsuf
              have hVT : tailAt b (posAt (skipWs b (i + 1)).toNat
                  (tailAt b (skipWs b (i + 1))) lv).toUSize = lv :=
                tailAt_posAt (by simp only [length_bytes]; exact hPle) hlvsuf
              have hVgt : (skipWs b (i + 1)).toNat
                  < (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat := by
                rw [hVn]; simp only [posAt]; omega
              have hVb : (posAt (skipWs b (i + 1)).toNat
                  (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat ≤ b.usize.toNat := by
                rw [hVn, posAt_tailAt hPle hlvsuf]; omega
              have hiV : i.toNat ≤ (posAt (skipWs b (i + 1)).toNat
                  (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat := by omega
              rw [if_neg (by
                simp only [beq_iff_eq]
                intro hx
                rw [hx] at hVgt
                omega)]
              cases hnum : naiveNum lv with
              | none =>
                have hgoal : liftRes b i (.err ErrTag.expectedNat lv : NRes HintsRec)
                    = .err ⟨(posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat,
                      ErrTag.expectedNat⟩ := by
                  conv => lhs; rw [← hVT]
                  exact liftRes_err_at hiV hVb
                rw [(numEnd_eq_self_iff b _).mpr (by rw [hVT]; exact hnum)]
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [hgoal]
              | some nr =>
                obtain ⟨n, r2⟩ := nr
                simp only []
                have hnum' : naiveNum (tailAt b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize) = some (n, r2) := by
                  rw [hVT]; exact hnum
                obtain ⟨hEeq, hEval⟩ := numEnd_of_some hnum'
                have hr2suf : r2 <:+ lv := naiveNum_rest_suffix hnum
                have hr2suf' : r2 <:+ tailAt b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize := by rw [hVT]; exact hr2suf
                have hEne : ¬ numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize
                    = (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize := by
                  intro hx
                  have := (numEnd_eq_self_iff b _).mp hx
                  rw [hnum'] at this
                  exact absurd this (by simp)
                have hET : tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize) = r2 := by
                  rw [hEeq]
                  exact tailAt_posAt (by simp only [length_bytes]; exact hVb) hr2suf'
                have hEN : (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize).toNat
                    = posAt (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize.toNat
                      (tailAt b (posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize) r2 := by
                  rw [hEeq]
                  exact toNat_toUSize_posAt (by simp only [length_bytes]; exact hVb) hr2suf'
                have hEb : (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize).toNat ≤ b.usize.toNat := by
                  rw [hEN, posAt_tailAt hVb hr2suf']; omega
                have hiE : i.toNat ≤ (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize).toNat := by
                  rw [hEN]; exact Nat.le_trans hiV (le_posAt _ _ _)
                rw [if_neg (by simpa using hEne), hEval]
                have hQsuf : (tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize)).dropWhile isWs
                    <:+ tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize) := List.dropWhile_suffix _
                have hQeq := skipWs_eq b (numEnd b (posAt (skipWs b (i + 1)).toNat
                  (tailAt b (skipWs b (i + 1))) lv).toUSize)
                have hQT : tailAt b (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize))
                    = (tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize)).dropWhile isWs := by
                  rw [hQeq]
                  exact tailAt_posAt (by simp only [length_bytes]; exact hEb) hQsuf
                have hQN : (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize)).toNat
                    = posAt (numEnd b (posAt (skipWs b (i + 1)).toNat
                      (tailAt b (skipWs b (i + 1))) lv).toUSize).toNat
                      (tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize))
                      ((tailAt b (numEnd b (posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize)).dropWhile isWs) := by
                  rw [hQeq]
                  exact toNat_toUSize_posAt (by simp only [length_bytes]; exact hEb) hQsuf
                have hQb : (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize)).toNat ≤ b.usize.toNat := by
                  rw [hQN, posAt_tailAt hEb hQsuf]; omega
                have hiQ : i.toNat ≤ (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize)).toNat := by
                  rw [hQN]; exact Nat.le_trans hiE (le_posAt _ _ _)
                rw [hET] at hQT
                rw [← hQT, byteAt_eq]
                cases hQc : tailAt b (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                    (tailAt b (skipWs b (i + 1))) lv).toUSize)) with
                | nil =>
                  simp only [List.headD_nil, beq_iff_eq]
                  rw [if_neg (by decide), ← hQc, liftRes_err_at hiQ hQb]
                | cons c t =>
                  by_cases hc : c = 125
                  · subst hc
                    have hQne : byteAt b (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize)) ≠ 0 := by
                      rw [byteAt_eq, hQc]; simp
                    have hQlt := lt_usize_of_byteAt_ne_zero hQne
                    have hQ1T : tailAt b (skipWs b (numEnd b (posAt (skipWs b (i + 1)).toNat
                        (tailAt b (skipWs b (i + 1))) lv).toUSize) + 1) = t := by
                      have hx := tailAt_of_lt hQlt
                      rw [hQc] at hx
                      simp only [List.cons.injEq] at hx
                      exact hx.2.symm
                    have hQ1N := usizeStep b _ hQlt
                    have hQltN := USize.lt_iff_toNat_lt.mp hQlt
                    simp only [List.headD_cons, beq_self_eq_true, ↓reduceIte]
                    rw [← hQ1T, liftRes_ok_at (by omega) (by omega)]
                  · simp only [List.headD_cons, beq_iff_eq, hc, ↓reduceIte]
                    split
                    · next rest heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 hc
                    · rw [← hQc, liftRes_err_at hiQ hQb]
        · have hnv : naiveHints (tailAt b i) = .err .badHints (tailAt b i) := by
            conv => lhs; rw [hT123]
            rw [naiveHints_cons_123_bad (by rw [← hPT, ← byteAt_eq]; exact hq), ← hT123]
          rw [hnv, liftRes_err_self, if_pos (bne_iff_ne.mpr hq)]
      · have hh1 : ¬ (tailAt b i).headD 0 = 34 := by rw [hhead]; exact h34
        have hh2 : ¬ (tailAt b i).headD 0 = 123 := by rw [hhead]; exact h123
        rw [naiveHints_of_ne hh1 hh2, liftRes_err_self]
        simp only [beq_iff_eq, h34, h123, ↓reduceIte]
  · have hnil := tailAt_of_not_lt hlt
    have hh1 : ¬ (tailAt b i).headD 0 = 34 := by rw [hnil]; simp
    have hh2 : ¬ (tailAt b i).headD 0 = 123 := by rw [hnil]; simp
    rw [naiveHints_of_ne hh1 hh2, liftRes_err_self]
    simp only [beq_iff_eq, hh1, hh2, ↓reduceIte]

/-! ## The header -/

/-- The same position, read from an earlier index. -/
theorem posAt_transfer {b : ByteArray} {i j : USize} {rest : List UInt8}
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ b.usize.toNat) (hiu : i.toNat ≤ b.usize.toNat)
    (hr : rest <:+ tailAt b j) :
    posAt i.toNat (tailAt b i) rest = posAt j.toNat (tailAt b j) rest := by
  rw [posAt_tailAt hj hr, posAt_tailAt hiu (hr.trans (tailAt_suffix hij))]

/-- The string the skipper steps over: its closing quote is not `0`,
and the rest after it is the naive body's rest. -/
theorem strClose_facts {b : ByteArray} {i : USize} {body r : List UInt8} (h : i < b.usize)
    (hs : naiveStrBody (tailAt b (i + 1)) = some (body, r)) :
    strClose b (i + 1) ≠ 0 ∧ (strClose b (i + 1)).toNat = i.toNat + 1 + body.length ∧
      tailAt b (strClose b (i + 1) + 1) = r ∧
      i.toNat + 1 + body.length + 1 + r.length = b.usize.toNat := by
  have hstep := usizeStep b i h
  have hlen := congrArg List.length (naiveStrBody_append hs)
  simp only [length_tailAt, List.length_append, List.length_cons, hstep] at hlen
  have hlt := USize.lt_iff_toNat_lt.mp h
  have hsz := USize.toNat_lt_size b.usize
  have hsum : i.toNat + 1 + body.length + 1 + r.length = b.usize.toNat := by omega
  have hsc : strClose b (i + 1) = (i.toNat + 1 + body.length).toUSize := by
    rw [strClose_eq, hs, hstep]
  have hscN : (strClose b (i + 1)).toNat = i.toNat + 1 + body.length := by
    rw [hsc, toNat_toUSize (by omega)]
  refine ⟨fun hx => ?_, hscN, ?_, hsum⟩
  · rw [hx] at hscN
    simp only [USize.toNat_ofNat, Nat.zero_mod] at hscN
    omega
  · have hstep2 : (strClose b (i + 1) + 1).toNat = i.toNat + 1 + body.length + 1 := by
      rw [usize_step_of_lt (by omega), hscN]
    show (bytes b).drop _ = r
    rw [hstep2]
    have hdd : (bytes b).drop (i.toNat + 1 + body.length + 1)
        = ((bytes b).drop (i.toNat + 1)).drop (body.length + 1) := by
      rw [List.drop_drop, Nat.add_assoc]
    rw [hdd, ← hstep, ← tailAt, naiveStrBody_append hs]
    simp

/-- The skipper's continuation: the position a later index reports is
the one `i` reports. -/
theorem skipBraced_pos_step {b : ByteArray} {i j : USize} {d d' : Nat}
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ b.usize.toNat) (hiu : i.toNat ≤ b.usize.toNat)
    (hnl : naiveSkipBraced (tailAt b i) d = naiveSkipBraced (tailAt b j) d') :
    (match naiveSkipBraced (tailAt b j) d' with
      | none => (0 : USize)
      | some r => (posAt j.toNat (tailAt b j) r).toUSize)
      = match naiveSkipBraced (tailAt b i) d with
        | none => 0
        | some r => (posAt i.toNat (tailAt b i) r).toUSize := by
  rw [hnl]
  cases hx : naiveSkipBraced (tailAt b j) d' with
  | none => rfl
  | some r =>
    simp only
    rw [posAt_transfer hij hj hiu (naiveSkipBraced_rest_suffix hx)]

theorem skipBraced_eq (b : ByteArray) (i : USize) (d : Nat) :
    skipBraced b i d = match naiveSkipBraced (tailAt b i) d with
      | none => 0
      | some r => (posAt i.toNat (tailAt b i) r).toUSize := by
  fun_induction skipBraced b i d with
  | case1 i depth h c h34 e he =>
    have h34' : (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have he' : strClose b (i + 1) = 0 := by
      have : (strClose b (i + 1) == 0) = true := he
      simpa using this
    have hsb : naiveStrBody (tailAt b (i + 1)) = none := by
      cases hx : naiveStrBody (tailAt b (i + 1)) with
      | none => rfl
      | some p =>
        obtain ⟨body, r⟩ := p
        exact absurd he' (strClose_facts h hx).1
    have hnl : naiveSkipBraced (tailAt b i) depth = none := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hsb, ↓reduceIte]
    rw [hnl]
  | case2 i depth h c h34 e he hlt ih =>
    have h34' : (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have he' : ¬ strClose b (i + 1) = 0 := by
      have : ¬ (strClose b (i + 1) == 0) = true := he
      simpa using this
    obtain ⟨body, r, hsb⟩ : ∃ body r, naiveStrBody (tailAt b (i + 1)) = some (body, r) := by
      cases hx : naiveStrBody (tailAt b (i + 1)) with
      | none => exact absurd (by rw [strClose_eq, hx]) he'
      | some p => obtain ⟨body, r⟩ := p; exact ⟨body, r, rfl⟩
    obtain ⟨_, hscN, hT2, hsum⟩ := strClose_facts h hsb
    have hltN := USize.lt_iff_toNat_lt.mp h
    have hsz := USize.toNat_lt_size b.usize
    have hstep2 : (strClose b (i + 1) + 1).toNat = i.toNat + 1 + body.length + 1 := by
      rw [usize_step_of_lt (by omega), hscN]
    have hguard : r.length < (tailAt b i).length := by
      simp only [length_tailAt]; omega
    rw [tailAt_of_lt h] at hguard
    have hnl : naiveSkipBraced (tailAt b i) depth
        = naiveSkipBraced (tailAt b (strClose b (i + 1) + 1)) depth := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hsb, dif_pos hguard, ↓reduceIte]
      rw [hT2]
    have hb1 : i.toNat ≤ (strClose b (i + 1) + 1).toNat := by omega
    have hb2 : (strClose b (i + 1) + 1).toNat ≤ b.usize.toNat := by omega
    have hb3 : i.toNat ≤ b.usize.toNat := by omega
    rw [ih]
    exact skipBraced_pos_step hb1 hb2 hb3 hnl
  | case3 i depth h c h34 e he hlt =>
    exfalso
    have he' : ¬ strClose b (i + 1) = 0 := by
      have : ¬ (strClose b (i + 1) == 0) = true := he
      simpa using this
    obtain ⟨body, r, hsb⟩ : ∃ body r, naiveStrBody (tailAt b (i + 1)) = some (body, r) := by
      cases hx : naiveStrBody (tailAt b (i + 1)) with
      | none => exact absurd (by rw [strClose_eq, hx]) he'
      | some p => obtain ⟨body, r⟩ := p; exact ⟨body, r, rfl⟩
    obtain ⟨_, hscN, _, hsum⟩ := strClose_facts h hsb
    have hltN := USize.lt_iff_toNat_lt.mp h
    have hsz := USize.toNat_lt_size b.usize
    have hstep2 : (strClose b (i + 1) + 1).toNat = i.toNat + 1 + body.length + 1 := by
      rw [usize_step_of_lt (by omega), hscN]
    have hb1 : i.toNat < (strClose b (i + 1) + 1).toNat := by omega
    exact hlt (USize.lt_iff_toNat_lt.mpr hb1)
  | case4 i depth h c h34 hbr ih =>
    have h34' : ¬ (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have hbr' : (b.uget i (usizeInBounds b i h) == 123
      || b.uget i (usizeInBounds b i h) == 91) = true := hbr
    have hstep := usizeStep b i h
    have hltN := USize.lt_iff_toNat_lt.mp h
    have hnl : naiveSkipBraced (tailAt b i) depth
        = naiveSkipBraced (tailAt b (i + 1)) (depth + 1) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hbr', ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    exact skipBraced_pos_step (by omega) (by omega) (by omega) hnl
  | case5 i h c h34 hbr hcl =>
    have h34' : ¬ (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have hbr' : ¬ (b.uget i (usizeInBounds b i h) == 123
      || b.uget i (usizeInBounds b i h) == 91) = true := hbr
    have hcl' : (b.uget i (usizeInBounds b i h) == 125
      || b.uget i (usizeInBounds b i h) == 93) = true := hcl
    have hnl : naiveSkipBraced (tailAt b i) 0 = some (tailAt b (i + 1)) := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hbr', hcl', ↓reduceIte, Bool.false_eq_true]
    have h1 : tailAt b (i + 1) = (tailAt b i).drop 1 := by rw [tailAt_of_lt h]; rfl
    have hlen : 1 ≤ (tailAt b i).length := by rw [tailAt_of_lt h]; simp
    rw [hnl]
    simp only
    rw [h1, pos_drop_eq b i 1 hlen]
    rfl
  | case6 i h c h34 hbr hcl d ih =>
    have h34' : ¬ (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have hbr' : ¬ (b.uget i (usizeInBounds b i h) == 123
      || b.uget i (usizeInBounds b i h) == 91) = true := hbr
    have hcl' : (b.uget i (usizeInBounds b i h) == 125
      || b.uget i (usizeInBounds b i h) == 93) = true := hcl
    have hstep := usizeStep b i h
    have hltN := USize.lt_iff_toNat_lt.mp h
    have hnl : naiveSkipBraced (tailAt b i) (d + 1)
        = naiveSkipBraced (tailAt b (i + 1)) d := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hbr', hcl', ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    exact skipBraced_pos_step (by omega) (by omega) (by omega) hnl
  | case7 i depth h c h34 hbr hcl ih =>
    have h34' : ¬ (b.uget i (usizeInBounds b i h) == 34) = true := h34
    have hbr' : ¬ (b.uget i (usizeInBounds b i h) == 123
      || b.uget i (usizeInBounds b i h) == 91) = true := hbr
    have hcl' : ¬ (b.uget i (usizeInBounds b i h) == 125
      || b.uget i (usizeInBounds b i h) == 93) = true := hcl
    have hstep := usizeStep b i h
    have hltN := USize.lt_iff_toNat_lt.mp h
    have hnl : naiveSkipBraced (tailAt b i) depth
        = naiveSkipBraced (tailAt b (i + 1)) depth := by
      conv => lhs; rw [tailAt_of_lt h]
      rw [naiveSkipBraced.eq_def]
      simp only [h34', hbr', hcl', ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    exact skipBraced_pos_step (by omega) (by omega) (by omega) hnl
  | case8 i depth h =>
    rw [tailAt_of_not_lt h, naiveSkipBraced.eq_def]

end ConLeche.Frontend
