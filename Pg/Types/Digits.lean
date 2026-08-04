module

public section

namespace Pg

/-!
Decimal digit strings and character-level string splitting — the kernel-visible
substrate every text codec in pg-lean is proved through.

Neither `Nat.repr` nor `String.toNat?` can carry a roundtrip proof:
`Nat.digitChar` is not exposed to the kernel, and core ships no lemma about
`String.toNat?` of a zero-padded argument. `String.splitOn` is worse —
`String.splitOnAux` is `@[irreducible]` and has no lemmas at all. So pg-lean
renders and parses decimals with its own `natDigits`/`padDigits`/`natOfDigits`
and splits with `List.splitOn`, which does have a full lemma set.

This module is shared by `Pg.Types.Numeric`, `Pg.Types.Interval` and
`Pg.Types.Codec`; it depends on nothing but core. Every definition is
`@[expose]`d — they exist to be unfolded by proofs in other modules.
-/

@[expose] def isAsciiDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

@[expose] def digitChar (d : Nat) : Char := Char.ofNat (48 + d % 10)

/-- Decimal digits of `n`, most significant first (`0` is `['0']`) — the same
characters `toString n` produces. -/
@[expose] def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `n` in decimal, left-padded with `'0'` to at least `width` characters
(never truncated — a wider value keeps all its digits, as PostgreSQL does with
5-digit years). -/
@[expose] def padDigits (width n : Nat) : List Char :=
  List.replicate (width - (natDigits n).length) '0' ++ natDigits n

/-- Fold a decimal digit list onto an accumulator; `none` on any non-digit. -/
@[expose] def natOfDigits (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    if isAsciiDigit c then natOfDigits (acc * 10 + (c.toNat - 48)) rest else none

/-- A whole decimal field: at least one character, all of them digits. -/
@[expose] def natOfDigitsFull : List Char → Option Nat
  | [] => none
  | chars => natOfDigits 0 chars

@[expose] def parseNatField (s : String) (what : String) : Except String Nat :=
  match natOfDigitsFull s.toList with
  | some v => pure v
  | none => throw s!"bad {what}: {s}"

/-- Split a string at every occurrence of one character.

Deliberately not `String.splitOn`: `String.splitOnAux` is `@[irreducible]` and
core ships no lemmas about it, so a `String.splitOn`-based parser is opaque to
the kernel. `List.splitOn` has a full lemma set and agrees with it for a
single-character separator. (Same trick as `Pg.Sasl.Scram.splitOnChar`.) -/
@[expose] def splitOnChar (c : Char) (s : String) : List String :=
  (s.toList.splitOn c).map String.ofList

@[expose] def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Trim ASCII whitespace on the character list. `String.trimAscii` goes
through `String.Slice`, which the kernel cannot follow. -/
@[expose] def trimAsciiChars (l : List Char) : List Char :=
  ((l.dropWhile isAsciiSpace).reverse.dropWhile isAsciiSpace).reverse

/-!
### Laws

`natOfDigits` reads back exactly what `natDigits`/`padDigits` wrote, at any
padding width; and every character of a rendered field is a digit, which is
what makes `-`, `:`, `.` and `,` separators unambiguous.
-/

theorem toNat_ofNat_ascii {n : Nat} (h : n ≤ 127) : (Char.ofNat n).toNat = n := by
  show (Char.ofNat n).val.toNat = n
  unfold Char.ofNat
  rw [dif_pos (by unfold Nat.isValidChar; omega)]
  unfold Char.ofNatAux
  simp [UInt32.toNat]

theorem toNat_digitChar {d : Nat} (h : d < 10) : (digitChar d).toNat = 48 + d := by
  unfold digitChar
  rw [Nat.mod_eq_of_lt h, toNat_ofNat_ascii (by omega)]

theorem isAsciiDigit_digitChar {d : Nat} (h : d < 10) :
    isAsciiDigit (digitChar d) = true := by
  unfold isAsciiDigit
  rw [toNat_digitChar h]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem natOfDigits_append : ∀ (l₁ : List Char) (acc : Nat) (l₂ : List Char),
    natOfDigits acc (l₁ ++ l₂)
      = (natOfDigits acc l₁).bind (fun a => natOfDigits a l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro acc l₂; rfl
  | cons c t ih =>
    intro acc l₂
    simp only [List.cons_append, natOfDigits]
    split
    · exact ih _ _
    · rfl

/-- `natDigits` is never empty, so a rendered field always has a digit. -/
theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  unfold natDigits
  split
  · exact List.cons_ne_nil _ _
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

theorem natOfDigits_natDigits : ∀ (n : Nat) (acc : Nat),
    natOfDigits acc (natDigits n) = some (acc * 10 ^ (natDigits n).length + n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · have hd : natDigits n = [digitChar n] := by rw [natDigits, if_pos h]
      rw [hd]
      simp only [natOfDigits, isAsciiDigit_digitChar h, if_pos, List.length_cons,
        List.length_nil, toNat_digitChar h]
      congr 1
      omega
    · have h10 : 10 ≤ n := by omega
      have hmod : n % 10 < 10 := Nat.mod_lt _ (by omega)
      have hd : natDigits n = natDigits (n / 10) ++ [digitChar (n % 10)] := by
        rw [natDigits, if_neg h]
      rw [hd, natOfDigits_append, ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) acc]
      simp only [Option.bind_some, natOfDigits, isAsciiDigit_digitChar hmod, if_pos,
        toNat_digitChar hmod, List.length_append, List.length_cons, List.length_nil]
      congr 1
      rw [show 48 + n % 10 - 48 = n % 10 from by omega, Nat.pow_succ,
        Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.div_add_mod']

theorem natOfDigits_zeros : ∀ (k acc : Nat),
    natOfDigits acc (List.replicate k '0') = some (acc * 10 ^ k) := by
  intro k
  induction k with
  | zero => intro acc; simp only [List.replicate_zero, natOfDigits, Nat.pow_zero, Nat.mul_one]
  | succ j ih =>
    intro acc
    have hz : ('0' : Char).toNat = 48 := by decide
    have hdig : isAsciiDigit '0' = true := by decide
    rw [List.replicate_succ]
    simp only [natOfDigits, hdig, if_pos, hz]
    rw [ih (acc * 10 + (48 - 48))]
    congr 1
    rw [show (48 : Nat) - 48 = 0 from rfl, Nat.add_zero, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm (10 : Nat) (10 ^ j)]

/-- **A padded decimal field reads back as the number it was rendered from**,
at any width. -/
theorem natOfDigits_padDigits (width n : Nat) :
    natOfDigits 0 (padDigits width n) = some n := by
  unfold padDigits
  rw [natOfDigits_append, natOfDigits_zeros, Option.bind_some, natOfDigits_natDigits]
  simp

theorem natOfDigitsFull_padDigits (width n : Nat) :
    natOfDigitsFull (padDigits width n) = some n := by
  have hval := natOfDigits_padDigits width n
  cases hl : padDigits width n with
  | nil => exact absurd (List.append_eq_nil_iff.mp hl).2 (natDigits_ne_nil n)
  | cons c t =>
    rw [hl] at hval
    exact hval

theorem parseNatField_padDigits (width n : Nat) (what : String) :
    parseNatField (String.ofList (padDigits width n)) what = .ok n := by
  unfold parseNatField
  rw [String.toList_ofList, natOfDigitsFull_padDigits]
  rfl

/-- Every character of a rendered decimal field is a digit — which is what
makes the `-`, `:` and `.` separators unambiguous. -/
theorem isAsciiDigit_of_mem_natDigits : ∀ (n : Nat) (c : Char),
    c ∈ natDigits n → isAsciiDigit c = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    by_cases h : n < 10
    · rw [natDigits, if_pos h] at hc
      rcases List.mem_singleton.mp hc with rfl
      exact isAsciiDigit_digitChar h
    · rw [natDigits, if_neg h] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) c hc
      · rcases List.mem_singleton.mp hc with rfl
        exact isAsciiDigit_digitChar (Nat.mod_lt _ (by omega))

theorem isAsciiDigit_of_mem_padDigits {width n : Nat} {c : Char}
    (hc : c ∈ padDigits width n) : isAsciiDigit c = true := by
  unfold padDigits at hc
  rcases List.mem_append.mp hc with hc | hc
  · rw [List.eq_of_mem_replicate hc]; decide
  · exact isAsciiDigit_of_mem_natDigits n c hc

/-- A separator that is not a digit never occurs inside a rendered field. -/
theorem ne_of_mem_padDigits {width n : Nat} {sep : Char}
    (hsep : isAsciiDigit sep = false) : ∀ c ∈ padDigits width n, c ≠ sep := by
  intro c hc heq
  have hd := isAsciiDigit_of_mem_padDigits hc
  rw [heq, hsep] at hd
  exact Bool.false_ne_true hd

/-- A decimal rendering of `n < 10^(k+1)` is at most `k+1` characters. -/
theorem natDigits_length_le : ∀ (k n : Nat), n < 10 ^ (k + 1) →
    (natDigits n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    rw [Nat.pow_one] at h
    rw [natDigits, if_pos h]
    simp
  | succ j ih =>
    intro n h
    by_cases hs : n < 10
    · rw [natDigits, if_pos hs]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [natDigits, if_neg hs]
      have hdiv : n / 10 < 10 ^ (j + 1) := by
        have : (10 : Nat) ^ (j + 1 + 1) = 10 ^ (j + 1) * 10 := Nat.pow_succ ..
        omega
      have := ih (n / 10) hdiv
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem padDigits_length {width n : Nat} (h : (natDigits n).length ≤ width) :
    (padDigits width n).length = width := by
  unfold padDigits
  rw [List.length_append, List.length_replicate]
  omega

theorem padDigits_ne_nil (width n : Nat) : padDigits width n ≠ [] :=
  fun h => absurd (List.append_eq_nil_iff.mp h).2 (natDigits_ne_nil n)

theorem not_mem_padDigits {width n : Nat} {sep : Char}
    (hsep : isAsciiDigit sep = false) : sep ∉ padDigits width n :=
  fun hmem => (ne_of_mem_padDigits hsep sep hmem) rfl

theorem splitOnChar_singleton {c : Char} {s : String} (h : c ∉ s.toList) :
    splitOnChar c s = [s] := by
  unfold splitOnChar
  rw [List.splitOn_eq_singleton h]
  simp only [List.map_cons, List.map_nil, String.ofList_toList]

theorem splitOnChar_cons {c : Char} {p rest : List Char} (h : c ∉ p) :
    splitOnChar c (String.ofList (p ++ c :: rest)) =
      String.ofList p :: splitOnChar c (String.ofList rest) := by
  unfold splitOnChar
  rw [String.toList_ofList, List.splitOn_append_cons_self_of_not_mem h,
    String.toList_ofList, List.map_cons]

/-- `natOfDigitsFull` reads back the digits `natDigits` wrote. -/
theorem natOfDigitsFull_natDigits (n : Nat) : natOfDigitsFull (natDigits n) = some n := by
  have hval := natOfDigits_natDigits n 0
  cases hl : natDigits n with
  | nil => exact absurd hl (natDigits_ne_nil n)
  | cons c t =>
    rw [hl] at hval
    rw [show natOfDigitsFull (c :: t) = natOfDigits 0 (c :: t) from rfl, hval]
    simp

/-- A non-digit separator never occurs inside a rendered decimal. -/
theorem not_mem_natDigits {n : Nat} {sep : Char} (hsep : isAsciiDigit sep = false) :
    sep ∉ natDigits n := by
  intro hmem
  have hd := isAsciiDigit_of_mem_natDigits n sep hmem
  rw [hsep] at hd
  exact Bool.false_ne_true hd

theorem beq_false_of_ne {a b : Char} (h : a ≠ b) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

/-- Trimming is the identity on a string that neither starts nor ends with
ASCII whitespace. -/
theorem trimAsciiChars_eq_self {l : List Char}
    (h1 : ∀ c, l.head? = some c → isAsciiSpace c = false)
    (h2 : ∀ c, l.getLast? = some c → isAsciiSpace c = false) :
    trimAsciiChars l = l := by
  unfold trimAsciiChars
  cases hl : l with
  | nil => rfl
  | cons c t =>
    rw [List.dropWhile_cons_of_neg (by rw [h1 c (by rw [hl]; rfl)]; exact Bool.false_ne_true)]
    cases hr : (c :: t).reverse with
    | nil => exact absurd hr (by simp)
    | cons d u =>
      have hd : (c :: t).getLast? = some d := by
        rw [← List.head?_reverse, hr]; rfl
      rw [List.dropWhile_cons_of_neg
        (by rw [h2 d (by rw [hl]; exact hd)]; exact Bool.false_ne_true), ← hr,
        List.reverse_reverse]

end Pg
