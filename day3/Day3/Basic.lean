import Day3.Util

@[simp]
def allowed_joltage (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 9
instance (n : Nat) : Decidable (allowed_joltage n) := by simp_all;infer_instance

structure Joltage where
  _mk ::
  n : Nat
  ok : allowed_joltage n
deriving DecidableEq
instance : ToString Joltage := ⟨toString ∘ Joltage.n⟩
instance : Inhabited Joltage := ⟨⟨1, by decide⟩⟩
instance : LT Joltage := ⟨λ a b => a.n < b.n⟩
instance : DecidableRel (fun a b : Joltage => a < b) :=
  fun a b => inferInstanceAs (Decidable (a.n < b.n))

namespace Joltage
  def mk (n: Nat) (ok: allowed_joltage n := by rw [allowed_joltage]; simp) := Joltage._mk n ok
  def mk! (n: Nat): Joltage :=
    if h : allowed_joltage n then
      ⟨n, h⟩
    else
      panic! s!"Bad Joltage: {n}"
  namespace Examples
    def ONE := Joltage.mk 1
    def NINE := Joltage.mk 9

    namespace Invalid
      /-- error: could not synthesize default value for parameter 'ok' using tactics --- error: unsolved goals ⊢ False-/
      #guard_msgs in
      private def ZERO := Joltage.mk 0
      /-- error: could not synthesize default value for parameter 'ok' using tactics --- error: unsolved goals ⊢ False-/
      #guard_msgs in
      private def TEN := Joltage.mk 10
end Joltage.Examples.Invalid

abbrev Bank := List Joltage

namespace parse_joltage_errs
def unparseable(input: String): String :=
  s!"Could not interpret {input} as a Joltage"
def invalid_value(input: Nat): String :=
  s!"A Joltage of {input} is not allowed."
end parse_joltage_errs

open parse_joltage_errs in
def parse_joltage(input:String): Except String Joltage :=
  match input.toNat? with
  | .none => .error (unparseable input)
  | .some n => if h: allowed_joltage n
                then .ok (Joltage.mk n h)
                else .error (invalid_value n)
#guard parse_joltage "1" = .ok Joltage.Examples.ONE
#guard parse_joltage "0" = .error (parse_joltage_errs.invalid_value 0)
#guard parse_joltage "-1" = .error (parse_joltage_errs.unparseable "-1")

def parse_bank(input: String): Except String Bank :=
  input.toList.mapM (parse_joltage ∘ Char.toString)
def parse_bank!(input: String): Bank :=
  match parse_bank input with
  | .ok x => x
  | .error x => panic! x

def parse_banks(input: String): Except String (List Bank) :=
  --dbg_trace (List.mapM parse_bank (input.splitOn "\n"))
  List.mapM parse_bank (input.splitOn "\n")

#guard parse_banks "1237623
4537823
682993984" = .ok ([[1,2,3,7,6,2,3],[4,5,3,7,8,2,3],[6,8,2,9,9,3,9,8,4]].map (λ l => l.map (λ x => Joltage.mk! x )))

namespace largest_joltage
structure Acc where
  --seen: List Joltage
  first: Joltage
  --best_first_pf: ∀ j ∈ seen, best_first ≥ j
  --best_first_idx: Nat
  --best_first_idx_lt_len: best_first_idx < seen.length
  second: Joltage
  --best_second_pf: ∀ j ∈ seen, f ∈ seen
def from_digits(a b : Joltage): Nat := a.n * 10 + b.n
#guard from_digits Joltage.Examples.ONE Joltage.Examples.NINE = 19
theorem from_digits_cmp (a b c d : Joltage): from_digits a b < from_digits c d ↔ a.n < c.n ∨ (a.n = c.n ∧  b.n < d.n) := by
  rw [from_digits,from_digits]
  have pa := a.ok
  have pb := b.ok
  have pc := c.ok
  have pd := d.ok
  simp_all
  grind

def helper(acc: Acc): List Joltage → Nat
| [] => from_digits acc.first acc.second
| new :: rest =>
   helper
    (if acc.first < acc.second
    then {first:= acc.second, second:= new}
    else {first:= acc.first, second:= if acc.second < new then new else acc.second})
    rest

end largest_joltage
open largest_joltage in
def largest_joltage: Bank →  Nat
| [] => 0
| _ :: [] => 0
| fst :: snd :: rest =>
  helper
    {first:=fst, second:=snd}
    rest

#guard largest_joltage (parse_bank! "987654321111111") = 98
#guard largest_joltage (parse_bank! "811111111111119") = 89
#guard largest_joltage (parse_bank! "234234234234278") = 78
#guard largest_joltage (parse_bank! "818181911112111") = 92
namespace largest_joltage
  theorem pf: ∀ (b : Bank) (j₁ j₂ : Joltage ), List.Sublist [j₁,j₂] b →
    largest_joltage b ≥  j₁.n *10 + j₂.n := by
      intros b j1 j2 sublist
      simp_all
      fun_cases largest_joltage
      grind; grind
      fun_cases helper
      rw [from_digits]
      grind
      simp_all
      rename_i fst snd new rest
      induction rest with
      | nil =>
        dsimp [helper]
        by_cases h: fst < snd <;> by_cases h2: snd < new <;> simp [h]
        <;> rw [LT.lt, instLTJoltage] at h
        <;> rw [LT.lt, instLTJoltage] at h2
        <;> simp at h <;> simp at h2 <;> rw [from_digits]
        cases sublist
        repeat (rename_i h <;> cases h)
        have H := from_digits_cmp fst fst j1 j2
        have hh := H.mpr (Or.inl h)
        grind
        repeat (rename_i h <;> cases h)
        have H := from_digits_cmp j1 j2 snd snd
        have hh := H.mpr (Or.inl h)
        grind
        repeat (rename_i h <;> cases h)
        all_goals sorry
      | cons hd tl ih => sorry

end largest_joltage

def sum_of_max_joltages(banks: List Bank): Nat :=
  (banks.map largest_joltage).sum

def part1 (input: String): Except String Nat:= do
  let banks ← parse_banks input
  .ok (sum_of_max_joltages banks)

structure Sum_Power where
  sum: Nat
  power: Nat
def from_digits'(l: List Joltage): Nat :=
  let res := l.foldr
    (fun cur acc =>
      let new_digit :Nat := (10 ^ acc.power) * cur.n
      {sum:= new_digit + acc.sum, power:= acc.power + 1})
    ({sum:= 0, power := 0}: Sum_Power)
  res.sum
namespace from_digits'.Guards
abbrev f := from_digits'
#guard f [] = 0
#guard f (parse_bank! "3454929") = 3454929
end from_digits'.Guards

namespace largest_joltage'
/-- removes the leftmost number lower than the one to its right-/
def remove_leftmost_lower_than_right{α} [LT α] [DecidableRel ((· < ·) : α → α → Prop)]: List α → List α
  | [] => []
  | _ :: [] => []
  | fst :: snd :: rest => if fst < snd then snd :: rest else fst :: remove_leftmost_lower_than_right (snd :: rest)
namespace remove_leftmost_lower_than_right.guards
abbrev f := @remove_leftmost_lower_than_right Nat
#guard f [] = []
#guard f [5] = []
#guard f [5, 6] = [6]
#guard f [1,2,3] = [2,3]
#guard f [3,2,1] = [3,2]
#guard f [1,4,3,2] = [4,3,2]
#guard f [5,1,3,7] = [5,3,7]

end remove_leftmost_lower_than_right.guards
def tick(acc : List Joltage)(new : Joltage) : List Joltage :=
  remove_leftmost_lower_than_right (snoc acc new)
end largest_joltage'
open largest_joltage' in
def largest_joltage'(b: Bank): Nat :=
  if b.length < 12 then 0
  else
    let (init, rest) := b.splitAt 12
    let selected_joltages := rest.foldl tick init
    from_digits' selected_joltages


def sum_of_max_joltages'(banks: List Bank): Nat :=
  (banks.map largest_joltage').sum

def part2 (input: String): Except String Nat:= do
  let banks ← parse_banks input
  .ok (sum_of_max_joltages' banks)
#guard part2 "987654321111111
811111111111119
234234234234278
818181911112111" = .ok 3121910778619








-- theorem concat_digits (a b : Joltage)
--   (ha : a.n ∈ List.range' 1 9) (hb : b.n ∈ List.range' 1 9) :
--   toString a.n ++ toString b.n = toString (concat a b) := by
--   -- Convert membership in range to explicit disjunction
--   have ha_disj : a.n = 1 ∨ a.n = 2 ∨ a.n = 3 ∨ a.n = 4 ∨ a.n = 5 ∨ a.n = 6 ∨ a.n = 7 ∨ a.n = 8 ∨ a.n = 9 := by grind
--   have hb_disj : b.n = 1 ∨ b.n = 2 ∨ b.n = 3 ∨ b.n = 4 ∨ b.n = 5 ∨ b.n = 6 ∨ b.n = 7 ∨ b.n = 8 ∨ b.n = 9 := by grind

--   -- Use fun_cases to split all possibilities automatically
--   fun_cases ha_disj
--   fun_cases hb_disj

--   -- Now every goal corresponds to one concrete pair (a.n, b.n)
--   all_goals grind

-- theorem concat_pf : ∀ a b : Joltage, toString a ++ toString b = toString (concat a b) := by
--   intros aj bj
--   dsimp [concat, toString]
--   have apf := aj.ok
--   have bpf := bj.ok
--   dsimp [allowed_joltage] at apf
--   dsimp [allowed_joltage] at bpf
--   have segments (n: Nat) : n < 1 ∨ n > 9 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by grind
--   have segments (n: Nat) : n < 1 ∨ n > 9 ∨ ((n-1) ∈ List.range 9) := by grind
--   have as := segments aj.n
--   have bs := segments bj.n

--   have : Nat.toDigits
--   cases as <;> rename_i tmp; grind; cases tmp <;> rename_i bar; grind;
--   cases bs <;> rename_i tmp; grind; cases tmp <;> rename_i barr; grind;
--   simp_all
--   if h: aj.n = 1 then if hh: bj.n = 1 then
--     rw [h, hh]; simp_all
--     dsimp [Nat.repr, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar]
--     rw [List.asString, String.mk]
--     dsimp [List.utf8Encode, HAppend.hAppend, Append.append]
--     simp_all
--     dsimp [String.utf8EncodeChar, List.toByteArray, List.toByteArray.loop]
--     rw [String.append]
--     sorry

--   else sorry
 -- else sorry
