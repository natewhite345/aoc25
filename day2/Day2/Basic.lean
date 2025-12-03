import Day2.Util

namespace ProductId
abbrev ProductId := Nat
/-- Inclusive Range of ProductIds -/
structure ProductIdRange where
  first : ProductId
  last : ProductId
deriving Repr, DecidableEq

abbrev ProductIdParseError := String

  private def from_string_err_syntax(input: String): String := "Must be two numbers separated by -, got "++ input
  private def from_string_err_order(first: Nat)(last: Nat): String := s!"Last cannot precede first, got first:={first} and last:={last}"

  /-- input should look like 145-3234 -/
  def from_string(input: String): Except String ProductIdRange :=
    match input.splitOn "-" with
    | [first, last] =>
        match [first, last].map String.toNat? with
        | [.some first, .some last] =>
          if first ≤ last then
          .ok { first:=first, last:=last }
          else .error (from_string_err_order first last)
        | _ => .error (from_string_err_syntax input)
    | _ => .error (from_string_err_syntax input)

  #guard from_string "145-3234" = .ok {first:= 145, last:= 3234}
  #guard from_string "0-0" = .ok {first:=0, last:=0}
  #guard from_string "0--4" = .error (from_string_err_syntax "0--4")
  #guard from_string "04" = .error (from_string_err_syntax "04")
  #guard from_string "150-16" = .error (from_string_err_order 150 16)

  /-- input should look like 132-145,345-765-/
  def list_from_string(input: String): Except String (List ProductIdRange) :=
    let split := input.splitOn ","
    split.mapM from_string

  #guard list_from_string "132-145,345-765" = .ok [⟨132, 145⟩,⟨345,765⟩]
  #guard list_from_string ",," = .error (from_string_err_syntax "")

  private def split_list_halfway(l: List α): Option (List α × List α) :=
    let N := l.length
    if N > 0 && N % 2 == 0 then
      .some (l.splitAt (N / 2))
    else .none
  #guard split_list_halfway ([]: List Nat) = .none
  #guard split_list_halfway [1] = .none
  #guard split_list_halfway [1,2] = .some ([1],[2])
  #guard split_list_halfway [1,2,3] = .none
  #guard split_list_halfway [1,2,3,4] = ([1,2],[3,4])

  def is_invalid_id(pid : ProductId.ProductId): Bool :=
    let digits := Nat.toDigits 10 pid
    match split_list_halfway digits with
    | .some (l1,l2) => List.all (List.zip l1 l2) (fun (a,b) => a == b)
    | .none => false
  #guard is_invalid_id 11 == true
  #guard is_invalid_id 12 == false
  #guard is_invalid_id 1 == false
  #guard is_invalid_id 123123 == true
  #guard is_invalid_id 123321 == false

  namespace InvalidIdPart2Helpers
  private structure AccOption where
    /-- the pattern that is repeated -/
    pat: List Char
    /--What index of the pattern the cursor would be at-/
    cur: Nat
    /-- if this pattern has repeated yet (cursor looped back to 0)-/
    hasRepeated: Bool
    safe: cur < pat.length
  private structure AccData where
    preceding : List Char
    options: List AccOption
  /-- Checks if the character matches with the character under the pointer in the pattern-/
  private def is_acc_option_valid (cur: Char) (opt: AccOption): Bool :=
    opt.pat[opt.cur]' opt.safe == cur
  private def tick_option (opt: AccOption) : AccOption :=
    let new_cur := opt.cur + 1
    if safe: new_cur < opt.pat.length then
      {pat:= opt.pat, cur:=new_cur, safe:= safe, hasRepeated:= opt.hasRepeated}
    else
      {pat:= opt.pat, cur:= 0, safe:= Nat.zero_lt_of_lt opt.safe, hasRepeated:= true}

  private def acc_fn(acc: AccData) (cur: Char): AccData :=
    let preceding := snoc acc.preceding cur
    have preceding_not_empty: preceding.length > 0 := snoc_len_gt_0 acc.preceding cur
    let options := acc.options.filter (is_acc_option_valid cur)
    let options := snoc (options.map tick_option) {pat:=preceding, cur:=0, safe:= preceding_not_empty, hasRepeated:=false}
    {options:=options, preceding:= preceding}
  end InvalidIdPart2Helpers

  open InvalidIdPart2Helpers in
  def is_invalid_id_part_2(pid : ProductId): Bool :=
    let digits := Nat.toDigits 10 pid
    let res_acc := digits.foldl acc_fn (⟨[],[]⟩: AccData)
    -- dbg_trace res_acc.options.map (fun o => o.pat)
    res_acc.options.any (fun o => o.hasRepeated && o.cur == 0)
  #guard is_invalid_id_part_2 11 == true
  #guard is_invalid_id_part_2 12 == false
  #guard is_invalid_id_part_2 1 == false
  #guard is_invalid_id_part_2 123123 == true
  #guard is_invalid_id_part_2 123321 == false
  #guard is_invalid_id_part_2 111 == true
  #guard is_invalid_id_part_2 565656 == true
  #guard is_invalid_id_part_2 824824824 == true
  #guard is_invalid_id_part_2 2121212121 == true
  #guard is_invalid_id_part_2 121312131213 == true
  #guard is_invalid_id_part_2 152153152153152153 == true
  #guard is_invalid_id_part_2 15215315215315215 == false
  #guard is_invalid_id_part_2 1521531521531521 == false

  private def expand_range(range: ProductIdRange): List ProductId :=
    List.range' range.first (1 + range.last - range.first)
  #guard expand_range ⟨5,15⟩ = [5,6,7,8,9,10,11,12,13,14,15]
  #guard expand_range ⟨3,3⟩ = [3]

  private def invalid_ids_in_range(range : ProductId.ProductIdRange) (is_invalid_id : ProductId → Bool := is_invalid_id): List ProductId :=
    List.filter is_invalid_id (expand_range range)
  #guard invalid_ids_in_range ⟨11,22⟩ = [11,22]
  #guard invalid_ids_in_range ⟨95,115⟩ = [99]

end ProductId

section
open ProductId

  /--
  Solves day2's challenge
  -/
  def day2(is_invalid_id: ProductId → Bool := is_invalid_id): String → Except String Nat :=
    fun input => do
      let parsed ← list_from_string input
      .ok (parsed.flatMap (fun x => invalid_ids_in_range x is_invalid_id)).sum

  def part1 := day2 is_invalid_id
  def part2 := day2 is_invalid_id_part_2

  private def example_input := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

  #guard part1 example_input = .ok 1227775554
  #guard part2 example_input = .ok 4174379265
end
