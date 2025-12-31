import Day6.Common
import Day6.Util
import Batteries.Data.List.Basic

private def ex := "123 328  51 64
 45 64  387 23
  6 98  215 314
*   +   *   +  "


def parse(s: String): Except String (List Problem):= do
  let lines := s.splitOn "\n"
  let lines := lines.filter (·.length > 0)
  if ne: lines = [] then Except.error "Empty input" else
  let ops := lines.getLast ne
  let ops := ops.toList.filter (¬ ·.isWhitespace)
  let ops := ops.map (parse_op ∘ Char.toString)
  let nums := lines.dropLast.map String.toList
  let nums := nums.transpose.splitOnP (·.all (· = ' '))
  if nums.length ≠ ops.length then .error s!"Operator length {ops.length} ≠ problem number length {nums.length}. Problems must be separated by a column of all empty spaces." else
  let nums ←  nums.mapM (·.mapM readColumn)
  .ok ((ops.zip nums).map (fun (op, nums) => ⟨op, nums⟩))
where
  readColumn(col : List Char): Except String Nat :=
    let x := String.ofList (col.filter (¬ ·.isWhitespace))
    match x.toNat? with
    | .none => .error s!"{x} can't be read as a number"
    | .some n => .ok n


def part2(s: String) : Except String Nat := do
  let parsed := parse s
  let parsed ← parsed
  let results := parsed.map eval_problem
  .ok results.sum

#guard part2 ex = .ok 3263827
