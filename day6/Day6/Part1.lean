import Day6.Util
import Day6.Common

def split_and_trim(line: String) :=
  (line.splitOn " ").filter (·.length > 0)
#guard split_and_trim "    fooo  bar baz   y " = ["fooo","bar","baz","y"]
#guard split_and_trim "*   +   *   + " = ["*","+","*","+"]

def parse!(input:String): List Problem:=
  let lines := input.splitOn "\n"
  let lines := (lines.filter (·.length >0)).map split_and_trim
  lines.zip_many.map parse_problem!

def part1 : String → Nat := List.sum ∘ (List.map eval_problem) ∘ parse!
private def ex := "123 328  51 64
 45 64  387 23
  6 98  215 314
*   +   *   + "
#guard part1 ex = 4277556
