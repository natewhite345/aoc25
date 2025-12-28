import Day6.Util

inductive Op | Add | Multiply
deriving Inhabited, DecidableEq
def parse_op: String → Op
| "*" => .Multiply
| "+" => .Add
| _ => panic! "Invalid Operator"
structure Problem where
  op: Op
  args: List Nat
deriving DecidableEq
def parse_problem!(input: List String): Problem :=
  {op:= parse_op input.getLast!, args:= (input.take (input.length -1)).map String.toNat!}
#guard parse_problem! ["5","43","2","+"] = {op:=.Add, args:=[5,43,2]}

def split_and_trim(line: String) :=
  (line.splitOn " ").filter (·.length > 0)
#guard split_and_trim "    fooo  bar baz   y " = ["fooo","bar","baz","y"]
#guard split_and_trim "*   +   *   + " = ["*","+","*","+"]

def eval_problem: Problem → Nat
| ⟨.Add, ops⟩ => List.sum ops
| ⟨.Multiply, ops⟩ => ops.foldl (·*·) 1

def parse!(input:String): List Problem:=
  let lines := input.splitOn "\n"
  let lines := lines.map split_and_trim
  List.zip_many lines.map parse_problem!


def part1 : String → Nat := List.sum ∘ (List.map eval_problem) ∘ parse!
def ex := "123 328  51 64
 45 64  387 23
  6 98  215 314
*   +   *   + "
#guard part1 ex = 4277556
