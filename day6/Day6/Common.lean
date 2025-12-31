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

def eval_problem: Problem → Nat
| ⟨.Add, ops⟩ => List.sum ops
| ⟨.Multiply, ops⟩ => ops.foldl (·*·) 1
