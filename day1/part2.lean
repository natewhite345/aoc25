inductive Direction
  | L: Direction
  | R: Direction
deriving Repr


structure Rotation where
  dir : Direction
  count: Nat
deriving Repr

namespace Direction
  def from_string(s: String): Except String Direction :=
    match s with
    | "L" => .ok .L
    | "R" => .ok .R
    | x => .error ("Must be L or R, found " ++ x)
end Direction

namespace Rotation
  def from_string (s: String) : Except String Rotation := do
    if s.isEmpty then
      throw "Cannot parse empty string"
    let dirStr := s.take 1
    let dir ← Direction.from_string dirStr
    let countStr := s.drop 1
    if countStr.isEmpty then
      throw "Can't parse empty string as number"
    match countStr.toNat? with
    | some n => pure { dir := dir, count := n }
    | none   => throw ("Cannot parse number: " ++ countStr)

  #eval from_string "R45" -- = .ok (Rotation.mk .R 45) := rfl
end Rotation


def parsePart1(input: String): Except String (List Rotation) :=
  let lines: List String := input.splitOn "\n"
  let valid_and_invalid := lines.map Rotation.from_string
  valid_and_invalid.mapM id

#eval parsePart1 "" -- error
#eval parsePart1 "L345" -- [Rotation.mk L 345]
#eval parsePart1  "L2
R45
R32" --= [Rotation.mk L 2, Rotation.mk R 45, Rotation.mk R 32] := rfl

structure _acc where
  count: Nat
  posn: Nat

def MAX_NUM := 99
def DIAL_START := 50
def spin(loc: Nat)(rot: Rotation): Nat :=
  let mod := MAX_NUM + 1 -- because of 0
  let raw := match rot.dir with
  | .R => loc + rot.count
  | .L => loc + mod - (rot.count % mod)
  raw % mod

#eval spin 0 (.mk .L 1) --99
#eval spin 99 (.mk .R 1) -- 0
#eval spin 5 (.mk .L 10) -- 95
#eval spin 0 (.mk .L 300) -- 0

def passes_zero_count_helper : Nat → Rotation → Nat → Nat
  | posn, ⟨dir, 0⟩, res_addend => res_addend + (if posn = 0 then 1 else 0)
  | posn, ⟨dir, count+1⟩, res_addend =>
      let res := res_addend + (if posn = 0 then 1 else 0)
      let new_loc := spin posn ⟨dir, 1⟩
      let new_rot := ⟨dir, count⟩
      passes_zero_count_helper new_loc new_rot res


def passes_zero_count(cur: Nat) (rot: Rotation): Nat :=
  let unadjusted := passes_zero_count_helper cur rot 0
  if cur = 0 then unadjusted - 1 else unadjusted -- don't want to count starting at 0

#eval passes_zero_count 5 (.mk .L 5) -- 1
#eval passes_zero_count 5 (.mk .R 200) --2
#eval passes_zero_count 0 (.mk .R 5) -- 0
#eval passes_zero_count 0 (.mk .L 400) --4

def computePart2(input: List Rotation): Nat :=
  let init : _acc := {posn:= DIAL_START, count:=0}
  let final_state := input.foldl (fun acc cur =>
    let new_posn := spin acc.posn cur
    let new_count := acc.count + (passes_zero_count acc.posn cur)
    {posn:= new_posn, count:= new_count}) init
  final_state.count

def part2 (input : String) : Except String Nat := do
  let parsed ← parsePart1 input
  .ok (computePart2 parsed)

#eval part2 "R340
L34
R2" -- 3
#eval part2 "L68" --1
#eval part2 "L68
L30
R48
L0" --1

def main : IO Unit := do
  let h ← IO.FS.Handle.mk "input.txt" IO.FS.Mode.read
  let contents ← IO.FS.Handle.readToEnd h
  IO.println (contents.splitOn "\n")
  IO.println (match (part2 contents) with
  | .ok p => s!"{p}"
  | .error s => s)
