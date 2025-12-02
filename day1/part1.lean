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

def computePart1(input: List Rotation): Nat :=
  let init : _acc := {posn:= DIAL_START, count:=0}
  let final_state := input.foldl (fun acc cur =>
    let new_posn := spin acc.posn cur
    let new_count := if new_posn = 0 then acc.count + 1 else acc.count
    {posn:= new_posn, count:= new_count}) init
  final_state.count

def part1 (input : String) : Except String Nat := do
  let parsed ← parsePart1 input
  .ok (computePart1 parsed)

#eval part1 "R340
L34
R2" -- 0
#eval part1 "R100" --1
#eval part1 "R100
L1
R2
L1" --2

def main : IO Unit := do
  let h ← IO.FS.Handle.mk "input.txt" IO.FS.Mode.read
  let contents ← IO.FS.Handle.readToEnd h
  IO.println (contents.splitOn "\n")
  IO.println (match (part1 contents) with
  | .ok p => s!"{p}"
  | .error s => s)
