inductive CellState
  | Roll
  | Empty
deriving Inhabited, Repr, DecidableEq
namespace CellState
  def from_char!: Char → CellState
  | '@' => Roll
  | '.' => Empty
  | invalid => panic! (s!"Can't parse {invalid}, must be @ or .")
  #guard from_char! '@' = .Roll
end CellState

def parse_line(input: String) :=
  (List.map CellState.from_char! input.data).toArray

def parse_input(input: String) :=
  (List.map parse_line (input.splitOn "\n")).toArray

abbrev Grid := Array (Array CellState)

def get_2d?(grid: Grid)(row_idx col_idx: Int): Option CellState := do
  let row_idx ←  row_idx.toNat?
  let col_idx ← col_idx.toNat?
  let row ← grid[row_idx]?
  row[col_idx]?

abbrev GridFn α := Grid → (row_idx: Int) → (col_idx: Int) → CellState → α

def is_accessible(grid:Grid)(row_idx col_idx: Int): Bool :=
  let offsets: List Int  := [-1,0,1]
  let neighbors := offsets.flatMap (fun (row_offset : Int) =>
    offsets.flatMap (fun (col_offset: Int) =>
      if row_offset == 0 && col_offset == 0 then [] else
        match get_2d? grid (row_idx+row_offset) (col_idx+col_offset) with
        | .none => []
        | .some x => [x]
        ))
  neighbors.countP (fun cs => cs = CellState.Roll) < 4

def has_accessible_roll(grid: Grid)(row_idx col_idx: Int): CellState → Bool
| .Empty => false
| .Roll => is_accessible grid row_idx col_idx

def grid_map{α}(fn: GridFn α ) (input: Grid) :=
  input.mapIdx
    (fun row_idx row =>
      row.mapIdx (fun col_idx cell => fn input row_idx col_idx cell))
def count_accessible := Array.count true ∘ Array.flatten ∘ (grid_map has_accessible_roll)

def remove_if_accessible: GridFn CellState
| _, _, _, .Empty => .Empty
| grid, row_idx, col_idx, .Roll =>
  if is_accessible grid row_idx col_idx
  then .Empty else .Roll

def count_rolls: Grid → Nat := Array.count .Roll ∘ Array.flatten

def remove_all_accessible_rolls(grid: Grid)(prev_roll_count: Nat):=
  let new_grid := grid_map remove_if_accessible grid
  let new_roll_count := count_rolls new_grid
  if new_roll_count < prev_roll_count
  then remove_all_accessible_rolls new_grid new_roll_count
  else grid

def count_removable(grid: Grid): Nat :=
  let prev := count_rolls grid
  let new_grid := remove_all_accessible_rolls grid prev
  let post := count_rolls new_grid
  prev - post

def part1 := count_accessible ∘ parse_input
def part2 := count_removable ∘ parse_input
def ex := "..@@.@@@@.
@@@.@.@.@@
@@@@@.@.@@
@.@@@@..@.
@@.@@@@.@@
.@@@@@@@.@
.@.@.@.@@@
@.@@@.@@@@
.@@@@@@@@.
@.@.@@@.@."
#guard part1 ex = 13
#guard part2 ex = 43
