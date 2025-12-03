import Day2

def main : List String → IO UInt32 :=
  fun args => do
    -- have args_right_length : PSum (args.length = 1) (args.length ≠ 1) :=
    --   if h : args.length = 1 then PSum.inl h else PSum.inr h
    -- let arg := match args_right_length with
    -- | .inl ok => "hi"
    -- | .inr bad => "bye"
    if h: args.length = 1 then
      let str := args[0]
      let input ← IO.FS.readFile str
      IO.println s!"Part One: {part1 input}"
      IO.println s!"Part Two: {part2 input}"
      return 0
    else
      IO.println "Must provide filepath"
      return 1
