import Day5

def main : List String → IO UInt32 :=
  fun args => do
    if h: args.length = 1 then
      let str := args[0]
      let input ← IO.FS.readFile str
      IO.println s!"Part One: {part1 input}"
      IO.println s!"Part Two: {part2 input}"
      return 0
    else
      IO.println "Must provide filepath"
      return 1
