import Day5.Util

def parse_simple! (s: String): (List (Nat × Nat)) × List Nat :=
    let s := s.splitOn "\n\n"
    let ranges := s[0]!.splitOn "\n"
    let ranges := ranges.map (fun v =>
        let items := v.splitOn "-"
        (items[0]!.toNat!, items[1]!.toNat!)
        )
    let ingredients := s[1]!.splitOn "\n"
    (ranges, ingredients.map String.toNat!)

def consolidate_ranges(l: List (Nat × Nat)): List (Nat × Nat ):=
    let l := l.mergeSort (fun (s1,_) (s2,_) => s1 ≤ s2)
    l.foldl (fun (prev:List (Nat × Nat)) (cur_start, cur_end) =>
        if h: prev ≠ []
        then let (prev_start, prev_end) := prev.getLast h
            if cur_start ≤ prev_end + 1 then if prev_end < cur_end
            then snoc prev.dropLast (prev_start, cur_end) -- cur extends prev
            else prev -- cur is embedded within prev
            else snoc prev (cur_start, cur_end)
        else snoc prev (cur_start, cur_end)
    ) ([]: List (Nat × Nat))
#guard consolidate_ranges [(5,10),(4,50)] == [(4,50)]
#guard consolidate_ranges [(3,4),(4,9)] == [(3,9)]
#guard consolidate_ranges [(4,9),(3,4)] == [(3,9)]
#guard consolidate_ranges [(4,9),(3,4),(9,15),(100,300)] == [(3,15),(100,300)]
#guard consolidate_ranges [(5,9),(3,4),(9,15),(100,300)] == [(3,15),(100,300)]


def in_range(range: Nat × Nat)(needle: Nat):= let (s,e) := range; s≤ needle && e ≥ needle

def check_if_in_ranges(haystack: List (Nat × Nat))(needle: Nat):Bool :=
    let l := haystack.length
    match (generalizing := false) _: l with
    | 0 => false
    | 1 => in_range haystack[0] needle
    | _ + 2 =>
        let midpoint := l /2
        have _: midpoint < haystack.length := by grind
        let (low, high) := haystack[midpoint]
        if needle < low
        then check_if_in_ranges (haystack.take midpoint) needle
        else check_if_in_ranges (haystack.drop midpoint) needle
termination_by haystack.length

#guard check_if_in_ranges [(1, 5),(6,20)] 19 == true
#guard check_if_in_ranges [(1, 5),(6,20)] 139 == false
#guard check_if_in_ranges [(3,4)] 4 == true
#guard check_if_in_ranges [(3,4)] 3 == true
#guard check_if_in_ranges [(3,4),(8,9)] 3 == true
#guard check_if_in_ranges [(3,4),(8,9)] 8 == true
#guard check_if_in_ranges [(3,4),(8,9)] 9 == true
#guard check_if_in_ranges [(3,4),(8,9)] 4 == true



def part1(input: String):=
    let (fresh_ranges, items) := parse_simple! input
    let fresh_ranges := consolidate_ranges fresh_ranges
    let fresh := items.filter (fun i => check_if_in_ranges fresh_ranges i)
    fresh.length

def ex:= "3-5
10-14
16-20
12-18

1
5
8
11
17
32"

#guard part1 ex = 3

def part2(input:String) :=
    let (fresh_ranges, _) := parse_simple! input
    let fresh_ranges := consolidate_ranges fresh_ranges
    let range_cts: List Nat := fresh_ranges.map (fun (low, high) => high-low+1)
    range_cts.sum

#guard part2 ex = 14
