instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | Except.error e1, Except.error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro eq; injection eq; contradiction)
  | Except.ok a1, Except.ok a2 =>
    match decEq a1 a2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro eq; injection eq; contradiction)
  | Except.error _, Except.ok _ => isFalse (by intro eq; contradiction)
  | Except.ok _, Except.error _ => isFalse (by intro eq; contradiction)

def snoc {α : Type} (list : List α) (element : α) : List α :=
  match list with
  | [] => [element]
  | head :: tail => head :: (snoc tail element)
#guard snoc [] 1 = [1]
#guard snoc [1] 2 = [1,2]
#guard snoc [5,4] 3 = [5,4,3]
#guard snoc [5,4,2,1] 3 = [5,4,2,1,3]

def snoc_len_gt_0 : ∀ (l: List α) (x: α), (snoc l x).length > 0
| [] => by intros; rw [snoc]; simp
| hd :: tl => by intros; rw [snoc]; simp
