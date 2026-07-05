import Sorting.Basic

universe u
variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/-- Sort a list using the insertion quick algorithm. -/
@[grind]
def quickSort (ls : List α) : List α :=
  match ls with
  | [] => []
  | [a] => [a]
  | a :: b :: tail =>
    let parts := (b :: tail).partition (· ≤ a)
    (quickSort parts.1) ++ [a] ++ (quickSort parts.2)
  termination_by ls.length
  decreasing_by repeat grind

-- Examples
#eval quickSort [3, 2, 1, 0]
#eval quickSort [3, 3, 2, 1]
#eval quickSort [0, 3, 1, 2]
#eval quickSort ['C', 'A', 'B']
#eval quickSort ["hello", "world", "!"]


/-==============================
#                     Theorems
==============================-/

theorem quickSort_Perm {ls : List α} : (quickSort ls).Perm ls := by
  match h_eq : ls with
  | [] | [a] => grind
  | a :: b :: tail =>
    let parts := (b :: tail).partition (· ≤ a)
    have h_induct_fst : (quickSort parts.1).Perm parts.1 := quickSort_Perm
    have h_induct_snd : (quickSort parts.2).Perm parts.2 := quickSort_Perm
    grind [List.perm_cons_append_cons, List.filter_append_perm]
  termination_by ls.length
  decreasing_by repeat grind

theorem quickSort_isSorted {ls : List α} : isSorted (quickSort ls) := by
  match h_eq : ls with
  | [] | [a] => grind
  | a :: b :: tail =>
    let parts := (b :: tail).partition (· ≤ a)
    have h_induct_fst : isSorted (quickSort parts.1) := quickSort_isSorted
    have h_induct_snd : isSorted (quickSort parts.2) := quickSort_isSorted
    grind [quickSort_Perm, append_isSorted_iff]
  termination_by ls.length
  decreasing_by repeat grind


/-==============================
#           Correctness Result
==============================-/

theorem quickSort_correct {ls : List α}
: isSorted (quickSort ls) ∧ (quickSort ls).Perm ls :=
  ⟨quickSort_isSorted, quickSort_Perm⟩
