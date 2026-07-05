import Sorting.Basic

universe u
variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/--
Auxiliary function for merge sort;
splits a list into two at the center element or element just prior to the center.
E.g., `splitInTwo [1, 2, 3] == ([1], [2, 3])`
and `splitInTwo [1, 2, 3, 4] == ([1, 2], [3, 4])`.
-/
@[grind]
def splitInTwo (ls : List α) : List α × List α := ls.splitAt (ls.length / 2)

/-- Sort a list using the merge sort algorithm. -/
@[grind]
def mergeSort (ls : List α) : List α :=
  match ls with
  | [] => []
  | [a] => [a]
  | a :: b :: tail =>
    let split := splitInTwo (a :: b :: tail)
    List.merge (mergeSort split.1) (mergeSort split.2) (· ≤ ·)
  termination_by ls.length
  decreasing_by repeat grind

-- Examples
#eval splitInTwo [1, 2, 3, 4] == ([1, 2], [3, 4])
#eval mergeSort [3, 2, 1, 0]
#eval mergeSort [3, 3, 2, 1]
#eval mergeSort [0, 3, 1, 2]
#eval mergeSort ['C', 'A', 'B']
#eval mergeSort ["hello", "world", "!"]


/-==============================
#                     Theorems
==============================-/

theorem mergeSort_Perm {ls : List α} : (mergeSort ls).Perm ls := by
  match  h_eq : ls with
  | [] | [a] => grind
  | a :: b :: tail =>
    let split := splitInTwo (a :: b :: tail)
    have h_induct_fst : (mergeSort split.1).Perm split.1 := mergeSort_Perm
    have h_induct_snd : (mergeSort split.2).Perm split.2 := mergeSort_Perm
    grind [List.take_append_drop, List.merge_perm_append]
  termination_by ls.length
  decreasing_by repeat grind

theorem mergeSort_isSorted {ls : List α} : isSorted (mergeSort ls) := by
  match  h_eq : ls with
  | [] | [a] => grind
  | a :: b :: tail =>
    let split := splitInTwo (a :: b :: tail)
    have h_induct_fst : isSorted (mergeSort split.1) := mergeSort_isSorted
    have h_induct_snd : isSorted (mergeSort split.2) := mergeSort_isSorted
    grind [cons_isSorted_iff, merge_isSorted]
  termination_by ls.length
  decreasing_by repeat grind


/-==============================
#           Correctness Result
==============================-/

theorem mergeSort_correct {ls : List α}
: isSorted (mergeSort ls) ∧ (mergeSort ls).Perm ls :=
  ⟨mergeSort_isSorted, mergeSort_Perm⟩
