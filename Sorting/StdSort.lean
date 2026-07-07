import Sorting.Basic

universe u
variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/-- Sort a list using the standard libarry merge sort algorithm. -/
@[grind]
def stdSort (ls : List α) : List α := ls.mergeSort

-- Examples
#eval stdSort [3, 2, 1, 0]
#eval stdSort [3, 3, 2, 1]
#eval stdSort [0, 3, 1, 2]
#eval stdSort ['C', 'A', 'B']
#eval stdSort ["hello", "world", "!"]


/-==============================
#                     Theorems
==============================-/

theorem stdSort_Perm {ls : List α} : (stdSort ls).Perm ls := by
  grind [List.mergeSort_perm]

theorem stdSort_isSorted {ls : List α} : isSorted (stdSort ls) := by
  rw [←pairwise_isSorted_iff]
  grind [List.pairwise_mergeSort]


/-==============================
#           Correctness Result
==============================-/

theorem stdSort_correct {ls : List α}
: isSorted (stdSort ls) ∧ (stdSort ls).Perm ls :=
  ⟨stdSort_isSorted, stdSort_Perm⟩
