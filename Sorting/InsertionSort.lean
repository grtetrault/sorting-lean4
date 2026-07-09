import Sorting.Basic

universe u
variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/--
Auxiliary function for insertion sort;
inserts a value into a list just before the first element that is less than or equal.
E.g., `insertBeforeLE [2, 1, 4] 3 == [2, 1, 3, 4]`.
-/
@[grind]
private def insertBeforeLE (ls : List α) (a : α) : List α :=
  ls.insertIdx (ls.findIdx (a ≤ ·)) a

/-- Sort a list using the insertion sort algorithm. -/
@[grind]
def insertionSort : List α → List α
  | [] => []
  | a :: ls => insertBeforeLE (insertionSort ls) a

-- Examples
#eval insertionSort [3, 2, 1, 0]
#eval insertionSort [3, 3, 2, 1]
#eval insertionSort [0, 3, 1, 2]
#eval insertionSort ['C', 'A', 'B']
#eval insertionSort ["hello", "world", "!"]


/-==============================
#                     Theorems
==============================-/

theorem insertionSort_Perm {ls : List α} : (insertionSort ls).Perm ls := by
  induction ls with
  | nil => trivial
  | cons b tail h_induct => grind [List.perm_insertIdx]

private theorem insertBeforeLE_isSorted {ls : List α} {a : α} (h_sorted : isSorted ls)
: isSorted (insertBeforeLE ls a) := by
  induction ls with
  | nil => trivial
  | cons b tail h_induct => grind [List.perm_insertIdx]

theorem insertionSort_isSorted {ls : List α} : isSorted (insertionSort ls) := by
  induction ls with
  | nil => trivial
  | cons a tail h_induct =>
    unfold insertionSort
    exact insertBeforeLE_isSorted h_induct


/-==============================
#           Correctness Result
==============================-/

theorem insertionSort_correct {ls : List α}
: isSorted (insertionSort ls) ∧ (insertionSort ls).Perm ls :=
  ⟨insertionSort_isSorted, insertionSort_Perm⟩
