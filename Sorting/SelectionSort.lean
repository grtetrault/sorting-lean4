import Sorting.Basic

universe u
variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/-- Sort a list using the selection sort algorithm. -/
@[grind]
def selectionSort (ls : List α) : List α :=
  match _ : ls.min? with
  | none => []
  | some min => min :: selectionSort (ls.erase min)
  termination_by ls.length
  decreasing_by grind [List.min?_mem]

-- Examples
#eval selectionSort [3, 2, 1, 0]
#eval selectionSort [3, 3, 2, 1]
#eval selectionSort [0, 3, 1, 2]
#eval selectionSort ['C', 'A', 'B']
#eval selectionSort ["hello", "world", "!"]


/-==============================
#                     Theorems
==============================-/

theorem selectionSort_Perm {ls : List α} : (selectionSort ls).Perm ls := by
  match h_min : ls.min? with
  | none => grind [List.min?_eq_none_iff]
  | some min =>
    suffices (min :: selectionSort (ls.erase min)).Perm ls by grind
    rw [List.cons_perm_iff_perm_erase]
    constructor
    · exact List.min?_mem h_min
    · exact selectionSort_Perm
  termination_by ls.length
  decreasing_by grind [List.min?_mem]

theorem selectionSort_isSorted {ls : List α} : isSorted (selectionSort ls) := by
  match h_min : ls.min? with
  | none => grind [List.min?_eq_none_iff]
  | some min =>
    suffices isSorted (min :: selectionSort (ls.erase min)) by grind
    rw [cons_isSorted_iff]
    constructor
    · suffices ∀ (a : α), a ∈ selectionSort (ls.erase min) → min ≤ a by grind
      intro a h_mem
      rw [List.Perm.mem_iff selectionSort_Perm] at h_mem
      by_cases h_eq : a = min <;> grind [List.min?_eq_some_iff]
    · exact selectionSort_isSorted
  termination_by ls.length
  decreasing_by grind [List.min?_mem]


/-==============================
#           Correctness Result
==============================-/

theorem selectionSort_correct {ls : List α}
: isSorted (selectionSort ls) ∧ (selectionSort ls).Perm ls :=
  ⟨selectionSort_isSorted, selectionSort_Perm⟩


variable {α : Type u} [Sortable α]
variable (sort : List α → List α)
