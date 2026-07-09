open Std
universe u

/-==============================
#                      Classes
==============================-/

/-- Type class for list element types that are able to be sorted. -/
public class Sortable (α : Type u) extends LE α, IsLinearOrder α where
  decidableLE : DecidableLE α
  decidableEq : DecidableEq α

-- Needed for type inference
public instance {α : Type u} [LE α] [IsLinearOrder α] [DecidableLE α] [DecidableEq α]
: Sortable α where
  decidableLE := by infer_instance
  decidableEq := by infer_instance

public instance {α : Type u} [Sortable α] : DecidableLE α := Sortable.decidableLE
public instance {α : Type u} [Sortable α] : DecidableEq α := Sortable.decidableEq
public instance {α : Type u} [Sortable α] : BEq α := {beq a b := decide (a = b)}
public instance {α : Type u} [Sortable α] : Min α := minOfLe
public instance {α : Type u} [Sortable α] : Max α := maxOfLe
public instance {α : Type u} [Sortable α] : Ord α := {
  compare a b := if a = b then Ordering.eq else if a ≤ b then Ordering.lt else Ordering.gt
}

variable {α : Type u} [Sortable α]


/-==============================
#                  Definitions
==============================-/

/-- Proposition whether a list is sorted. Note that less-than is used to decide sort order. -/
@[grind]
def isSorted : List α → Prop
  | []       => True
  | a :: ls  => ls.all (a ≤ ·) ∧ isSorted ls


/-==============================
#                     Theorems
==============================-/

/--
A list is sorted if and only if:
  1) The first element is less than or equal to all other elements, and,
  2) the remaining elements are sorted.
-/
theorem cons_isSorted_iff {ls : List α} {a : α}
: isSorted (a :: ls) ↔ ls.all (a ≤ ·) ∧ isSorted ls := by grind

/--
A list is sorted if and only if:
  1) The first element is less or equal to than the second element and,
  2) the remaining elements (including the second) are sorted.
-/
theorem cons_isSorted_iff' {ls : List α} {a b : α}
: isSorted (a :: b :: ls) ↔ a ≤ b ∧ isSorted (b :: ls) := by grind

/-- A list is sorted if and only if:
  1) All elements with earlier indices are less than all elements later indices.
-/
theorem pairwise_isSorted_iff {ls : List α} : ls.Pairwise (· ≤ ·) ↔ isSorted ls := by
  induction ls with
  | nil => grind [List.Pairwise.nil]
  | cons a tail h_induct => grind [List.pairwise_cons]

/-- If a list is sorted, the tail of the list is also sorted. -/
theorem tail_isSorted {ls : List α} {a : α} (h_sorted : isSorted (a :: ls))
: isSorted ls := by grind

/-- Merging two sorted lists using the less-than or equal to operator produces a sorted list. -/
theorem merge_isSorted {ls₁ ls₂ : List α} (h_sorted₁ : isSorted ls₁) (h_sorted₂ : isSorted ls₂)
: isSorted (ls₁.merge ls₂ (· ≤ ·)) := by
  induction ls₁ with
  | nil => grind [List.merge_of_le]
  | cons a tail₁ h_induct =>
    match ls₂ with
    | [] => grind [List.merge_of_le]
    | b :: tail₂ =>
      rw [List.cons_merge_cons]
      by_cases h_le : a ≤ b
      · suffices isSorted (a :: tail₁.merge (b :: tail₂) (· ≤ ·)) by grind [Nat.ble_eq]
        grind [List.mem_merge]
      · suffices isSorted (b :: (a :: tail₁).merge tail₂ (· ≤ ·)) by grind [Nat.ble_eq]
        constructor
        · grind [List.mem_merge]
        · exact merge_isSorted h_sorted₁ (tail_isSorted h_sorted₂)

/--
Appending two sorted lists produces a sorted list if and only if
all elements of the first list are less than all elements of the second.
-/
theorem append_isSorted_iff {ls₁ ls₂ : List α} (h_sorted₁ : isSorted ls₁) (h_sorted₂ : isSorted ls₂)
: isSorted (ls₁ ++ ls₂) ↔ (∀ a₁ ∈ ls₁, ∀ a₂ ∈ ls₂, a₁ ≤ a₂) := by
  constructor <;> induction ls₁ with repeat grind
