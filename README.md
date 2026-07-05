# Sorting in Lean4

This repo contains implementations of several classic sorting algorithms in Lean4, along with proofs of their correctness. Sorting algorithms implemented include [insertion sort](./Sorting/InsertionSort.lean),
[merge sort](./Sorting/MergeSort.lean),
[quick sort](./Sorting/QuickSort.lean), and
[selection sort](./Sorting/SelectionSort.lean).

## Correctness

A sorting algorithm is correct if and only if the result is both sorted and a permutation of the input list. In Lean4, we've chosen to define the sorted proposition recursively as:
```lean
def isSorted : List α → Prop
  | []       => True
  | a :: ls  => ls.all (a ≤ ·) ∧ isSorted ls
```
That is, a list is sorted if it is empty, or, if the first element is minimal and the remaining elements are sorted. Using this, the correctness of a sorting algorithm `sort : List α → List α` can be defined as:

```lean
theorem sort_correct {ls : List α}
: isSorted (sort ls) ∧ (sort ls).Perm ls := by sorry
```

Each sorting algorithm implementation has a corresponding correctness theorem in this manner.

## Grind tactic

The proofs here make liberal use of the `grind` tactic, a tool to automatically construct proofs. I like to think of using `grind` where a textbook would leave a proof "for the reader". The tactic is very capable and, in several cases, can reduce proofs to one-line `by grind` statements. For more complex proofs, what is left is typically the "structural" parts of the proof - e.g., induction clauses, goal reduction, and case splitting. I generally find these easier to read, however quite a bit of detail is obfuscated; in cases where reading alone isn't clear, replacing usage with `grind?` gives a readout of what theorems are used behind the scenes.

Definitions across the repo (e.g., the sorted proposition and algorithm implementations) are annotated with `@[grind]` to register automated use with `grind`, cutting down on what we have to supply to the tactic.

## Further reading

- [The grind tactic](https://lean-lang.org/doc/reference/4.32.0-rc1/The--grind--tactic/#grind-tactic): Lean4 language reference page on the `grind` tactic.
- [Proving the Correctness of Insertion Sort in Lean4](https://jamesoswald.dev/posts/lean4-insertion-sort/): Blog post by James Oswald going through the correctness proof of insertion sort without the use of `grind`.
