import Std
import Sorting

/-- Test harness parameters. -/
def numTrials  : Nat := 100
def listLength : Nat := 1000
def valueBound : Nat := 1000000

/-- Sorting algorithms to test, along with a display label. -/
def algorithms : List (String × (List Nat → List Nat)) := [
  ("Insertion Sort", insertionSort),
  ("Merge Sort"    , mergeSort),
  ("Quick Sort"    , quickSort),
  ("Selection Sort", selectionSort),
  ("Std Sort"      , stdSort),
]

def randomList (n : Nat) : IO (List Nat) := do
  let mut ls : List Nat := []
  for _ in [:n] do
    ls := (← IO.rand 0 valueBound) :: ls
  return ls

def main : IO Unit := do
  IO.println s!"Benchmarking sorting algorithms..."
  IO.println ""
  IO.println s!"Number of trials : {numTrials}"
  IO.println s!"List length      : {listLength}"
  IO.println s!"List value range : [0, {valueBound}]"
  IO.println ""
  IO.println "Algorithm        Total Runtime  Average Runtime"
  IO.println "---------------  -------------  ---------------"

  -- Generate benchmark data that will be the same for each algorithm.
  let mut benchmarkData : List (List Nat) := []
  for _ in [:numTrials] do
    benchmarkData := (← randomList listLength) :: benchmarkData

  -- For each algorithm, time against all benchmarks and report.
  let mut checksums : List Nat := []
  for (label, sortAlgorithm) in algorithms do
    let start := ← IO.monoNanosNow

    -- Compute a checksum so the compiler cannot discard the sort.
    let sorted := benchmarkData.map sortAlgorithm
    let checksum := ← IO.lazyPure fun _ => sorted.flatten.foldr (· + ·) 0
    checksums := checksum :: checksums

    let stop := ← IO.monoNanosNow

    let totMs : Float := (stop - start).toFloat / 1e6
    let avgMs := totMs / numTrials.toFloat
    IO.print s!"{String.ofList (label.toList.rightpad 15 ' ')}  "
    IO.print s!"{String.ofList (totMs.toString.toList.leftpad 13 ' ')}  "
    IO.print s!"{String.ofList (avgMs.toString.toList.leftpad 15 ' ')}"
    IO.println ""

  -- Make sure checksums are all the same as a sanity check.
  let guard := decide (checksums.Pairwise (· = ·))
  IO.println s!""
  IO.println s!"Checksum guard passed: {guard}"
