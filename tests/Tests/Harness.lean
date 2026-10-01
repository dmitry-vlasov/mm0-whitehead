/-
A minimal test harness: checks are counted, failures are printed as they happen, and
the driver exits non-zero if any check failed.
-/
namespace Tests

structure Stats where
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0

abbrev TestM := StateT Stats IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit := do
  if ok then
    modify fun s => { s with passed := s.passed + 1 }
  else
    modify fun s => { s with failed := s.failed + 1 }
    IO.eprintln s!"FAIL {name}{if detail.isEmpty then "" else "\n  " ++ detail}"

def checkEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) :
    TestM Unit :=
  check name (actual == expected) s!"expected: {expected}\n  actual:   {actual}"

/-- Records that a group of checks could not run, and says why. -/
def skip (name reason : String) : TestM Unit := do
  modify fun s => { s with skipped := s.skipped + 1 }
  IO.println s!"SKIP {name}: {reason}"

/-- True if `part` occurs somewhere in `s`. -/
def contains (s part : String) : Bool :=
  (s.splitOn part).length > 1

end Tests
