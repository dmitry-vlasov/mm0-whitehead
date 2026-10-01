/-
Tests for `import` resolution, on the small files in `tests/fixtures/imports`.
The tests are run from the package root, as `lake test` does.
-/
import Whitehead.Mm0.Load
import Whitehead.Mm0.Print
import Tests.Harness

open Whitehead.Mm0

namespace Tests.Mm0

def importFixtures : System.FilePath := "tests/fixtures/imports"

/-- The joined specification of `file` prints as `expected`. -/
def joinsAs (name file expected : String) : TestM Unit := do
  match ← load (importFixtures / file) with
  | .ok spec => checkEq name (printStmts (spec.stmts.map (·.stmt))) expected
  | .error e => check name false e.format

/-- Loading `file` fails, and the formatted error contains every one of `parts`. -/
def loadFails (name file : String) (parts : List String) : TestM Unit := do
  match ← load (importFixtures / file) with
  | .ok _ => check name false "loaded without error"
  | .error e => check name (parts.all (contains e.format ·)) e.format

def loadTests : TestM Unit := do
  joinsAs "import: no imports" "base.mm0" "sort base;\n"
  -- main imports left and sub/right; both import base, which is included once
  joinsAs "import: diamond, with a path relative to a subdirectory" "main.mm0"
    "sort base;\nsort left;\nsort right;\nsort main;\n"
  joinsAs "import: in the middle of a file" "mid.mm0" "sort a;\nsort base;\nsort b;\n"
  joinsAs "import: the same file twice" "twice.mm0" "sort base;\nsort t;\n"
  match ← load (importFixtures / "main.mm0") with
  | .error e => check "import: statements know their file" false e.format
  | .ok spec =>
    checkEq "import: each file is read once" spec.sources.size 4
    checkEq "import: statements know their file"
      (spec.stmts.toList.map fun s => (spec.sources[s.file]!.path.fileName.getD ""))
      ["base.mm0", "left.mm0", "right.mm0", "main.mm0"]
  loadFails "import: cycle through the root" "cycle_a.mm0"
    ["cycle_b.mm0:1:8", "import cycle", "cycle_a.mm0 -> ", "cycle_b.mm0 -> "]
  loadFails "import: a file importing itself" "self.mm0" ["self.mm0:1:8", "import cycle"]
  loadFails "import: missing file, reported at the import" "missing.mm0"
    ["missing.mm0:2:8", "cannot read the imported file \"nope.mm0\""]
  loadFails "import: parse error inside an imported file" "bad_child.mm0"
    ["broken.mm0:2:6", "expected a sort name"]
  loadFails "import: missing root file" "no_such_file.mm0" ["no_such_file.mm0", "cannot read"]

end Tests.Mm0
