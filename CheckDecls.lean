/-
Blueprint declaration checker

This script checks that all Lean declarations listed in a file exist in the
compiled Lean environment.

Usage: lake exe checkdecls <path-to-declaration-list>
-/

import Lean
import ChebyshevCircles

open Lean

/-- Main entry point for the checkdecls executable -/
unsafe def main (args : List String) : IO UInt32 := do
  -- Check arguments
  unless args.length == 1 do
    IO.eprintln "Usage: lake exe checkdecls <declaration-file>"
    IO.eprintln "Checks that all declarations listed in the file exist."
    return 1

  let filename : System.FilePath := args[0]!

  -- Check file exists
  unless ← filename.pathExists do
    IO.eprintln s!"Error: Could not find declaration list file: {filename}"
    return 1

  -- Initialize search path for finding compiled modules
  initSearchPath (← findSysroot)

  -- Get the current environment (all imported modules)
  let env ← importModules
    #[{ module := `ChebyshevCircles : Import }]
    {}
    0

  -- Read declaration list and check each one
  let mut allFound := true
  let mut checkedCount := 0

  for line in ← IO.FS.lines filename do
    let declName := line.trim
    -- Skip empty lines
    if declName.isEmpty then
      continue

    checkedCount := checkedCount + 1
    let name := declName.toName

    if env.contains name then
      IO.println s!"✓ {declName}"
    else
      IO.eprintln s!"✗ {declName} - NOT FOUND"
      allFound := false

  IO.println s!"\nChecked {checkedCount} declarations"

  if allFound then
    IO.println "✓ All declarations found!"
    return 0
  else
    IO.eprintln "✗ Some declarations are missing"
    return 1
