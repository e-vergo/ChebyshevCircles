import Lake
open Lake DSL

package ChebyshevCircles where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩
  ]
  moreLeanArgs := #["-DmaxSynthPendingDepth=3"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib ChebyshevCircles where
  -- Library sources

-- Blueprint declaration checker executable
lean_exe checkdecls where
  root := `CheckDecls
  supportInterpreter := true
