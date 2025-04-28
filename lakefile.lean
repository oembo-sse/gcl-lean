import Lake
open Lake DSL

package «gcl» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.53"

@[default_target]
lean_lib «Gcl» where
  -- add any library configuration options here

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
