import Lake
open Lake DSL

package «group» where
  -- add package configuration options here
@[default_target]
lean_lib «Group» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
