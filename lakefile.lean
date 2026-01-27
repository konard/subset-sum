import Lake
open Lake DSL

package «subset-sum» where
  -- Subset Sum formal proofs package

@[default_target]
lean_lib «proofs» where
  globs := #[.submodules `proofs]
  -- Automatically discovers and builds all .lean files in proofs/
