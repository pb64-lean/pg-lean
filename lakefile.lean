import Lake
open Lake DSL

/-!
# lakefile.lean — IDE project model only.

Bazel owns the real build and tests in this repository; Lake exists so that
`lake serve` / editors resolve imports like `Pg.Protocol.Message` from the
repo root.

Use Bazel for validation:

  bazel test //...
-/

package «pg-lean» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «tls13-lean» from "../tls13-lean"

lean_lib «Pg» where
  srcDir := "."
  roots := #[`Pg]
