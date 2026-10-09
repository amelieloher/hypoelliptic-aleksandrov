module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Graph

/-!
# The canonical complete `H¹` carrier

The complete quotient-level carrier for `H¹(U)` is not a second graph
construction. It is the `p = 2` specialization of `W1pGraph`, whose value and
gradient components are `L²` equivalence classes satisfying the closed weak
gradient constraints.

`H1Function U` remains the field-name-compatible concrete-representative
interface. A representative-to-graph map belongs to the generic `W^{1,p}`
bridge and is intentionally not duplicated here.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

/-- The canonical complete quotient-level `H¹(U)` carrier. Completeness and
the normed linear structure are inherited definitionally from `W1pGraph U 2`.
-/
abbrev H1Graph {d : ℕ} (U : Set (Vec d)) :=
  W1pGraph U (2 : ℝ≥0∞)

namespace H1Graph

/-- The inherited graph norm is the product maximum, just as for the generic
`W1pGraph` carrier. -/
theorem norm_eq_max {d : ℕ} {U : Set (Vec d)} (v : H1Graph U) :
    ‖v‖ = max ‖v.1.1‖ ‖v.1.2‖ :=
  W1pGraph.norm_eq_max v

end H1Graph

end PDE
