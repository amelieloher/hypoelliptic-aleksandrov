module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.EuclideanBall

/-!
# Ambient Euclidean geometry

`PDE.Vec d` inherits the finite-product supremum norm and its associated
metric. That inherited norm and metric cannot be used as the manuscript's
round Euclidean geometry; this module instead exposes the sibling project's
explicit Euclidean dot product, norm, balls, closed balls, and spheres.
-/

@[expose] public section
