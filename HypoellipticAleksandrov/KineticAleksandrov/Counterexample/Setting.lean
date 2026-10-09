module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry

/-!
# Initial and full lateral boundary for Appendix C

Unlike `kineticBoundary`, this includes the entire relative-position sphere.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Initial face and full lateral boundary of an open backward kinetic cylinder. -/
def initialFullLateralBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    Set (KineticPoint d) :=
  closure (backwardCylinder P₀ R) ∩
    ({P | P.time = P₀.time - R ^ 2} ∪
      {P | P.velocity ∈ PDE.euclideanSphere P₀.velocity R} ∪
      {P | relativePosition P₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d) (R ^ 3)})

end HypoellipticAleksandrov.KineticAleksandrov
