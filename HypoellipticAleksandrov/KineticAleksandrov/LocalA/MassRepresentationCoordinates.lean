module

public import HypoellipticAleksandrov.Parabolic.KineticClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionJets
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry

/-! # Physical C112 jets in packed evolution coordinates

The packed coordinates have order `(time, velocity, position)`. These lemmas use
the physical slice derivatives directly, without imposing second position derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Evolution
variable {d : ℕ}

/-- Convert a packed native point to the physical `(time, position, velocity)` point. -/
def massPhysicalPoint (x : EvolutionVec d) : KineticPoint d :=
  ⟨timeCoord d x, transportedCoord d x, diffusedCoord d x⟩

/-- The physical unpacking map is continuous. -/
theorem continuous_massPhysicalPoint : Continuous (massPhysicalPoint (d := d)) :=
  TheoremA.continuous_sectionTwoPoint d |>.comp (evolutionHomeomorph d).continuous

private theorem physical_time_line (x : EvolutionVec d) (t : ℝ) :
    massPhysicalPoint (x + t • basisT) =
      ⟨timeCoord d x + t, transportedCoord d x, diffusedCoord d x⟩ := by
  simp [massPhysicalPoint, basisT]

private theorem physical_velocity_line (x : EvolutionVec d) (i : Fin d) (t : ℝ) :
    massPhysicalPoint (x + t • basisV i) =
      ⟨timeCoord d x, transportedCoord d x,
        diffusedCoord d x + t • PDE.basisVec i⟩ := by
  simp [massPhysicalPoint, basisV, PDE.basisVec]

private theorem physical_position_line (x : EvolutionVec d) (i : Fin d) (t : ℝ) :
    massPhysicalPoint (x + t • basisZ i) =
      ⟨timeCoord d x, transportedCoord d x + t • PDE.basisVec i,
        diffusedCoord d x⟩ := by
  simp [massPhysicalPoint, basisZ, PDE.basisVec]

/-- The physical time slice supplies the packed time line derivative. -/
theorem mass_time_hasLineDerivAt {phi : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec d}
    (hx : massPhysicalPoint x ∈ D) :
    HasLineDerivAt ℝ (phi ∘ massPhysicalPoint)
      (kineticTimeDerivative phi (massPhysicalPoint x)) x basisT := by
  have h := (hphi.timeSlice_hasDerivAt hx).comp_of_eq
    (h := fun t : ℝ => timeCoord d x + t) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).const_add (timeCoord d x))
    (by simp [massPhysicalPoint])
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_time_line]
  simpa only [Function.comp_def, mul_one, massPhysicalPoint] using! h

/-- The physical velocity slice supplies each packed diffused line derivative. -/
theorem mass_velocity_hasLineDerivAt {phi : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec d}
    (hx : massPhysicalPoint x ∈ D) (i : Fin d) :
    HasLineDerivAt ℝ (phi ∘ massPhysicalPoint)
      (kineticVelocityGradient phi (massPhysicalPoint x) i) x (basisV i) := by
  have h := ((hphi.velocitySlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_velocity_line]
  exact h

/-- The physical position slice supplies each packed transported line derivative. -/
theorem mass_position_hasLineDerivAt {phi : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec d}
    (hx : massPhysicalPoint x ∈ D) (i : Fin d) :
    HasLineDerivAt ℝ (phi ∘ massPhysicalPoint)
      (kineticPositionGradient phi (massPhysicalPoint x) i) x (basisZ i) := by
  have h := ((hphi.positionSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_position_line]
  exact h

/-- Differentiating a physical velocity gradient entry gives the actual Hessian entry. -/
theorem mass_hessian_hasLineDerivAt {phi : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec d}
    (hx : massPhysicalPoint x ∈ D) (i j : Fin d) :
    HasLineDerivAt ℝ
      (fun y => kineticVelocityGradient phi (massPhysicalPoint y) i)
      (kineticVelocityHessian phi (massPhysicalPoint x) j i) x (basisV j) := by
  let p := massPhysicalPoint x
  let f : PDE.Vec d → ℝ := fun v => phi ⟨p.time, p.position, v⟩
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p.velocity :=
    ((hphi.velocitySlice_contDiffAt hx).fderiv_right (m := 1) (by norm_num))
      |>.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (PDE.classicalGradient f) p.velocity := by
    apply differentiableAt_pi.mpr
    intro k
    exact hd.clm_apply (differentiableAt_const (PDE.basisVec k))
  have h := (hasFDerivAt_pi'.mp hg.hasFDerivAt i).hasLineDerivAt (PDE.basisVec j)
  unfold HasLineDerivAt
  simp only [physical_velocity_line]
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
