module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionJets
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry

/-! # Physical C112 jets in packed evolution coordinates

The packed coordinates have order `(time, velocity, position)`. These lemmas use
the physical slice derivatives directly, without imposing second position derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution

/-- Convert a packed native point to the physical `(time, position, velocity)` point. -/
def reconstructionPhysicalPoint (x : EvolutionVec 1) : Point :=
  ⟨timeCoord 1 x, transportedCoord 1 x, diffusedCoord 1 x⟩

/-- The physical unpacking map is continuous. -/
theorem continuous_reconstructionPhysicalPoint : Continuous reconstructionPhysicalPoint :=
  TheoremA.continuous_sectionTwoPoint 1 |>.comp (evolutionHomeomorph 1).continuous

private theorem physical_time_line (x : EvolutionVec 1) (t : ℝ) :
    reconstructionPhysicalPoint (x + t • basisT) =
      ⟨timeCoord 1 x + t, transportedCoord 1 x, diffusedCoord 1 x⟩ := by
  simp [reconstructionPhysicalPoint, basisT]

private theorem physical_velocity_line (x : EvolutionVec 1) (i : Fin 1) (t : ℝ) :
    reconstructionPhysicalPoint (x + t • basisV i) =
      ⟨timeCoord 1 x, transportedCoord 1 x,
        diffusedCoord 1 x + t • PDE.basisVec i⟩ := by
  simp [reconstructionPhysicalPoint, basisV, PDE.basisVec]

private theorem physical_position_line (x : EvolutionVec 1) (i : Fin 1) (t : ℝ) :
    reconstructionPhysicalPoint (x + t • basisZ i) =
      ⟨timeCoord 1 x, transportedCoord 1 x + t • PDE.basisVec i,
        diffusedCoord 1 x⟩ := by
  simp [reconstructionPhysicalPoint, basisZ, PDE.basisVec]

/-- The physical time slice supplies the packed time line derivative. -/
theorem reconstruction_time_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticTimeDerivative phi (reconstructionPhysicalPoint x)) x basisT := by
  have h := (hphi.timeSlice_hasDerivAt hx).comp_of_eq
    (h := fun t : ℝ => timeCoord 1 x + t) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).const_add (timeCoord 1 x))
    (by simp [reconstructionPhysicalPoint])
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_time_line]
  simpa only [Function.comp_def, mul_one, reconstructionPhysicalPoint] using! h

/-- The physical velocity slice supplies each packed diffused line derivative. -/
theorem reconstruction_velocity_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i : Fin 1) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticVelocityGradient phi (reconstructionPhysicalPoint x) i) x (basisV i) := by
  have h := ((hphi.velocitySlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_velocity_line]
  exact h

/-- The physical position slice supplies each packed transported line derivative. -/
theorem reconstruction_position_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i : Fin 1) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticPositionGradient phi (reconstructionPhysicalPoint x) i) x (basisZ i) := by
  have h := ((hphi.positionSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_position_line]
  exact h

/-- Differentiating a physical velocity gradient entry gives the actual Hessian entry. -/
theorem reconstruction_hessian_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i j : Fin 1) :
    HasLineDerivAt ℝ
      (fun y => kineticVelocityGradient phi (reconstructionPhysicalPoint y) i)
      (kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i) x (basisV j) := by
  let p := reconstructionPhysicalPoint x
  let f : PDE.Vec 1 → ℝ := fun v => phi ⟨p.time, p.position, v⟩
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

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
