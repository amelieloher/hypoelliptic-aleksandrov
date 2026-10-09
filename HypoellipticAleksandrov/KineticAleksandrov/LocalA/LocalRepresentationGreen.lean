module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationBounds
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportTransition

/-! # The local position cutoff defect has zero actual Green integral -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo TheoremA
open scoped Topology

/-- A cutoff constant on a position ball has zero transport defect inside that ball. -/
theorem localCutoffTransport_zero_of_one {d : ℕ} (Z₀ P : KineticPoint d)
    (χ : PDE.Vec d → ℝ) {r : ℝ}
    (hχ : ∀ x ∈ PDE.euclideanClosedBall 0 r, χ x = 1)
    (hx : relativePosition Z₀ P ∈ PDE.euclideanBall 0 r) :
    localCutoffTransport Z₀ χ P = 0 := by
  have he : χ =ᶠ[𝓝 (relativePosition Z₀ P)] (fun _ => (1 : ℝ)) := by
    filter_upwards [(PDE.isOpen_euclideanBall 0 r).mem_nhds hx] with x hx'
    exact hχ x (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx')
  rw [localCutoffTransport, he.fderiv_eq, fderiv_const_apply, zero_apply]

/-- The exact cutoff interior ball contains the reached cone, with a strict margin. -/
theorem local_cone_cutoff_mem {d : ℕ} (Z₀ P Q : KineticPoint d)
    {R : ℝ} (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (htlo : P.time ≤ Q.time) (hthi : Q.time ≤ P.time + R ^ 2 / 8)
    (hcone : PDE.vecEuclideanNorm
      (Q.position - P.position - (Q.time - P.time) • Z₀.velocity) ≤
        R * (Q.time - P.time)) :
    relativePosition Z₀ Q ∈ PDE.euclideanBall 0 ((3 / 4 : ℝ) * R ^ 3) := by
  have hmargin := (local_cone_margins Z₀ P Q hR hP htlo hthi hcone).2.2
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
  simp only [sub_zero]
  nlinarith only [hmargin, pow_pos hR 3]

/-- The actual killed Green potential vanishes for the cutoff defect outside its cone. -/
theorem ballSourcePotential_local_cutoff_zero
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart Z₀.velocity R)
    (hP : P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (T : {t : ℝ // P.1.time < t}) (hT : T.1 - P.1.time = R ^ 2 / 8)
    (χ : PDE.Vec d → ℝ)
    (hχ : ∀ x ∈ PDE.euclideanClosedBall 0 ((3 / 4 : ℝ) * R ^ 3), χ x = 1)
    (u : KineticPoint d → ℝ) :
    ballSourcePotential hH hLE hd hlam hLam B hB Z₀.velocity hR P.1.time T.1
      ((localStrip P.1.time T.1 Z₀.velocity R).indicator
        (fun Q => localCutoffTransport Z₀ χ Q * u Q)) P.1 = 0 := by
  classical
  unfold ballSourcePotential duhamelPotential
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro r hr
  have hvalid : (sectionTwoPoint P.1).time ≤ r ∧
      (sectionTwoPoint P.1).position ∈
        movingDomain (PDE.euclideanBall Z₀.velocity R) (fun _ => 0)
          (sectionTwoPoint P.1).time := by
    exact ⟨hr.1.le, (movingDomain_ball_zero _ _ _).symm ▸ P.2⟩
  rw [duhamelIntegrand, dite_eq_left hvalid]
  change (∫ w, (localStrip P.1.time T.1 Z₀.velocity R).indicator
    ((localStrip P.1.time T.1 Z₀.velocity R).indicator
      (fun Q => localCutoffTransport Z₀ χ Q * u Q))
        (⟨r, w.2, w.1⟩ : KineticPoint d)
    ∂ballTransition hH hLE hd hlam hLam B hB Z₀.velocity hR P ⟨r, hr.1⟩) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [ballTransition_cone hH hLE hd hlam hLam B hB Z₀.velocity hR
    P ⟨r, hr.1⟩] with w hw
  have ht : r ≤ P.1.time + R ^ 2 / 8 := by linarith only [hr.2, hT]
  have hx := local_cone_cutoff_mem Z₀ P.1 ⟨r, w.2, w.1⟩ hR hP hr.1.le ht hw
  have hz := localCutoffTransport_zero_of_one Z₀ ⟨r, w.2, w.1⟩ χ hχ hx
  by_cases hmem : (⟨r, w.2, w.1⟩ : KineticPoint d) ∈
      localStrip P.1.time T.1 Z₀.velocity R
  · rw [indicator_of_mem hmem, indicator_of_mem hmem, hz, zero_mul]
    rfl
  · rw [indicator_of_notMem hmem]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
