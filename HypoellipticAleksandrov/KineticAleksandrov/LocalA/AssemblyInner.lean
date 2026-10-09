module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothLocalStatement
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsReflection
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelDerivativeLimit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelHolderLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry

/-! # Transfer of the joint estimate on a fixed compact interior cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Filter Metric Holder
open scoped Topology Matrix.Norms.Elementwise

/-- The data-dependent part of the authorized smooth joint estimate. -/
def SmoothEstimateFor {d : ℕ} (lam Lam : ℝ) (C_m : ℕ → ℝ) (C α : ℝ) : Prop :=
  ∀ A : CoefficientField d, IsSmoothCoefficient A → IsSymmetricCoefficient A →
    HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
  ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R → ∀ u : KineticPoint d → ℝ,
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
    (∀ P ∈ backwardCylinder P₀ R,
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
    (∀ m, 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
      R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
        C_m m * Holder.oscillationOn u (backwardCylinder P₀ R)) ∧
    (∀ P ∈ backwardCylinder P₀ (R / 2), ∀ Q ∈ backwardCylinder P₀ (R / 2),
      |u P - u Q| ≤ C * Holder.oscillationOn u (backwardCylinder P₀ R) *
        (kineticIncrement P₀ P Q / R) ^ α)

/-- Correctors recover smoothness and quantitative estimates on a fixed inner cylinder. -/
theorem borel_inner_joint_estimates
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (C_m : ℕ → ℝ) (hCm : ∀ m, 0 ≤ C_m m) (C α : ℝ)
    (hest : SmoothEstimateFor (d := d) lam Lam C_m C α)
    (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticityAE lam A)
    (hhi : HasUpperEllipticityAE Lam A)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u (backwardCylinder P₀ R))
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hKD : closure (backwardCylinder P₁ r) ⊆ backwardCylinder P₀ R) :
    (∀ P ∈ backwardCylinder P₁ (3 * r / 4),
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position ∧
      ∀ m, 1 ≤ m → r ^ (3 * m) *
        ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
          C_m m * Holder.oscillationOn u (backwardCylinder P₁ r)) ∧
    (∀ P ∈ backwardCylinder P₁ (r / 2), ∀ Q ∈ backwardCylinder P₁ (r / 2),
      |u P - u Q| ≤ C * Holder.oscillationOn u (backwardCylinder P₁ r) *
        (kineticIncrement P₁ P Q / r) ^ α) := by
  let E := backwardCylinder P₁ r
  have hK := isCompact_closure_backwardCylinder P₁ r hr
  have huc := hu.continuousOn.mono hKD
  obtain ⟨B, w, O, hO, hKO, hB, hw, hew, ht⟩ :=
    exists_backward_homogeneous_correctors hH hLE hd lam Lam hlam hLam A hA hs hlo hhi
      P₀ R hR u hu he (closure E) hK hKD
  have hEO : E ⊆ O := subset_closure.trans hKO
  have heQ j : ∀ᵐ P ∂volume.restrict E,
      backwardOperatorOfTimeVelocityCoefficient (B j) (w j) P = 0 := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₁ r hr).measurableSet]
      with P hP
    exact hew j P (hEO hP)
  have hestj j := hest (B j) (hB j).1 (hB j).2.1 (hB j).2.2.1 (hB j).2.2.2
    P₁ r hr (w j) ((hw j).continuousOn.mono hKO)
    (comparison_regular_mono (hw j) hEO)
    (heQ j)
  have hne : E.Nonempty := backwardCylinder_nonempty P₁ hr
  have hab : BddAbove (u '' E) := (hK.bddAbove_image huc).mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := (hK.bddBelow_image huc).mono (image_mono subset_closure)
  have hos := corrector_oscillation_tendsto hne hab hbb (ht.mono subset_closure)
  have hos0 := Holder.oscillationOn_nonneg hne hab hbb
  have h34 : backwardCylinder P₁ (3 * r / 4) ⊆ E :=
    Holder.backwardCylinder_radius_mono P₁ (by positivity) (by linarith)
  have h12 : backwardCylinder P₁ (r / 2) ⊆ E :=
    Holder.backwardCylinder_radius_mono P₁ (by positivity) (by linarith)
  refine ⟨?_, ?_⟩
  · intro P hP
    let s := fun x : PDE.Vec d => (⟨P.time, x, P.velocity⟩ : KineticPoint d)
    have hsc : Continuous s := KineticPoint.continuous_mk continuous_const continuous_id
      continuous_const
    have hpre := (isOpen_backwardCylinder P₁ (3 * r / 4) (by positivity)).preimage hsc
    have hPin : P.position ∈ s ⁻¹' backwardCylinder P₁ (3 * r / 4) := hP
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hpre.mem_nhds hPin)
    have hsq : closedBall P.position ρ ⊆ s ⁻¹' closure E :=
      fun x hx => subset_closure (h34 (hball hx))
    have hfs j x hx := (hestj j).1 (s x) (h34 (hball hx))
    have hconv : TendstoUniformlyOn (fun j => physicalPositionSlice (w j) P)
        (physicalPositionSlice u P) atTop (closedBall P.position ρ) := (ht.comp s).mono hsq
    have hcont : ContinuousOn (physicalPositionSlice u P) (closedBall P.position ρ) :=
      huc.comp hsc.continuousOn hsq
    let b := fun m => C_m m / r ^ (3 * m)
    have hb m : 0 ≤ b m := div_nonneg (hCm m) (pow_pos hr _).le
    have hbounds : ∀ j m, 1 ≤ m → ∀ x ∈ closedBall P.position ρ,
        ‖iteratedFDeriv ℝ m (physicalPositionSlice (w j) P) x‖ ≤
          b m * Holder.oscillationOn (w j) E := by
      intro j m hm x hx
      have hh := (hestj j).2.1 m hm (s x) (hball hx)
      have hp : 0 < r ^ (3 * m) := pow_pos hr _
      change r ^ (3 * m) * ‖iteratedFDeriv ℝ m
        (physicalPositionSlice (w j) P) x‖ ≤ C_m m * Holder.oscillationOn (w j) E at hh
      have hh' : ‖iteratedFDeriv ℝ m (physicalPositionSlice (w j) P) x‖ ≤
          (C_m m * Holder.oscillationOn (w j) E) / r ^ (3 * m) :=
        (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
      convert hh' using 1; dsimp only [b]; ring
    obtain ⟨hsp, hbd⟩ := corrector_derivative_estimates
      (fun j => physicalPositionSlice (w j) P) (physicalPositionSlice u P)
      P.position ρ hρ hfs hconv hcont b hb
      (fun j => Holder.oscillationOn (w j) E) (Holder.oscillationOn u E) hos0 hos hbounds
    refine ⟨hsp, fun m hm => ?_⟩
    have hh := hbd m hm
    have hp : 0 < r ^ (3 * m) := pow_pos hr _
    have hh' := mul_le_mul_of_nonneg_left hh hp.le
    convert hh' using 1
    dsimp only [b, E]
    field_simp
  · apply corrector_holder_limit ((ht.mono subset_closure).mono h12) hos P₁
    intro j P hP Q hQ
    exact (hestj j).2.2 P hP Q hQ

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
