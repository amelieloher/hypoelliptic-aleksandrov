module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ParameterChoice
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullThreshold
import Mathlib.Tactic

/-! # Coherent choices of near-full threshold, stack height, positivity and reference scale -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory

/-- The same near-full threshold determines the contractive height and both positivity steps.
The gain `c` is the dimension-only gain supplied by the internally proved ink-spots theorem. -/
theorem exists_joint_growth_parameters (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∃ (eta : ℝ) (m : ℕ) (delta eps : ℝ),
      0 < eta ∧ eta < 1 ∧ 0 < m ∧
      0 < (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) ∧
      (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) < 1 ∧
      0 < delta ∧ delta < 1 ∧ 0 < eps ∧ eps < 1 ∧
      kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps ''
        referenceRegion d m (referenceBound m) ⊆
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
      closure (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' samplingCylinder d m) ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
      (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
        ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
        ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 r) ⊆ O →
        ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
          IsAdmissibleSupersolution A O p C_A u →
          (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
            (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
          ∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) ∧
      (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
        ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
        ∀ O : Set (KineticPoint d), IsOpen O →
          closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
        ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
          IsAdmissibleSupersolution A O p C_A u →
          (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
            (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
          ∀ Z ∈ forwardStack P0 r m, delta * ell ≤ u Z) := by
  obtain ⟨eta, heta, heta1, hnear⟩ := near_full_threshold d hd Lam p C_A hp
  obtain ⟨m, hm, ha, ha1⟩ := exists_contractive_stack_height hc hc1 heta heta1
  obtain ⟨delta, hdelta, hdelta1, hstack⟩ :=
    exists_stack_positivity_constant d hd lam Lam hlam hLam m
  obtain ⟨eps, heps, heps1, _, _, _, _, hscaled, hsigma⟩ := exists_reference_geometry d m
  refine ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelta, hdelta1,
    heps, heps1, hscaled, hsigma, hnear lam hlam hLam, ?_⟩
  intro A hA P0 r ell hr hell O hO hregion u hnonneg hu hdensity
  have hQO : closure (backwardCylinder P0 r) ⊆ O := by
    apply (closure_mono ?_).trans hregion
    rw [← kineticAffine_image_unitCylinder P0 hr]
    apply image_mono
    exact subset_closure.trans (stackComparisonRegion_geometry d m).2.2.1
  exact hstack p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu
    (hnear lam hlam hLam A hA P0 r ell hr hell O hO hQO u hnonneg hu hdensity)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
