module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
import Mathlib.Tactic.Ring

/-! # The favorable convexity term in the cutoff source equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic MeasureTheory
open scoped MatrixOrder

/-- Contraction of the full positive second-chain representative. -/
theorem contraction_cutoff_identity {d : ℕ} (A B : PDE.Mat d)
    (w : PDE.Vec d) (s t : ℝ) :
    matrixContraction A (fun i k => s * B i k + t * w i * w k) =
      s * matrixContraction A B + t * PDE.vecDot (A.mulVec w) w := by
  simpa only [neg_neg, neg_mul, sub_neg_eq_add] using
    contraction_flattening_identity A B w (-s) (-t)

/-- Contraction distributes over an entrywise difference. -/
theorem contraction_sub_right {d : ℕ} (A B C : PDE.Mat d) :
    matrixContraction A (fun i k => B i k - C i k) =
      matrixContraction A B - matrixContraction A C := by
  simp only [matrixContraction, mul_sub, Finset.sum_sub_distrib]

/-- The cutoff source representative uses the actual first and second weak jets.
The time derivative of the stationary profile vanishes. -/
def timeCutoffSourceRepresentative {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) : ℝ :=
  let q := (P.position, P.velocity)
  let s := selectedFlatProfile h r q - barrier mu R P
  let w := flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) P
  (-(deriv timeCutoffTheta s) * kineticTimeDerivative (barrier mu R) P) +
    PDE.vecDot P.velocity (fun i => deriv timeCutoffTheta s * flatProfilePositionJet h r q i) -
    matrixContraction (profileMatrix h q) (fun i k =>
      deriv timeCutoffTheta s *
        (flatProfileHessian h r q i k - kineticVelocityHessian (barrier mu R) P i k) +
      deriv (deriv timeCutoffTheta) s * w i * w k)

/-- The exact source identity has a nonpositive quadratic correction. -/
theorem timeCutoff_source_identity_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    ∀ᵐ q ∂volume,
      timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ =
        deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q -
            backwardOperator (fun _t x v => profileMatrix h (x, v))
              (barrier mu R) ⟨t, q.1, q.2⟩) -
        deriv (deriv timeCutoffTheta)
          (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
          PDE.vecDot ((profileMatrix h q).mulVec
            (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
              ⟨t, q.1, q.2⟩))
            (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
              ⟨t, q.1, q.2⟩) := by
  filter_upwards [flatProfile_representatives_source h r] with q hq
  unfold timeCutoffSourceRepresentative
  dsimp only
  have he := contraction_cutoff_identity (profileMatrix h q)
    (fun i k => flatProfileHessian h r q i k -
      kineticVelocityHessian (barrier mu R) ⟨t, q.1, q.2⟩ i k)
    (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩)
    (deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
    (deriv (deriv timeCutoffTheta)
      (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
  simp only [Pi.sub_apply, Prod.mk.eta] at he ⊢
  rw [he, contraction_sub_right]
  rw [backwardOperator_apply, barrier_positionGradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    fullKineticCoefficientAt_apply] at hq ⊢
  have hdot (a : ℝ) :
      (∑ i, q.2 i * (a * flatProfilePositionJet h r q i)) =
        a * ∑ i, q.2 i * flatProfilePositionJet h r q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot, ← hq]
  ring

/-- The actual selected stationary source is nonnegative almost everywhere. -/
theorem flatSource_nonneg_ae_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, 0 ≤ flatSource (profileMatrix h) (profileFunction h)
      flatteningPsi alpha r q := by
  obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
  filter_upwards [flatSource_ae_eq_jet_of_profile h r] with q hq
  rw [hq]
  unfold flatSourceWithJet
  exact mul_nonneg
    (mul_nonneg (Real.rpow_pos_of_pos hr _).le (flatteningPsi_deriv2_nonneg _))
    (quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1 _)

/-- The favorable convexity term and barrier sign bound the weak source by the shell source. -/
theorem timeCutoff_source_le_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (R : ℝ) (hR : 0 < R) (t : ℝ) :
    ∀ᵐ q ∂volume,
      timeCutoffSourceRepresentative h r ((d : ℝ) * profileLowerEllipticity h / R ^ 2) R
        ⟨t, q.1, q.2⟩ ≤
        flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
  filter_upwards [timeCutoff_source_identity_of_profile h r mu R t,
    flatSource_nonneg_ae_of_profile h r hr] with q he hf
  rw [he]
  have hb := barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h) R
    hlam hR (fun y => (hA y).1) ⟨t, q.1, q.2⟩
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)
  have hquad := quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1
    (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩)
  have hterm := mul_nonneg (timeCutoffTheta_deriv2_nonneg
    (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)) hquad
  have hfirst := mul_le_mul_of_nonneg_left (sub_le_self
    (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q) hb) htheta.1
  have hlast := mul_le_of_le_one_left hf htheta.2
  exact (sub_le_self _ hterm).trans (hfirst.trans hlast)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
