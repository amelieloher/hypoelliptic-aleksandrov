module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Classical flattened-profile regularity in dimensions at least two -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set Filter

/-- Flattening removes the only nonsmooth point of the higher-dimensional profile. -/
theorem contDiff_selectedFlatProfile_ge_two_of_profile {d : ℕ} (hd : 2 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (selectedFlatProfile h r) := by
  have hs := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hd
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q
    exact contDiffAt_const.congr_of_eventuallyEq (selectedFlatProfile_plateau_of_profile h r hr)
  · have hH := hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))
    unfold selectedFlatProfile flatProfile
    exact contDiffAt_const.sub (contDiffAt_const.mul
      (contDiff_flatteningPsi.contDiffAt.comp q (hH.div_const _)))

/-- The explicit selected flattening jets are the classical jets almost everywhere. -/
theorem flatProfile_jets_ae_ge_two_of_profile {d : ℕ} (hd : 2 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q := by
  have hs := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hd
  have hjets := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hjets, coordinates_ne_zero_ae d (by omega)] with q hj hq
  have hq0 : q ≠ 0 := fun hz => hq.1 (congrArg Prod.fst hz)
  have hH : ContDiffAt ℝ 2 (profileFunction h) q :=
    (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq0))).of_le (by simp)
  refine ⟨?_, ?_, ?_⟩
  · ext i
    unfold dx selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profilePositionJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dx (profileFunction h) q i
    rw [hj.1]
  · ext i
    unfold dv selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profileVelocityJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dv (profileFunction h) q i
    rw [hj.2.1]
  · ext i k
    rw [selectedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q hH i k]
    unfold flatProfileHessian
    rw [hj.2.1, hj.2.2]

/-- The literal stationary operator equals the source formula a.e. in the classical branch. -/
theorem flatProfile_operator_ae_ge_two_of_profile {d : ℕ} (hd : 2 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, statOp (profileMatrix h) (selectedFlatProfile h r) q =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  filter_upwards [flatProfile_jets_ae_ge_two_of_profile hd h r hr,
    flatProfile_representatives_source h r] with q hj hs
  unfold statOp
  rw [← hj.1, ← hj.2.2]
  exact hs

/-- The explicit selected flattening jets are the classical jets almost everywhere. -/
theorem flatProfile_jets_ae_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q := by
  have hC2 := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hjets := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hjets, hC2] with q hj hH
  refine ⟨?_, ?_, ?_⟩
  · ext i
    unfold dx selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profilePositionJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dx (profileFunction h) q i
    rw [hj.1]
  · ext i
    unfold dv selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profileVelocityJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dv (profileFunction h) q i
    rw [hj.2.1]
  · ext i k
    rw [selectedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q hH i k]
    unfold flatProfileHessian
    rw [hj.2.1, hj.2.2]

/-- The literal stationary operator equals the source formula a.e. in the classical branch. -/
theorem flatProfile_operator_ae_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, statOp (profileMatrix h) (selectedFlatProfile h r) q =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  filter_upwards [flatProfile_jets_ae_of_profile h r hr,
    flatProfile_representatives_source h r] with q hj hs
  unfold statOp
  rw [← hj.1, ← hj.2.2]
  exact hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
