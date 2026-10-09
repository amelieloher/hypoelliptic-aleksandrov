module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Extension
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Shell
import Mathlib.Tactic.Positivity

/-! # Fixed compact geometry for the profile sublevel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/-- The closed unit profile sublevel is compact, with the native Euclidean gauge. -/
theorem isCompact_profile_unit_sublevel {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) : IsCompact {q | profileFunction h q ≤ 1} := by
  obtain ⟨_, _, hc, _, _, _, hH, _, _, hcomp, _⟩ := selectedProfile_spec h
  exact (isCompact_rho_sublevel d
    (Real.rpow (1 / profileLowerComparison h) alpha⁻¹)).of_isClosed_subset
    (isClosed_le hH continuous_const)
    (profile_sublevel_subset_rho _ alpha _ 1 ha hc zero_lt_one (fun q => (hcomp q).1))

/-- One fixed radius strictly bounds every velocity in the closed profile domain. -/
theorem exists_profile_barrier_radius {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) :
    ∃ R : ℝ, 0 < R ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2 := by
  obtain ⟨_, _, hc, _, _, _, _, _, _, hcomp, _⟩ := selectedProfile_spec h
  let L := Real.rpow (1 / profileLowerComparison h) alpha⁻¹
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos zero_lt_one hc) _
  refine ⟨L + 1, by positivity, ?_⟩
  intro q hq
  have hr := profile_sublevel_subset_rho (profileFunction h) alpha
    (profileLowerComparison h) 1 ha hc zero_lt_one (fun y => (hcomp y).1) hq
  have hv := (rho_coordinate_bounds q).2.trans hr
  have hs := sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg q.2) hL.le |>.2 hv
  rw [PDE.vecEuclideanNorm_sq] at hs
  nlinarith

/-- The profile domain lies strictly inside one Euclidean kinetic cylinder radius.
The time and spatial radii are fixed before the flattening and smoothing scales. -/
theorem exists_profile_cylinder_radius {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) (T : ℝ) :
    ∃ S : ℝ, 0 < S ∧ T < S ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S := by
  obtain ⟨_, _, hc, _, _, _, _, _, _, hcomp, _⟩ := selectedProfile_spec h
  let L := Real.rpow (1 / profileLowerComparison h) alpha⁻¹
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos zero_lt_one hc) _
  let S := L + |T| + 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hLS : L < S := by dsimp [S]; linarith [abs_nonneg T]
  refine ⟨S, hS, ?_, ?_⟩
  · have ht : T ≤ |T| := le_abs_self T
    have hbig : |T| + 2 ≤ S := by dsimp [S]; linarith
    nlinarith [abs_nonneg T]
  · intro q hq
    have hr := profile_sublevel_subset_rho (profileFunction h) alpha
      (profileLowerComparison h) 1 ha hc zero_lt_one (fun y => (hcomp y).1) hq
    have hb := rho_coordinate_bounds q
    exact ⟨lt_of_le_of_lt (hb.1.trans (pow_le_pow_left₀ (rho_nonneg q) hr 3))
      (pow_lt_pow_left₀ hLS hL.le (by decide)), lt_of_le_of_lt (hb.2.trans hr) hLS⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
