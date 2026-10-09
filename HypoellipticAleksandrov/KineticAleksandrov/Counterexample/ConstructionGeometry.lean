module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Alpha
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
import Mathlib.Tactic.Linarith

/-! # Fixed cylinder and genuine interior height points for the Appendix C construction -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/-- With a stationary spatial base point, the cylinder is the literal product cylinder. -/
theorem construction_mem_cylinder_iff {d : ℕ} (T S : ℝ) (hS : 0 < S) (P : KineticPoint d) :
    P ∈ backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ↔
      T - S ^ 2 < P.time ∧ P.time < T ∧
      PDE.vecEuclideanNorm P.velocity < S ∧ PDE.vecEuclideanNorm P.position < S ^ 3 := by
  simp [backwardCylinder, relativePosition,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hS,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hS 3)]

/-- A positive earlier time at the spatial origin belongs to the chosen fixed cylinder. -/
theorem construction_origin_mem_cylinder {d : ℕ} (T S t : ℝ)
    (hS : 0 < S) (hTS : T < S ^ 2) (ht : 0 < t) (htT : t < T) :
    (⟨t, 0, 0⟩ : KineticPoint d) ∈ backwardCylinder ⟨T, 0, 0⟩ S := by
  rw [construction_mem_cylinder_iff T S hS]
  refine ⟨by linarith, htT, ?_, ?_⟩
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hS
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using pow_pos hS 3

/-- The unsmoothed zero extension vanishes on the full initial and lateral boundary. -/
theorem construction_zero_extension_boundary {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R T S : ℝ) (hTS : T < S ^ 2)
    (hgeom : ∀ q, H q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S)
    (P : KineticPoint d)
    (hP : P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  have hfaces : P.time = T - S ^ 2 ∨
      P.velocity ∈ PDE.euclideanSphere 0 S ∨
      P.position ∈ PDE.euclideanSphere 0 (S ^ 3) := by
    simpa only [relativePosition, sub_zero, smul_zero,
      mem_union, mem_ofPred_eq, or_assoc] using hP.2
  rcases hfaces with htime | hvel | hpos
  · apply zeroExtendedProfile_eq_zero_of_time
    change P.time = T - S ^ 2 at htime
    linarith
  · apply zeroExtendedProfile_eq_zero_of_profile
    by_contra hn
    have hb := (hgeom (P.position, P.velocity) (not_le.mp hn).le).2
    have hv : PDE.vecNormSq P.velocity = S ^ 2 := by
      simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hvel
    have hn := PDE.vecEuclideanNorm_nonneg P.velocity
    rw [← PDE.vecEuclideanNorm_sq] at hv
    nlinarith
  · apply zeroExtendedProfile_eq_zero_of_profile
    by_contra hn
    have hb := (hgeom (P.position, P.velocity) (not_le.mp hn).le).1
    have hx : PDE.vecNormSq P.position = (S ^ 3) ^ 2 := by
      simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hpos
    have hn := PDE.vecEuclideanNorm_nonneg P.position
    rw [← PDE.vecEuclideanNorm_sq] at hx
    nlinarith

/-- The explicit cutoff has a genuine interior height witness in the fixed cylinder. -/
theorem construction_zero_extension_interior_height {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hS : 0 < S)
    (hTS : barrierTime mu < S ^ 2)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4) :
    ∃ P ∈ backwardCylinder (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) S,
      5 / 16 < zeroExtendedProfile (profileFunction h) alpha r mu R P := by
  have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
  obtain ⟨t, ht, htT, hh⟩ := timeCutoff_interior_height (profileFunction h)
    alpha r mu R hzero hr hmu hsmall
  refine ⟨⟨t, 0, 0⟩, construction_origin_mem_cylinder _ _ _ hS hTS ht htT, ?_⟩
  have hz : profileFunction h ((0 : PDE.Vec d), (0 : PDE.Vec d)) = 0 := hzero
  simpa [zeroExtendedProfile, ht, hz] using hh

/-- Barrier and cylinder radii are chosen once, independently of all flattening scales. -/
theorem construction_fixed_geometry_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) :
    ∃ R mu S : ℝ, 0 < R ∧ 0 < mu ∧ 0 < S ∧
      mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2 ∧
      barrierTime mu < S ^ 2 ∧
      (∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) ∧
      (∀ q, profileFunction h q ≤ 1 →
        PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) ∧
      (∀ P, 0 ≤ backwardOperator (fun _t x v => profileMatrix h (x, v))
        (barrier mu R) P) := by
  obtain ⟨R, hR, hv⟩ := exists_profile_barrier_radius ha h
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlam := (selectedProfile_spec h).1
  have hmu : 0 < mu := div_pos (mul_pos hd0 hlam) (sq_pos_of_pos hR)
  obtain ⟨S, hS, hTS, hgeom⟩ := exists_profile_cylinder_radius ha h (barrierTime mu)
  refine ⟨R, mu, S, hR, hmu, hS, rfl, hTS, hv, hgeom, ?_⟩
  intro P
  exact barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h)
    R hlam hR (fun q => ((selectedProfile_spec h).2.2.2.2.2.1 q).1) P

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
