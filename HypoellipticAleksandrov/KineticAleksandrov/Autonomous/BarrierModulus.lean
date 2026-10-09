module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrier

/-! # The anisotropic modulus of the zero-extended homogeneous barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set BarrierRegularization

/-- A function already assigned zero at the origin equals its canonical extension. -/
theorem barrierOriginExtension_eq_self (Phi : (ℝ × ℝ) → ℝ) (hzero : Phi (0, 0) = 0) :
    bellmanOriginExtension Phi = Phi := by
  funext q
  by_cases hq : q = (0, 0)
  · subst q
    exact (bellmanOriginExtension_zero Phi).trans hzero.symm
  · exact bellmanOriginExtension_eqOn Phi hq

/-- Source coordinate-line modulus with literal C² and homogeneity hypotheses.
For an arbitrary function the existential constant can depend on that function. -/
theorem homogeneous_barrier_modulus (alpha : ℝ) (ha : 0 < alpha ∧ alpha < 1)
    (Phi : (ℝ × ℝ) → ℝ) (hPhi : ContDiffOn ℝ 2 Phi {z | z ≠ (0, 0)})
    (hhom : ∀ r : ℝ, 0 < r → ∀ z : ℝ × ℝ, z ≠ (0, 0) →
      Phi (r ^ 3 * z.1, r * z.2) = r ^ alpha * Phi z)
    (hzero : Phi (0, 0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : ℝ × ℝ,
      |Phi z - Phi w| ≤ C * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  have hh : IsBellmanHomogeneous alpha Phi := ⟨hPhi, hhom⟩
  simpa only [barrierOriginExtension_eq_self Phi hzero] using
    barrier_coordinate_modulus hh ha.1 ha.2

/-- The source's selected witness and its modulus are chosen before any coefficient field.
Thus both constants and the witness have only the source parameter dependencies. -/
theorem exists_bellman_barrier_with_modulus (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) :
    ∃ phi : (ℝ × ℝ) → ℝ, ∃ c C : ℝ,
      IsBellmanHomogeneous alpha phi ∧ 0 < c ∧ 0 ≤ C ∧
      (∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
        c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q) ∧
      ∀ z w : ℝ × ℝ,
        |bellmanOriginExtension phi z - bellmanOriginExtension phi w| ≤
          C * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  obtain ⟨hlo, _, hb⟩ := exists_bellman_barrier lam Lam hlam hLam
  obtain ⟨phi, c, hhom, hc, hbound⟩ := hb alpha ha ha1
  have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha
  obtain ⟨C, hC, hmod⟩ := barrier_coordinate_modulus hhom ha0 ha1
  exact ⟨phi, c, C, hhom, hc, hC, hbound, hmod⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
