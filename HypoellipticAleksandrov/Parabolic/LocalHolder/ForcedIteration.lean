module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationScaling
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementForward

/-! # Forced range contraction

The internally constructed homogeneous replacement differs from the given solution by
at most `M r²`. Its contracted range therefore yields a genuine forced recurrence.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Bounded forcing adds at most `4 M r²` to the structural range contraction. -/
theorem exists_forced_range_contraction
    (hLE : KineticAleksandrov.LiebermanEllipsoidDirichletStatement)
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ (A : CoefficientField N), IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (T : ℝ) (v₀ : PDE.Vec N) (r : ℝ), 0 < r →
      ∀ (w : TimeVelocity N → ℝ) (M : ℝ), 0 ≤ M →
        IsScalarC12On w
          (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
        ContinuousOn w
          (scalarParabolicClosedCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
        (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
          |scalarTimeDerivative w z -
            matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) →
        ∀ l b : ℝ,
          (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
            l ≤ w z ∧ w z ≤ b) →
        ∃ l' b' : ℝ, b' - l' ≤ θ * (b - l) + 4 * M * r ^ 2 ∧
          ∀ z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
            (PDE.euclideanBall v₀ (r / 2)), l' ≤ w z ∧ w z ≤ b' := by
  obtain ⟨θ, hθ, hθ1, hc⟩ := exists_homogeneous_range_contraction N hN lam Lam hlam hLam
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro A hA hs hlo hhi T v₀ r hr w M hM hw hwc hf l b hb
  have haT : T - r ^ 2 < T := sub_lt_self T (sq_pos_of_pos hr)
  obtain ⟨v, hv, hvc, htrace, he, herr⟩ := exists_parabolic_homogeneous_replacement
    hLE hN lam Lam hlam hLam A hA hs hlo hhi (T - r ^ 2) T haT v₀ r hr w M hM hw hwc hf
  have herr' (z : TimeVelocity N)
      (hz : z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) :
      |w z - v z| ≤ M * r ^ 2 := by
    have h := herr z ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
    simpa only [sub_sub_cancel] using h
  have hvb : ∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
      l - M * r ^ 2 ≤ v z ∧ v z ≤ b + M * r ^ 2 := by
    intro z hz
    have hd := abs_le.mp (herr' z hz)
    constructor <;> linarith only [hd.1, hd.2, (hb z hz).1, (hb z hz).2]
  obtain ⟨l', b', hwidth, hbounds⟩ := hc A hA hs hlo hhi T v₀ r hr v hv he
    (l - M * r ^ 2) (b + M * r ^ 2) hvb
  refine ⟨l' - M * r ^ 2, b' + M * r ^ 2, ?_, ?_⟩
  · have hh : 0 ≤ (1 - θ) * (M * r ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hθ1.le) (mul_nonneg hM (sq_nonneg r))
    linarith only [hwidth, hh]
  · intro z hz
    have hzU : z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T
        (PDE.euclideanBall v₀ r) := by
      constructor
      · constructor
        · nlinarith only [hz.1.1, sq_pos_of_pos hr]
        · exact hz.1.2
      · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
        have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr)).mp hz.2
        exact hn.trans (half_lt_self hr)
    have hd := abs_le.mp (herr' z hzU)
    constructor <;> linarith only [hd.1, hd.2, (hbounds z hz).1, (hbounds z hz).2]

end HypoellipticAleksandrov.Parabolic.LocalHolder
