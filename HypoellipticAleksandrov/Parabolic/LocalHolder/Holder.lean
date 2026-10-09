module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationDyadic
public import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderExponent
public import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderGeometry

/-! # The inhomogeneous parabolic Hölder estimate

The homogeneous Harnack theorem and the proved replacement produce the forced
recurrence. Its dyadic decay is converted to the literal parabolic distance, including
pairs arbitrarily close to the top time. Constants precede all coefficient and solution data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Set LocalHolder KineticAleksandrov.LocalA

/-- The smooth-coefficient bounded-source instance of Krylov--Safonov Lemma 4.3. -/
theorem parabolic_holder_of_bounded_source
    (hLE : KineticAleksandrov.LiebermanEllipsoidDirichletStatement)
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField N), IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (w : TimeVelocity N → ℝ) (M : ℝ), 0 ≤ M →
      IsScalarC12On w (scalarParabolicOpenCylinder (-9/16) 0
        (PDE.euclideanBall 0 (3/4 : ℝ))) →
      (∀ z ∈ scalarParabolicOpenCylinder (-9/16) 0
        (PDE.euclideanBall 0 (3/4 : ℝ)), |w z| ≤ M) →
      (∀ z ∈ scalarParabolicOpenCylinder (-9/16) 0
        (PDE.euclideanBall 0 (3/4 : ℝ)),
        |scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
          (scalarSpatialHessian w z)| ≤ M) →
      ∀ z ∈ scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall 0 (1/2 : ℝ)),
      ∀ z' ∈ scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall 0 (1/2 : ℝ)),
        |w z - w z'| ≤ C * M * parabolicDistance z z' ^ α := by
  obtain ⟨q, K, hqhalf, hq1, hK, hdecay⟩ :=
    exists_forced_dyadic_range_decay hLE N hN lam Lam hlam hLam
  obtain ⟨α, hα, hα1, hqα⟩ := exists_holder_exponent_of_contraction hq1
  let C := K * (32 : ℝ) ^ α + 2 * (64 : ℝ) ^ α
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, α, hC, hα, hα1, ?_⟩
  intro A hA hs hlo hhi w M hM hw hb hf z hz z' hz'
  have hsub : scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall (0 : PDE.Vec N) (1/2)) ⊆
      scalarParabolicOpenCylinder (-9/16) 0 (PDE.euclideanBall 0 (3/4)) := by
    intro y hy
    constructor
    · constructor
      · linarith only [hy.1.1]
      · exact hy.1.2
    · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
      exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by norm_num : (0 : ℝ) < 1 / 2)).mp hy.2).trans (by norm_num)
  by_cases heq : z = z'
  · rw [heq, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hC.le hM) (Real.rpow_nonneg (parabolicDistance_nonneg _ _) _)
  let δ := parabolicDistance z z'
  have hδ : 0 < δ := parabolicDistance_pos heq
  by_cases hsmall : δ < 1 / 64
  · obtain ⟨T, hTpair, hT0, hmargin⟩ := exists_pair_top hz.1.2 hz'.1.2 hδ
    have hzt : z.1 < T := (le_max_left _ _).trans_lt hTpair
    have hbase := pair_base_closed_cylinder_subset hz hzt hT0
    have hx : 0 < 16 * δ := mul_pos (by norm_num) hδ
    have hx1 : 16 * δ ≤ 1 := by linarith only [hsmall]
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hx hx1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hrad : 2 * δ ≤ dyadicRadius (1 / 8) n := by
      dsimp only [dyadicRadius]
      linarith only [hnhi]
    obtain ⟨hzn, hz'n⟩ := pair_mem_common_backward_cylinder heq hTpair hmargin hrad
    have hbound := hdecay A hA hs hlo hhi _ T z.2 (1 / 8) (by norm_num) (by norm_num)
      hbase w M hM hw hb hf n z z' hzn hz'n
    have hpower : q ^ n ≤ (32 * δ) ^ α := by
      have hp := geometric_decay_le_holder_power (by linarith only [hqhalf]) hα hqα n hnlo
      have he : 2 * (16 * δ) = 32 * δ := by ring
      rw [he] at hp
      exact hp
    have hC32 : K * (32 : ℝ) ^ α ≤ C :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    calc |w z - w z'| ≤ K * M * q ^ n := hbound
      _ ≤ K * M * (32 * δ) ^ α :=
        mul_le_mul_of_nonneg_left hpower (mul_nonneg hK.le hM)
      _ = (K * (32 : ℝ) ^ α) * M * δ ^ α := by
        rw [Real.mul_rpow (by norm_num) hδ.le]
        ring
      _ ≤ C * M * δ ^ α := by gcongr
  · have hlarge : (1 / 64 : ℝ) ≤ δ := not_lt.mp hsmall
    have hprod : 1 ≤ (64 : ℝ) ^ α * δ ^ α := by
      rw [← Real.mul_rpow (by norm_num) hδ.le]
      have hscale : (1 : ℝ) ≤ 64 * δ := by linarith only [hlarge]
      simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hscale hα.le
    have hC64 : 2 * (64 : ℝ) ^ α ≤ C :=
      le_add_of_nonneg_left (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
    have habs : |w z - w z'| ≤ 2 * M :=
      (abs_sub_le (w z) 0 (w z')).trans (by
        simpa only [sub_zero, zero_sub, abs_neg, two_mul] using
          add_le_add (hb z (hsub hz)) (hb z' (hsub hz')))
    calc |w z - w z'| ≤ 2 * M := habs
      _ ≤ (2 * (64 : ℝ) ^ α) * M * δ ^ α := by
        have h := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
        nlinarith only [h]
      _ ≤ C * M * δ ^ α := by gcongr

end HypoellipticAleksandrov.Parabolic
