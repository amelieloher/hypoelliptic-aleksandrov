module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIteration
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometry
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometric

/-! # Dyadic decay of the forced solution's actual range

The supremum and infimum are those of the solution on each literal Euclidean cylinder.
The preceding forced contraction proves their recurrence; no decay premise is assumed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- The forced recurrence gives uniform geometric decay on nested physical cylinders. -/
theorem exists_forced_dyadic_range_decay
    (hLE : KineticAleksandrov.LiebermanEllipsoidDirichletStatement)
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ q K : ℝ, (1 / 2 : ℝ) ≤ q ∧ q < 1 ∧ 0 < K ∧
      ∀ (A : CoefficientField N), IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (U : Set (TimeVelocity N)) (T : ℝ) (v₀ : PDE.Vec N) (r : ℝ),
        0 < r → r ≤ 1 →
        scalarParabolicClosedCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r) ⊆ U →
      ∀ (w : TimeVelocity N → ℝ) (M : ℝ), 0 ≤ M →
        IsScalarC12On w U → (∀ z ∈ U, |w z| ≤ M) →
        (∀ z ∈ U, |scalarTimeDerivative w z -
          matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) →
        ∀ (n : ℕ) (z z' : TimeVelocity N),
          z ∈ scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
            (PDE.euclideanBall v₀ (dyadicRadius r n)) →
          z' ∈ scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
            (PDE.euclideanBall v₀ (dyadicRadius r n)) →
          |w z - w z'| ≤ K * M * q ^ n := by
  obtain ⟨θ, hθ, hθ1, hc⟩ := exists_forced_range_contraction hLE N hN lam Lam hlam hLam
  let q := (1 + θ) / 2
  have hqhalf : (1 / 2 : ℝ) ≤ q := by dsimp [q]; linarith only [hθ]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hθ1]
  have hgap : 0 < q - θ := by dsimp [q]; linarith only [hθ1]
  let K := 2 + 4 / (q - θ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (div_nonneg (by norm_num) hgap.le)
  have hKgap : 4 ≤ (q - θ) * K := by
    dsimp [K]
    have heq : (q - θ) * (2 + 4 / (q - θ)) = 2 * (q - θ) + 4 := by
      field_simp [hgap.ne']
    rw [heq]
    linarith only [hgap]
  refine ⟨q, K, hqhalf, hq1, hK, ?_⟩
  intro A hA hs hlo hhi U T v₀ r hr hr1 hU w M hM hw hb hf
  let Q (n : ℕ) := scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
    (PDE.euclideanBall v₀ (dyadicRadius r n))
  have hclosed (n : ℕ) : scalarParabolicClosedCylinder (T - dyadicRadius r n ^ 2) T
      (PDE.euclideanBall v₀ (dyadicRadius r n)) ⊆ U :=
    (backward_ball_closed_mono T v₀ (dyadicRadius_pos hr n)
      (dyadicRadius_le hr.le n)).trans hU
  have hQU (n : ℕ) : Q n ⊆ U := by
    intro z hz
    exact hclosed n ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
  have hne (n : ℕ) : (w '' Q n).Nonempty :=
    (backward_ball_nonempty T v₀ (dyadicRadius_pos hr n)).image w
  have hab (n : ℕ) : BddAbove (w '' Q n) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact le_of_abs_le (hb z (hQU n hz))
  have hbb (n : ℕ) : BddBelow (w '' Q n) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact neg_le_of_abs_le (hb z (hQU n hz))
  let f (n : ℕ) := sSup (w '' Q n) - sInf (w '' Q n)
  have hrec (n : ℕ) : f (n + 1) ≤ θ * f n + (4 * M * r ^ 2) * (1 / 4 : ℝ) ^ n := by
    have hbounds : ∀ z ∈ Q n, sInf (w '' Q n) ≤ w z ∧ w z ≤ sSup (w '' Q n) :=
      fun z hz => ⟨csInf_le (hbb n) (mem_image_of_mem w hz),
        le_csSup (hab n) (mem_image_of_mem w hz)⟩
    obtain ⟨l, b, hwidth, hbounds'⟩ := hc A hA hs hlo hhi T v₀ (dyadicRadius r n)
      (dyadicRadius_pos hr n) w M hM (scalarC12On_mono hw (hQU n))
      (hw.continuousOn.mono (hclosed n)) (fun z hz => hf z (hQU n hz))
      (sInf (w '' Q n)) (sSup (w '' Q n)) hbounds
    have hb' : ∀ z ∈ Q (n + 1), l ≤ w z ∧ w z ≤ b := by
      intro z hz
      apply hbounds'
      simpa only [Q, dyadicRadius_succ] using hz
    have hsup : sSup (w '' Q (n + 1)) ≤ b := csSup_le (hne _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact (hb' z hz).2)
    have hinf : l ≤ sInf (w '' Q (n + 1)) := le_csInf (hne _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact (hb' z hz).1)
    have hwidth' := hwidth
    rw [dyadicRadius_sq] at hwidth'
    change _ ≤ θ * f n + _ at hwidth'
    dsimp only [f]
    nlinarith only [hsup, hinf, hwidth']
  have hbase : f 0 ≤ K * M := by
    have hsup : sSup (w '' Q 0) ≤ M := csSup_le (hne _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact le_of_abs_le (hb z (hQU 0 hz)))
    have hinf : -M ≤ sInf (w '' Q 0) := le_csInf (hne _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact neg_le_of_abs_le (hb z (hQU 0 hz)))
    have hkm := mul_le_mul_of_nonneg_right hK2 hM
    dsimp [f]
    linarith only [hsup, hinf, hkm]
  have hforce : 4 * M * r ^ 2 ≤ (q - θ) * (K * M) := by
    have hrsq : r ^ 2 ≤ 1 := by nlinarith only [hr.le, hr1]
    have h := mul_le_mul_of_nonneg_right hKgap hM
    nlinarith only [h, mul_le_mul_of_nonneg_left hrsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hM)]
  have hdecay := forced_recurrence_le_geometric hθ (by linarith only [hqhalf])
    (by positivity : 0 ≤ 4 * M * r ^ 2) hforce f hbase hrec
  intro n z z' hz hz'
  have hlz := csInf_le (hbb n) (mem_image_of_mem w hz)
  have huz := le_csSup (hab n) (mem_image_of_mem w hz)
  have hlz' := csInf_le (hbb n) (mem_image_of_mem w hz')
  have huz' := le_csSup (hab n) (mem_image_of_mem w hz')
  have hn := hdecay n
  dsimp only [f] at hn
  rw [abs_le]
  constructor <;> linarith only [hlz, huz, hlz', huz', hn]

end HypoellipticAleksandrov.Parabolic.LocalHolder
