module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationRegularized

/-! # Signed terminal endpoint convergence under actual position regularization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Actual mollification preserves uniform integrability of signed endpoint differences. -/
theorem barrier_mollifier_endpoint_tendsto
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam alpha : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Tendsto (fun n : ℕ =>
      (∫ q, positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
        (q.1 - Y, q.2) ∂kernelXV E T z) -
      positionConvolution (barrierMollifier n) (bellmanOriginExtension phi) (z.1 - Y, z.2))
      atTop (𝓝 (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z)) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
  obtain ⟨D, hD, hm⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
  let Phi := fun n : ℕ => positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
  have hc (n : ℕ) : Continuous (Phi n) :=
    (barrier_position_regularization_joint h ha ha1 _ (barrierMollifier_spec n)).continuous
  have hmod (n : ℕ) := positionConvolution_modulus (barrierMollifier n) (barrierMollifier_spec n)
    (bellmanOriginExtension phi) (h.origin_extension_continuous ha) alpha D hD hm
  let f := fun n : ℕ => fun q : Z => Phi n (q.1 - Y, q.2) - Phi n (z.1 - Y, z.2)
  let g := fun q : Z => D * (|q.1 - z.1| ^ (alpha / 3) + |q.2 - z.2| ^ alpha)
  have hx := terminal_position_fractional_moment hH hLE hlam hLam A z T
    (a := alpha / 3) (by linarith) (by linarith)
  have hv := terminal_velocity_fractional_moment hH hLE hlam hLam A z T ha.le (by linarith)
  have hgi : Integrable g (kernelXV E T z) := (hx.1.add hv.1).const_mul D
  have hfm (n : ℕ) : Measurable (f n) :=
    ((hc n).measurable.comp ((measurable_fst.sub_const Y).prodMk measurable_snd)).sub_const _
  have hfb (n : ℕ) (q : Z) : ‖f n q‖ ≤ g q := by
    have he : q.1 - Y - (z.1 - Y) = q.1 - z.1 := by ring
    simpa only [f, Phi, g, Real.norm_eq_abs, he] using hmod n (q.1 - Y, q.2) (z.1 - Y, z.2)
  have hlim : Tendsto (fun n => ∫ q, f n q ∂kernelXV E T z) atTop
      (𝓝 (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z)) := by
    apply tendsto_integral_of_dominated_convergence g (fun n => (hfm n).aestronglyMeasurable) hgi
      (fun n => Eventually.of_forall (hfb n))
    filter_upwards with q
    exact (barrier_position_mollifier_tendsto h ha (q.1 - Y, q.2)).sub
      (barrier_position_mollifier_tendsto h ha (z.1 - Y, z.2))
  apply hlim.congr'
  filter_upwards with n
  have hdiff : Integrable (f n) (kernelXV E T z) :=
    hgi.mono' (hfm n).aestronglyMeasurable (Eventually.of_forall (hfb n))
  have hi : Integrable (fun q : Z => Phi n (q.1 - Y, q.2)) (kernelXV E T z) := by
    convert hdiff.add (integrable_const (Phi n (z.1 - Y, z.2))) using 1
    funext q
    simp only [Pi.add_apply, f]
    ring
  change (∫ q, Phi n (q.1 - Y, q.2) - Phi n (z.1 - Y, z.2) ∂kernelXV E T z) = _
  rw [integral_sub hi (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
    kernelXV_mass_one hlam A E hE, ENNReal.toReal_one, one_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
