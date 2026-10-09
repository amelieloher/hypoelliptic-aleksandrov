module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportGeometry

/-! # Literal Euclidean finite propagation for the actual ball exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Parabolic SectionTwo

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The actual ambient exit measure lies on the prescribed terminal/lateral trace. -/
theorem ballExitRaw_ae_trace (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    ∀ᵐ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T,
      Q ∈ localTrace P.1.time T.1 v₀ R := by
  rw [ae_iff]
  exact (ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.1

/-- Both time endpoints and the full centered Euclidean cone hold almost everywhere. -/
theorem ballExitRaw_cone (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    ∀ᵐ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T,
      P.1.time ≤ Q.time ∧ Q.time ≤ T.1 ∧
      PDE.vecEuclideanNorm (Q.position - P.1.position - (Q.time - P.1.time) • v₀) ≤
        R * (Q.time - P.1.time) := by
  have htr := ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T
  have ht : ∀ᵐ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T,
      P.1.time ≤ Q.time := htr.mono (fun Q hQ => (localTrace_subset_closed T.2.le v₀ R hQ).1)
  have hcone := cone_norm_of_directional_ae
    (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) P.1 v₀ R hR.le ht (fun e => by
      have he := ballExitRaw_directional_cone hH hLE hd hlam hLam B hB v₀ hR P T
        (-(PDE.vecEuclideanNorm e * R) - PDE.vecDot e v₀) e
        (-(-(PDE.vecEuclideanNorm e * R) - PDE.vecDot e v₀) * P.1.time -
          PDE.vecDot e P.1.position)
        (by unfold coneCoordinate; ring) (cone_directional_speed e v₀ hR)
      filter_upwards [he] with Q hQ
      rw [coneCoordinate_centered] at hQ
      exact sub_nonpos.mp hQ)
  filter_upwards [htr, hcone] with Q hQ hQc
  exact ⟨(localTrace_subset_closed T.2.le v₀ R hQ).1,
    (localTrace_subset_closed T.2.le v₀ R hQ).2.1, hQc⟩

/-- The canonical exit-coordinate measure has the source's exact Euclidean cone support. -/
theorem ballExit_cone (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    ∀ᵐ z ∂ballExit hH hLE hd hlam hLam B hB v₀ hR P T,
      P.1.time ≤ z.2.1 ∧ z.2.1 ≤ T.1 ∧
      PDE.vecEuclideanNorm z.1 ≤ R * (z.2.1 - P.1.time) := by
  unfold ballExit
  apply ae_map_iff (continuous_exitCoordinates P.1 v₀).measurable.aemeasurable
    (by
      exact ((isClosed_le continuous_const continuous_snd.fst).inter
        ((isClosed_le continuous_snd.fst continuous_const).inter
          (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_fst)
            (continuous_const.mul (continuous_snd.fst.sub continuous_const))))).measurableSet)
    |>.mpr
  exact ballExitRaw_cone hH hLE hd hlam hLam B hB v₀ hR P T

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
