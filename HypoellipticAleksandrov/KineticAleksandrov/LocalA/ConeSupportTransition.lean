module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalMeasure

/-! # Finite propagation of the actual killed terminal transition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- The killed kernel has the same centered Euclidean propagation cone as the exit measure. -/
theorem ballTransition_cone
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    ∀ᵐ w ∂ballTransition hH hLE hd hlam hLam B hB v₀ hR P T,
      PDE.vecEuclideanNorm (w.2 - P.1.position - (T.1 - P.1.time) • v₀) ≤
        R * (T.1 - P.1.time) := by
  let S : Set (KineticPoint d) := {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}
  have hS : MeasurableSet S :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage continuous_velocity.measurable
  rw [← ballExit_terminal_interior_map hH hLE hd hlam hLam B hB v₀ hR P T]
  apply (ae_map_iff continuous_exitStateCoordinates.measurable.aemeasurable
    (isClosed_le (PDE.continuous_vecEuclideanNorm.comp
      ((continuous_snd.sub continuous_const).sub continuous_const))
      continuous_const).measurableSet).mpr
  filter_upwards [ae_restrict_mem hS,
    ae_restrict_of_ae (ballExitRaw_cone hH hLE hd hlam hLam B hB v₀ hR P T),
    ae_restrict_of_ae (ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T)]
    with Q hv hcone hQ
  change Q.velocity ∈ PDE.euclideanBall v₀ R at hv
  have ht : Q.time = T.1 := by
    rcases hQ with hQ | hQ
    · exact hQ.1
    · exact False.elim ((mem_interior_iff_notMem_frontier hv).mp
        ((PDE.isOpen_euclideanBall v₀ R).interior_eq.symm ▸ hv) hQ.2.2)
  change PDE.vecEuclideanNorm (Q.position - P.1.position - (T.1 - P.1.time) • v₀) ≤
    R * (T.1 - P.1.time)
  simpa only [ht] using hcone.2.2

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
