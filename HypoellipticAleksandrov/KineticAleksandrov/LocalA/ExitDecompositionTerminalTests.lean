module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar

/-! # Identifying genuine terminal probes in the actual local boundary measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic TheoremA

/-- Compact terminal data extend to a smooth compact physical probe with zero lateral trace. -/
theorem exists_exit_terminal_probe {d : ℕ} (v₀ : PDE.Vec d) (R T : ℝ)
    (F : BoundedBorel (EvolutionAmbientState d))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall v₀ R) (fun _ => 0) T F) :
    ∃ φ : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) ∧
      HasCompactSupport φ ∧
      (∀ Q : KineticPoint d, Q.time = T → φ Q = F (Q.velocity, Q.position)) ∧
      (∀ Q : KineticPoint d, Q.velocity ∉ PDE.euclideanBall v₀ R → φ Q = 0) := by
  let K : Set (ℝ × EvolutionAmbientState d) := {T} ×ˢ tsupport F
  have hK : IsCompact K := isCompact_singleton.prod hF.2.1
  obtain ⟨χ, hχs, hχc, _, _, hχK⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f (q : ℝ × PDE.Vec d × PDE.Vec d) := χ q * F q.2
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := hχs.mul (hF.1.comp contDiff_snd)
  have hfc : HasCompactSupport f := hχc.mul_right
  let J : (ℝ × PDE.Vec d × PDE.Vec d) ≃ₜ (ℝ × PDE.Vec d × PDE.Vec d) :=
    Homeomorph.prodCongr (Homeomorph.refl ℝ) (Homeomorph.prodComm _ _)
  let φ : KineticPoint d → ℝ := f ∘ J ∘ KineticPoint.homeomorphProd d
  have hJs : ContDiff ℝ (⊤ : ℕ∞) J :=
    contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · have heq : φ ∘ (KineticPoint.equivProd d).symm = f ∘ J := by
      funext q
      rfl
    rw [heq]
    exact hfs.comp hJs
  · exact (hfc.comp_homeomorph J).comp_homeomorph (KineticPoint.homeomorphProd d)
  · intro Q hQ
    change χ (Q.time, Q.velocity, Q.position) * F (Q.velocity, Q.position) = _
    by_cases h : F (Q.velocity, Q.position) = 0
    · rw [h, mul_zero]
    · rw [hχK (Q.time, Q.velocity, Q.position)
        ⟨hQ, subset_tsupport F
          (show (Q.velocity, Q.position) ∈ Function.support F from h)⟩, one_mul]
  · intro Q hQ
    have hz : F (Q.velocity, Q.position) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hm := hF.2.2 h
      have hv : Q.velocity ∈ PDE.euclideanBall v₀ R := by
        simpa only [evolutionStateSet, movingDomain_ball_zero, mem_prod, mem_univ,
          and_true] using hm
      exact hQ hv
    change χ (Q.time, Q.velocity, Q.position) * F (Q.velocity, Q.position) = 0
    rw [hz, mul_zero]

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Terminal interior probes see exactly the actual valid-state transition measure. -/
theorem ballExit_terminal_probe_identity
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (F : BoundedBorel (EvolutionAmbientState d))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall v₀ R) (fun _ => 0) T.1 F) :
    (∫ Q, F (Q.velocity, Q.position)
      ∂(ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
        {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}) =
      ∫ w, F w.1 ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
        (ballStartState P) := by
  have hreal := localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR
  obtain ⟨u, hu, hval, _⟩ := hreal.1 T.1 F hF
  have hur := exit_terminal_physical_regular (a := P.1.time) B F u hu
  have hi := ballExit_represents hH hLE hd hlam hLam B hB v₀ hR P T
    (u ∘ sectionTwoPoint) hur.2.1
    (isKineticC112On_of_contDiffOn (isOpen_localStrip _ _ _ _)
      (boundary_physical_smooth_to_native hur.1)) hur.2.2.1 hur.2.2.2
  have hside : MeasurableSet {Q : KineticPoint d | Q.velocity ∈ PDE.euclideanBall v₀ R} :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage
      continuous_velocity.measurable
  have heq : (u ∘ sectionTwoPoint) =ᵐ[ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T]
      ({Q | Q.velocity ∈ PDE.euclideanBall v₀ R}.indicator
        (fun Q => F (Q.velocity, Q.position))) := by
    filter_upwards [ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T] with Q hQ
    by_cases hv : Q.velocity ∈ PDE.euclideanBall v₀ R
    · rw [indicator_of_mem (show Q ∈ {Q | Q.velocity ∈ PDE.euclideanBall v₀ R} from hv)]
      rcases hQ with hQ | hQ
      · exact hu.2.2.2.2.1 _ ⟨hQ.1, by
          simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2⟩
      · exact False.elim ((mem_interior_iff_notMem_frontier hv).mp
          ((PDE.isOpen_euclideanBall v₀ R).interior_eq.symm ▸ hv) hQ.2.2)
    · rw [indicator_of_notMem
        (show Q ∉ {Q | Q.velocity ∈ PDE.euclideanBall v₀ R} from hv)]
      have hl : Q.velocity ∈ frontier (PDE.euclideanBall v₀ R) := by
        rcases hQ with hQ | hQ
        · exact ⟨hQ.2, by
            simpa only [(PDE.isOpen_euclideanBall v₀ R).interior_eq] using hv⟩
        · exact hQ.2.2
      have ht : Q.time ≤ T.1 := by rcases hQ with hQ | hQ <;> grind
      exact hu.2.2.2.2.2 _ ⟨ht, by
        simpa only [sectionTwoPoint, movingDomain_ball_zero] using hl⟩
  rw [← integral_indicator hside]
  rw [← integral_congr_ae heq, ← hi]
  exact (hval P.1.time T.2.le (ballStartState P)).trans
    (hreal.2.1 P.1.time T.1 T.2.le (ballStartState P) (terminalStateDatum F))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
