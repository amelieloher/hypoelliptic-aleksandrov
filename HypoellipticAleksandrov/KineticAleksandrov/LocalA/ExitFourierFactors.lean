module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierLater

/-! # Exact centered phase factorization and genuine later translation covariance -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- Centering the first time step multiplies its displacement Fourier transform by this phase. -/
def exitFourierStepPhase {d : ℕ} (P : KineticPoint d) (s : ℝ) (v₀ ξ : PDE.Vec d) : ℂ :=
  Complex.exp (Complex.I * (PDE.vecDot ξ ((s - P.time) • v₀) : ℂ))

/-- The centering step is a phase of modulus one. -/
theorem norm_exitFourierStepPhase {d : ℕ}
    (P : KineticPoint d) (s : ℝ) (v₀ ξ : PDE.Vec d) :
    ‖exitFourierStepPhase P s v₀ ξ‖ = 1 := by
  simp [exitFourierStepPhase, Complex.norm_exp, Complex.mul_re]

/-- Physical centered Fourier tests factor at the true intermediate physical pole. -/
theorem exitFourierTest_factor {d : ℕ} (P W Q : KineticPoint d)
    (v₀ ξ : PDE.Vec d) (E : Set (TimeVelocity d)) :
    exitFourierTest P v₀ ξ E Q =
      exitFourierStepPhase P W.time v₀ ξ *
        fourierPhase ξ P.position (W.velocity, W.position) * exitFourierTest W v₀ ξ E Q := by
  have hd : PDE.vecDot ξ (Q.position - P.position - (Q.time - P.time) • v₀) =
      -PDE.vecDot ξ ((W.time - P.time) • v₀) +
        (PDE.vecDot ξ (W.position - P.position) +
          PDE.vecDot ξ (Q.position - W.position - (Q.time - W.time) • v₀)) := by
    unfold PDE.vecDot
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hex : -Complex.I *
      (PDE.vecDot ξ (Q.position - P.position - (Q.time - P.time) • v₀) : ℂ) =
      Complex.I * (PDE.vecDot ξ ((W.time - P.time) • v₀) : ℂ) +
        (-Complex.I * (PDE.vecDot ξ (W.position - P.position) : ℂ) +
          -Complex.I *
            (PDE.vecDot ξ (Q.position - W.position - (Q.time - W.time) • v₀) : ℂ)) := by
    rw [hd]
    push_cast
    ring
  by_cases hQ : (Q.time, Q.velocity) ∈ E
  · simp only [exitFourierTest,
      indicator_of_mem (show Q ∈ {Q | (Q.time, Q.velocity) ∈ E} from hQ),
      Function.comp_apply, exitPhase, exitCoordinates, exitFourierStepPhase, fourierPhase]
    rw [hex, Complex.exp_add, Complex.exp_add, mul_assoc]
  · simp only [exitFourierTest,
      indicator_of_notMem (show Q ∉ {Q | (Q.time, Q.velocity) ∈ E} from hQ), mul_zero]

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Position covariance identifies later poles with the zero-position Fourier family. -/
theorem ballLaterExitFourier_eq_state (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s) :
    ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ
      ⟨w.1.1, w.2.1⟩ =
      exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart s w) ⟨T, hsT⟩) ξ := by
  let v : EvolutionPosition (PDE.euclideanBall v₀ R) (fun _ => 0) s := ⟨w.1.1, w.2.1⟩
  let P := ballStateStart s (positionStateZero _ _ s v)
  have h := ballExit_translation hH hLE hd hlam hLam B hB v₀ hR w.1.2 P ⟨T, hsT⟩
  let F (x : PDE.Vec d) := exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR
    ⟨⟨s, x, w.1.1⟩, ball_state_velocity_mem s w⟩ ⟨T, hsT⟩) ξ
  have hh : F 0 = F (0 + w.1.2) := congrArg (fun μ => exitFourier μ ξ) h.symm
  exact hh.trans (congrArg F (zero_add w.1.2))

/-- The zero-extended scalar test has modulus at most one on every ambient velocity. -/
theorem norm_ballLaterExitFourierTest_le_one (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (v : PDE.Vec d) :
    ‖ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ E v‖ ≤ 1 := by
  by_cases hv : v ∈ movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) s
  · rw [ballLaterExitFourierTest_valid hH hLE hd hlam hLam B hB v₀ hR
      s T hsT ξ E ⟨v, hv⟩]
    let ν := ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ ⟨v, hv⟩
    have he : ν.variation E ≤ 1 := (measure_mono (subset_univ E)).trans
      (ballLaterExitFourier_variation_le_one hH hLE hd hlam hLam B hB v₀ hR
        s T hsT ξ ⟨v, hv⟩)
    exact (VectorMeasure.norm_measure_le_variation
      (μ := ν) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))).trans
      (by simpa only [Measure.real, ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top he)
  · rw [ballLaterExitFourierTest_invalid hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ E v hv]
    simp only [norm_zero, zero_le_one]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
