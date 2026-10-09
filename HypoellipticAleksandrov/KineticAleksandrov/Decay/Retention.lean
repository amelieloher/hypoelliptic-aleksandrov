module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reduction of moving-tube mass to the scalar marginal

This source-step identity uses the shared parabolic marginal bundle and the
canonical ambient pushforward of the fixed-time marginal.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set MeasureTheory
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Moving-tube mass equals the mass of the supplied scalar marginal. -/
theorem tube_mass_eq_parabolic_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (B : CoefficientField d)
    (K : MovingFiberKernel Ω γ)
    (hpar : HasParabolicMarginalBundle Ω γ hΩ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d)
    (hv : v ∈ movingDomain Ω γ σ) :
    K.master (movingQuery σ τ hστ v z hv) (movingDomain Ω γ τ ×ˢ univ) =
      P K hΩ (scalarQuery σ τ hστ v hv) (movingDomain Ω γ τ) := by
  obtain ⟨_Q, hfirst, _⟩ := hpar (fun _ _ _ _ => rfl)
  change _ = (Measure.map Subtype.val
    (parabolicMarginalKernel K hΩ σ τ hστ ⟨v, hv⟩)) (movingDomain Ω γ τ)
  rw [hfirst σ τ hστ ⟨v, hv⟩ z,
    K.map_fiberFirstMarginal_eq_firstMarginal hΩ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)]
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst (measurableSet_movingDomain hΩ τ)]
  have hq : evolutionQueryOfState Ω γ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z) = movingQuery σ τ hστ v z hv := rfl
  rw [hq]
  congr 1
  ext p
  simp


private theorem master_mass_on_terminal_domain {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) :
    K.master q (evolutionStateSet Ω γ q.val.2.1) = K.master q univ := by
  have h := congrArg (fun μ : Measure (EvolutionAmbientState d) => μ univ)
    (K.terminal_support q)
  rw [Measure.restrict_apply MeasurableSet.univ] at h
  simpa only [univ_inter] using h

/-- The source moving-ball retention estimate for the supplied joint evolution. -/
theorem moving_ball_retention (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        PiecewiseC1On γ σ τ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ),
        ENNReal.ofReal (Real.exp (-C * (ρ⁻¹ ^ 2 + H ^ 2) * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv)
            (PDE.euclideanBall (γ τ) ρ ×ˢ univ) := by
  obtain ⟨N, hN, hchoice, hc⟩ := exists_retention_barrier_order d hd lam Lam hlam hlamLam
  let C : ℝ := 2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv
  have hlimit := moving_ball_retention_at_radius d hd lam Lam hlam hlamLam
    m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv
    N hN hchoice
  have hrate := retention_rate_uniform hN lam Lam ρ H hlam hlamLam hρ hc
  have hexp : Real.exp (-C * (ρ⁻¹ ^ 2 + H ^ 2) * (τ - σ)) ≤
      Real.exp (-barrierRate d N lam Lam ρ H * (τ - σ)) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hστ)
    convert neg_le_neg ht using 1 <;> ring
  have hmass := master_mass_on_terminal_domain K (movingQuery σ τ hστ' (γ σ) z hv)
  have hτ : clippedCurve γ σ τ τ = γ τ := clippedCurve_eq_of_mem γ ⟨hστ, le_rfl⟩
  have hdomain : movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) τ =
      PDE.euclideanBall (γ τ) ρ := by
    ext v
    rw [mem_movingDomain_euclideanBall_iff]
    simp only [hτ, add_zero, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq]
  change K.master (movingQuery σ τ hστ' (γ σ) z hv)
    (movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) τ ×ˢ univ) = _ at hmass
  rw [hdomain] at hmass
  rw [hmass]
  exact (ENNReal.ofReal_le_ofReal hexp).trans hlimit

end HypoellipticAleksandrov.KineticAleksandrov.Decay
