module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitMass

/-! # Gaussian short-time loss for the actual killed velocity-ball evolution

The source constants are `2*d` and `1/(64*d*Lam)`. The proof compares compact
terminal solutions with the explicit two-sign exponential barrier and then
identifies marginal mass with the joint master mass at the physical starting point.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic SectionTwo Set MeasureTheory

/-- The explicit source Gaussian bound for the lost ball-kernel mass. -/
theorem ballKernel_short_time_loss_explicit
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4)) :
    1 - (ballTransition hH hLE hd hlam hLam B hB v₀ hR P T).real univ ≤
      2 * (d : ℝ) * Real.exp
        (-R ^ 2 / (64 * (d : ℝ) * Lam * (T.1 - P.1.time))) := by
  let δ := R / (4 * Real.sqrt d)
  let α := δ / (2 * Lam * (T.1 - P.1.time))
  let Ψ := ballExitBarrier Lam α δ T.1 P.1.velocity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  have hα : 0 ≤ α := by
    dsimp only [α, δ]
    exact (div_pos (div_pos hR (by positivity))
      (mul_pos (mul_pos (by norm_num) hLam0) (sub_pos.mpr T.2))).le
  have h := ballExit_marginal_loss_le v₀ hR T.2 B hB
    (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (localBallKernel_marginal hH hLE hd hlam hLam B hB v₀ hR) Ψ
    (ballExitBarrier_contDiff _ _ _ _ _)
    (fun p _ => ballExitBarrier_nonneg _ _ _ _ _ p)
    (fun p _ => ballExitBarrier_operator_nonpos B hB _ _ _ _ p)
    (fun p hp => ballExitBarrier_lateral hd hR hLam0 α T.1 hα v₀ P.1.velocity hv p hp)
    P.1.velocity P.2
  have hm := ballTransition_mass_eq_marginal hH hLE hd hlam hLam B hB v₀ hR P T
  have hbound := h.trans_eq (ballExitBarrier_optimized hd hLam0 hR T.2 P.1.velocity)
  calc
    _ = _ := congrArg (fun m : ℝ => 1 - m) hm
    _ ≤ _ := hbound

/-- The planned short-time exit estimate, with constants uniform over the coefficient,
center, radius, physical starting point, and terminal time. -/
theorem ballKernel_short_time_loss
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time ≤ R ^ 2 / 8 →
      let Kpt := ballTransition hH hLE hd hlam hLam B hB v₀ hR
      1 - (Kpt P T).real univ ≤ C * Real.exp (-c * R ^ 2 / (T.1 - P.1.time)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  refine ⟨2 * d, 1 / (64 * d * Lam), mul_pos (by norm_num) hdR,
    div_pos one_pos (mul_pos (mul_pos (by norm_num) hdR) hLam0), ?_⟩
  intro B hB v₀ R hR P T hv _hsmall
  have h := ballKernel_short_time_loss_explicit hH hLE hd hlam hLam B hB v₀ hR P T hv
  convert h using 1
  congr 2
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
