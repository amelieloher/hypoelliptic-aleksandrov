module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierDefect
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierWhole
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierConstants

/-! # Short-time Fourier decay for the actual killed ball kernel

Domain monotonicity produces a positive full-minus-killed terminal measure.
Its variation costs exactly the lost mass, which has the proved Gaussian bound.
Full-space frequency decay supplies the second exponential term. Constants are
chosen uniformly before the coefficient, center, radius, and query.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic SectionTwo Set MeasureTheory

/-- The killed Fourier estimate, relative only to the two analytic hypotheses (Hörmander and
Lieberman) and with the literal valid query of the canonical ball kernel. -/
theorem ballKernel_short_time_fourier
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time ≤ R ^ 2 / 8 →
      let Kb := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
      ∀ (ξ : PDE.Vec d)
        (q : EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0)),
        q.1 = (P.1.time, (T.1, (P.1.velocity, P.1.position))) →
        ((fourierProjection Kb q ξ).variation univ).toReal ≤
          C * (Real.exp (-c * R ^ 2 / (T.1 - P.1.time)) +
            Real.exp (-c * (T.1 - P.1.time) *
              PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
  obtain ⟨Cs, cs, hCs, hcs, hloss⟩ :=
    ballKernel_short_time_loss hH hLE d hd lam Lam hlam hLam
  obtain ⟨Cf, cf, hCf, hcf, hdecay⟩ :=
    ballExit_full_fourier_decay hH hLE d hd lam Lam hlam hLam
  refine ⟨max Cs Cf, min cs cf, hCs.trans_le (le_max_left _ _), lt_min hcs hcf, ?_⟩
  intro B hB v₀ R hR P T hv hsmall
  dsimp only
  intro ξ q hq
  have hq0 : q = ballEvolutionQuery P T := Subtype.ext hq
  rw [hq0]
  obtain ⟨Sf, Kf, hreal, hdom⟩ :=
    ballExit_exists_full_evolution hH hLE hd hlam hLam B hB v₀ hR
  let Kb := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
  let qf := wholeSpaceQuery P.1.time T.1 T.2.le P.1.velocity P.1.position
  have hdef := killedFourier_variation_le_full_add_loss Kb Kf (ballEvolutionQuery P T)
    qf rfl (hdom (ballEvolutionQuery P T)) ξ
  have hf := hdecay B hB Sf Kf hreal P.1.time T.1 T.2
    P.1.velocity ξ P.1.position
  have hs := hloss B hB v₀ R hR P T hv hsmall
  let x := R ^ 2 / (T.1 - P.1.time)
  let y := (T.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
  have hx : 0 ≤ x := div_nonneg (sq_nonneg R) (sub_pos.mpr T.2).le
  have hy : 0 ≤ y := mul_nonneg (sub_pos.mpr T.2).le
    (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg ξ) _)
  have hs' : 1 - (Kb.master (ballEvolutionQuery P T)).real univ ≤
      Cs * Real.exp (-cs * x) := by
    change 1 - (Kb.master (ballEvolutionQuery P T)).real univ ≤
      Cs * Real.exp (-cs * R ^ 2 / (T.1 - P.1.time)) at hs
    have he : -cs * R ^ 2 / (T.1 - P.1.time) = -cs * x := by
      dsimp only [x]
      ring
    rwa [he] at hs
  have hf' : ((fourierProjection Kf qf ξ).variation univ).toReal ≤
      Cf * Real.exp (-cf * y) := by
    convert hf using 1
    congr 2
    dsimp only [y]
    ring
  calc
    _ ≤ ((fourierProjection Kf qf ξ).variation univ).toReal +
        (1 - (Kb.master (ballEvolutionQuery P T)).real univ) := by
      linarith only [hdef]
    _ ≤ Cs * Real.exp (-cs * x) + Cf * Real.exp (-cf * y) := by
      exact (add_le_add hf' hs').trans_eq (add_comm _ _)
    _ ≤ max Cs Cf * (Real.exp (-min cs cf * x) + Real.exp (-min cs cf * y)) :=
      ballExit_combine_exponentials hCs.le hCf.le hx hy
    _ = _ := by
      congr 2 <;> congr 1 <;> dsimp only [x, y] <;> ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
