module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationEndpoint
import Mathlib.Tactic

/-! # Uniform source time power for signed barrier endpoint differences -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory
open scoped ENNReal

/-- The source velocity restriction gives the cubic position moment scale. -/
theorem position_moment_scale_le {v M T Lam : ℝ} (hT : 0 ≤ T)
    (hv : |v| ≤ M*Real.sqrt T) :
    2*v^2*T^2+4/3*Lam*T^3 ≤ (2*M^2+4/3*Lam)*T^3 := by
  have hs := Real.sq_sqrt hT
  have hsq : v^2 ≤ M^2*T := by
    have h := mul_self_le_mul_self (abs_nonneg v) hv
    rw [← pow_two, ← pow_two, sq_abs, mul_pow, hs] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg T)
  nlinarith only [hmul]

/-- The origin-extension modulus yields the exact source uniform endpoint time power.
The constant is fixed before the coefficient, pole, terminal time and spatial shift. -/
theorem deterministic_barrier_endpoint_uniform_of_modulus
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha B M : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hB : 0 ≤ B)
    (Phi : Z → ℝ) (hPhi : Continuous Phi)
    (hmod : ∀ z w : Z, |Phi z-Phi w| ≤
      B*(|z.1-w.1|^(alpha/3)+|z.2-w.2|^alpha)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ),
      |z.2| ≤ M*Real.sqrt (T : ℝ) →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      Integrable (fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)) (kernelXV E T z) ∧
        (∫ w, |Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)| ∂kernelXV E T z) ≤
          C*(T : ℝ)^(alpha/2) := by
  let D := 2*M^2+4/3*Lam
  let C0 := B*(D^(alpha/6)+(2*Lam)^(alpha/2))
  have hL : 0 ≤ Lam := hlam.le.trans hLam
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 ≤ C0 := by
    exact mul_nonneg hB (add_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg (by positivity) _))
  refine ⟨C0+1, by linarith, ?_⟩
  intro A z T Y hv
  have h := deterministic_barrier_endpoint_of_modulus hH hLE hlam hLam
    alpha B ha0 ha1 hB Phi hPhi hmod A z T Y
  refine ⟨h.1, h.2.trans ?_⟩
  have hp : 0 ≤ 2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3 := by
    have ht := T.property
    positivity
  have hbound := Real.rpow_le_rpow hp (position_moment_scale_le T.property hv)
    (show 0 ≤ alpha/6 by linarith)
  have he : ((T : ℝ)^(3 : ℕ))^(alpha/6) = (T : ℝ)^(alpha/2) := by
    exact (Real.rpow_natCast_mul T.property 3 (alpha/6)).symm.trans
      (congrArg (fun a : ℝ => (T : ℝ)^a) (by ring))
  have hpos : (D*(T : ℝ)^(3 : ℕ))^(alpha/6) = D^(alpha/6)*(T : ℝ)^(alpha/2) :=
    (Real.mul_rpow hD (pow_nonneg T.property 3)).trans
      (congrArg (fun a : ℝ => D^(alpha/6)*a) he)
  have hvel : (2*Lam*(T : ℝ))^(alpha/2) = (2*Lam)^(alpha/2)*(T : ℝ)^(alpha/2) :=
    Real.mul_rpow (by positivity) T.property
  calc
    _ ≤ B*((D*(T : ℝ)^(3 : ℕ))^(alpha/6)+(2*Lam*(T : ℝ))^(alpha/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbound le_rfl) hB
    _ = C0*(T : ℝ)^(alpha/2) := by
      rw [hpos, hvel]
      change B*(D^(alpha/6)*(T : ℝ)^(alpha/2)+
        (2*Lam)^(alpha/2)*(T : ℝ)^(alpha/2)) =
          (B*(D^(alpha/6)+(2*Lam)^(alpha/2)))*(T : ℝ)^(alpha/2)
      ring
    _ ≤ (C0+1)*(T : ℝ)^(alpha/2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg T.property _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
