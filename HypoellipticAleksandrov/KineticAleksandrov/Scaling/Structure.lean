module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Structural bounds are unchanged by the kinetic scaling (companion paper, Lemma 2.5)

For `b_r(Y) = r⁻¹ (b(v₀ + r Y) - b(v₀))` one has `D b_r (Y) = D b (v₀ + r Y)`, so the transport
bounds `HasTransportBounds m L_b` and smoothness pass from `b` to `b_r` with the same constants.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo (scaledDrift HasTransportBounds)

variable {d : ℕ} (b : PDE.Vec d → PDE.Vec d) (v₀ : PDE.Vec d) (r : {r : ℝ // 0 < r})

theorem scaledDrift_apply (Y : PDE.Vec d) :
    scaledDrift b v₀ r Y = r.1⁻¹ • (b (v₀ + r.1 • Y) - b v₀) := rfl

/-- The Euclidean Lipschitz constant of the drift is unchanged. -/
theorem scaledDrift_lipschitz {L_b : ℝ} (h : HasEuclideanLipschitzDrift L_b b) :
    HasEuclideanLipschitzDrift L_b (scaledDrift b v₀ r) := by
  intro Y Y'
  have hr : r.1 ≠ 0 := r.2.ne'
  have hsub : scaledDrift b v₀ r Y - scaledDrift b v₀ r Y' =
      r.1⁻¹ • (b (v₀ + r.1 • Y) - b (v₀ + r.1 • Y')) := by
    rw [scaledDrift_apply, scaledDrift_apply]
    module
  have harg : (v₀ + r.1 • Y) - (v₀ + r.1 • Y') = r.1 • (Y - Y') := by module
  rw [hsub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 r.2)]
  have h1 := h (v₀ + r.1 • Y) (v₀ + r.1 • Y')
  rw [harg, PDE.vecEuclideanNorm_smul, abs_of_pos r.2] at h1
  calc r.1⁻¹ * PDE.vecEuclideanNorm (b (v₀ + r.1 • Y) - b (v₀ + r.1 • Y'))
      ≤ r.1⁻¹ * (L_b * (r.1 * PDE.vecEuclideanNorm (Y - Y'))) := by
        gcongr
        exact inv_nonneg.2 r.2.le
    _ = L_b * PDE.vecEuclideanNorm (Y - Y') := by field_simp

/-- The affine rescaling of the drift has the shifted derivative. -/
theorem fderiv_scaledDrift (Y : PDE.Vec d) :
    fderiv ℝ (scaledDrift b v₀ r) Y = fderiv ℝ b (v₀ + r.1 • Y) := by
  have hr : r.1 ≠ 0 := r.2.ne'
  by_cases hb : DifferentiableAt ℝ b (v₀ + r.1 • Y)
  · have hA : HasFDerivAt (fun y : PDE.Vec d => v₀ + r.1 • y)
        (r.1 • ContinuousLinearMap.id ℝ (PDE.Vec d)) Y :=
      ((hasFDerivAt_id (𝕜 := ℝ) Y).const_smul r.1).const_add v₀
    have h1 := ((hb.hasFDerivAt.comp Y hA).sub_const (b v₀)).const_smul r.1⁻¹
    have h2 : (r.1⁻¹ • ((fderiv ℝ b (v₀ + r.1 • Y)).comp
        (r.1 • ContinuousLinearMap.id ℝ (PDE.Vec d)))) = fderiv ℝ b (v₀ + r.1 • Y) := by
      ext v : 1
      simp [smul_smul, hr]
    rw [h2] at h1
    exact h1.fderiv
  · have hnd : ¬ DifferentiableAt ℝ (scaledDrift b v₀ r) Y := by
      intro hd
      apply hb
      have hA : DifferentiableAt ℝ (fun y : PDE.Vec d => r.1⁻¹ • (y - v₀)) (v₀ + r.1 • Y) := by
        fun_prop
      have hpt : r.1⁻¹ • ((v₀ + r.1 • Y) - v₀) = Y := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      have hd' : DifferentiableAt ℝ (scaledDrift b v₀ r) (r.1⁻¹ • ((v₀ + r.1 • Y) - v₀)) := by
        rw [hpt]
        exact hd
      have hcomp := ((hd'.comp (v₀ + r.1 • Y) hA).const_smul r.1).add_const (b v₀)
      have hfun : b = fun y => r.1 • ((scaledDrift b v₀ r ∘ fun y => r.1⁻¹ • (y - v₀)) y) +
          b v₀ := by
        funext y
        simp only [Function.comp_apply, scaledDrift_apply, smul_smul, smul_sub,
          mul_inv_cancel₀ hr, one_smul, add_sub_cancel, sub_add_cancel]
      convert hcomp using 1
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hb]

/-- The unit-direction derivative coercivity constant of the drift is unchanged. -/
theorem scaledDrift_coercivity {m : ℝ} (h : HasUnitDirectionDriftCoercivity m b) :
    HasUnitDirectionDriftCoercivity m (scaledDrift b v₀ r) := by
  intro Y ξ hξ
  rw [fderiv_scaledDrift]
  exact h _ ξ hξ

/-- Both transport bounds are unchanged (`D b_r (Y) = D b (v_* + r Y)`). -/
theorem scaledDrift_transportBounds {m L_b : ℝ} (h : HasTransportBounds m L_b b) :
    HasTransportBounds m L_b (scaledDrift b v₀ r) :=
  ⟨scaledDrift_lipschitz b v₀ r h.1, scaledDrift_coercivity b v₀ r h.2⟩

/-- Smoothness of the drift is preserved. -/
theorem scaledDrift_smooth (h : IsSmoothDrift b) : IsSmoothDrift (scaledDrift b v₀ r) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => v₀ + r.1 • y) := by fun_prop
  have h1 := (h.comp hA).sub (contDiff_const (c := b v₀))
  exact h1.const_smul r.1⁻¹

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
