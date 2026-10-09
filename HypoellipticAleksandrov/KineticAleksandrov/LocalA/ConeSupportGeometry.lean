module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportProbes
import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Fourier

/-! # Directional transport inequalities determine the literal Euclidean cone -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Parabolic
open scoped Topology

/-- The Euclidean ball controls every directional transport speed. -/
theorem cone_directional_speed {d : ℕ} (e v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (w : PDE.Vec d) (hw : w ∈ PDE.euclideanBall v₀ R) :
    -(PDE.vecEuclideanNorm e * R) - PDE.vecDot e v₀ + PDE.vecDot w e ≤ 0 := by
  have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hw
  have hd := (le_abs_self (PDE.vecDot e (w - v₀))).trans
    (PDE.abs_vecDot_le_vecEuclideanNorm_mul e (w - v₀))
  have hb := mul_le_mul_of_nonneg_left hv.le (PDE.vecEuclideanNorm_nonneg e)
  rw [Scaling.vecDot_sub_right] at hd
  rw [PDE.vecDot_comm w e]
  linarith only [hd, hb]

/-- The chosen affine coordinate is exactly a centered directional cone defect. -/
theorem coneCoordinate_centered {d : ℕ} (P Q : KineticPoint d)
    (e v₀ : PDE.Vec d) (R : ℝ) :
    coneCoordinate (-(PDE.vecEuclideanNorm e * R) - PDE.vecDot e v₀) e
      (-(-(PDE.vecEuclideanNorm e * R) - PDE.vecDot e v₀) * P.time -
        PDE.vecDot e P.position) Q =
      PDE.vecDot e (Q.position - P.position - (Q.time - P.time) • v₀) -
        PDE.vecEuclideanNorm e * (R * (Q.time - P.time)) := by
  rw [coneCoordinate, Scaling.vecDot_sub_right, Scaling.vecDot_sub_right,
    Scaling.vecDot_smul_right]
  ring

/-- Countably many dense directions upgrade almost-everywhere directional bounds to a norm bound. -/
theorem cone_norm_of_directional_ae {d : ℕ} (μ : Measure (KineticPoint d))
    (P : KineticPoint d) (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 ≤ R)
    (ht : ∀ᵐ Q ∂μ, P.time ≤ Q.time)
    (hd : ∀ e : PDE.Vec d, ∀ᵐ Q ∂μ,
      PDE.vecDot e (Q.position - P.position - (Q.time - P.time) • v₀) ≤
        PDE.vecEuclideanNorm e * (R * (Q.time - P.time))) :
    ∀ᵐ Q ∂μ, PDE.vecEuclideanNorm
      (Q.position - P.position - (Q.time - P.time) • v₀) ≤ R * (Q.time - P.time) := by
  obtain ⟨D, hc, hD⟩ := TopologicalSpace.exists_countable_dense (PDE.Vec d)
  let : Countable D := hc.to_subtype
  have ha : ∀ᵐ Q ∂μ, ∀ e : D,
      PDE.vecDot e.1 (Q.position - P.position - (Q.time - P.time) • v₀) ≤
        PDE.vecEuclideanNorm e.1 * (R * (Q.time - P.time)) :=
    ae_all_iff.mpr (fun e => hd e.1)
  filter_upwards [ha, ht] with Q hQ hqt
  let y := Q.position - P.position - (Q.time - P.time) • v₀
  have hl : ∀ e ∈ closure D, PDE.vecDot e y ≤
      PDE.vecEuclideanNorm e * (R * (Q.time - P.time)) :=
    le_on_closure (fun e he => hQ ⟨e, he⟩)
      (by unfold PDE.vecDot; fun_prop)
      (PDE.continuous_vecEuclideanNorm.mul continuous_const).continuousOn
  have hy := hl y (by rw [hD.closure_eq]; exact mem_univ y)
  rw [← PDE.vecNormSq, ← PDE.vecEuclideanNorm_sq, pow_two] at hy
  by_cases hz : PDE.vecEuclideanNorm y = 0
  · rw [hz]
    exact mul_nonneg hR (sub_nonneg.mpr hqt)
  · exact le_of_mul_le_mul_left hy
      (lt_of_le_of_ne (PDE.vecEuclideanNorm_nonneg y) (Ne.symm hz))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
