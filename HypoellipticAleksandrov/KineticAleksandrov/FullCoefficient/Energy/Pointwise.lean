module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Flux
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Norms
import Mathlib.Algebra.Order.Chebyshev

/-!
# Pointwise algebra of the energy inequality

The energy inequality: coercivity (the coercivity estimate), the Young inequality and
the bound `|div_v β|² ≤ d |∇_v β|² ≤ (4d/λ) |Dβ|²_{M^h}`, all at a point of phase space.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- `|Dβ|²_{M^h} = ∑_{ij} Γ_{M^h}(β_ij, β_ij)`. -/
def coefficientGammaSum (lam h : ℝ) (β : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, ∑ j, flowGamma lam h (fun y => β y i j) (fun y => β y i j) y

/-- The `i`-th component `∑_j ∂_{v_j} β_ij` of `div_v β`. -/
def divCoefficient (β : EvolutionAmbientState d → PDE.Mat d) (y : EvolutionAmbientState d)
    (i : Fin d) : ℝ :=
  ∑ j, velocityPartial j (fun y => β y i j) y

theorem flowGamma_self_nonneg' {lam h : ℝ} (hlam : 0 < lam) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : 0 ≤ flowGamma lam h F F y :=
  flowGamma_self_nonneg hlam F y

theorem coefficientGammaSum_nonneg {lam h : ℝ} (hlam : 0 < lam)
    (β : EvolutionAmbientState d → PDE.Mat d) (y : EvolutionAmbientState d) :
    0 ≤ coefficientGammaSum lam h β y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => flowGamma_self_nonneg hlam _ _

theorem sum_sq_velocityPartial_le {lam h : ℝ} (hlam : 0 < lam) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    ∑ k, velocityPartial k F y ^ 2 ≤ 4 / lam * flowGamma lam h F F y := by
  rw [flowGamma_self]
  have h1 := Mform_ge (h := h) hlam (fun i => positionPartial i F y)
    (fun i => velocityPartial i F y)
  simp only [PDE.vecDot] at h1
  have e : ∑ k, velocityPartial k F y ^ 2 = ∑ k, velocityPartial k F y * velocityPartial k F y := by
    simp [sq]
  rw [e]
  have e2 : 4 / lam * Mform lam h (fun i => positionPartial i F y) (fun i => velocityPartial i F y)
      = 4 * Mform lam h (fun i => positionPartial i F y) (fun i => velocityPartial i F y) /
        lam := by
    ring
  rw [e2, le_div_iff₀ hlam]
  linarith

theorem sum_sq_sum_le (a : Fin d → Fin d → ℝ) :
    ∑ i, (∑ j, a i j) ^ 2 ≤ d * ∑ i, ∑ j, a i j ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => a i j)
  simpa using this

/-- `|div_v β|² ≤ (4d/λ) |Dβ|²_{M^h}`. -/
theorem sum_sq_divCoefficient_le {lam h : ℝ} (hlam : 0 < lam)
    (β : EvolutionAmbientState d → PDE.Mat d) (y : EvolutionAmbientState d) :
    ∑ i, divCoefficient β y i ^ 2 ≤ 4 * d / lam * coefficientGammaSum lam h β y := by
  have h1 : ∀ i j : Fin d, velocityPartial j (fun y => β y i j) y ^ 2 ≤
      4 / lam * flowGamma lam h (fun y => β y i j) (fun y => β y i j) y := fun i j =>
    (Finset.single_le_sum (f := fun k => velocityPartial k (fun y => β y i j) y ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans (sum_sq_velocityPartial_le hlam _ y)
  calc ∑ i, divCoefficient β y i ^ 2
      ≤ d * ∑ i, ∑ j, velocityPartial j (fun y => β y i j) y ^ 2 :=
        sum_sq_sum_le fun i j => velocityPartial j (fun y => β y i j) y
    _ ≤ d * ∑ i, ∑ j, 4 / lam * flowGamma lam h (fun y => β y i j) (fun y => β y i j) y := by
        gcongr with i _ j _
        exact h1 i j
    _ = 4 * d / lam * coefficientGammaSum lam h β y := by
        unfold coefficientGammaSum
        simp only [← Finset.mul_sum]
        ring

/-- Upper bound of the `M^h`-norm by the Euclidean gradient norm. -/
theorem flowGamma_self_le {lam h : ℝ} (hlam : 0 < lam) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    flowGamma lam h F F y ≤ lam / 2 * (3 * h ^ 2 + 2) * gradNormSq F y := by
  rw [flowGamma_self]
  set ξz : PDE.Vec d := fun i => positionPartial i F y with hξz
  set ξv : PDE.Vec d := fun i => velocityPartial i F y with hξv
  have hg : gradNormSq F y = PDE.vecDot ξz ξz + PDE.vecDot ξv ξv := by
    unfold gradNormSq
    rw [Fintype.sum_sum_type]
    simp only [PDE.vecDot, sq, hξz, hξv, velocityPartial_eq, positionPartial_eq]
    ring
  have hs : 0 ≤ ∑ i, (h * ξz i + ξv i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i, (h * ξz i + ξv i) ^ 2 =
      h ^ 2 * PDE.vecDot ξz ξz + 2 * h * PDE.vecDot ξz ξv + PDE.vecDot ξv ξv := by
    have : ∑ i, (h * ξz i + ξv i) ^ 2 = ∑ i, (h ^ 2 * (ξz i * ξz i) + (2 * h) * (ξz i * ξv i) +
        1 * (ξv i * ξv i)) := Finset.sum_congr rfl fun i _ => by ring
    rw [this, sum_quad]
    ring
  have h1 : 0 ≤ PDE.vecDot ξz ξz := PDE.vecNormSq_nonneg ξz
  have h2 : 0 ≤ PDE.vecDot ξv ξv := PDE.vecNormSq_nonneg ξv
  rw [hg]
  unfold Mform
  have : 2 * h ^ 2 * PDE.vecDot ξz ξz - 2 * h * PDE.vecDot ξz ξv + PDE.vecDot ξv ξv ≤
      (3 * h ^ 2 + 2) * (PDE.vecDot ξz ξz + PDE.vecDot ξv ξv) := by
    nlinarith [sq_nonneg h, mul_nonneg (sq_nonneg h) h2, mul_nonneg (sq_nonneg h) h1]
  calc lam / 2 * (2 * h ^ 2 * PDE.vecDot ξz ξz - 2 * h * PDE.vecDot ξz ξv + PDE.vecDot ξv ξv)
      ≤ lam / 2 * ((3 * h ^ 2 + 2) * (PDE.vecDot ξz ξz + PDE.vecDot ξv ξv)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- Coercivity and Young's inequality at a point:
`s (¼ |Dρ|²_M - (ρ²/λ) |w|²) ≤ s (ξ·Gξ + ρ ξ_v·w)`. -/
theorem energy_pointwise {lam h ρ s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s)
    {β : PDE.Mat d} (hβ : lam • (1 : PDE.Mat d) ≤ β) (ξz ξv w : PDE.Vec d) :
    s * (1 / 4 * Mform lam h ξz ξv - ρ ^ 2 / lam * ∑ i, w i ^ 2) ≤
      s * (Gform lam h β ξz ξv + ρ * ∑ i, ξv i * w i) := by
  refine mul_le_mul_of_nonneg_left ?_ hs
  have hG := Gform_ge (h := h) hlam hβ ξz ξv
  have hsq : 0 ≤ ∑ i, (1 / lam) * (lam / 2 * ξv i + ρ * w i) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_nonneg zero_le_one hlam.le) (sq_nonneg _)
  have hexp : ∑ i, (1 / lam) * (lam / 2 * ξv i + ρ * w i) ^ 2 =
      lam / 4 * PDE.vecDot ξv ξv + ρ * ∑ i, ξv i * w i + ρ ^ 2 / lam * ∑ i, w i ^ 2 := by
    simp only [PDE.vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
