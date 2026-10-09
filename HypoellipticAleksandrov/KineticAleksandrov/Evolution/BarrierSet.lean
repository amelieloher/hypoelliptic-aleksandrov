module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry

/-!
# The collar region and the scaled supersolution

Definitions for the collar comparison of (A.1): the profile
`w(t) = (1 - exp (-κ t))/κ`, the collar region `{r₀ - d_* ≤ |y - m(σ)| ≤ r₀}` of the moving
ball, and the supersolution `‖F‖ w(d)/w(d_*)` with `m = γ + c`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Filter Set
open scoped Topology

/-- The profile `w(t) = (1 - exp (-κ t))/κ`. -/
def barrierW (κ t : ℝ) : ℝ := (1 - Real.exp (-κ * t)) / κ

/-- The constant `κ = (1 + L_γ)/λ`. -/
def collarKappa (Lγ lam : ℝ) : ℝ := (1 + Lγ) / lam

/-- The squared distance of the position from the moving centre `γ(σ) + c`. -/
def centreSq {n : ℕ} (c : PDE.Vec n) (γ : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  PDE.vecNormSq (p.position - (γ p.time + c))

/-- The closed collar region of the moving ball on the time slab `[a, b]`. -/
def collarClosed {n : ℕ} (c : PDE.Vec n) (r₀ dstar : ℝ) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  movingClosedSlab (PDE.euclideanBall c r₀) γ a b ∩ {p | (r₀ - dstar) ^ 2 ≤ centreSq c γ p}

/-- The active part of the collar region on `[a, b)`. -/
def collarActive {n : ℕ} (c : PDE.Vec n) (r₀ dstar : ℝ) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  movingActiveSlab (PDE.euclideanBall c r₀) γ a b ∩ {p | (r₀ - dstar) ^ 2 < centreSq c γ p}

/-- The scaled supersolution `FB * w(d)/w(d_*)`, with `d = r₀ - |y - γ(σ) - c|`. -/
def collarSupersolution {n : ℕ} (c : PDE.Vec n) (r₀ dstar Lγ lam FB : ℝ)
    (γ : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  FB / barrierW (collarKappa Lγ lam) dstar *
    collarBarrier (collarKappa Lγ lam) r₀ (fun t => γ t + c) p

/-- The profile `w` is positive on positive arguments. -/
theorem barrierW_pos {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) : 0 < barrierW κ t := by
  unfold barrierW
  have : Real.exp (-κ * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  exact div_pos (by linarith) hκ

/-- Continuity of the squared distance to the moving centre. -/
theorem continuous_centreSq {n : ℕ} (c : PDE.Vec n) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    Continuous (centreSq c γ) := by
  have h1 : Continuous (fun p : KineticPoint n => p.position - (γ p.time + c)) :=
    continuous_position.sub ((hγ.comp continuous_time).add continuous_const)
  have : centreSq c γ = fun p => ∑ i, (p.position i - (γ p.time + c) i) ^ 2 := by
    funext p
    unfold centreSq
    rw [PDE.vecNormSq_eq_sum_sq]
    rfl
  rw [this]
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact ((continuous_apply i).comp h1).pow 2

/-- Continuity of the collar barrier. -/
theorem continuous_collarBarrier {n : ℕ} (c : PDE.Vec n) (κ r₀ : ℝ) {γ : ℝ → PDE.Vec n}
    (hγ : Continuous γ) :
    Continuous (collarBarrier κ r₀ (fun t => γ t + c)) := by
  have h := continuous_centreSq c hγ
  unfold collarBarrier collarProfile
  have h' : Continuous (fun p : KineticPoint n => PDE.vecNormSq (p.position - (γ p.time + c))) := h
  fun_prop

/-- Continuity of the scaled collar supersolution. -/
theorem continuous_collarSupersolution {n : ℕ} (c : PDE.Vec n) (r₀ dstar Lγ lam FB : ℝ)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    Continuous (collarSupersolution c r₀ dstar Lγ lam FB γ) :=
  continuous_const.mul (continuous_collarBarrier c _ r₀ hγ)

/-- The collar barrier is nonnegative inside the closed ball. -/
theorem collarBarrier_nonneg {n : ℕ} {c : PDE.Vec n} {κ r₀ : ℝ} (hκ : 0 < κ) (hr₀ : 0 ≤ r₀)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p ≤ r₀ ^ 2) :
    0 ≤ collarBarrier κ r₀ (fun t => γ t + c) p := by
  unfold collarBarrier collarProfile
  have h1 : Real.sqrt (PDE.vecNormSq (p.position - (γ p.time + c))) ≤ r₀ :=
    Real.sqrt_le_iff.mpr ⟨hr₀, hS⟩
  have h2 : Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - (γ p.time + c))))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  exact div_nonneg (by linarith) hκ.le

/-- On the inner edge of the collar the barrier equals `w(d_*)`. -/
theorem collarBarrier_inner {n : ℕ} {c : PDE.Vec n} {κ r₀ dstar : ℝ} (hd : dstar < r₀)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p = (r₀ - dstar) ^ 2) :
    collarBarrier κ r₀ (fun t => γ t + c) p = barrierW κ dstar := by
  unfold collarBarrier collarProfile barrierW
  have h : PDE.vecNormSq (p.position - (γ p.time + c)) = (r₀ - dstar) ^ 2 := hS
  rw [h, Real.sqrt_sq (by linarith)]
  congr 3
  ring

/-- On the inner edge of the collar the supersolution equals `‖F‖`. -/
theorem collarSupersolution_inner {n : ℕ} {c : PDE.Vec n} {r₀ dstar Lγ lam FB : ℝ}
    (hd : dstar < r₀) (hκ : 0 < collarKappa Lγ lam) (hdpos : 0 < dstar)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p = (r₀ - dstar) ^ 2) :
    collarSupersolution c r₀ dstar Lγ lam FB γ p = FB := by
  unfold collarSupersolution
  rw [collarBarrier_inner hd hS]
  have := (barrierW_pos hκ hdpos).ne'
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov
