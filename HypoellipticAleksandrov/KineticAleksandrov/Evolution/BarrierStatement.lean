module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierTwo

/-!
# Statement of (A.1)

The two uniform barriers for a viscous classical terminal solution `u_ε` on the moving ball
`B_{r₀}(γ(σ) + c)`: with `κ = (1 + L_γ)/λ` and `w(t) = (1 - exp (-κ t))/κ`,

* `|u_ε| ≤ ‖F‖ min {1, w(d)/w(d_*)}` with `d = r₀ - |y - γ(σ) - c|`;
* `|u_ε - F| ≤ (τ - σ) M_F` for `τ - σ ≤ d_*/(1 + L_γ)`,

where `‖F‖` is an upper bound of `|F|` (in particular the supremum norm) and `M_F` an upper
bound of `|L_ε F|` on `σ ≤ τ` (in particular `sup_ε ‖L_ε F‖`).  The constant `d_*` obeys the two
source smallness conditions `d_* < r₀/4` and `2 d_* ≤ dist (supp F, ∂ Ω_τ)`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- (A.1). -/
theorem two_barriers {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r₀) γ τ F)
    {dstar : ℝ} (hd : 0 < dstar) (hd4 : dstar < r₀ / 4)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * dstar ≤ r₀ - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    {FB M : ℝ} (hFB : ∀ q, |F q| ≤ FB)
    (hM : ∀ p : KineticPoint n, p.time ≤ τ →
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u) :
    (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      |u p| ≤ FB * min 1
        (barrierW (collarKappa Lγ lam)
            (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa Lγ lam) dstar)) ∧
    (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      τ - dstar / (1 + Lγ) ≤ p.time →
        |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M) := by
  have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
  have hdr : dstar < r₀ := by linarith
  have hκ : 0 < collarKappa Lγ lam := div_pos (by linarith) hlam
  have hFB0 : 0 ≤ FB := le_trans (abs_nonneg _) (hFB 0)
  have hWpos : 0 < barrierW (collarKappa Lγ lam) dstar := barrierW_pos hκ hd
  refine ⟨?_, classical_sub_terminalDatum_le hr₀ hγ.1 hLγ hγL hlam hB hb hε0 hε1 hF hd hsupp hFB hM
    hu⟩
  intro p hp
  have hAbs := classical_abs_le_const hΩo hγ.1 hlam hB hb hε0 hε1 hu hFB
  have hnu := hu.neg hΩo hγ.1
  rcases le_total 1 (barrierW (collarKappa Lγ lam)
      (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
        barrierW (collarKappa Lγ lam) dstar) with h1 | h1
  · rw [min_eq_left h1]
    have := hAbs p hp
    linarith
  · rw [min_eq_right h1]
    have hle : barrierW (collarKappa Lγ lam)
        (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) ≤
          barrierW (collarKappa Lγ lam) dstar := by
      rwa [div_le_one hWpos] at h1
    have hd' := le_of_barrierW_le hκ hle
    have hnorm : r₀ - dstar ≤ PDE.vecEuclideanNorm (p.position - (γ p.time + c)) := by
      linarith
    have hS : (r₀ - dstar) ^ 2 ≤ centreSq c γ p := by
      have h2 : (r₀ - dstar) ^ 2 ≤ PDE.vecEuclideanNorm (p.position - (γ p.time + c)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hnorm 2
      rw [PDE.vecEuclideanNorm_sq] at h2
      exact h2
    have hup := classical_le_collarSupersolution (c := c) hd hdr hγ hLγ hγL hlam hB hb hε0 hε1 hu
      hFB0 (fun q hq => (le_abs_self _).trans (hAbs q hq))
      (fun q hq hqS => by
        rw [hu.2.2.2.2.1 q hq, terminalDatum_eq_zero_of_collar hd hdr hsupp hq.1 hqS])
      p hp hS
    have hdown := classical_le_collarSupersolution (c := c) hd hdr hγ hLγ hγL hlam hB hb hε0 hε1 hnu
      hFB0 (fun q hq => (neg_le_abs _).trans (hAbs q hq))
      (fun q hq hqS => by
        have h := hnu.2.2.2.2.1 q hq
        simp only [BoundedBorel.neg_apply] at h
        show -u q ≤ 0
        rw [h, terminalDatum_eq_zero_of_collar hd hdr hsupp hq.1 hqS]
        simp)
      p hp hS
    have hG : collarSupersolution c r₀ dstar Lγ lam FB γ p =
        FB * (barrierW (collarKappa Lγ lam)
            (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa Lγ lam) dstar) := by
      have : collarBarrier (collarKappa Lγ lam) r₀ (fun t => γ t + c) p =
          barrierW (collarKappa Lγ lam)
            (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) := rfl
      unfold collarSupersolution
      rw [this]
      ring
    rw [← hG]
    have hdown' : -u p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := hdown
    exact abs_le.mpr ⟨by linarith, hup⟩

/-- The terminal barriers `±F + (τ - σ) M` of Proposition 2.1 are
supersolutions of `L_ε` wherever `|L_ε F| ≤ M`. -/
theorem viscousTransportedOperator_terminalBarrier_nonpos {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε τ M : ℝ} {φ : KineticPoint n → ℝ} {p : KineticPoint n}
    (hφ : IsSliceRegularAt φ p) (hM : |viscousTransportedOperator B b ε φ p| ≤ M)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    viscousTransportedOperator B b ε (fun q => s * φ q + M * (τ - q.time)) p ≤ 0 := by
  have hT := isSliceRegularAt_time_sub (n := n) τ p
  have e1 : viscousTransportedOperator B b ε (fun q => s * φ q + M * (τ - q.time)) p =
      viscousTransportedOperator B b ε (fun q => s * φ q) p +
        viscousTransportedOperator B b ε (fun q => (-M) * (q.time - τ)) p := by
    have h : (fun q : KineticPoint n => s * φ q + M * (τ - q.time)) =
        fun q => s * φ q + (-M) * (q.time - τ) := by
      funext q
      ring
    rw [h]
    exact viscousTransportedOperator_add (u := fun q => s * φ q)
      (v := fun q => (-M) * (q.time - τ)) (hφ.const_mul s) (hT.const_mul (-M))
  rw [e1, viscousTransportedOperator_const_mul s hφ, viscousTransportedOperator_const_mul (-M) hT,
    viscousTransportedOperator_time_sub]
  have := abs_le.mp hM
  rcases hs with rfl | rfl <;> nlinarith [this.1, this.2]

/-- The supremum norm `‖F‖_∞` of a bounded Borel function. -/
def boundedBorelSupNorm {α : Type*} [MeasurableSpace α] (F : BoundedBorel α) : ℝ :=
  sSup (range fun x => |F x|)

/-- A bounded Borel function is bounded by its supremum norm. -/
theorem abs_le_boundedBorelSupNorm {α : Type*} [MeasurableSpace α] (F : BoundedBorel α)
    (x : α) : |F x| ≤ boundedBorelSupNorm F := by
  obtain ⟨C, -, hC⟩ := F.exists_bound
  exact le_csSup ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ ⟨x, rfl⟩

/-- The terminal generator bound `M_F = sup_{0 ≤ ε ≤ 1} ‖L_ε F‖_∞` over `σ ≤ τ`. -/
def terminalGeneratorSup {n : ℕ} (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) : ℝ :=
  sSup {x | ∃ ε ∈ Icc (0 : ℝ) 1, ∃ p : KineticPoint n, p.time ≤ τ ∧
    x = |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p|}

end HypoellipticAleksandrov.KineticAleksandrov
