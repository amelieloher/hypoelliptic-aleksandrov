module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftWeakDerivativeFamilyAddTwo
public import HypoellipticAleksandrov.Parabolic.SmoothScalarWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeLocalL2StrongJet

/-!
# Higher-order source weak-derivative family

This file assembles a canonical finite weak-derivative family for a source
that is smooth on a neighborhood of a compact carrier.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- A source smooth near a compact carrier has one canonical weak-derivative
family through weight `2 * d + 6`, with compact derivative majorants and the
corresponding finite-family squared `L²` estimate. -/
theorem exists_higherOrderSourceWeakDerivativeFamily
    (d : ℕ)
    (K Q : Set (TimeVelocity d))
    (F : ℝ → PDE.Vec d → ℝ)
    (hQopen : IsOpen Q)
    (hQcompact : IsCompact (closure Q))
    (hQK : closure Q ⊆ K)
    (hFsmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2) K) :
    ∃ (B : ParabolicDerivativeIndex d (2 * d + 6) → ℝ)
      (Emax : ParabolicWeakDerivativeFamily d (2 * d + 6) Q
        (fun z : TimeVelocity d => F z.1 z.2)),
      (∀ beta, 0 ≤ B beta) ∧
      (∀ beta z, z ∈ closure Q →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (fun x : TimeVelocity d => F x.1 x.2) z| ≤ B beta) ∧
      (∀ beta, Emax.representative beta =
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (fun x : TimeVelocity d => F x.1 x.2)) ∧
      ParabolicWeakDerivativeFamily.squaredL2Norm Emax ≤
        volume.real Q *
          ∑ beta : ParabolicDerivativeIndex d (2 * d + 6),
            (B beta) ^ 2 := by
  obtain ⟨U, hUopen, hKU, hFsmoothU⟩ := hFsmooth
  let f : TimeVelocity d → ℝ := fun z ↦ F z.1 z.2
  have hfU : ContDiffOn ℝ (2 * d + 6) f U :=
    hFsmoothU.of_le (by
      norm_cast
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨V, B, hVopen, hQV, hVU, hVcompact, hBnonneg, hBbound⟩ :=
    exists_precompactOpen_coordinateIteratedFDeriv_majorants
      hUopen hQcompact (hQK.trans hKU) (fun _ : Unit ↦ f) (fun _ ↦ hfU)
  have hQfinite : (volume : Measure (TimeVelocity d)) Q < ∞ :=
    lt_of_le_of_lt (measure_mono subset_closure) hQcompact.measure_lt_top
  have hfQ : ContDiffOn ℝ (2 * d + 6) f Q :=
    hfU.mono (subset_closure.trans
      (hQV.trans (subset_closure.trans hVU)))
  have hboundQ : ∀ (beta : ParabolicDerivativeIndex d (2 * d + 6))
      (z : TimeVelocity d), z ∈ Q →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 f z| ≤ B () beta := by
    intro beta z hz
    exact hBbound () beta z (subset_closure (hQV (subset_closure hz)))
  let Emax : ParabolicWeakDerivativeFamily d (2 * d + 6) Q f :=
    ParabolicWeakDerivativeFamily.ofContDiffOnBounded
      d (2 * d + 6) Q hQopen hQfinite (B ()) f hfQ hboundQ
  refine ⟨B (), Emax, hBnonneg (), ?_, ?_, ?_⟩
  · intro beta z hz
    exact hBbound () beta z (subset_closure (hQV hz))
  · intro beta
    rfl
  · exact ParabolicWeakDerivativeFamily.squaredL2Norm_ofContDiffOnBounded_le
      d (2 * d + 6) Q hQopen hQfinite (B ()) f hfQ hboundQ

end HypoellipticAleksandrov.Parabolic
