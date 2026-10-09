module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionInterface
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyOperator

/-! # The smooth-coefficient family from the measurable-coefficient family

The functions and all cylinder parameters are retained. Only the coefficient smoothing
scale is chosen separately after fixing each function.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- Coefficient mollification after fixing each smooth function proves the literal smooth
family conjunct, with the same ellipticity bounds, cylinder and function sequence. -/
theorem smoothFamily_of_measurable {d : ℕ} {p lam Lam : ℝ}
    {P₀ : KineticPoint d} {R : ℝ} (hp : 1 ≤ p) (hR : 0 < R)
    (h : MeasurableFamilyStatement d p lam Lam P₀ R) :
    SmoothFamilyStatement d p lam Lam P₀ R := by
  classical
  obtain ⟨A, U, hA, hb, hU, hnonneg, hboundary, hheight, hsource⟩ := h
  have hpn : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hchoose : ∀ j : ℕ, ∃ k : ℕ,
      eLpNorm (fun P => matrixContraction
        (mollifiedMatrix (standardMollifierSequence k) A (P.position, P.velocity) -
          A (P.position, P.velocity)) (kineticVelocityHessian (U j) P))
        (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) <
        ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have he := smooth_coefficient_error_tendsto A lam Lam hA hb (U j) (hU j)
      P₀ R hR (ENNReal.ofReal p) hpn ENNReal.ofReal_ne_top
    exact (he.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))).exists
  choose k hk using hchoose
  let B : ℕ → XV d → PDE.Mat d := fun j => mollifiedMatrix (standardMollifierSequence (k j)) A
  have hB j := smooth_coefficients_same_bounds (standardMollifierSequence (k j)) A lam Lam hA hb
  have hBm : ∀ j i l, Measurable (fun q => B j q i l) := by
    intro j i l
    exact ((continuous_apply l).comp ((continuous_apply i).comp (hB j).1.continuous)).measurable
  refine ⟨B, U, ?_, ?_, hU, hnonneg, hboundary, hheight, ?_⟩
  · intro j i l
    exact (ContinuousLinearMap.proj l).contDiff.comp
      ((ContinuousLinearMap.proj i).contDiff.comp (hB j).1)
  · intro j q
    exact (hB j).2 q
  · let E := fun j P => matrixContraction
      (B j (P.position, P.velocity) - A (P.position, P.velocity))
      (kineticVelocityHessian (U j) P)
    have heps : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat
    have he : Tendsto (fun j => eLpNorm (E j) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds heps
        (fun j => bot_le) (fun j => (hk j).le)
    have hlim := hsource.add he
    have hlim0 : Tendsto (fun j =>
        eLpNorm (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
          (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) +
        eLpNorm (E j) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
        atTop (𝓝 0) := by
      simpa only [add_zero] using! hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun j => bot_le)
    intro j
    exact positive_source_norm_le_coefficient_error A (B j) hA (hBm j) (U j) (hU j)
      (volume.restrict (backwardCylinder P₀ R)) (ENNReal.ofReal p) hp1

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
