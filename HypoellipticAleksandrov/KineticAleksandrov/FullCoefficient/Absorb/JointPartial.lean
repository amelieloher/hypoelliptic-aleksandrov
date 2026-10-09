module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.SliceDeriv
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Heat

/-!
# Joint continuity of the heat operator on a smooth family of slices

For `g : ℝ × ℝ^{2d} → ℝ` smooth, the map `(τ, y) ↦ (M^h : D²)(g τ)(y)` is continuous. Needed for
the measurability in the slice time `τ` of the slice integrals of the `h`-derivatives.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {g : ℝ → EvolutionAmbientState d → ℝ}

theorem contDiff_coordPartial_slice (hg : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)) (c : Fin d ⊕ Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × EvolutionAmbientState d => coordPartial c (g p.1) p.2 := by
  have : (fun p : ℝ × EvolutionAmbientState d => coordPartial c (g p.1) p.2) = fun p =>
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) p (0, coordDir c) :=
    funext fun p => coordPartial_slice hg c p.1 p.2
  rw [this]
  exact (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem continuous_coordPartial₂_slice (hg : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)) (c c' : Fin d ⊕ Fin d) :
    Continuous fun p : ℝ × EvolutionAmbientState d =>
      coordPartial c' (coordPartial c (g p.1)) p.2 :=
  continuous_coordPartial_slice (g := fun τ y => coordPartial c (g τ) y)
    (contDiff_coordPartial_slice hg c) c'

theorem continuous_heatOperator_slice (hg : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)) (lam h : ℝ) :
    Continuous fun p : ℝ × EvolutionAmbientState d => heatOperator lam h (g p.1) p.2 := by
  have h2 := continuous_coordPartial₂_slice hg
  unfold heatOperator positionLaplacian mixedDivergence velocityLaplacian
  refine continuous_const.mul ?_
  refine Continuous.add (Continuous.sub ?_ ?_) ?_
  · exact continuous_const.mul (continuous_finsetSum _ fun i _ => h2 (Sum.inr i) (Sum.inr i))
  · exact continuous_const.mul (continuous_finsetSum _ fun i _ => h2 (Sum.inl i) (Sum.inr i))
  · exact continuous_finsetSum _ fun i _ => h2 (Sum.inl i) (Sum.inl i)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
