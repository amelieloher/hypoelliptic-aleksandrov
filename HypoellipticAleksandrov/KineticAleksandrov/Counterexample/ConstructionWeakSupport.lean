module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
public import PDEFoundation.Sobolev.WeakDerivative.Algebra

/-! # Locality of the selected weak representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- A locally integrable weak derivative vanishes on every open region where the value
vanishes almost everywhere. The derivative representative is preserved by uniqueness. -/
theorem construction_weak_derivative_zero_on_open {n : ℕ} (D : Set (PDE.Vec n))
    (hD : IsOpen D) (i : Fin n) (u g : PDE.Vec n → ℝ)
    (hg : LocallyIntegrable g volume)
    (hu : u =ᵐ[volume.restrict D] 0)
    (hw : PDE.HasWeakPartialDerivOn D i u g) :
    g =ᵐ[volume.restrict D] 0 := by
  have hz : PDE.HasWeakPartialDerivOn D i u 0 := by
    intro test _ht _hs _hsub
    have he : (∫ x in D, u x * fderiv ℝ test x (PDE.basisVec i)) = 0 := by
      calc
        _ = ∫ x in D, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [hu] with x hx
          simp only [Pi.zero_apply] at hx
          rw [hx, zero_mul]
        _ = 0 := by simp only [integral_zero]
    simpa only [Pi.zero_apply, zero_mul, integral_zero, neg_zero] using he
  exact PDE.HasWeakPartialDerivOn.ae_eq hD (hg.locallyIntegrableOn D)
    (continuous_const.locallyIntegrable.locallyIntegrableOn D) hw hz

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
