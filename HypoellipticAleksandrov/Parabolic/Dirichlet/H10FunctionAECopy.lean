module

public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Changing an H1 zero-boundary carrier almost everywhere

An `H10Function` approximation certificate can be transported to an `H1Function`
carrier whose function and gradient representatives agree almost everywhere.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.H10Function

open Filter MeasureTheory

/-- Copy an `H10Function` approximation certificate to an almost-everywhere equal
`H1Function` carrier. -/
noncomputable def copyToH1Function_of_ae_eq
    {d : ℕ} {U : Set (PDE.Vec d)}
    (w : PDE.H10Function U) (q : PDE.H1Function U)
    (hfun : w.toH1Function.toFun =ᵐ[PDE.volumeOn U] q.toFun)
    (hgrad : ∀ i : Fin d,
      (fun x => w.toH1Function.grad x i) =ᵐ[PDE.volumeOn U]
        (fun x => q.grad x i)) : PDE.H10Function U where
  toH1Function := q
  approx := w.approx
  approx_smooth := w.approx_smooth
  approx_hasCompactSupport := w.approx_hasCompactSupport
  approx_support_subset := w.approx_support_subset
  tendsto_approx := by
    rw [show
      (fun n =>
        eLpNorm (fun x => w.approx n x - q.toFun x)
          (2 : ℝ≥0∞) (PDE.volumeOn U)) =
      (fun n =>
        eLpNorm (fun x => w.approx n x - w.toH1Function.toFun x)
          (2 : ℝ≥0∞) (PDE.volumeOn U)) by
        funext n
        apply eLpNorm_congr_ae
        filter_upwards [hfun] with x hx
        rw [hx]]
    exact w.tendsto_approx
  tendsto_approx_grad := by
    intro i
    rw [show
      (fun n =>
        eLpNorm
          (fun x => (fderiv ℝ (w.approx n) x) (basisVec i) - q.grad x i)
          (2 : ℝ≥0∞) (PDE.volumeOn U)) =
      (fun n =>
        eLpNorm
          (fun x =>
            (fderiv ℝ (w.approx n) x) (basisVec i) -
              w.toH1Function.grad x i)
          (2 : ℝ≥0∞) (PDE.volumeOn U)) by
        funext n
        apply eLpNorm_congr_ae
        filter_upwards [hgrad i] with x hx
        rw [hx]]
    exact w.tendsto_approx_grad i

@[simp] theorem copyToH1Function_of_ae_eq_toH1Function
    {d : ℕ} {U : Set (PDE.Vec d)}
    (w : PDE.H10Function U) (q : PDE.H1Function U)
    (hfun : w.toH1Function.toFun =ᵐ[PDE.volumeOn U] q.toFun)
    (hgrad : ∀ i : Fin d,
      (fun x => w.toH1Function.grad x i) =ᵐ[PDE.volumeOn U]
        (fun x => q.grad x i)) :
    (copyToH1Function_of_ae_eq w q hfun hgrad).toH1Function = q :=
  rfl

end PDE.H10Function
