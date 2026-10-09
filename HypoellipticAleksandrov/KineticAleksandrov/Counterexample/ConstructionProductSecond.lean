module

public import PDEFoundation.Sobolev.WeakDerivative.Product
public import PDEFoundation.Sobolev.WeakDerivative.Algebra

/-! # Second weak product rule with the same first representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- Multiplication by a smooth function preserves a prescribed second weak derivative.
The two first representatives are the ones appearing in both weak identities. -/
theorem construction_weak_second_product {n : ℕ} {D : Set (PDE.Vec n)}
    (u gi gk hik phi : PDE.Vec n → ℝ) (i k : Fin n)
    (hu : PDE.HasWeakPartialDerivOn D i u gi)
    (hg : PDE.HasWeakPartialDerivOn D i gk hik)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (huL : LocallyIntegrable u (PDE.volumeOn D))
    (hgiL : LocallyIntegrable gi (PDE.volumeOn D))
    (hgkL : LocallyIntegrable gk (PDE.volumeOn D))
    (hhL : LocallyIntegrable hik (PDE.volumeOn D)) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k))
      (fun x => phi x * hik x + gk x * fderiv ℝ phi x (PDE.basisVec i) +
        fderiv ℝ phi x (PDE.basisVec k) * gi x +
        u x * fderiv ℝ (fun y => fderiv ℝ phi y (PDE.basisVec k)) x
          (PDE.basisVec i)) := by
  let dk := fun x => fderiv ℝ phi x (PDE.basisVec k)
  let di := fun x => fderiv ℝ phi x (PDE.basisVec i)
  have hdk : ContDiff ℝ (⊤ : ℕ∞) dk :=
    (hphi.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hdi : Continuous di :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdik : Continuous (fun x => fderiv ℝ dk x (PDE.basisVec i)) :=
    (hdk.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 := hg.mul_contDiff hphi hgkL hhL
  have h2 := hu.mul_contDiff hdk huL hgiL
  have h1L : LocallyIntegrable (fun x => phi x * gk x) (PDE.volumeOn D) :=
    hgkL.continuous_mul hphi.continuous
  have h2L : LocallyIntegrable (fun x => dk x * u x) (PDE.volumeOn D) :=
    huL.continuous_mul hdk.continuous
  have hD1L : LocallyIntegrable (fun x => phi x * hik x + gk x * di x)
      (PDE.volumeOn D) :=
    (hhL.continuous_mul hphi.continuous).add (hgkL.mul_continuous hdi)
  have hD2L : LocallyIntegrable
      (fun x => dk x * gi x + u x * fderiv ℝ dk x (PDE.basisVec i))
      (PDE.volumeOn D) :=
    (hgiL.continuous_mul hdk.continuous).add (huL.mul_continuous hdik)
  have he := h1.add h2 h1L h2L hD1L hD2L
  have hv : (fun x => phi x * gk x + dk x * u x) =
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k)) := by
    funext x
    dsimp only [dk]
    rw [mul_comm (fderiv ℝ phi x (PDE.basisVec k))]
  change PDE.HasWeakPartialDerivOn D i
    (fun x => phi x * gk x + dk x * u x)
    (fun x => (phi x * hik x + gk x * di x) +
      (dk x * gi x + u x * fderiv ℝ dk x (PDE.basisVec i))) at he
  rw [hv] at he
  simpa only [dk, di, add_assoc] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
