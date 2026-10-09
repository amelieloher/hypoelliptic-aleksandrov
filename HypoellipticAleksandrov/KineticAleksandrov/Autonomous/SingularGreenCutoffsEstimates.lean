module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLeibniz
import Mathlib.Tactic

/-! # Pointwise quantitative bounds on the genuine cutoff product error

These lemmas isolate the spatial and velocity derivative scales and require no
coefficient derivatives. They are estimates on cutoffs, not a singular Green function.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Bound the three product-error terms from scalar cutoff and barrier bounds. -/
theorem cutoff_error_abs_le (a Lam v chi psi dx dv dvv phi phiv DX DV DVV B0 B1 : ℝ)
    (ha : 0 ≤ a) (haL : a ≤ Lam) (hc : |chi| ≤ 1) (hp : |psi| ≤ 1)
    (hx : |dx| ≤ DX) (hv : |dv| ≤ DV) (hvv : |dvv| ≤ DVV)
    (hb : |phi| ≤ B0) (hbv : |phiv| ≤ B1) :
    |v*dx*psi*phi+a*chi*dvv*phi+2*a*chi*dv*phiv| ≤
      |v| *DX*B0+Lam*DVV*B0+2*Lam*DV*B1 := by
  have hDX := (abs_nonneg dx).trans hx
  have hDV := (abs_nonneg dv).trans hv
  have hDVV := (abs_nonneg dvv).trans hvv
  have hB0 := (abs_nonneg phi).trans hb
  have hB1 := (abs_nonneg phiv).trans hbv
  have hLam := ha.trans haL
  have ha' : |a| ≤ Lam := by rwa [abs_of_nonneg ha]
  have h₁ : |v*dx*psi*phi| ≤ |v| *DX*B0 := by
    simp only [abs_mul]
    calc
      _ ≤ |v| *DX*1*B0 := by gcongr
      _ = _ := by ring
  have h₂ : |a*chi*dvv*phi| ≤ Lam*DVV*B0 := by
    simp only [abs_mul]
    calc
      _ ≤ Lam*1*DVV*B0 := by gcongr
      _ = _ := by ring
  have h₃ : |2*a*chi*dv*phiv| ≤ 2*Lam*DV*B1 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2*Lam*1*DV*B1 := by gcongr
      _ = _ := by ring
  have hsum := (abs_add_le (v*dx*psi*phi+a*chi*dvv*phi) (2*a*chi*dv*phiv)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  linarith only [hsum, h₁, h₂, h₃]

/-- Quantitative error bound for the actual physical cutoff test. -/
theorem spatialCutoffTest_error_le (a : ℝ → ℝ → ℝ) (chi psi : ℝ → ℝ)
    (hchi : ContDiff ℝ 2 chi) (hpsi : ContDiff ℝ 2 psi)
    (phi : Point → ℝ) (p : Point)
    (ht : DifferentiableAt ℝ (fun t => phi ⟨t, p.position, p.velocity⟩) p.time)
    (hx : DifferentiableAt ℝ (fun x => phi ⟨p.time, fun _ => x, p.velocity⟩)
      (p.position 0))
    (hv : ContDiff ℝ 2 (fun v => phi ⟨p.time, p.position, fun _ => v⟩))
    (Lam DX DV DVV B0 B1 : ℝ)
    (ha : 0 ≤ a (p.position 0) (p.velocity 0))
    (haL : a (p.position 0) (p.velocity 0) ≤ Lam)
    (hc : |chi (p.position 0)| ≤ 1) (hp : |psi (p.velocity 0)| ≤ 1)
    (hdx : |deriv chi (p.position 0)| ≤ DX)
    (hdv : |deriv psi (p.velocity 0)| ≤ DV)
    (hdvv : |deriv (deriv psi) (p.velocity 0)| ≤ DVV)
    (hb : |phi p| ≤ B0) (hbv : |kineticVelocityGradient phi p 0| ≤ B1) :
    |forwardScalarOperator a (spatialCutoffTest chi psi phi) p-
      chi (p.position 0)*psi (p.velocity 0)*forwardScalarOperator a phi p| ≤
      |p.velocity 0| *DX*B0+Lam*DVV*B0+2*Lam*DV*B1 := by
  rw [spatialCutoffTest_operator a chi psi hchi hpsi phi p ht hx hv]
  have he :
      chi (p.position 0)*psi (p.velocity 0)*forwardScalarOperator a phi p+
        p.velocity 0*deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
        a (p.position 0) (p.velocity 0)*chi (p.position 0)*
          deriv (deriv psi) (p.velocity 0)*phi p+
        2*a (p.position 0) (p.velocity 0)*chi (p.position 0)*deriv psi (p.velocity 0)*
          kineticVelocityGradient phi p 0-
        chi (p.position 0)*psi (p.velocity 0)*forwardScalarOperator a phi p =
      p.velocity 0*deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
        a (p.position 0) (p.velocity 0)*chi (p.position 0)*
          deriv (deriv psi) (p.velocity 0)*phi p+
        2*a (p.position 0) (p.velocity 0)*chi (p.position 0)*deriv psi (p.velocity 0)*
          kineticVelocityGradient phi p 0 := by ring
  rw [he]
  exact cutoff_error_abs_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha haL hc hp hdx hdv hdvv hb hbv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
