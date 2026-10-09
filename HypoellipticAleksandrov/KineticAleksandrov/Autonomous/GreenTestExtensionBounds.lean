module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionProbe
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Closed-velocity bounds for smooth physical tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Smoothness in packed coordinates supplies physical continuity. -/
theorem reconstruction_smooth_physical_continuous (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph)) :
    Continuous phi := by
  have hh := hphi.continuous.comp reconstructionPhysicalHomeomorph.symm.continuous
  have heq : (phi ∘ reconstructionPhysicalHomeomorph) ∘
      reconstructionPhysicalHomeomorph.symm = phi := by
    funext p
    exact congrArg phi (reconstructionPhysicalHomeomorph.apply_symm_apply p)
  rwa [heq] at hh

/-- An open-velocity bound extends to both velocity endpoints by actual continuity. -/
theorem reconstruction_smooth_closed_velocity_bound
    (H : Interval) (phi : Point → ℝ) (hc : Continuous phi) (M : ℝ)
    (hb : ∀ p, p.velocity 0 ∈ H.carrier → |phi p| ≤ M)
    (p : Point) (hp : p.velocity 0 ∈ Icc H.lo H.hi) : |phi p| ≤ M := by
  let f : ℝ → ℝ := fun v => |phi ⟨p.time, p.position, fun _ => v⟩|
  have hf : Continuous f :=
    (hc.comp ((KineticPoint.homeomorphProd 1).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk
        (continuous_pi fun _ => continuous_id))))).abs
  have hcl : p.velocity 0 ∈ closure (Ioo H.lo H.hi) := by
    rw [closure_Ioo H.ordered.ne]
    exact hp
  have hh := le_on_closure (f := f) (g := fun _ => M)
    (fun v hv => hb ⟨p.time, p.position, fun _ => v⟩ hv)
    hf.continuousOn continuousOn_const hcl
  have he : (fun _ : Fin 1 => p.velocity 0) = p.velocity := by
    ext i
    rw [Fin.eq_zero i]
  simpa only [f, he] using hh

/-- The same endpoint bound needs only the physical time and position slice at the point. -/
theorem reconstruction_closed_velocity_slice_bound
    (H : Interval) (phi : Point → ℝ) (hc : Continuous phi) (M : ℝ)
    (p : Point) (hp : p.velocity 0 ∈ Icc H.lo H.hi)
    (hb : ∀ v ∈ H.carrier, |phi ⟨p.time, p.position, fun _ => v⟩| ≤ M) :
    |phi p| ≤ M := by
  let f : ℝ → ℝ := fun v => |phi ⟨p.time, p.position, fun _ => v⟩|
  have hf : Continuous f :=
    (hc.comp ((KineticPoint.homeomorphProd 1).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk
        (continuous_pi fun _ => continuous_id))))).abs
  have hcl : p.velocity 0 ∈ closure (Ioo H.lo H.hi) := by
    rw [closure_Ioo H.ordered.ne]
    exact hp
  have hh := le_on_closure (f := f) (g := fun _ => M) hb
    hf.continuousOn continuousOn_const hcl
  have he : (fun _ : Fin 1 => p.velocity 0) = p.velocity := by
    ext i
    rw [Fin.eq_zero i]
  simpa only [f, he] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
