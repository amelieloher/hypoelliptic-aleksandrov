module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenDensity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity

/-!
# The density hypothesis of the abstract ABP estimate from the Green density

Density bound for the Green measure `Γ_P`.  Given a
per-realization Green density bound with unit point mass and horizon `T`
(`‖G‖_{L^q} ≤ C T^{(1-2d(q-1))/q}`), the Green measure of the reflected cylinder `Q` has, for every
`P ∈ Q`, a real nonnegative density with `L^q(Q)` norm at most `(C+1) R^{2-(4d+2)/p}`, using the
horizon `S_P = Z₀.time + R² - P.time ≤ R²` and the exponent identity of `greenDelta_rpow_le`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open scoped ENNReal

variable {d : ℕ}

/-- The density hypothesis of `kinetic_abp_abstract`, from a Green density bound at the
exponent `q = p/(p-1)`. -/
theorem cylinder_density_of_greenDensity (p C : ℝ) (hp : 2 * (d : ℝ) + 1 < p) (hC : 0 ≤ C)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hG : ∀ (σ₀ : ℝ) (pt : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
        (T : ℝ), 0 < T →
      ∀ (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)),
        IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac pt) Γ →
        ∃ G : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ≥0∞,
          Measurable G ∧
          Γ = ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
          eLpNorm G (ENNReal.ofReal (p / (p - 1))) ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))) ≤
            ENNReal.ofReal (C * T ^ ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1)))))
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    ∀ P ∈ forwardCylinder Z₀ R hR, ∃ F : KineticPoint d → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z) ∧
      cylinderGreenMeasure K Z₀ R hR P =
        (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
          (fun z => ENNReal.ofReal (F z)) ∧
      (eLpNorm F (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤
        (C + 1) * R ^ (2 - (4 * (d : ℝ) + 2) / p) ∧
      MemLp F (ENNReal.ofReal (p / (p - 1))) (volume.restrict (forwardCylinder Z₀ R hR)) := by
  intro P hP
  have hp1 : 1 < p := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hq : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hRp : 0 < R ^ (2 - (4 * (d : ℝ) + 2) / p) := Real.rpow_pos_of_pos hR _
  have hP' := (mem_forwardCylinder_iff Z₀ P R hR).1 hP
  have ht := hP'.2.1
  have hSR : remainingTime Z₀ P R < R ^ 2 := by
    unfold remainingTime
    linarith [hP'.1]
  have hSP : 0 < remainingTime Z₀ P R := by
    unfold remainingTime
    linarith
  let GP := greenMeasure K P.time (ENNReal.ofReal (remainingTime Z₀ P R))
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
  have hGP := greenMeasure_spec K P.time _
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
  obtain ⟨G₀, hG₀m, hΓP', hnorm⟩ := hG P.time (kineticStartState d P)
    (remainingTime Z₀ P R) hSP GP hGP
  obtain ⟨hGm, hGden, hGnorm⟩ := greenKineticPoint_density P.time _ GP G₀ hG₀m hΓP'
    (measurableSet_forwardCylinder' Z₀ R hR)
  have hscale : C * remainingTime Z₀ P R ^
      ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1))) ≤
      C * R ^ (2 - (4 * (d : ℝ) + 2) / p) :=
    mul_le_mul_of_nonneg_left (greenDelta_rpow_le hp hSP.le hSR.le hR) hC
  have hnorm' : eLpNorm (Function.extend (greenKineticPoint d P.time) G₀ 0)
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict (forwardCylinder Z₀ R hR)) ≤
      ENNReal.ofReal (C * R ^ (2 - (4 * (d : ℝ) + 2) / p)) :=
    (hGnorm _).trans (hnorm.trans (ENNReal.ofReal_le_ofReal hscale))
  have hden' : cylinderGreenMeasure K Z₀ R hR P =
      (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
        (Function.extend (greenKineticPoint d P.time) G₀ 0) := by
    dsimp only [cylinderGreenMeasure]
    rw [dite_eq_left ht]
    exact hGden
  obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound
    (volume.restrict (forwardCylinder Z₀ R hR)) _ _ hGm hden' (p / (p - 1))
    (C * R ^ (2 - (4 * (d : ℝ) + 2) / p)) (lt_trans zero_lt_one hq)
    (mul_nonneg hC hRp.le) hnorm'
  refine ⟨F, hFm, hFn, hFd, hFN.trans ?_, hFLp⟩
  exact mul_le_mul_of_nonneg_right (by linarith) hRp.le

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly
