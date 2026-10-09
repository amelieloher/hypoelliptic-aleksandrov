module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Measurable zero extension of a cylinder source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped ENNReal

/-- Subtype measurability yields a globally measurable zero extension. -/
theorem measurable_source_indicator {d : ℕ} {Q : Set (KineticPoint d)}
    (hQ : MeasurableSet Q) (f : KineticPoint d → ℝ)
    (hf : Measurable (fun P : Q => f P)) : Measurable (Q.indicator f) := by
  classical
  apply measurable_of_restrict_of_restrict_compl hQ
  · have heq : Q.domRestrict (Q.indicator f) = fun P : Q => f P := by
      funext P
      exact Set.indicator_of_mem P.property f
    rw [heq]
    exact hf
  · have heq : Qᶜ.domRestrict (Q.indicator f) = fun _ => (0 : ℝ) := by
      funext P
      exact Set.indicator_of_notMem P.property f
    rw [heq]
    exact measurable_const

/-- Zero extension agrees with the original source almost everywhere on its cylinder. -/
theorem source_indicator_ae_eq {d : ℕ} {Q : Set (KineticPoint d)}
    (hQ : MeasurableSet Q) (f : KineticPoint d → ℝ) :
    Q.indicator f =ᵐ[volume.restrict Q] f := by
  filter_upwards [ae_restrict_mem hQ] with P hP
  exact Set.indicator_of_mem hP f

/-- The positive source norm is unchanged by the measurable zero extension. -/
theorem eLpNorm_positive_source_indicator {d : ℕ} {Q : Set (KineticPoint d)}
    (hQ : MeasurableSet Q) (f : KineticPoint d → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun P => max (Q.indicator f P) 0) p (volume.restrict Q) =
      eLpNorm (fun P => max (f P) 0) p (volume.restrict Q) := by
  apply eLpNorm_congr_ae
  filter_upwards [source_indicator_ae_eq hQ f] with P hP
  rw [hP]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
