module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalOperator

/-! # Exact stationary Duhamel integration in physical coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution MeasureTheory Set Filter

/-- On the open source time interval, the stationary source integral is the physical kernel
  action. -/
theorem duhamelIntegrand_physical (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (g : Z → ℝ) (hg : Measurable g) {s : ℝ} (hs : 0 < s) (hsT : s < T) :
    duhamelIntegrand E.2
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => g (nativeToXV (q.position, q.velocity))))
      ⟨0, fun _ => z.2, fun _ => z.1⟩ s =
      ∫ w, g w ∂kernelXV E (Real.toNNReal s) z := by
  rw [duhamelIntegrand, dite_eq_left ⟨hs.le, by simp [movingDomain, autonomousWholeDomain,
    PDE.translateSet]⟩, duhamelSourceIntegral]
  rw [kernelXV, integral_map nativeToXV_measurable.aemeasurable hg.aestronglyMeasurable]
  have hq : (⟨(0, (s, ((fun _ : Fin 1 => z.2), (fun _ : Fin 1 => z.1)))),
      hs.le, by simp [movingDomain, autonomousWholeDomain, PDE.translateSet], by trivial⟩ :
        EvolutionQuery autonomousWholeDomain (fun _ => 0)) =
      wholeQuery (Real.toNNReal s) z := by
    apply Subtype.ext
    simp only [wholeQuery, wholeSpaceQuery, Real.coe_toNNReal s hs.le]
  rw [← hq]
  apply integral_congr_ae
  filter_upwards with w
  rw [indicator_of_mem]
  exact ⟨hsT, by simp [movingDomain, autonomousWholeDomain, PDE.translateSet]⟩

/-- Stationary Duhamel potentials are literal iterated physical kernel integrals. -/
theorem duhamelPotential_physical (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (g : Z → ℝ) (hg : Measurable g) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => g (nativeToXV (q.position, q.velocity))))
      ⟨0, fun _ => z.2, fun _ => z.1⟩ =
      ∫ t in Ioc 0 T, ∫ w, g w ∂kernelXV E (Real.toNNReal t) z := by
  unfold duhamelPotential
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [volume.ae_ne T] with t ht hmem
  exact duhamelIntegrand_physical E z T g hg hmem.1 (lt_of_le_of_ne hmem.2 ht)

/-- An integrable stationary test has the actual occupation measure as its Duhamel integral. -/
theorem duhamelPotential_physical_occupation (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (g : Z → ℝ) (hg : Measurable g)
    (hgi : Integrable g (physicalOccupationMeasure E z T)) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => g (nativeToXV (q.position, q.velocity))))
      ⟨0, fun _ => z.2, fun _ => z.1⟩ =
      ∫ w, g w ∂physicalOccupationMeasure E z T := by
  rw [duhamelPotential_physical E z T g hg,
    ← physicalOccupationMeasure_integral E z T g hgi]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
