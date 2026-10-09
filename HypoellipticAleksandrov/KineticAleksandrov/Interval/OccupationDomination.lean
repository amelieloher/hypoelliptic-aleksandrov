module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Domination of the killed scalar transition measure

Smooth terminal comparison and interior support imply domination as measures.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The scalar interval transition is dominated by the whole-space scalar transition. -/
theorem interval_parabolic_le_whole {a c lam Lam σ τ : ℝ}
    (hac : a < c) (hστ : σ < τ) (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) MeasurableSet.univ
      (zIndependentCoefficient B) Kw)
    (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    P K hJ (scalarQuery σ τ hστ.le v hv) ≤
      Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0) := by
  let ν := P K hJ (scalarQuery σ τ hστ.le v hv)
  have : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [← interval_firstMarginal_eq_parabolic hJ K B hp σ τ hστ.le v 0 hv]
    unfold MovingFiberKernel.firstMarginal
    infer_instance
  have : IsFiniteMeasure (Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0)) := by
    refine ⟨?_⟩
    rw [Kw.firstMarginal_apply _ _ MeasurableSet.univ]
    simp

  have hcompl : ν (PDE.oneDimensionalAxisBox a c)ᶜ = 0 := by
    change (Measure.map Subtype.val
      (parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩)) _ = 0
    rw [Measure.map_apply measurable_subtype_coe hJ.compl]
    have he : (Subtype.val : EvolutionPosition (PDE.oneDimensionalAxisBox a c)
        stationary τ → PDE.Vec 1) ⁻¹' (PDE.oneDimensionalAxisBox a c)ᶜ = ∅ := by
      ext w
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      simpa only [movingDomain_stationary] using w.2
    rw [he, measure_empty]
  have hs : ν.restrict (PDE.oneDimensionalAxisBox a c) = ν :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact hcompl)
  exact HypoellipticAleksandrov.KineticAleksandrov.measure_le_of_smooth_integral_le
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac)) hs
    (fun φ hφs hφc hφJ hφ0 => interval_scalar_test_le_whole hac hστ B hB
      hJ K hp Kw hpw φ hφs hφc hφJ hφ0 v hv)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
