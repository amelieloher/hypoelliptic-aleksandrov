module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Compact geometry for fixed-function coefficient errors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

/-- A fixed backward kinetic cylinder is contained in an explicit compact set. -/
theorem backwardCylinder_subset_compact {d : ℕ} (P₀ : KineticPoint d) (R : ℝ)
    (hR : 0 < R) : ∃ K : Set (KineticPoint d), IsCompact K ∧ backwardCylinder P₀ R ⊆ K := by
  let D := Icc (P₀.time - R ^ 2) P₀.time ×ˢ
    (PDE.euclideanClosedBall (0 : PDE.Vec d) (R ^ 3) ×ˢ
      PDE.euclideanClosedBall P₀.velocity R)
  let f : ℝ × (PDE.Vec d × PDE.Vec d) → KineticPoint d := fun z =>
    ⟨z.1, P₀.position + z.2.1 + (z.1 - P₀.time) • P₀.velocity, z.2.2⟩
  have hD : IsCompact D := isCompact_Icc.prod
    ((PDE.isCompact_euclideanClosedBall 0 (pow_pos hR 3).le).prod
      (PDE.isCompact_euclideanClosedBall P₀.velocity hR.le))
  have hf : Continuous f := KineticPoint.continuous_mk continuous_fst
    ((continuous_const.add continuous_snd.fst).add
      ((continuous_fst.sub continuous_const).smul continuous_const)) continuous_snd.snd
  refine ⟨f '' D, hD.image hf, ?_⟩
  intro P hP
  refine ⟨(P.time, relativePosition P₀ P, P.velocity), ?_, ?_⟩
  · exact ⟨⟨hP.1.le, hP.2.1.le⟩,
      PDE.euclideanBall_subset_euclideanClosedBall 0 (R ^ 3) hP.2.2.2,
      PDE.euclideanBall_subset_euclideanClosedBall P₀.velocity R hP.2.2.1⟩
  · apply KineticPoint.ext <;> dsimp only [f, relativePosition]; abel

/-- Compact sets have finite native kinetic volume with exactly the product normalization. -/
theorem kineticPoint_compact_volume_lt_top {d : ℕ} (K : Set (KineticPoint d))
    (hK : IsCompact K) : volume K < ⊤ := by
  change Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))) K < ⊤
  rw [Measure.map_apply (KineticPoint.measurable_equivProd_symm d) hK.isClosed.measurableSet]
  have hc : IsCompact ((KineticPoint.equivProd d).symm ⁻¹' K) :=
    (KineticPoint.homeomorphProd d).symm.isCompact_preimage.mpr hK
  exact hc.measure_lt_top

/-- The cylinder restriction is a finite measure; no closure or Euclidean normalization changes. -/
theorem backwardCylinder_volume_lt_top {d : ℕ} (P₀ : KineticPoint d) (R : ℝ)
    (hR : 0 < R) : volume (backwardCylinder P₀ R) < ⊤ := by
  obtain ⟨K, hK, hQK⟩ := backwardCylinder_subset_compact P₀ R hR
  exact lt_of_le_of_lt (measure_mono hQK) (kineticPoint_compact_volume_lt_top K hK)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
