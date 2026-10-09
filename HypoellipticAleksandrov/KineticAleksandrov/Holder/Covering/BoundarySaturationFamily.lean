module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DensityDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageVolume
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-! # The literal family of critical cylinders and its measure reduction -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Critical cylinders have exactly the prescribed density and lie inside Q. -/
def criticalParameters {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) :
    Set (KineticPoint d × ℝ) :=
  {z | 0 < z.2 ∧ backwardCylinder z.1 z.2 ⊆ unitCylinder d ∧
    (volume (E ∩ backwardCylinder z.1 z.2)).toReal =
      (1-eta)*(volume (backwardCylinder z.1 z.2)).toReal}

/-- The open union of all critical cylinders. -/
def criticalUnion {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  ⋃ z ∈ criticalParameters E eta, backwardCylinder z.1 z.2

/-- The critical union is open. -/
theorem isOpen_criticalUnion {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) :
    IsOpen (criticalUnion E eta) := isOpen_biUnion fun z _ => isOpen_cylinder z.1 z.2

/-- The critical union lies in Q. -/
theorem criticalUnion_subset_unit {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) :
    criticalUnion E eta ⊆ unitCylinder d := by
  intro X hX
  obtain ⟨z, hz, hmem⟩ := mem_iUnion₂.mp hX
  exact hz.2.1 hmem

/-- A countable family of critical cylinders has exactly the same union. -/
theorem exists_countable_critical_subcover {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) :
    ∃ T ⊆ criticalParameters E eta, T.Countable ∧
      (⋃ z ∈ T, backwardCylinder z.1 z.2) = criticalUnion E eta := by
  let : SecondCountableTopology (KineticPoint d) :=
    (KineticPoint.homeomorphProd d).secondCountableTopology
  exact TopologicalSpace.isOpen_biUnion_countable (criticalParameters E eta)
    (fun z => backwardCylinder z.1 z.2) (fun z _ => isOpen_cylinder z.1 z.2)

/-- Outside the critical union, E costs only the spatial boundary layer. -/
theorem volume_outside_criticalUnion_le {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta)
    (hR : 0 < R) (hRsmall : R ≤ 1/4)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    (volume (E \ criticalUnion E eta)).toReal ≤
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
  have hc := ae_exists_critical_cylinder hE hbounded hEQ heta hR
    (hRsmall.trans (by norm_num : (1 : ℝ)/4 ≤ 1)) hcutoff
  have hae := (ae_restrict_iff'₀ hE).mp hc
  have hsub : (E \ criticalUnion E eta) ≤ᵐ[volume] (unitCylinder d \ spatialCore d R) := by
    filter_upwards [hae] with X hX
    intro hEX
    refine ⟨hEQ hEX.1, ?_⟩
    intro hcore
    have hx : PDE.vecEuclideanNorm X.position < 1-2*R^2 := by
      have h := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by nlinarith : 0 < 1-2*R^2)).mp hcore.2.2.1
      simpa only [sub_zero] using h
    obtain ⟨P, r, hr, _, hmem, hPQ, heq⟩ := hX hEX.1 hx
    apply hEX.2
    exact mem_iUnion₂.mpr ⟨(P,r), ⟨hr, hPQ, heq⟩, hmem⟩
  have hf : volume (unitCylinder d \ spatialCore d R) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono sdiff_subset)
  exact (ENNReal.toReal_mono hf (measure_mono_ae hsub)).trans
    (spatial_shell_volume d hR hRsmall)

/-- Exact-density cylinders yield a fixed proportional density reduction in their union. -/
theorem criticalUnion_density_reduction {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) {eta R : ℝ} (heta : 0 ≤ eta)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    (volume (E ∩ criticalUnion E eta)).toReal ≤
      (1-eta/((8 : ℝ)^(4*d+2)))*(volume (criticalUnion E eta)).toReal := by
  have hf : volume (criticalUnion E eta) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono (criticalUnion_subset_unit E eta))
  exact cylinder_union_density_reduction Prod.fst Prod.snd (criticalParameters E eta) R
    (fun _ hz => hz.1)
    (fun z hz => (hcutoff z.1 z.2 hz.1 hz.2.1 (le_of_eq hz.2.2.symm)).le)
    E hE hf heta (fun _ hz => hz.2.2.le)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
