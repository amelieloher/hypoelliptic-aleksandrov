module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionInitial
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Joint smoothness after the actual fixed-domain zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

/-- Spatial smoothing of the actual zero extension is globally jointly smooth.
The integration carrier is the fixed compact profile domain; no time smoothing is used. -/
theorem spatial_zeroExtendedProfile_contDiff_of_profile {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha)
    (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨z.1, y.1, y.2⟩) z.2) := by
  let K : Set (XV d) := {q | profileFunction h q ≤ 1}
  let Omega : Set (XV d) := {q | profileFunction h q < 1}
  have hK : IsCompact K := isCompact_profile_unit_sublevel ha h
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hOmega : MeasurableSet Omega := (isOpen_lt hH continuous_const).measurableSet
  have hOK : Omega ⊆ K := by
    intro q hq
    change profileFunction h q ≤ 1
    exact le_of_lt hq
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let nu : Measure K := Measure.comap Subtype.val (volume.restrict Omega)
  have : IsFiniteMeasureOnCompacts nu := IsFiniteMeasureOnCompacts.comap'
    (volume.restrict Omega) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure nu := inferInstance
  have hc := compact_cutoff_mollification_contDiff nu (fun y : K => (y : XV d))
    continuous_subtype_val (fun y : K => selectedFlatProfile h r y)
    ((continuous_selectedFlatProfile h r).comp continuous_subtype_val) phi mu R
  have he : (fun z : ℝ × XV d => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨z.1, y.1, y.2⟩) z.2) =
      (fun z : ℝ × XV d => ∫ y : K, phi.normed volume (z.2 - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * z.1) *
          (2 - PDE.vecNormSq (y : XV d).2 / R ^ 2)) ∂nu) := by
    funext z
    rw [spatialMollify, convolution_lsmul_swap]
    simp only [smul_eq_mul]
    dsimp only [nu]
    rw [integral_subtype_comap hK.measurableSet (fun y : XV d =>
      phi.normed volume (z.2 - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * z.1) *
          (2 - PDE.vecNormSq y.2 / R ^ 2)))]
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
    rw [← integral_indicator hOmega]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Omega
    · rw [indicator_of_mem hy,
        zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel ⟨z.1, y.1, y.2⟩ hy]
      rfl
    · rw [indicator_of_notMem hy,
        zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R ⟨z.1, y.1, y.2⟩ (not_lt.mp hy),
        mul_zero]
  rw [he]
  exact hc

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
