module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The exact time jet of spatially smoothed zero extensions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped Convolution

/-- The time representative is the literal raw time derivative inside the profile domain. -/
def constructionExtendedTimeJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) : ℝ :=
  {y | profileFunction h y < 1}.indicator
    (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
      ⟨t, y.1, y.2⟩) q

/-- The actual time derivative of the mollified value is convolution of its time representative.
The fixed compact integration carrier includes the initial collar, so this holds at all times. -/
theorem construction_mollified_time_jet {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) (t : ℝ) (q : XV d) :
    deriv (fun s => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) t =
      spatialMollify phi (constructionExtendedTimeJet h r mu R t) q := by
  let K : Set (XV d) := {y | profileFunction h y ≤ 1}
  let Omega : Set (XV d) := {y | profileFunction h y < 1}
  have hK : IsCompact K := isCompact_profile_unit_sublevel ha h
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hOmega : MeasurableSet Omega := (isOpen_lt hH continuous_const).measurableSet
  have hOK : Omega ⊆ K := by
    intro y hy
    change profileFunction h y ≤ 1
    exact le_of_lt hy
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let nu : Measure K := Measure.comap Subtype.val (volume.restrict Omega)
  have : IsFiniteMeasureOnCompacts nu := IsFiniteMeasureOnCompacts.comap'
    (volume.restrict Omega) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure nu := inferInstance
  have he : (fun s => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) =
      (fun s => ∫ y : K, phi.normed volume (q - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * s) *
          (2 - PDE.vecNormSq (y : XV d).2 / R ^ 2)) ∂nu) := by
    funext s
    rw [spatialMollify, convolution_lsmul_swap]
    simp only [smul_eq_mul]
    dsimp only [nu]
    rw [integral_subtype_comap hK.measurableSet (fun y : XV d =>
      phi.normed volume (q - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * s) *
          (2 - PDE.vecNormSq y.2 / R ^ 2)))]
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
    rw [← integral_indicator hOmega]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Omega
    · rw [indicator_of_mem hy,
        zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel ⟨s, y.1, y.2⟩ hy]
      rfl
    · rw [indicator_of_notMem hy,
        zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R ⟨s, y.1, y.2⟩ (not_lt.mp hy),
        mul_zero]
  rw [he, construction_deriv_cutoff_integral nu (fun y : K => (y : XV d))
    continuous_subtype_val (fun y : K => selectedFlatProfile h r y)
    ((continuous_selectedFlatProfile h r).comp continuous_subtype_val)]
  dsimp only [nu]
  rw [integral_subtype_comap hK.measurableSet (fun y : XV d => phi.normed volume (q - y) *
    deriv (fun s => timeCutoffTheta (selectedFlatProfile h r y - Real.exp (-mu * s) *
      (2 - PDE.vecNormSq y.2 / R ^ 2))) t)]
  rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
  rw [← integral_indicator hOmega, spatialMollify, convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards [] with y
  change Omega.indicator (fun y : XV d => phi.normed volume (q - y) *
    deriv (fun s => timeCutoffTheta (selectedFlatProfile h r y - Real.exp (-mu * s) *
      (2 - PDE.vecNormSq y.2 / R ^ 2))) t) y =
    phi.normed volume (q - y) * Omega.indicator
      (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, y.1, y.2⟩) y
  by_cases hy : y ∈ Omega
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    rfl
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
