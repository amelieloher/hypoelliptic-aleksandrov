module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Support

/-! # Compact cutoff support and integrability on local cylinders

Multiplication by an interior compact cutoff makes locally continuous quantities globally
integrable, and fixed-time slices retain compact support inside the spatial carrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology

/-- A continuous local field times an interior compact cutoff is globally integrable. -/
theorem integrable_local_cutoff_mul {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (f χ : TimeVelocity d → ℝ) (hf : ContinuousOn f U)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    Integrable (fun z => f z * χ z) := by
  have hprod : Continuous (fun z => f z * χ z) :=
    (hf.mul hχ.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hsub)
  exact hprod.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)

/-- Squared interior cutoffs also globalize continuous local integrands. -/
theorem integrable_local_cutoff_square_mul {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (f ρ : TimeVelocity d → ℝ) (hf : ContinuousOn f U)
    (hρ : Continuous ρ) (hc : HasCompactSupport ρ) (hsub : tsupport ρ ⊆ U) :
    Integrable (fun z => f z * ρ z ^ 2) := by
  have hpowc : HasCompactSupport (fun z => ρ z ^ 2) := by
    rw [show (fun z => ρ z ^ 2) = ρ * ρ by funext z; exact pow_two (ρ z)]
    exact HasCompactSupport.mul_left hc
  have hpows : tsupport (fun z => ρ z ^ 2) ⊆ U := by
    have hp : tsupport (fun z => ρ z ^ 2) ⊆ tsupport ρ := by
      simpa only [pow_two] using
        (tsupport_mul_subset_right : tsupport (fun z => ρ z * ρ z) ⊆ tsupport ρ)
    exact hp.trans hsub
  exact integrable_local_cutoff_mul hU f (fun z => ρ z ^ 2) hf
    (hρ.pow 2) hpowc hpows

/-- A fixed-time slice of a compact spacetime cutoff has compact spatial support. -/
theorem hasCompactSupport_local_cutoff_time_slice {d : ℕ}
    (χ : TimeVelocity d → ℝ) (hc : HasCompactSupport χ) (t : ℝ) :
    HasCompactSupport (fun y => χ (t, y)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight t, ?_⟩
  have hrange : Set.range (fun y : PDE.Vec d => (t, y)) = {t} ×ˢ univ := by
    simp only [singleton_prod, image_univ]
  rw [hrange]
  exact isClosed_singleton.prod isClosed_univ

/-- The support of a fixed-time cutoff slice stays in the spatial carrier. -/
theorem tsupport_local_cutoff_time_slice_subset {d : ℕ}
    (χ : TimeVelocity d → ℝ) {a T : ℝ} {O : Set (PDE.Vec d)}
    (hsub : tsupport χ ⊆ Ioo a T ×ˢ O) (t : ℝ) :
    tsupport (fun y => χ (t, y)) ⊆ O := by
  have hpre : tsupport (fun y => χ (t, y)) ⊆
      (fun y => (t, y)) ⁻¹' tsupport χ := by
    apply closure_minimal
    · intro y hy
      exact subset_tsupport χ hy
    · exact (isClosed_tsupport χ).preimage (continuous_const.prodMk continuous_id)
  exact fun y hy => (hsub (hpre hy)).2

/-- Spatial slice derivatives vanish outside the actual spacetime support. -/
theorem scalarSpatialGradient_eq_zero_of_notMem_tsupport {d : ℕ}
    (ρ : TimeVelocity d → ℝ) (z : TimeVelocity d) (i : Fin d)
    (hz : z ∉ tsupport ρ) : scalarSpatialGradient ρ z i = 0 := by
  have heq : ρ =ᶠ[𝓝 z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hs : (fun y => ρ (z.1, y)) =ᶠ[𝓝 z.2] fun _ => 0 :=
    heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hd := (hs.fderiv (𝕜 := ℝ)).self_of_nhds
  change fderiv ℝ (fun y => ρ (z.1, y)) z.2 (PDE.basisVec i) = 0
  rw [hd]
  simp only [fderiv_const_apply, zero_apply]

/-- Each spatial gradient entry of a compact spacetime function has compact support. -/
theorem hasCompactSupport_scalarSpatialGradient_entry {d : ℕ}
    (ρ : TimeVelocity d → ℝ) (hc : HasCompactSupport ρ) (i : Fin d) :
    HasCompactSupport (fun z => scalarSpatialGradient ρ z i) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro z hz
  by_contra hnot
  exact hz (scalarSpatialGradient_eq_zero_of_notMem_tsupport ρ z i hnot)

end HypoellipticAleksandrov.Parabolic.LocalHolder
