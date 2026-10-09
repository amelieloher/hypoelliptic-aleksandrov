module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesExtension
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics

/-! # Compact boundary data and centered free-transport coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- Local data, after subtracting one value, extend with norm at most their raw oscillation. -/
theorem spatialData_local_extension {d : ℕ} (Z₀ P : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z₀ R hR) (U : KineticPoint d → ℝ)
    (hU : ContinuousOn U (closure (forwardCylinder Z₀ R hR))) :
    let M := Holder.oscillationOn U (forwardCylinder Z₀ R hR)
    0 ≤ M ∧ ∃ H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ,
      Continuous H ∧ HasCompactSupport H ∧ (∀ q, ‖H q‖ ≤ M) ∧
      ∀ Q ∈ closure (forwardCylinder Z₀ R hR),
        H (KineticPoint.equivProd d Q) = U Q - U P := by
  let E := forwardCylinder Z₀ R hR
  let e := KineticPoint.homeomorphProd d
  have hc := isCompact_closure_forwardCylinder Z₀ R hR
  have hab := hc.bddAbove_image hU
  have hbb := hc.bddBelow_image hU
  have ho := Holder.oscillationOn_closure ⟨P, hP⟩ hc hU
  have hM : 0 ≤ Holder.oscillationOn U E := by
    rw [← ho]
    exact Holder.oscillationOn_nonneg ⟨P, subset_closure hP⟩ hab hbb
  refine ⟨hM, ?_⟩
  have hdata : ContinuousOn (fun q => U (e.symm q) - U P) (e '' closure E) :=
    (hU.comp e.symm.continuous.continuousOn
      (fun q hq => by rcases hq with ⟨Q, hQ, rfl⟩; simpa using hQ)).sub continuousOn_const
  have hb : ∀ q ∈ e '' closure E, ‖U (e.symm q) - U P‖ ≤
      Holder.oscillationOn U E := by
    rintro q ⟨Q, hQ, rfl⟩
    simp only [e.symm_apply_apply, Real.norm_eq_abs]
    rw [← ho]
    exact Holder.abs_sub_le_oscillationOn hab hbb hQ (subset_closure hP)
  obtain ⟨H, hH, hHc, hHb, hHe⟩ := spatialData_compact_extension
    (e '' closure E) (hc.image e.continuous) _ hdata _ hM hb
  refine ⟨H, hH, hHc, hHb, fun Q hQ => ?_⟩
  have hv := hHe (e Q) ⟨Q, hQ, rfl⟩
  rw [e.symm_apply_apply] at hv
  simpa only [e, KineticPoint.homeomorphProd, KineticPoint.isometryEquivProd,
    IsometryEquiv.coe_toHomeomorph, IsometryEquiv.coe_mk] using hv

/-- Boundary displacement and exit data give literal physical product coordinates. -/
def spatialBoundaryCoordinates {d : ℕ} (P : KineticPoint d) (v₀ : PDE.Vec d)
    (p : PDE.Vec d × TimeVelocity d) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (p.2.1, (P.position + p.1 + (p.2.1 - P.time) • v₀, p.2.2))

/-- Centered free-transport reconstruction is uniformly continuous. -/
theorem uniformContinuous_spatialBoundaryCoordinates {d : ℕ}
    (P : KineticPoint d) (v₀ : PDE.Vec d) :
    UniformContinuous (spatialBoundaryCoordinates P v₀) := by
  have hs : UniformContinuous (fun p : PDE.Vec d × TimeVelocity d =>
      (p.2.1 - P.time) • v₀) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v₀).uniformContinuous.comp
      ((uniformContinuous_fst.comp uniformContinuous_snd).sub uniformContinuous_const)
  exact (uniformContinuous_fst.comp uniformContinuous_snd).prodMk
    ((uniformContinuous_const.add uniformContinuous_fst).add hs |>.prodMk
      (uniformContinuous_snd.comp uniformContinuous_snd))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
