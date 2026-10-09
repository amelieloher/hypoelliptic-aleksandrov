module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Classical transport differentiation with anisotropic regularity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/-- The position differential encoded by the existing classical gradient. -/
def comparisonPositionDifferential {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, kineticPositionGradient u P i • ContinuousLinearMap.proj i

/-- The encoded differential agrees with the actual position-slice differential. -/
theorem comparisonPositionDifferential_eq_fderiv {d : ℕ}
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    comparisonPositionDifferential u P =
      fderiv ℝ (fun x => u ⟨P.time,x,P.velocity⟩) P.position := by
  ext v
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  simp only [comparisonPositionDifferential, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    kineticPositionGradient, PDE.vecDot]

/-- Continuity of the existing position gradient implies continuity of its differential. -/
theorem continuousOn_comparisonPositionDifferential {d : ℕ}
    {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) :
    ContinuousOn (comparisonPositionDifferential u) D := by
  unfold comparisonPositionDifferential
  apply continuousOn_finsetSum
  intro i _
  exact ((continuous_apply i).comp_continuousOn
    hu.continuousOn_kineticPositionGradient).smul continuousOn_const

/-- Continuous partial derivatives give the derivative along physical free transport. -/
theorem hasDerivAt_freeTransport {d : ℕ} {D : Set (KineticPoint d)}
    (hD : IsOpen D) {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    {P : KineticPoint d} (hP : P ∈ D) :
    HasDerivAt (fun r : ℝ => u ⟨P.time + r,P.position + r • P.velocity,P.velocity⟩)
      (kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P)) 0 := by
  let ι : ℝ × PDE.Vec d → KineticPoint d := fun z => ⟨z.1,z.2,P.velocity⟩
  have hι : Continuous ι :=
    KineticPoint.continuous_mk continuous_fst continuous_snd continuous_const
  have hev : ∀ᶠ z in 𝓝 (P.time,P.position), ι z ∈ D :=
    hι.continuousAt (hD.mem_nhds hP)
  let f : ℝ → PDE.Vec d → ℝ := fun s x => u ⟨s,x,P.velocity⟩
  let ft : ℝ → PDE.Vec d → ℝ →L[ℝ] ℝ := fun s x =>
    ContinuousLinearMap.toSpanSingleton ℝ (kineticTimeDerivative u ⟨s,x,P.velocity⟩)
  let fx : ℝ → PDE.Vec d → PDE.Vec d →L[ℝ] ℝ := fun s x =>
    comparisonPositionDifferential u ⟨s,x,P.velocity⟩
  have ht : ∀ᶠ z in 𝓝 (P.time,P.position), HasFDerivAt (f · z.2) (ft z.1 z.2) z.1 := by
    filter_upwards [hev] with z hz
    exact (hu.timeSlice_differentiableAt hz).hasDerivAt.hasFDerivAt
  have hx : ∀ᶠ z in 𝓝 (P.time,P.position), HasFDerivAt (f z.1 ·) (fx z.1 z.2) z.2 := by
    filter_upwards [hev] with z hz
    dsimp only [fx]
    rw [comparisonPositionDifferential_eq_fderiv]
    exact (hu.positionSlice_contDiffAt hz).differentiableAt (by norm_num) |>.hasFDerivAt
  have hiP : ι (P.time,P.position) = P := by cases P; rfl
  have hct : ContinuousAt (fun z : ℝ × PDE.Vec d => ft z.1 z.2) (P.time,P.position) := by
    have hc : ContinuousAt (kineticTimeDerivative u) (ι (P.time,P.position)) := by
      rw [hiP]
      exact hu.continuousOn_kineticTimeDerivative.continuousAt (hD.mem_nhds hP)
    have hcι : ContinuousAt (kineticTimeDerivative u ∘ ι) (P.time,P.position) :=
      hc.comp hι.continuousAt
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp
      hcι
  have hcx : ContinuousAt (fun z : ℝ × PDE.Vec d => fx z.1 z.2) (P.time,P.position) := by
    have hc : ContinuousAt (comparisonPositionDifferential u) (ι (P.time,P.position)) := by
      rw [hiP]
      exact (continuousOn_comparisonPositionDifferential hu).continuousAt (hD.mem_nhds hP)
    change ContinuousAt (comparisonPositionDifferential u ∘ ι) (P.time,P.position)
    exact hc.comp hι.continuousAt
  have hj := (hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := ft) (f₂ := fx)
    (u := (P.time,P.position)) ht hx hct hcx).hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => (P.time + r,P.position + r • P.velocity))
      (1,P.velocity) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id 0).const_add P.time).prodMk
        (((hasDerivAt_id 0).smul_const P.velocity).const_add P.position)
  have hj' := hj
  rw [show (P.time,P.position) =
    (P.time + 0,P.position + (0 : ℝ) • P.velocity) by simp only [add_zero,zero_smul]] at hj'
  have hc := hj'.comp_hasDerivAt 0 hline
  convert hc using 1
  · rfl
  · simp only [Function.HasUncurry.uncurry,id_eq,add_zero,zero_smul,
      ContinuousLinearMap.coprod_apply,
      ft,fx,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    rw [comparisonPositionDifferential_eq_fderiv,
      PDE.fderiv_apply_eq_vecDot_classicalGradient, PDE.vecDot_comm]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov
