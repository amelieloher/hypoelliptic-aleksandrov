module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.Parabolic.KineticClassical
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-! # Moving-position chain rule for anisotropic classical solutions

Continuous classical slice jets give the joint first derivative in time and position.
No second position derivatives are required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Parabolic
open scoped Topology

/-- The position differential reconstructed from the coordinate gradient. -/
def positionDifferential {d : ℕ} (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, kineticPositionGradient u P i • ContinuousLinearMap.proj i

/-- Reconstruction agrees with the actual physical slice differential. -/
theorem positionDifferential_eq {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    positionDifferential u P = fderiv ℝ (physicalPositionSlice u P) P.position := by
  ext v
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  simp only [positionDifferential, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rfl

/-- Continuous position jets give a continuous family of linear differentials. -/
theorem continuousOn_positionDifferential {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) :
    ContinuousOn (positionDifferential u) D := by
  apply continuousOn_finsetSum
  intro i _
  exact ((continuous_apply i).comp_continuousOn
    hu.continuousOn_kineticPositionGradient).smul continuousOn_const

/-- Time and position partial derivatives assemble at every interior point. -/
theorem kinetic_timePosition_hasFDerivAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D) (hu : IsKineticC112On u D)
    {P : KineticPoint d} (hP : P ∈ D) :
    HasFDerivAt (fun q : ℝ × PDE.Vec d => u ⟨q.1, q.2, P.velocity⟩)
      ((kineticTimeDerivative u P • ContinuousLinearMap.id ℝ ℝ).coprod
        (positionDifferential u P)) (P.time, P.position) := by
  let e : ℝ × PDE.Vec d → KineticPoint d := fun q => ⟨q.1, q.2, P.velocity⟩
  have he : Continuous e :=
    KineticPoint.continuous_mk continuous_fst continuous_snd continuous_const
  let E := e ⁻¹' D
  have hE : IsOpen E := hD.preimage he
  have hp : (P.time, P.position) ∈ E := hP
  have ht : ContinuousOn (fun q => kineticTimeDerivative u (e q)) E :=
    hu.continuousOn_kineticTimeDerivative.comp he.continuousOn (fun _ h => h)
  have hx : ContinuousOn (fun q => positionDifferential u (e q)) E :=
    (continuousOn_positionDifferential hu).comp he.continuousOn (fun _ h => h)
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun t x => u ⟨t, x, P.velocity⟩) (u := (P.time, P.position))
    (f₁ := fun t x => kineticTimeDerivative u ⟨t, x, P.velocity⟩ •
      ContinuousLinearMap.id ℝ ℝ)
    (f₂ := fun t x => positionDifferential u ⟨t, x, P.velocity⟩)
  · filter_upwards [hE.mem_nhds hp] with q hq
    change HasFDerivAt (fun r => u ⟨r, q.2, P.velocity⟩)
      (kineticTimeDerivative u (e q) • ContinuousLinearMap.id ℝ ℝ) q.1
    convert (hu.timeSlice_hasDerivAt hq).hasFDerivAt using 1
    ext
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  · filter_upwards [hE.mem_nhds hp] with q hq
    change HasFDerivAt (physicalPositionSlice u (e q))
      (positionDifferential u (e q)) q.2
    rw [positionDifferential_eq]
    exact ((hu.positionSlice_contDiffAt hq).differentiableAt (by norm_num)).hasFDerivAt
  · exact (ht.continuousAt (hE.mem_nhds hp)).smul continuousAt_const
  · exact hx.continuousAt (hE.mem_nhds hp)

/-- A moving physical position contributes its transport derivative to the time jet. -/
theorem kinetic_moving_time_hasDerivAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D) (hu : IsKineticC112On u D)
    (a c : ℝ) (b w v : PDE.Vec d) (t : ℝ)
    (hp : (⟨a + c * t, b + t • w, v⟩ : KineticPoint d) ∈ D) :
    HasDerivAt (fun s => u ⟨a + c * s, b + s • w, v⟩)
      (c * kineticTimeDerivative u ⟨a + c * t, b + t • w, v⟩ +
        PDE.vecDot w (kineticPositionGradient u ⟨a + c * t, b + t • w, v⟩)) t := by
  have hc : HasDerivAt (fun s : ℝ => (a + c * s, b + s • w)) (c, w) t :=
    by simpa only [mul_one, one_smul, id_eq] using
      (((hasDerivAt_id t).const_mul c).const_add a).prodMk
        (((hasDerivAt_id t).smul_const w).const_add b)
  have h := (kinetic_timePosition_hasFDerivAt hD hu hp).comp_hasDerivAt t hc
  simp only [Function.comp_def, ContinuousLinearMap.coprod_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] at h
  convert h using 1
  rw [positionDifferential_eq, PDE.fderiv_apply_eq_vecDot_classicalGradient]
  simp only [PDE.vecDot, kineticPositionGradient, mul_comm]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
