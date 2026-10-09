module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear

/-! # Exact degrees of the homogeneous Bellman jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- Homogeneity is an equality on a neighborhood of every punctured point. -/
theorem IsBellmanHomogeneous.eventually_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) {r : ℝ} (hr : 0 < r)
    {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
    (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q] fun z => r ^ alpha * phi z := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact h.2 r hr z hz

/-- The first position jet has homogeneous degree alpha minus three. -/
theorem IsBellmanHomogeneous.dx_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) {r : ℝ} (hr : 0 < r)
    {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
    bellmanDx phi (bellmanPlaneDilation r q) = r ^ (alpha - 3) * bellmanDx phi q := by
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds
    (bellmanPlaneDilation_ne_zero r hr q hq))).differentiableAt (by norm_num)
  have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0))
    (h.eventually_scaling hr hq).fderiv_eq
  change bellmanDx (fun z => phi (bellmanPlaneDilation r z)) q =
    (fderiv ℝ ((r ^ alpha) • phi) q) (1, 0) at hh
  rw [bellmanDx_comp_dilation r phi q hd] at hh
  rw [fderiv_const_smul_field] at hh
  apply mul_left_cancel₀ (pow_ne_zero 3 hr.ne')
  calc
    r ^ 3 * bellmanDx phi (bellmanPlaneDilation r q) =
        r ^ alpha * bellmanDx phi q := hh
    _ = r ^ 3 * (r ^ (alpha - 3) * bellmanDx phi q) := by
      rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
      congr 2
      ring

/-- The first velocity jet has homogeneous degree alpha minus one. -/
theorem IsBellmanHomogeneous.dv_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) {r : ℝ} (hr : 0 < r)
    {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
    bellmanDv phi (bellmanPlaneDilation r q) = r ^ (alpha - 1) * bellmanDv phi q := by
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds
    (bellmanPlaneDilation_ne_zero r hr q hq))).differentiableAt (by norm_num)
  have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
    (h.eventually_scaling hr hq).fderiv_eq
  change bellmanDv (fun z => phi (bellmanPlaneDilation r z)) q =
    (fderiv ℝ ((r ^ alpha) • phi) q) (0, 1) at hh
  rw [bellmanDv_comp_dilation r phi q hd] at hh
  rw [fderiv_const_smul_field] at hh
  apply mul_left_cancel₀ hr.ne'
  calc
    r * bellmanDv phi (bellmanPlaneDilation r q) = r ^ alpha * bellmanDv phi q := hh
    _ = r * (r ^ (alpha - 1) * bellmanDv phi q) := by
      have he : r * r ^ (alpha - 1) = r ^ alpha := by
        calc
          r * r ^ (alpha - 1) = r ^ (1 : ℝ) * r ^ (alpha - 1) := by
            rw [Real.rpow_one]
          _ = r ^ (1 + (alpha - 1)) := (Real.rpow_add hr _ _).symm
          _ = r ^ alpha := by congr 1; ring
      rw [← mul_assoc, he]

/-- The second velocity jet has homogeneous degree alpha minus two. -/
theorem IsBellmanHomogeneous.dvv_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) {r : ℝ} (hr : 0 < r)
    {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
    bellmanDvv phi (bellmanPlaneDilation r q) = r ^ (alpha - 2) * bellmanDvv phi q := by
  have he : bellmanDv (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
      (r ^ alpha) • bellmanDv phi := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
      (h.eventually_scaling hr hz).fderiv_eq
    change bellmanDv (fun z => phi (bellmanPlaneDilation r z)) z =
      (fderiv ℝ ((r ^ alpha) • phi) z) (0, 1) at hh
    rw [fderiv_const_smul_field] at hh
    exact hh
  have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) he.fderiv_eq
  change bellmanDvv (fun z => phi (bellmanPlaneDilation r z)) q = _ at hh
  rw [bellmanDvv_comp_dilation r hr phi h.1 q hq, fderiv_const_smul_field] at hh
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    r ^ 2 * bellmanDvv phi (bellmanPlaneDilation r q) =
        r ^ alpha * bellmanDvv phi q := hh
    _ = r ^ 2 * (r ^ (alpha - 2) * bellmanDvv phi q) := by
      rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
      congr 2
      ring

end HypoellipticAleksandrov.KineticAleksandrov
