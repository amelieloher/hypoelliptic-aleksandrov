module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

/-! # Linearity of the C² homogeneous Bellman image -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The first directional derivative respects addition on the punctured carrier. -/
theorem bellman_directional_add {alpha : ℝ} {phi psi : (ℝ × ℝ) → ℝ}
    (hf : IsBellmanHomogeneous alpha phi) (hg : IsBellmanHomogeneous alpha psi)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (e : ℝ × ℝ) :
    fderiv ℝ (phi + psi) q e = fderiv ℝ phi q e + fderiv ℝ psi q e := by
  have hfq := (hf.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  have hgq := (hg.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  rw [fderiv_add hfq hgq, add_apply]

/-- The second velocity derivative respects addition on the punctured carrier. -/
theorem bellmanDvv_add {alpha : ℝ} {phi psi : (ℝ × ℝ) → ℝ}
    (hf : IsBellmanHomogeneous alpha phi) (hg : IsBellmanHomogeneous alpha psi)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    bellmanDvv (phi + psi) q = bellmanDvv phi q + bellmanDvv psi q := by
  have he : bellmanDv (phi + psi) =ᶠ[𝓝 q] bellmanDv phi + bellmanDv psi := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    exact bellman_directional_add hf hg z hz (0, 1)
  have hfq := ((hf.directional_contDiffOn (0, 1)).contDiffAt
    (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
  have hgq := ((hg.directional_contDiffOn (0, 1)).contDiffAt
    (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (bellmanDv phi) q at hfq
  change DifferentiableAt ℝ (bellmanDv psi) q at hgq
  unfold bellmanDvv
  rw [he.fderiv_eq, fderiv_add hfq hgq, add_apply]

/-- Scalar multiplication commutes with the second velocity derivative. -/
theorem bellmanDvv_smul (c : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    bellmanDvv (c • phi) q = c * bellmanDvv phi q := by
  have he : bellmanDv (c • phi) = c • bellmanDv phi := by
    funext z
    simp only [bellmanDv, fderiv_const_smul_field, Pi.smul_apply,
      smul_apply, smul_eq_mul]
  simp only [bellmanDvv, he, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, smul_eq_mul]

/-- The continuous operator image is a linear map from the actual homogeneous space. -/
def bellmanImageLinearMap (alpha lam Lam : ℝ) :
    bellmanHomogeneousSpace alpha →ₗ[ℝ] C(BellmanSphere × BellmanCoefficient lam Lam, ℝ) where
  toFun phi := bellmanImage lam Lam phi.val phi.property
  map_add' phi psi := by
    ext w
    change bellmanOperator w.2.val (phi.val + psi.val) w.1.val =
      bellmanOperator w.2.val phi.val w.1.val + bellmanOperator w.2.val psi.val w.1.val
    unfold bellmanOperator bellmanDx
    rw [bellman_directional_add phi.property psi.property _ w.1.ne_zero,
      bellmanDvv_add phi.property psi.property _ w.1.ne_zero]
    ring
  map_smul' c phi := by
    ext w
    change bellmanOperator w.2.val (c • phi.val) w.1.val =
      c * bellmanOperator w.2.val phi.val w.1.val
    unfold bellmanOperator bellmanDx
    rw [fderiv_const_smul_field, bellmanDvv_smul]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    ring

/-- The literal image subspace in the source's uniform function space. -/
def bellmanImageSpace (alpha lam Lam : ℝ) :
    Submodule ℝ C(BellmanSphere × BellmanCoefficient lam Lam, ℝ) :=
  (bellmanImageLinearMap alpha lam Lam).range

/-- Membership in the image means exactly that a C² homogeneous witness produces it. -/
theorem mem_bellmanImageSpace_iff (alpha lam Lam : ℝ)
    (f : C(BellmanSphere × BellmanCoefficient lam Lam, ℝ)) :
    f ∈ bellmanImageSpace alpha lam Lam ↔
      ∃ phi : (ℝ × ℝ) → ℝ, ∃ h : IsBellmanHomogeneous alpha phi,
        bellmanImage lam Lam phi h = f := by
  constructor
  · rintro ⟨phi, hphi⟩
    exact ⟨phi.val, phi.property, hphi⟩
  · rintro ⟨phi, hphi, he⟩
    exact ⟨⟨phi, hphi⟩, he⟩

end HypoellipticAleksandrov.KineticAleksandrov
