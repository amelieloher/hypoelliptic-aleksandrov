module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Weak passage for the actual whole-space ball exhaustion -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- The actual expanding-ball limit satisfies the regularized weak equation on
strict bounded whole-space cylinders. No weak equation or limit estimate is assumed. -/
theorem weakRegularized_wholeSpace_ball_limit :
    IsKineticWeakRegularizedSolution B b ε (wholeSpaceInnerCylinder α τ S0)
      (fun p => limUnder atTop (fun j => v j p)) (fun _ => 0) := by
  let U := wholeSpaceInnerCylinder (n := n) α τ S0
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hU : IsOpen U := isOpen_wholeSpaceInnerCylinder α τ S0
  have hUK : U ⊆ K := wholeSpaceInnerCylinder_subset_closed α τ S0
  have hcont := (tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv).2.1.mono hUK
  refine ⟨hcont.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  let φ (p : KineticPoint n) := regularizedAdjoint B b ε ψ
    ((evolutionHomeomorph n).symm p)
  have hφ : Continuous φ := (contDiff_regularizedAdjoint hBs hbs hψ ε).continuous.comp
    (evolutionHomeomorph n).symm.continuous
  have hzeroU (p : KineticPoint n) (hp : p ∉ U) : φ p = 0 := by
    apply regularizedAdjoint_eq_zero_of_notMem_tsupport
    intro hx
    exact hp (by simpa using hs hx)
  have hzeroK (p : KineticPoint n) (hp : p ∉ K) : φ p = 0 :=
    hzeroU p (fun h => hp (hUK h))
  have hInt := tendsto_setIntegral_mul_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv φ hφ
  have hnear : ∀ᶠ j : ℕ in atTop, |S0| < r j :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hIz : ∀ᶠ j : ℕ in atTop, (∫ p in K, v j p * φ p) = 0 := by
    filter_upwards [hnear] with j hj
    let V := evolutionHomeomorph n ⁻¹' U
    have hV : IsOpen V := hU.preimage (evolutionHomeomorph n).continuous
    have hball (p : KineticPoint n) (hp : p ∈ U) :
        p.position ∈ movingDomain (PDE.euclideanBall 0 (r j)) (fun _ => 0) p.time :=
      mem_movingBall_of_radialSq_le (abs_nonneg S0) hj
        (by simpa only [sq_abs] using (show radialSq p < S0 ^ 2 from hp.2.2).le)
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (v j ∘ evolutionHomeomorph n) V := by
      exact (hv j).2.2.1.comp (evolutionProdCLE n).contDiff.contDiffOn
        (fun x hx => ⟨hx.2.1, hball _ hx⟩)
    have hop : ∀ x ∈ V, regularizedOperator B b ε (v j ∘ evolutionHomeomorph n) x = 0 := by
      intro x hx
      have hc2 : ContDiffAt ℝ 2 (v j ∘ evolutionHomeomorph n) x :=
        (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
      rw [regularizedOperator_comp ε hc2]
      exact (hv j).2.2.2.1 _ ⟨hx.2.1, hball _ hx⟩
    have hePack : (∫ x in V, v j (evolutionHomeomorph n x) *
        regularizedAdjoint B b ε ψ x) = 0 := by
      change (∫ x in V, (v j ∘ evolutionHomeomorph n) x *
        regularizedAdjoint B b ε ψ x) = 0
      rw [integral_regularizedAdjoint_contDiffOn hV hBs hBsym hbs ε hsm ψ hψ hc hs]
      have he : (∫ x in V, regularizedOperator B b ε
          (v j ∘ evolutionHomeomorph n) x * ψ x) = ∫ x in V, (0 : ℝ) :=
        setIntegral_congr_fun hV.measurableSet
        (fun x hx => by rw [hop x hx, zero_mul])
      exact he.trans (by simp only [integral_zero])
    have heU : (∫ p in U, v j p * φ p) = 0 := by
      have ht := setIntegral_comp_evolutionHomeomorph (fun p => v j p * φ p) U
      simp only [φ, Homeomorph.symm_apply_apply] at ht
      exact ht.symm.trans hePack
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroK p hp, mul_zero])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroU p hp, mul_zero])] at heU
    exact heU
  have heLim : (∫ p in K, limUnder atTop (fun j => v j p) * φ p) = 0 :=
    tendsto_nhds_unique hInt (tendsto_const_nhds.congr' (hIz.mono fun j hj => hj.symm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroK p hp, mul_zero])] at heLim
  simp only [zero_mul, integral_zero]
  change (∫ p in U, limUnder atTop (fun j => v j p) * φ p) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroU p hp, mul_zero])]
  exact heLim

end Data

end HypoellipticAleksandrov.KineticAleksandrov
