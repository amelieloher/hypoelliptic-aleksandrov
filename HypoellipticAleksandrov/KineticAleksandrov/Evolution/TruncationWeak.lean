module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakJets
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Weak transfer of the actual straightened Dirichlet solution

Only the anisotropic regularity supplied by the Dirichlet predicate is used.
The time chain rule and spatial integration by parts yield the regularized kinetic
weak equation. No interior smoothness or weak equation is assumed as a premise.
-/

@[expose] public section

open Set Filter MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped Topology MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov
open Evolution

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive

/-- The actual classical Dirichlet solution pulls back to a
weak regularized kinetic solution, using its supplied slice C1,2 regularity. -/
theorem weakRegularized_of_straightened_dirichlet
    (a τ r R : ℝ) (haτ : a < τ) (hr : 0 < r) (hR : 0 < R)
    (g : ℝ → PDE.Vec n) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (ε : ℝ) (hε : 0 < ε) (F : BoundedBorel (EvolutionAmbientState n))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    IsKineticWeakRegularizedSolution B b ε
      {p : KineticPoint n | a < p.time ∧ p.time < τ ∧
        spatialPack (p.position - g p.time) p.velocity ∈
          openEllipsoid (straightenedEllipsoidMatrix n r R)}
      (fun p => u (p.time, spatialPack (p.position - g p.time) p.velocity))
      (fun _ => 0) := by
  let D := openEllipsoid (straightenedEllipsoidMatrix n r R)
  let W := scalarParabolicOpenCylinder a τ D
  let Q := truncationPoint g
  let U := Q ⁻¹' W
  let w := u ∘ Q
  let T (x : EvolutionVec n) := scalarTimeDerivative u (Q x) +
    PDE.vecDot (-deriv g (timeCoord n x)) (spatialY (scalarSpatialGradient u (Q x)))
  let V (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialGradient u (Q x) (Fin.castAdd n i)
  let Z (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialGradient u (Q x) (Fin.natAdd n i)
  let H (i j : Fin n) (x : EvolutionVec n) :=
    scalarSpatialHessian u (Q x) (Fin.castAdd n i) (Fin.castAdd n j)
  let K (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialHessian u (Q x) (Fin.natAdd n i) (Fin.natAdd n i)
  have hD : IsOpen D := by
    have he : D = {x : PDE.Vec (n + n) |
        PDE.vecNormSq (spatialY x) / r ^ 2 + PDE.vecNormSq (spatialZ x) / R ^ 2 < 1} := by
      ext x
      exact (straightenedEllipsoid_characterization n r R hr hR).2 x
    rw [he]
    exact isOpen_lt
      (((PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous).div_const _).add
        ((PDE.continuous_vecNormSq.comp (contDiff_spatialZ (m := 0)).continuous).div_const _))
      continuous_const
  have hW : IsOpen W := isOpen_Ioo.prod hD
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_truncationPoint hg
  have hU : IsOpen U := hW.preimage hQ.continuous
  have huc : IsScalarC12On u W := hu.2.1
  have hw : ContinuousOn w U := huc.continuousOn.comp hQ.continuous.continuousOn
    (fun x hx => hx)
  have ht0 : ContinuousOn (fun x => scalarTimeDerivative u (Q x)) U :=
    huc.continuousOn_scalarTimeDerivative.comp hQ.continuous.continuousOn (fun x hx => hx)
  have hg0 : ContinuousOn (fun x => scalarSpatialGradient u (Q x)) U :=
    huc.continuousOn_scalarSpatialGradient.comp hQ.continuous.continuousOn (fun x hx => hx)
  have hh0 : ContinuousOn (fun x => scalarSpatialHessian u (Q x)) U :=
    huc.continuousOn_scalarSpatialHessian.comp hQ.continuous.continuousOn (fun x hx => hx)
  have hT : ContinuousOn T U := by
    apply ht0.add
    unfold PDE.vecDot
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp
      (((hg.continuous_deriv (by simp)).comp (timeCoord n).continuous).neg)).continuousOn.mul
      ((continuous_apply (Fin.castAdd n i)).comp_continuousOn hg0)
  have hV : ∀ i, ContinuousOn (V i) U := fun i => (continuous_apply _).comp_continuousOn hg0
  have hZ : ∀ i, ContinuousOn (Z i) U := fun i => (continuous_apply _).comp_continuousOn hg0
  have hentry (i j : Fin (n + n)) :
      ContinuousOn (fun x => scalarSpatialHessian u (Q x) i j) U :=
    (show Continuous (fun A : PDE.Mat (n + n) => A i j) from
      (continuous_apply j).comp (continuous_apply i)).comp_continuousOn hh0
  have hH : ∀ i j, ContinuousOn (H i j) U := fun i j => hentry _ _
  have hK : ∀ i, ContinuousOn (K i) U := fun i => hentry _ _
  have hdirV (i : Fin n) : spatialPack (diffusedCoord n (basisV i))
      (transportedCoord n (basisV i)) = PDE.basisVec (Fin.castAdd n i) := by
    simpa only [basisV, diffusedCoord_packPoint, transportedCoord_packPoint,
      PDE.basisVec, embedYCLM_apply, embedZCLM_apply] using embedYCLM_basisVec (n := n) i
  have hdirZ (i : Fin n) : spatialPack (diffusedCoord n (basisZ i))
      (transportedCoord n (basisZ i)) = PDE.basisVec (Fin.natAdd n i) := by
    simpa only [basisZ, diffusedCoord_packPoint, transportedCoord_packPoint,
      PDE.basisVec, embedYCLM_apply, embedZCLM_apply] using embedZCLM_basisVec (n := n) i
  have hdT : ∀ x ∈ U, HasLineDerivAt ℝ w (T x) x basisT := fun x hx =>
    truncation_hasLineDerivAt_time hg hW huc hx
  have hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ w (V i x) x (basisV i) := by
    intro i x hx
    have h := truncation_hasLineDerivAt_spatial (w := basisV i) huc hx (by simp [basisV])
    simpa only [hdirV, PDE.vecDot_basisVec_right] using! h
  have hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ w (Z i x) x (basisZ i) := by
    intro i x hx
    have h := truncation_hasLineDerivAt_spatial (w := basisZ i) huc hx (by simp [basisZ])
    simpa only [hdirZ, PDE.vecDot_basisVec_right] using! h
  have hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j) := by
    intro i j x hx
    have h := truncation_gradient_hasLineDerivAt (w := basisV j) huc hx (by simp [basisV])
      (Fin.castAdd n j) (Fin.castAdd n i) (hdirV j)
    have hsymm := scalarSpatialHessian_isSymm_of_c12 huc hx
    have he : scalarSpatialHessian u (Q x) (Fin.castAdd n j) (Fin.castAdd n i) =
        H i j x := congrFun (congrFun hsymm (Fin.castAdd n i)) (Fin.castAdd n j)
    change HasLineDerivAt ℝ (V i)
      (scalarSpatialHessian u (Q x) (Fin.castAdd n j) (Fin.castAdd n i)) x (basisV j) at h
    rw [he] at h
    exact h
  have hdK : ∀ i x, x ∈ U → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i) :=
    fun i x hx => truncation_gradient_hasLineDerivAt (w := basisZ i) huc hx (by simp [basisZ])
      (Fin.natAdd n i) (Fin.natAdd n i) (hdirZ i)
  have heq : ∀ x ∈ U, T x +
      (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
      (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x = 0 := by
    intro x hx
    have h := hu.2.2.1 (Q x) hx
    simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at h
    rw [scalarParabolicOperator_apply] at h
    have ha : straightenedCoefficient B g ε (Q x).1 (Q x).2 =
        viscousBlockMatrix (B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x)) ε := by
      simp [Q, truncationPoint, straightenedCoefficient]
    have hb : straightenedDrift b g (Q x).1 (Q x).2 =
        spatialPack (-deriv g (timeCoord n x)) (b (diffusedCoord n x)) := by
      simp [Q, truncationPoint, straightenedDrift]
    rw [ha, hb, matrixContraction_viscousBlockMatrix, vecDot_spatialPack_left] at h
    dsimp only [T, H, Z, K]
    simp only [matrixContraction, PDE.vecDot, spatialZ, Fin.natAdd_eq_addNat] at h ⊢
    linarith
  apply (isWeakRegularizedSolution_comp_iff B b ε _ _ (fun _ => 0)).mp
  have hUeq : evolutionHomeomorph n ⁻¹'
      {p : KineticPoint n | a < p.time ∧ p.time < τ ∧
        spatialPack (p.position - g p.time) p.velocity ∈ D} = U := by
    ext x
    simp only [U, Q, W, D, truncationPoint, Set.mem_preimage, Set.mem_ofPred_eq,
      mem_scalarParabolicOpenCylinder_iff, time_evolutionHomeomorph,
      position_evolutionHomeomorph, velocity_evolutionHomeomorph]
  rw [hUeq]
  change IsWeakRegularizedSolution B b ε U w (fun _ => 0)
  refine ⟨hw.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
  rw [integral_regularizedAdjoint_of_jets B b ε hB_smooth hb_smooth
    w T V Z H K hw hT hV hZ hH hK hdT hdV hdZ hdH hdK ψ hψ hc hs]
  have hz : (fun x => (T x +
      (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
      (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x) * ψ x) =ᵐ[volume.restrict U]
        fun _ => (0 : ℝ) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [heq x hx, zero_mul]
  simp only [zero_mul, integral_zero]
  exact integral_eq_zero_of_ae hz

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
