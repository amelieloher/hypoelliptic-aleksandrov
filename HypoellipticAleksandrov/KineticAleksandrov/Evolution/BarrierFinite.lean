module

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierStatement

/-!
# Finiteness of `M_F`

For a smooth compactly supported terminal datum `F`, coefficients with Loewner bounds and a
Lipschitz drift, the constant `M_F = sup_{0 ≤ ε ≤ 1} ‖L_ε F‖_∞` of (A.1) is
finite.  This removes the finiteness premise from `two_barriers_sup`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- Derivative of `x ↦ c x w` in the direction `v`, for a differentiable `c`. -/
theorem fderiv_clm_apply_const_eval {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E → E →L[ℝ] F} {x : E}
    (hc : DifferentiableAt ℝ c x) (w v : E) :
    fderiv ℝ (fun y => c y w) x v = fderiv ℝ c x v w := by
  have := (hc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  rw [this]
  simp

/-- The Hessian of the restriction of `F` along an affine embedding with derivative `J`. -/
theorem sliceHessian_comp_embed {n : ℕ} {F : PDE.Vec n × PDE.Vec n → ℝ} (hF : ContDiff ℝ 2 F)
    {ι : PDE.Vec n → PDE.Vec n × PDE.Vec n} (hιc : ContDiff ℝ 2 ι)
    {J : PDE.Vec n →L[ℝ] PDE.Vec n × PDE.Vec n} (hι : ∀ x, HasFDerivAt ι J x)
    (x : PDE.Vec n) (i j : Fin n) :
    sliceHessian (fun x' => F (ι x')) x i j =
      fderiv ℝ (fderiv ℝ F) (ι x) (J (PDE.basisVec i)) (J (PDE.basisVec j)) := by
  have hg : ContDiffAt ℝ 2 (fun x' => F (ι x')) x := (hF.comp hιc).contDiffAt
  rw [sliceHessian_apply_eq_sndFDeriv hg]
  have hFd : ∀ w, DifferentiableAt ℝ F w := fun w => hF.differentiable (by norm_num) w
  have hfd : ∀ x', fderiv ℝ (fun x' => F (ι x')) x' = (fderiv ℝ F (ι x')).comp J := by
    intro x'
    exact ((hFd (ι x')).hasFDerivAt.comp x' (hι x')).fderiv
  have hgd : DifferentiableAt ℝ (fderiv ℝ (fun x' => F (ι x'))) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := fderiv_clm_apply_const_eval hgd (PDE.basisVec j) (PDE.basisVec i)
  rw [← h1]
  have hfun : (fun y => fderiv ℝ (fun x' => F (ι x')) y (PDE.basisVec j)) =
      fun y => fderiv ℝ F (ι y) (J (PDE.basisVec j)) := by
    funext y
    rw [hfd y]
    rfl
  rw [hfun]
  have hF1 : DifferentiableAt ℝ (fderiv ℝ F) (ι x) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (ι x))
  have hh : HasFDerivAt (fun w => fderiv ℝ F w (J (PDE.basisVec j)))
      (fderiv ℝ (fun w => fderiv ℝ F w (J (PDE.basisVec j))) (ι x)) (ι x) :=
    (hF1.clm_apply (differentiableAt_const _)).hasFDerivAt
  have hcomp := hh.comp x (hι x)
  have := hcomp.fderiv
  rw [show (fun y => fderiv ℝ F (ι y) (J (PDE.basisVec j))) =
      (fun w => fderiv ℝ F w (J (PDE.basisVec j))) ∘ ι from rfl, this]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply_const_eval hF1]

/-- Entries of a matrix with `0 ≤ A ≤ Λ I` are bounded by `Λ`. -/
theorem abs_apply_le_of_loewner {n : ℕ} {A : PDE.Mat n} {Lam : ℝ} (h0 : A.PosSemidef)
    (h1 : (Lam • (1 : PDE.Mat n) - A).PosSemidef) (i j : Fin n) : |A i j| ≤ Lam := by
  have hsymm : ∀ k l, A k l = A l k := fun k l => by
    simpa using (h0.isHermitian.apply l k)
  have hdiag : ∀ k, 0 ≤ A k k ∧ A k k ≤ Lam := by
    intro k
    have a0 := h0.dotProduct_mulVec_nonneg (PDE.basisVec k)
    have a1 := h1.dotProduct_mulVec_nonneg (PDE.basisVec k)
    simp [dotProduct, Matrix.mulVec, PDE.basisVec_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply] at a0 a1
    constructor <;> linarith
  have hpm : ∀ s : ℝ, 0 ≤ A i i + s ^ 2 * A j j + 2 * s * A i j := by
    intro s
    have h := h0.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) + Pi.single j s)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_single, dotProduct_add,
      add_dotProduct, single_dotProduct, Pi.smul_apply, Matrix.col_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at h
    rw [hsymm j i] at h
    nlinarith [h]
  have hii := hdiag i
  have hjj := hdiag j
  rw [abs_le]
  constructor
  · have := hpm 1
    nlinarith
  · have := hpm (-1)
    nlinarith

/-- Coordinate basis vectors have sup-norm at most one. -/
theorem norm_basisVec_le {n : ℕ} (i : Fin n) : ‖(PDE.basisVec i : PDE.Vec n)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  rw [Real.norm_eq_abs, PDE.basisVec_apply]
  split_ifs <;> simp

/-- The embedded basis vector `(e_i, 0)` has norm at most one. -/
theorem norm_inl_basisVec_le {n : ℕ} (i : Fin n) :
    ‖((PDE.basisVec i : PDE.Vec n), (0 : PDE.Vec n))‖ ≤ 1 := by
  rw [Prod.norm_def]
  exact max_le (norm_basisVec_le i) (by simp)

/-- The embedded basis vector `(0, e_i)` has norm at most one. -/
theorem norm_inr_basisVec_le {n : ℕ} (i : Fin n) :
    ‖((0 : PDE.Vec n), (PDE.basisVec i : PDE.Vec n))‖ ≤ 1 := by
  rw [Prod.norm_def]
  exact max_le (by simp) (norm_basisVec_le i)

/-- The derivative of the embedding `y ↦ (y, z)`. -/
theorem hasFDerivAt_embedLeft {n : ℕ} (z y : PDE.Vec n) :
    HasFDerivAt (fun y' : PDE.Vec n => (y', z))
      ((ContinuousLinearMap.id ℝ (PDE.Vec n)).prod (0 : PDE.Vec n →L[ℝ] PDE.Vec n)) y :=
  (hasFDerivAt_id y).prodMk (hasFDerivAt_const z y)

/-- The derivative of the embedding `z ↦ (y, z)`. -/
theorem hasFDerivAt_embedRight {n : ℕ} (y z : PDE.Vec n) :
    HasFDerivAt (fun z' : PDE.Vec n => (y, z'))
      ((0 : PDE.Vec n →L[ℝ] PDE.Vec n).prod (ContinuousLinearMap.id ℝ (PDE.Vec n))) z :=
  (hasFDerivAt_const y z).prodMk (hasFDerivAt_id z)

/-- Entries of the `y`-Hessian are bounded by the second derivative bound. -/
theorem abs_sliceHessian_position_le {n : ℕ} {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ 2 F) {K2 : ℝ} (hK2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ K2)
    (y z : PDE.Vec n) (i j : Fin n) :
    |sliceHessian (fun y' => F (y', z)) y i j| ≤ K2 := by
  have hιc : ContDiff ℝ 2 (fun y' : PDE.Vec n => (y', z)) := contDiff_id.prodMk contDiff_const
  rw [sliceHessian_comp_embed hF hιc (fun x => hasFDerivAt_embedLeft z x) y i j]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply]
  have h := (fderiv ℝ (fderiv ℝ F) (y, z)).le_opNorm₂
    ((PDE.basisVec i : PDE.Vec n), (0 : PDE.Vec n))
    ((PDE.basisVec j : PDE.Vec n), (0 : PDE.Vec n))
  rw [Real.norm_eq_abs] at h
  have h1 := norm_inl_basisVec_le i
  have h2 := norm_inl_basisVec_le j
  have h3 := hK2 (y, z)
  have h4 : 0 ≤ ‖fderiv ℝ (fderiv ℝ F) (y, z)‖ := ContinuousLinearMap.opNorm_nonneg _
  have h5 : 0 ≤ K2 := h4.trans h3
  calc _ ≤ _ := h
    _ ≤ K2 * 1 * 1 := by
      gcongr
    _ = K2 := by ring

/-- Entries of the `z`-Hessian are bounded by the second derivative bound. -/
theorem abs_sliceHessian_velocity_le {n : ℕ} {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ 2 F) {K2 : ℝ} (hK2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ K2)
    (y z : PDE.Vec n) (i j : Fin n) :
    |sliceHessian (fun z' => F (y, z')) z i j| ≤ K2 := by
  have hιc : ContDiff ℝ 2 (fun z' : PDE.Vec n => (y, z')) := contDiff_const.prodMk contDiff_id
  rw [sliceHessian_comp_embed hF hιc (fun x => hasFDerivAt_embedRight y x) z i j]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply]
  have h := (fderiv ℝ (fderiv ℝ F) (y, z)).le_opNorm₂
    ((0 : PDE.Vec n), (PDE.basisVec i : PDE.Vec n))
    ((0 : PDE.Vec n), (PDE.basisVec j : PDE.Vec n))
  rw [Real.norm_eq_abs] at h
  have h1 := norm_inr_basisVec_le i
  have h2 := norm_inr_basisVec_le j
  have h3 := hK2 (y, z)
  have h4 : 0 ≤ ‖fderiv ℝ (fderiv ℝ F) (y, z)‖ := ContinuousLinearMap.opNorm_nonneg _
  have h5 : 0 ≤ K2 := h4.trans h3
  calc _ ≤ _ := h
    _ ≤ K2 * 1 * 1 := by
      gcongr
    _ = K2 := by ring

/-- The `z`-gradient is the partial Fréchet derivative. -/
theorem classicalGradient_velocity_eq {n : ℕ} {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ 1 F) (y z : PDE.Vec n) (j : Fin n) :
    PDE.classicalGradient (fun z' => F (y, z')) z j =
      fderiv ℝ F (y, z) ((0 : PDE.Vec n), (PDE.basisVec j : PDE.Vec n)) := by
  have hd : DifferentiableAt ℝ F (y, z) := hF.differentiable (by norm_num) _
  have h1 := (hd.hasFDerivAt.comp z (hasFDerivAt_embedRight y z)).fderiv
  rw [PDE.classicalGradient_apply]
  have e : fderiv ℝ (fun z' => F (y, z')) z = (fderiv ℝ F (y, z)).comp
      ((0 : PDE.Vec n →L[ℝ] PDE.Vec n).prod (ContinuousLinearMap.id ℝ (PDE.Vec n))) := h1
  rw [e, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply]

/-- The `z`-gradient is bounded by the first derivative bound. -/
theorem abs_classicalGradient_velocity_le {n : ℕ} {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ 1 F) {K1 : ℝ} (hK1 : ∀ x, ‖fderiv ℝ F x‖ ≤ K1)
    (y z : PDE.Vec n) (j : Fin n) :
    |PDE.classicalGradient (fun z' => F (y, z')) z j| ≤ K1 := by
  have hd : DifferentiableAt ℝ F (y, z) := hF.differentiable (by norm_num) _
  have h1 := (hd.hasFDerivAt.comp z (hasFDerivAt_embedRight y z)).fderiv
  rw [PDE.classicalGradient_apply]
  have e : fderiv ℝ (fun z' => F (y, z')) z = (fderiv ℝ F (y, z)).comp
      ((0 : PDE.Vec n →L[ℝ] PDE.Vec n).prod (ContinuousLinearMap.id ℝ (PDE.Vec n))) := h1
  rw [e, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply]
  have h := (fderiv ℝ F (y, z)).le_opNorm ((0 : PDE.Vec n), (PDE.basisVec j : PDE.Vec n))
  rw [Real.norm_eq_abs] at h
  have h2 := norm_inr_basisVec_le j
  have h3 := hK1 (y, z)
  have h4 : 0 ≤ ‖fderiv ℝ F (y, z)‖ := ContinuousLinearMap.opNorm_nonneg _
  have h5 : 0 ≤ K1 := h4.trans h3
  calc _ ≤ _ := h
    _ ≤ K1 * 1 := by gcongr
    _ = K1 := by ring

/-- `M_F = sup_ε ‖L_ε F‖_∞` is finite for a smooth compactly supported `F`, for coefficients
with Loewner bounds and a Lipschitz drift. -/
theorem exists_terminalGenerator_bound {n : ℕ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hcs : HasCompactSupport (F : EvolutionAmbientState n → ℝ))
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ p : KineticPoint n,
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M := by
  have hF2 : ContDiff ℝ 2 (F : EvolutionAmbientState n → ℝ) :=
    hF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hF1 : ContDiff ℝ 1 (F : EvolutionAmbientState n → ℝ) :=
    hF.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨K1, hK1⟩ : ∃ K1, ∀ x, ‖fderiv ℝ (F : EvolutionAmbientState n → ℝ) x‖ ≤ K1 :=
    (hF.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcs.fderiv ℝ)
  obtain ⟨K2, hK2⟩ : ∃ K2, ∀ x, ‖fderiv ℝ (fderiv ℝ (F : EvolutionAmbientState n → ℝ)) x‖ ≤ K2 :=
    ((hF.fderiv_right (m := 1) (by simp)).continuous_fderiv
      one_ne_zero).bounded_above_of_compact_support ((hcs.fderiv ℝ).fderiv ℝ)
  have hK1nn : 0 ≤ K1 := (ContinuousLinearMap.opNorm_nonneg _).trans (hK1 0)
  have hK2nn : 0 ≤ K2 := (ContinuousLinearMap.opNorm_nonneg _).trans (hK2 0)
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
  set R' := max R 0 with hR'
  have hR'nn : 0 ≤ R' := le_max_right _ _
  set b0 := PDE.vecEuclideanNorm (b 0) with hb0
  set Bb := b0 + |Lb| * (Real.sqrt n * R') with hBb
  have hb0nn : 0 ≤ b0 := PDE.vecEuclideanNorm_nonneg _
  have hBbnn : 0 ≤ Bb := by positivity
  refine ⟨(n : ℝ) ^ 2 * |Lam| * K2 + n * Bb * K1 + n * K2, fun ε hε0 hε1 p => ?_⟩
  set Fe : KineticPoint n → ℝ := fun q => F (q.position, q.velocity) with hFe
  have htime : kineticTimeDerivative Fe p = 0 := by
    unfold kineticTimeDerivative
    simp [hFe]
  have hApsd : (B p.time p.position p.velocity).PosSemidef :=
    posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _
  have hAup : (Lam • (1 : PDE.Mat n) - B p.time p.position p.velocity).PosSemidef :=
    Matrix.le_iff.mp (hB _ _ _).2
  have hAent : ∀ i j, |B p.time p.position p.velocity i j| ≤ |Lam| := fun i j =>
    (abs_apply_le_of_loewner hApsd hAup i j).trans (le_abs_self _)
  have hH : ∀ i j, |diffusedHessian Fe p i j| ≤ K2 := by
    intro i j
    rw [diffusedHessian_eq_sliceHessian]
    exact abs_sliceHessian_position_le hF2 hK2 _ _ i j
  have hHz : ∀ i j, |kineticVelocityHessian Fe p i j| ≤ K2 := by
    intro i j
    rw [kineticVelocityHessian_eq_sliceHessian]
    exact abs_sliceHessian_velocity_le hF2 hK2 _ _ i j
  have hc2 : |matrixContraction (B p.time p.position p.velocity) (diffusedHessian Fe p)| ≤
      (n : ℝ) ^ 2 * |Lam| * K2 := by
    unfold matrixContraction
    calc |∑ i, ∑ j, B p.time p.position p.velocity i j * diffusedHessian Fe p i j|
        ≤ ∑ i, |∑ j, B p.time p.position p.velocity i j * diffusedHessian Fe p i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |Lam| * K2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
          rw [abs_mul]
          exact mul_le_mul (hAent i j) (hH i j) (abs_nonneg _) (abs_nonneg _)
      _ = (n : ℝ) ^ 2 * |Lam| * K2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hlap : |∑ i, kineticVelocityHessian Fe p i i| ≤ n * K2 := by
    calc |∑ i, kineticVelocityHessian Fe p i i| ≤ ∑ i, |kineticVelocityHessian Fe p i i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, K2 := Finset.sum_le_sum (fun i _ => hHz i i)
      _ = n * K2 := by simp
  have hdrift : |PDE.vecDot (b p.position) (kineticVelocityGradient Fe p)| ≤ n * Bb * K1 := by
    have hg : ∀ j, |kineticVelocityGradient Fe p j| ≤ K1 := fun j =>
      abs_classicalGradient_velocity_le hF1 hK1 _ _ j
    by_cases hmem : (p.position, p.velocity) ∈ tsupport (F : EvolutionAmbientState n → ℝ)
    · have hy : ‖p.position‖ ≤ R' := (norm_fst_le _).trans ((hR _ hmem).trans (le_max_left _ _))
      have hyE : PDE.vecEuclideanNorm p.position ≤ Real.sqrt n * R' :=
        (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _).trans
          (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
      have hbj : ∀ j, |b p.position j| ≤ Bb := by
        intro j
        calc |b p.position j| ≤ PDE.vecEuclideanNorm (b p.position) :=
              PDE.abs_apply_le_vecEuclideanNorm _ _
          _ ≤ b0 + |Lb| * PDE.vecEuclideanNorm p.position :=
              vecEuclideanNorm_le_of_lipschitz hb _
          _ ≤ Bb := by
              rw [hBb]
              have := mul_le_mul_of_nonneg_left hyE (abs_nonneg Lb)
              linarith
      unfold PDE.vecDot
      calc |∑ j, b p.position j * kineticVelocityGradient Fe p j|
          ≤ ∑ j, |b p.position j * kineticVelocityGradient Fe p j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin n, Bb * K1 := Finset.sum_le_sum (fun j _ => by
            rw [abs_mul]
            exact mul_le_mul (hbj j) (hg j) (abs_nonneg _) hBbnn)
        _ = n * Bb * K1 := by simp; ring
    · have hz : fderiv ℝ (F : EvolutionAmbientState n → ℝ) (p.position, p.velocity) = 0 := by
        by_contra hne
        exact hmem (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      have hg0 : ∀ j, kineticVelocityGradient Fe p j = 0 := by
        intro j
        show PDE.classicalGradient (fun z' => F (p.position, z')) p.velocity j = 0
        rw [classicalGradient_velocity_eq hF1, hz]
        simp
      unfold PDE.vecDot
      simp only [hg0, mul_zero, Finset.sum_const_zero, abs_zero]
      positivity
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply, htime]
  simp only [fullKineticCoefficientAt_apply, zero_add]
  have h1 := abs_le.mp hc2
  have h2 := abs_le.mp hdrift
  have h3 := abs_le.mp hlap
  have h4 : |ε * ∑ i, kineticVelocityHessian Fe p i i| ≤ n * K2 := by
    rw [abs_mul, abs_of_nonneg hε0]
    have : (0 : ℝ) ≤ n * K2 := by positivity
    calc ε * |∑ i, kineticVelocityHessian Fe p i i| ≤ 1 * (n * K2) :=
          mul_le_mul hε1 hlap (abs_nonneg _) zero_le_one
      _ = n * K2 := one_mul _
  have h5 := abs_le.mp h4
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h5.1, h5.2]

/-- (A.1) with `‖F‖ = ‖F‖_∞` and `M_F = sup_ε ‖L_ε F‖_∞`. -/
theorem two_barriers_sup {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r₀) γ τ F)
    {dstar : ℝ} (hd : 0 < dstar) (hd4 : dstar < r₀ / 4)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * dstar ≤ r₀ - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u) :
    (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      |u p| ≤ boundedBorelSupNorm F * min 1
        (barrierW (collarKappa Lγ lam)
            (r₀ - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa Lγ lam) dstar)) ∧
    (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      τ - dstar / (1 + Lγ) ≤ p.time →
        |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * terminalGeneratorSup B b τ F) := by
  obtain ⟨M, hM⟩ := exists_terminalGenerator_bound hF.1 hF.2.1 hlam hB hb
  have hMbdd : BddAbove {x | ∃ ε ∈ Icc (0 : ℝ) 1, ∃ p : KineticPoint n, p.time ≤ τ ∧
      x = |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p|} := by
    refine ⟨M, ?_⟩
    rintro x ⟨ε', hε', p, -, rfl⟩
    exact hM ε' hε'.1 hε'.2 p
  exact two_barriers hr₀ hγ hLγ hγL hlam hB hb hε0 hε1 hF hd hd4 hsupp
    (abs_le_boundedBorelSupNorm F)
    (fun p hp => le_csSup hMbdd ⟨ε, ⟨hε0, hε1⟩, p, hp, rfl⟩) hu

end HypoellipticAleksandrov.KineticAleksandrov
