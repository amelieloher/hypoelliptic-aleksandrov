module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketLie

/-!
# The sum-of-squares identity `Lop = X_0 + ∑ X_i²`

For `u` of class `C²` at `x`, the first-order operators `X_0, X_i` (and `Y_l`) satisfy, in the
packed coordinates `x = (σ, v, z)`,

`X_0 u + ∑_i X_i (X_i u) = ∂_σ u + B(σ,v,z) : D_v² u + b(v) · ∇_z u`

(Proposition 2.1), and, adding the constant fields `Y_l = √ε ∂_{z_l}`,
`X_0 u + ∑ X_i² u + ∑ Y_l² u = Lop u + ε Δ_z u` (Proposition 2.1).
No `z`-derivative falls on `β` in `X_i`, so the identity holds also when `B` depends on `z`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder Matrix

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- The unit time direction `∂_σ`. -/
def basisT : EvolutionVec n := packPoint 1 0 0

/-- The unit diffused direction `∂_{v_j}`. -/
def basisV (j : Fin n) : EvolutionVec n := packPoint 0 (Pi.single j 1) 0

/-- The unit transported direction `∂_{z_l}`. -/
def basisZ (l : Fin n) : EvolutionVec n := packPoint 0 0 (Pi.single l 1)

/-- A first-order operator: the derivation `u ↦ X u = Du · X` of a vector field `X`. -/
def fieldApply (X : EvolutionVec n → EvolutionVec n) (u : EvolutionVec n → ℝ)
    (x : EvolutionVec n) : ℝ :=
  fderiv ℝ u x (X x)

/-- Decomposition of `packPoint` along the coordinate directions. -/
theorem packPoint_eq_sum (s : ℝ) (v z : PDE.Vec n) :
    packPoint s v z = s • basisT + ∑ k, v k • basisV k + ∑ l, z l • basisZ l := by
  refine ext_coords ?_ ?_ ?_
  · simp [basisT, basisV, basisZ]
  · simp only [basisT, basisV, basisZ, map_add, map_sum, map_smul, diffusedCoord_packPoint]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  · simp only [basisT, basisV, basisZ, map_add, map_sum, map_smul, transportedCoord_packPoint]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]

/-- A linear map applied to `packPoint s v z`. -/
theorem map_packPoint {F : Type*} [AddCommGroup F] [Module ℝ F] {G : Type*}
    [FunLike G (EvolutionVec n) F] [LinearMapClass G ℝ (EvolutionVec n) F] (ℓ : G)
    (s : ℝ) (v z : PDE.Vec n) :
    ℓ (packPoint s v z) = s • ℓ basisT + ∑ k, v k • ℓ (basisV k) + ∑ l, z l • ℓ (basisZ l) := by
  rw [packPoint_eq_sum]
  simp [map_add, map_sum, map_smul]

/-- A bilinear form on two purely diffused vectors. -/
theorem bilin_packPoint_diffused (Q : EvolutionVec n →L[ℝ] EvolutionVec n →L[ℝ] ℝ)
    (f g : PDE.Vec n) :
    Q (packPoint 0 f 0) (packPoint 0 g 0) = ∑ j, ∑ k, f j * g k * Q (basisV j) (basisV k) := by
  have h1 : Q (packPoint 0 f 0) = ∑ j, f j • Q (basisV j) := by
    simpa using map_packPoint Q 0 f 0
  rw [h1, sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply, smul_eq_mul]
  have h2 : Q (basisV j) (packPoint 0 g 0) = ∑ k, g k * Q (basisV j) (basisV k) := by
    simpa using map_packPoint (Q (basisV j)) 0 g 0
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- The second derivative with one direction held fixed. -/
theorem fderiv_fderiv_apply {u : EvolutionVec n → ℝ} {x : EvolutionVec n}
    (hD : DifferentiableAt ℝ (fderiv ℝ u) x) (w w' : EvolutionVec n) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x w' = fderiv ℝ (fderiv ℝ u) x w' w := by
  have h := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hD.hasFDerivAt
  have h' : HasFDerivAt (fun y => fderiv ℝ u y w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ u) x)) x := h
  rw [h'.fderiv]
  rfl

/-- The second application of a field `V`: `V (V u) = Du · (DV · V) + D²u (V, V)`. -/
theorem fieldApply_fieldApply {u : EvolutionVec n → ℝ} {V : EvolutionVec n → EvolutionVec n}
    {x : EvolutionVec n} (hD : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hV : DifferentiableAt ℝ V x) :
    fieldApply V (fieldApply V u) x =
      fderiv ℝ u x (fderiv ℝ V x (V x)) + fderiv ℝ (fderiv ℝ u) x (V x) (V x) := by
  unfold fieldApply
  rw [fderiv_clm_apply hD hV]
  simp

section Algebra

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- The derivative of `X_i` is purely diffused, with entries the derivatives of `β_ik`. -/
theorem fderiv_diffusionField
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (i : Fin n)
    (x w : EvolutionVec n) :
    fderiv ℝ (diffusionField B i) x w =
      packPoint 0 (fun k => fderiv ℝ (fun y => sqrtCoeffAt B y i k) x w) 0 := by
  have hV : DifferentiableAt ℝ (diffusionField B i) x :=
    ((contDiff_diffusionField hβ i).differentiable (by simp)) x
  refine ext_coords ?_ ?_ ?_
  · simpa using coord_fderiv_const (timeCoord n) hV 0 (fun y => by simp [diffusionField]) w
  · funext k
    have := coord_fderiv_comp ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n => ℝ) k).comp (diffusedCoord n)) hV
      (g := fun y => sqrtCoeffAt B y i k) (fun y => by simp [diffusionField]) w
    simpa using this
  · simpa using coord_fderiv_const (transportedCoord n) hV 0
      (fun y => by simp [diffusionField]) w

/-- `∑_i β_ij β_ik = B_jk`: the square-root factorisation (uses symmetry of `β`). -/
theorem sum_sqrtCoeffAt_mul {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (x : EvolutionVec n) (j k : Fin n) :
    ∑ i, sqrtCoeffAt B x i j * sqrtCoeffAt B x i k =
      B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) j k := by
  set A := B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) with hA
  have hApd : A.PosDef := posDef_of_smul_one_le hlam (hell _ _ _).1
  have hsq : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hApd.posSemidef.nonneg
  have hsymm : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have hsymm' : ∀ i j, CFC.sqrt A i j = CFC.sqrt A j i := fun i j => by
    have := congrFun (congrFun hsymm j) i
    simpa [Matrix.conjTranspose_apply] using this
  have := congrFun (congrFun hsq j) k
  rw [Matrix.mul_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sqrtCoeffAt, ← hA]
  rw [hsymm' i j]

/-- The transported operator `Lop = ∂_σ + B(σ,v,z) : D_v² + b(v) · ∇_z` in packed
coordinates (`B_ij ∂_{v_i} ∂_{v_j} u`, with the same index convention as
`transportedForwardOperator`). -/
def transportedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  fderiv ℝ u x basisT +
    ∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j *
      fderiv ℝ (fun y => fderiv ℝ u y (basisV j)) x (basisV i) +
    ∑ l, b (diffusedCoord n x) l * fderiv ℝ u x (basisZ l)

/-- The regularised operator `L_ε = Lop + ε Δ_z` in packed coordinates. -/
def regularizedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  transportedOperator B b u x +
    ε * ∑ l, fderiv ℝ (fun y => fderiv ℝ u y (basisZ l)) x (basisZ l)

theorem differentiableAt_fderiv_of_contDiffAt {u : EvolutionVec n → ℝ} {x : EvolutionVec n}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (fderiv ℝ u) x :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- The second-order part of `∑ X_i²` and the first-order correction, for one field. -/
theorem fieldApply_diffusion_sq {lam Lam : ℝ} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    {u : EvolutionVec n → ℝ} {x : EvolutionVec n} (hu : ContDiffAt ℝ 2 u x) (i : Fin n) :
    fieldApply (diffusionField B i) (fieldApply (diffusionField B i) u) x =
      (∑ k, (∑ j, sqrtCoeffAt B x i j *
        fderiv ℝ (fun y => sqrtCoeffAt B y i k) x (basisV j)) * fderiv ℝ u x (basisV k)) +
      ∑ j, ∑ k, sqrtCoeffAt B x i j * sqrtCoeffAt B x i k *
        fderiv ℝ (fderiv ℝ u) x (basisV j) (basisV k) := by
  have hβ := contDiff_sqrtCoeffAt_entry hlam hB hell
  have hV : DifferentiableAt ℝ (diffusionField B i) x :=
    ((contDiff_diffusionField hβ i).differentiable (by simp)) x
  have hD := differentiableAt_fderiv_of_contDiffAt hu
  rw [fieldApply_fieldApply hD hV, fderiv_diffusionField hβ i]
  have hxi : diffusionField B i x = packPoint 0 (fun j => sqrtCoeffAt B x i j) 0 := rfl
  rw [hxi, bilin_packPoint_diffused]
  congr 1
  have h : fderiv ℝ u x (packPoint 0 (fun k => fderiv ℝ (fun y => sqrtCoeffAt B y i k) x
      (packPoint 0 (fun j => sqrtCoeffAt B x i j) 0)) 0) = ∑ k, fderiv ℝ (fun y =>
      sqrtCoeffAt B y i k) x (packPoint 0 (fun j => sqrtCoeffAt B x i j) 0) *
        fderiv ℝ u x (basisV k) := by
    simpa using map_packPoint (F := ℝ) (fderiv ℝ u x) 0
      (fun k => fderiv ℝ (fun y => sqrtCoeffAt B y i k) x
        (packPoint 0 (fun j => sqrtCoeffAt B x i j) 0)) 0
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h2 : fderiv ℝ (fun y => sqrtCoeffAt B y i k) x
      (packPoint 0 (fun j => sqrtCoeffAt B x i j) 0) =
      ∑ j, sqrtCoeffAt B x i j * fderiv ℝ (fun y => sqrtCoeffAt B y i k) x (basisV j) := by
    simpa using map_packPoint (F := ℝ) (fderiv ℝ (fun y => sqrtCoeffAt B y i k) x) 0
      (fun j => sqrtCoeffAt B x i j) 0
  exact h2

/-- **Sum-of-squares identity** `Lop = X_0 + ∑_i X_i²` (Proposition 2.1), applied to
a function of class `C²` at `x`.  Holds also when `B` depends on `z`. -/
theorem fieldApply_drift_add_sum_sq {lam Lam : ℝ} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    {u : EvolutionVec n → ℝ} {x : EvolutionVec n} (hu : ContDiffAt ℝ 2 u x) :
    fieldApply (driftField B b) u x +
      ∑ i, fieldApply (diffusionField B i) (fieldApply (diffusionField B i) u) x =
      transportedOperator B b u x := by
  have hD := differentiableAt_fderiv_of_contDiffAt hu
  rw [Finset.sum_congr rfl fun i _ => fieldApply_diffusion_sq hlam hB hell hu i,
    Finset.sum_add_distrib]
  have h0 : fieldApply (driftField B b) u x = fderiv ℝ u x basisT -
      ∑ k, driftCorrection B k x * fderiv ℝ u x (basisV k) +
        ∑ l, b (diffusedCoord n x) l * fderiv ℝ u x (basisZ l) := by
    unfold fieldApply driftField
    have := map_packPoint (F := ℝ) (fderiv ℝ u x) 1 (fun k => - driftCorrection B k x)
      (b (diffusedCoord n x))
    simp only [smul_eq_mul] at this
    rw [this, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp
  have h1 : ∑ i, ∑ k, (∑ j, sqrtCoeffAt B x i j *
        fderiv ℝ (fun y => sqrtCoeffAt B y i k) x (basisV j)) * fderiv ℝ u x (basisV k) =
      ∑ k, driftCorrection B k x * fderiv ℝ u x (basisV k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [driftCorrection, basisV, Finset.sum_mul]
  have h2 : ∑ i, ∑ j, ∑ k, sqrtCoeffAt B x i j * sqrtCoeffAt B x i k *
        fderiv ℝ (fderiv ℝ u) x (basisV j) (basisV k) =
      ∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j *
        fderiv ℝ (fun y => fderiv ℝ u y (basisV j)) x (basisV i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fderiv_fderiv_apply hD, ← sum_sqrtCoeffAt_mul hlam hell x j k, Finset.sum_mul]
  rw [h0, h1, h2, transportedOperator]
  ring

/-- For the constant field `Y_l = √ε ∂_{z_l}`: `Y_l (Y_l u) = ε ∂_{z_l}² u`. -/
theorem fieldApply_regularizing_sq {ε : ℝ} (hε : 0 ≤ ε)
    {u : EvolutionVec n → ℝ} {x : EvolutionVec n} (hu : ContDiffAt ℝ 2 u x) (l : Fin n) :
    fieldApply (regularizingField ε l) (fieldApply (regularizingField ε l) u) x =
      ε * fderiv ℝ (fun y => fderiv ℝ u y (basisZ l)) x (basisZ l) := by
  have hD := differentiableAt_fderiv_of_contDiffAt hu
  have hY' : DifferentiableAt ℝ (regularizingField (n := n) ε l) x := differentiableAt_const _
  rw [fieldApply_fieldApply hD hY', fderiv_fderiv_apply hD]
  have hY : regularizingField ε l x = Real.sqrt ε • basisZ l := by
    refine ext_coords ?_ ?_ ?_
    · simp [regularizingField, basisZ]
    · simp [regularizingField, basisZ]
    · simp only [regularizingField, basisZ, map_smul, transportedCoord_packPoint]
      funext j
      simp [Pi.single_apply]
  have hconst : fderiv ℝ (regularizingField (n := n) ε l) x = 0 :=
    congrFun (fderiv_fun_const (𝕜 := ℝ) (packPoint 0 0 (Pi.single l (Real.sqrt ε)))) x
  rw [hconst, hY]
  simp only [zero_apply, map_zero, map_smul, smul_apply, smul_eq_mul, mul_zero, zero_add]
  rw [← mul_assoc, Real.mul_self_sqrt hε]

/-- **Sum-of-squares identity** `L_ε = X_0 + ∑ X_i² + ∑ Y_l²`
(Proposition 2.1), for `ε ≥ 0` and `u` of class `C²` at `x`. -/
theorem fieldApply_drift_add_sum_sq_regularized {lam Lam ε : ℝ} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hε : 0 ≤ ε) {u : EvolutionVec n → ℝ} {x : EvolutionVec n} (hu : ContDiffAt ℝ 2 u x) :
    fieldApply (driftField B b) u x +
      ∑ i, fieldApply (diffusionField B i) (fieldApply (diffusionField B i) u) x +
      ∑ l, fieldApply (regularizingField ε l) (fieldApply (regularizingField ε l) u) x =
      regularizedOperator B b ε u x := by
  rw [fieldApply_drift_add_sum_sq hlam hB hell hu, regularizedOperator, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => fieldApply_regularizing_sq hε hu l

end Algebra

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
