module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord

/-! # Adjoint integration for continuous anisotropic directional jets -/

@[expose] public section

open Set MeasureTheory
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

/-- Integration against the formal adjoint equals integration of the corresponding
continuous anisotropic jet. Every derivative relation is used in integration by parts. -/
theorem integral_regularizedAdjoint_of_jets
    {n : ℕ} {U : Set (EvolutionVec n)}
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (u T : EvolutionVec n → ℝ) (V Z : Fin n → EvolutionVec n → ℝ)
    (H : Fin n → Fin n → EvolutionVec n → ℝ) (K : Fin n → EvolutionVec n → ℝ)
    (hu : ContinuousOn u U) (hT : ContinuousOn T U)
    (hV : ∀ i, ContinuousOn (V i) U) (hZ : ∀ i, ContinuousOn (Z i) U)
    (hH : ∀ i j, ContinuousOn (H i j) U) (hK : ∀ i, ContinuousOn (K i) U)
    (hdT : ∀ x ∈ U, HasLineDerivAt ℝ u (T x) x basisT)
    (hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (V i x) x (basisV i))
    (hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (Z i x) x (basisZ i))
    (hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j))
    (hdK : ∀ i x, x ∈ U → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, (T x +
        (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
        (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x) * ψ x := by
  let A i j (x : EvolutionVec n) :=
    B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j
  let β i (x : EvolutionVec n) := b (diffusedCoord n x) i
  let D (v : EvolutionVec n) (φ : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ φ x v
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (A i j) := fun i j =>
    (hB i j).comp (evolutionProdCLE n).contDiff
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (β i) := fun i =>
    (contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff
  have hD : ∀ v φ, ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (D v φ) :=
    fun v φ hφ => (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc : ∀ v φ, HasCompactSupport φ → HasCompactSupport (D v φ) :=
    fun v φ hφ => hφ.fderiv_apply (𝕜 := ℝ) v
  have hDs : ∀ v φ, tsupport (D v φ) ⊆ tsupport φ :=
    fun v φ => tsupport_evolution_fderiv_apply φ v
  have eqT : (∫ x in U, u x * D basisT ψ x) = -∫ x in U, T x * ψ x :=
    setIntegral_mul_evolution_directional_test hu hT basisT hdT hψ hc hs
  have eqH : ∀ i j,
      (∫ x in U, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) =
        ∫ x in U, (A i j x * H i j x) * ψ x := by
    intro i j
    have h := setIntegral_mul_evolution_second_test hu (hV i) (hH i j)
      (basisV i) (basisV j) (hdV i) (hdH i j) ((hA i j).mul hψ)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
    convert h using 1
    congr 1
    funext x
    ring
  have eqZ : ∀ i, (∫ x in U, u x * (β i x * D (basisZ i) ψ x)) =
      -∫ x in U, (β i x * Z i x) * ψ x := by
    intro i
    have he : D (basisZ i) (fun y => β i y * ψ y) =
        fun x => β i x * D (basisZ i) ψ x := by
      funext x
      dsimp only [D]
      rw [fderiv_fun_mul ((hβ i).differentiable (by simp) x)
        (hψ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      change β i x * fderiv ℝ ψ x (basisZ i) +
        ψ x * fderiv ℝ (fun y => b (diffusedCoord n y) i) x (basisZ i) = _
      rw [fderiv_drift_transported_zero hb, mul_zero, add_zero]

    have h := setIntegral_mul_evolution_directional_test hu (hZ i) (basisZ i)
      (hdZ i) ((hβ i).mul hψ) hc.mul_left (tsupport_mul_subset_right.trans hs)
    change (∫ z in U, u z * D (basisZ i) (fun y => β i y * ψ y) z) = _ at h
    rw [he] at h
    convert h using 1
    congr 2
    funext x
    ring
  have eqK : ∀ i, (∫ x in U, u x * D (basisZ i) (D (basisZ i) ψ) x) =
      ∫ x in U, K i x * ψ x := fun i =>
    setIntegral_mul_evolution_second_test hu (hZ i) (hK i) (basisZ i) (basisZ i)
      (hdZ i) (hdK i) hψ hc hs
  have iT : IntegrableOn (fun x => u x * D basisT ψ x) U volume :=
    (integrable_evolution_mul_test hu (hD basisT ψ hψ).continuous
      (hDc basisT ψ hc) ((hDs basisT ψ).trans hs)).integrableOn
  have iH : ∀ i j, IntegrableOn (fun x =>
      u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) U volume := by
    intro i j
    exact (integrable_evolution_mul_test hu
      (hD _ _ (hD _ _ ((hA i j).mul hψ))).continuous
      (hDc _ _ (hDc _ _ hc.mul_left))
      ((hDs _ _).trans ((hDs _ _).trans (tsupport_mul_subset_right.trans hs)))).integrableOn
  have iZ : ∀ i, IntegrableOn (fun x => u x * (β i x * D (basisZ i) ψ x)) U volume :=
    fun i => (integrable_evolution_mul_test hu
      ((hβ i).continuous.mul (hD _ _ hψ).continuous)
      (hDc _ _ hc).mul_left (tsupport_mul_subset_right.trans ((hDs _ _).trans hs))).integrableOn
  have iK : ∀ i, IntegrableOn (fun x => u x * D (basisZ i) (D (basisZ i) ψ) x) U volume :=
    fun i => (integrable_evolution_mul_test hu (hD _ _ (hD _ _ hψ)).continuous
      (hDc _ _ (hDc _ _ hc)) ((hDs _ _).trans ((hDs _ _).trans hs))).integrableOn
  have jT : IntegrableOn (fun x => T x * ψ x) U volume :=
    (integrable_evolution_mul_test hT hψ.continuous hc hs).integrableOn
  have jH : ∀ i j, IntegrableOn (fun x => (A i j x * H i j x) * ψ x) U volume :=
    fun i j => (integrable_evolution_mul_test ((hA i j).continuous.continuousOn.mul (hH i j))
      hψ.continuous hc hs).integrableOn
  have jZ : ∀ i, IntegrableOn (fun x => (β i x * Z i x) * ψ x) U volume :=
    fun i => (integrable_evolution_mul_test ((hβ i).continuous.continuousOn.mul (hZ i))
      hψ.continuous hc hs).integrableOn
  have jK : ∀ i, IntegrableOn (fun x => K i x * ψ x) U volume :=
    fun i => (integrable_evolution_mul_test (hK i) hψ.continuous hc hs).integrableOn
  have sumInt {ι : Type} [Fintype ι] (f : ι → EvolutionVec n → ℝ)
      (hf : ∀ i, IntegrableOn (f i) U volume) :
      IntegrableOn (fun x => ∑ i, f i x) U volume :=
    integrable_finsetSum _ (fun i _ => hf i)
  change (∫ x in U, u x * (-D basisT ψ x +
    (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
    (∑ i, β i x * D (basisZ i) ψ x) + ε * ∑ i, D (basisZ i) (D (basisZ i) ψ) x)) =
    ∫ x in U, (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x) + ε * ∑ i, K i x) * ψ x
  have hleft : (fun x => u x * (-D basisT ψ x +
      (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
      (∑ i, β i x * D (basisZ i) ψ x) + ε * ∑ i, D (basisZ i) (D (basisZ i) ψ) x)) =
      fun x => -(u x * D basisT ψ x) +
        (∑ i, ∑ j, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
        (∑ i, u x * (β i x * D (basisZ i) ψ x)) +
        ε * ∑ i, u x * D (basisZ i) (D (basisZ i) ψ) x := by
    funext x
    simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum]
    congr 1
    simp only [mul_left_comm]
  rw [hleft]
  erw [integral_add ((iT.neg.add (sumInt _ (fun i => sumInt _ (iH i)))).sub
    (sumInt _ iZ)) ((sumInt _ iK).const_mul ε),
    integral_sub (iT.neg.add (sumInt _ (fun i => sumInt _ (iH i)))) (sumInt _ iZ),
    integral_add iT.neg (sumInt _ (fun i => sumInt _ (iH i))), integral_neg,
    integral_const_mul]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (iH i))]
  simp_rw [integral_finsetSum _ (fun j _ => iH _ j)]
  erw [integral_finsetSum _ (fun i _ => iZ i),
    integral_finsetSum _ (fun i _ => iK i)]
  simp_rw [eqT, eqH, eqZ, eqK]
  simp only [neg_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  have hright : (fun x => (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x) + ε * ∑ i, K i x) * ψ x) =
      fun x => T x * ψ x + (∑ i, ∑ j, (A i j x * H i j x) * ψ x) +
        (∑ i, (β i x * Z i x) * ψ x) + ε * ∑ i, K i x * ψ x := by
    funext x
    simp only [add_mul, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  rw [hright]
  erw [integral_add ((jT.add (sumInt _ (fun i => sumInt _ (jH i)))).add
    (sumInt _ jZ)) ((sumInt _ jK).const_mul ε),
    integral_add (jT.add (sumInt _ (fun i => sumInt _ (jH i)))) (sumInt _ jZ),
    integral_add jT (sumInt _ (fun i => sumInt _ (jH i))), integral_const_mul]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (jH i))]
  simp_rw [integral_finsetSum _ (fun j _ => jH _ j)]
  erw [integral_finsetSum _ (fun i _ => jZ i), integral_finsetSum _ (fun i _ => jK i)]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
