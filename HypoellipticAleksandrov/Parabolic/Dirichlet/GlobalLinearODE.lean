module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Global finite-coordinate linear ODEs on compact intervals

This file supplies the finite-dimensional nonautonomous linear ODE engine
needed by the Dirichlet Galerkin construction.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

noncomputable section

private def clip {n : ℕ} (R : NNReal) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)

private theorem lipschitzWith_clip {n : ℕ} (R : NNReal) :
    LipschitzWith 1 (clip (n := n) R) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) dist_nonneg)).mpr fun i => ?_
  change dist (clip R z i) (clip R w i) ≤ (1 : ℝ) * dist z w
  calc
    dist (clip R z i) (clip R w i) ≤ (1 : ℝ) * dist (z i) (w i) := by
      exact (LipschitzWith.projIcc (neg_le_self R.2)).dist_le_mul _ _
    _ ≤ (1 : ℝ) * dist z w := by
      gcongr
      simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (z - w) i

private theorem norm_clip_le_radius {n : ℕ} (R : NNReal) (z : Fin n → ℝ) :
    ‖clip R z‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg R.2).mpr fun i => ?_
  change ‖(Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)‖ ≤ R
  rw [Real.norm_eq_abs]
  exact abs_le.2 (Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i)).property

private theorem norm_clip_le {n : ℕ} (R : NNReal) (z : Fin n → ℝ) :
    ‖clip R z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => ?_
  have hzero : (0 : ℝ) ∈ Set.Icc (-(R : ℝ)) (R : ℝ) := by
    exact ⟨neg_nonpos.mpr R.2, R.2⟩
  have h := (LipschitzWith.projIcc (neg_le_self R.2)).dist_le_mul (z i) 0
  have hprojzero :
      ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) 0 :
        Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) = 0 := by
    simpa using congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self R.2) hzero)
  change ‖(Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)‖ ≤ ‖z‖
  rw [← dist_zero_right]
  calc
    dist ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
      Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) 0 =
        dist ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
          Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ)
          ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) 0 :
            Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) := by
      rw [hprojzero]
    _ ≤ (1 : ℝ) * dist (z i) 0 := h
    _ = ‖z i‖ := by simp only [one_mul, dist_zero_right]
    _ ≤ ‖z‖ := norm_le_pi_norm z i

private theorem clip_eq_self_of_norm_lt {n : ℕ} {R : NNReal} {z : Fin n → ℝ}
    (hz : ‖z‖ < R) : clip R z = z := by
  ext i
  have hzi : ‖z i‖ < (R : ℝ) :=
    (norm_le_pi_norm z i).trans_lt hz
  rw [Real.norm_eq_abs] at hzi
  have hz_mem : z i ∈ Set.Icc (-(R : ℝ)) (R : ℝ) :=
    ⟨(abs_lt.mp hzi).1.le, (abs_lt.mp hzi).2.le⟩
  change ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
    Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) = z i
  simpa using congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self R.2) hz_mem)

/-- A continuous affine linear field on a compact interval has a solution on that interval. -/
theorem exists_linear_ode_on_Icc
    {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : ℝ → Fin n → ℝ)
    (hA : ContinuousOn A (Set.Icc a b))
    (hf : ContinuousOn f (Set.Icc a b))
    (x0 : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ,
      x a = x0 ∧
      ContinuousOn x (Set.Icc a b) ∧
      ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt x (A t (x t) + f t) (Set.Icc a b) t := by
  let t0 : Set.Icc a b := ⟨a, le_rfl, hab⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (A a)).trans (hC a t0.2)
  have hD_nonneg : 0 ≤ D :=
    (norm_nonneg (f a)).trans (hD a t0.2)
  let Cnn : NNReal := Real.toNNReal C
  let Dnn : NNReal := Real.toNNReal D
  have hCnn : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ (Cnn : ℝ) := by
    intro t ht
    simpa only [Cnn, Real.coe_toNNReal _ hC_nonneg] using hC t ht
  have hDnn : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ (Dnn : ℝ) := by
    intro t ht
    simpa only [Dnn, Real.coe_toNNReal _ hD_nonneg] using hD t ht
  let G : ℝ := gronwallBound ‖x0‖ C D (b - a)
  let R : NNReal := Real.toNNReal (|G| + 1)
  let L : NNReal := Cnn * R + Dnn
  let r : NNReal := ‖x0‖₊
  let T : NNReal := Real.toNNReal (b - a)
  let q : NNReal := r + L * T
  let g : ℝ → (Fin n → ℝ) → Fin n → ℝ :=
    fun t z => A t (clip R z) + f t
  have hT_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hT : (T : ℝ) = b - a := by
    simp only [T, Real.coe_toNNReal _ hT_nonneg]
  have hG_lt_R : G < (R : ℝ) := by
    dsimp [R]
    exact (lt_add_of_le_of_pos (le_abs_self G) zero_lt_one).trans_le (le_max_left _ _)
  have hPL : IsPicardLindelof g t0 0 q r L Cnn := {
    lipschitzOnWith := by
      intro t ht
      apply (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
      calc
        dist (g t z) (g t w) = dist (A t (clip R z)) (A t (clip R w)) := by
          simp only [g, dist_add_right]
        _ ≤ ‖A t‖ * dist (clip R z) (clip R w) := (A t).dist_le_opNorm _ _
        _ ≤ (Cnn : ℝ) * dist (clip R z) (clip R w) := by
          gcongr
          exact hCnn t ht
        _ ≤ (Cnn : ℝ) * ((1 : ℝ) * dist z w) := by
          gcongr
          exact (lipschitzWith_clip R).dist_le_mul z w
        _ = (Cnn : ℝ) * dist z w := by ring
    continuousOn := by
      intro z hz
      simpa only [g] using
        (hA.clm_apply continuousOn_const).fun_add hf
    norm_le := by
      intro t ht z hz
      calc
        ‖g t z‖ ≤ ‖A t (clip R z)‖ + ‖f t‖ := norm_add_le _ _
        _ ≤ (Cnn : ℝ) * ‖clip R z‖ + (Dnn : ℝ) := by
          gcongr
          · exact (A t).le_of_opNorm_le (hCnn t ht) _
          · exact hDnn t ht
        _ ≤ (Cnn : ℝ) * (R : ℝ) + (Dnn : ℝ) := by
          gcongr
          exact norm_clip_le_radius R z
        _ = (L : ℝ) := by simp only [L, NNReal.coe_add, NNReal.coe_mul]
    mul_max_le := by
      calc
        (L : ℝ) * max (b - (t0 : ℝ)) ((t0 : ℝ) - a) ≤ (L : ℝ) * (b - a) := by
          simp only [t0, sub_self, max_eq_left hT_nonneg]
          exact le_rfl
        _ = (q : ℝ) - (r : ℝ) := by
          dsimp [q]
          rw [NNReal.coe_add, NNReal.coe_mul, hT]
          ring }
  have hx0_ball : x0 ∈ Metric.closedBall (0 : Fin n → ℝ) r := by
    simpa only [r, Metric.mem_closedBall, dist_zero_right, coe_nnnorm] using (le_refl ‖x0‖)
  obtain ⟨x, hx0, hdx⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx0_ball
  have hx_cont : ContinuousOn x (Set.Icc a b) := fun t ht =>
    (hdx t ht).continuousWithinAt
  have hdx_right : ∀ t ∈ Set.Ico a b, HasDerivWithinAt x (g t (x t)) (Set.Ici t) t := by
    intro t ht
    exact (hdx t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hg_bound : ∀ t ∈ Set.Ico a b, ‖g t (x t)‖ ≤ C * ‖x t‖ + D := by
    intro t ht
    calc
      ‖g t (x t)‖ ≤ ‖A t (clip R (x t))‖ + ‖f t‖ := norm_add_le _ _
      _ ≤ ‖A t‖ * ‖clip R (x t)‖ + D := by
        gcongr
        · exact (A t).le_of_opNorm_le le_rfl _
        · exact hD t (Set.Ico_subset_Icc_self ht)
      _ ≤ C * ‖clip R (x t)‖ + D := by
        gcongr
        exact hC t (Set.Ico_subset_Icc_self ht)
      _ ≤ C * ‖x t‖ + D := by
        gcongr
        exact norm_clip_le R (x t)
  have hxG : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ G := by
    intro t ht
    have hxa : ‖x a‖ ≤ ‖x0‖ := by
      rw [show a = (t0 : ℝ) by rfl, hx0]
    refine (norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖x0‖)
      hx_cont hdx_right hxa hg_bound t ht).trans ?_
    · simpa only [G] using
        gronwallBound_mono (norm_nonneg x0) hD_nonneg hC_nonneg
          (sub_le_sub_right ht.2 a)
  have hclip : ∀ t ∈ Set.Icc a b, clip R (x t) = x t := by
    intro t ht
    apply clip_eq_self_of_norm_lt
    exact (hxG t ht).trans_lt hG_lt_R
  refine ⟨x, hx0, hx_cont, ?_⟩
  intro t ht
  simpa only [g, hclip t ht] using hdx t ht

/-- Two solutions of the same continuous affine linear ODE agree on its compact interval. -/
theorem linear_ode_on_Icc_eqOn
    {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : ℝ → Fin n → ℝ)
    (hA : ContinuousOn A (Set.Icc a b))
    {x y : ℝ → Fin n → ℝ}
    (hxy0 : x a = y a)
    (hx : ContinuousOn x (Set.Icc a b))
    (hy : ContinuousOn y (Set.Icc a b))
    (hdx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (A t (x t) + f t) (Set.Icc a b) t)
    (hdy : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt y (A t (y t) + f t) (Set.Icc a b) t) :
    Set.EqOn x y (Set.Icc a b) := by
  let t0 : Set.Icc a b := ⟨a, le_rfl, hab⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (A a)).trans (hC a t0.2)
  let Cnn : NNReal := Real.toNNReal C
  have hCnn : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ (Cnn : ℝ) := by
    intro t ht
    simpa only [Cnn, Real.coe_toNNReal _ hC_nonneg] using hC t ht
  let v : ℝ → (Fin n → ℝ) → Fin n → ℝ := fun t z => A t z + f t
  have hv : ∀ t ∈ Set.Ico a b, LipschitzOnWith Cnn (v t) Set.univ := by
    intro t ht
    apply (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
    calc
      dist (v t z) (v t w) = dist (A t z) (A t w) := by
        simp only [v, dist_add_right]
      _ ≤ ‖A t‖ * dist z w := (A t).dist_le_opNorm _ _
      _ ≤ (Cnn : ℝ) * dist z w := by
        gcongr
        exact hCnn t (Set.Ico_subset_Icc_self ht)
  have hdx_right : ∀ t ∈ Set.Ico a b, HasDerivWithinAt x (v t (x t)) (Set.Ici t) t := by
    intro t ht
    simpa only [v] using
      (hdx t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
  have hdy_right : ∀ t ∈ Set.Ico a b, HasDerivWithinAt y (v t (y t)) (Set.Ici t) t := by
    intro t ht
    simpa only [v] using
      (hdy t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
  exact ODE_solution_unique_of_mem_Icc_right hv hx hdx_right (fun _ _ => Set.mem_univ _)
    hy hdy_right (fun _ _ => Set.mem_univ _) hxy0

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
