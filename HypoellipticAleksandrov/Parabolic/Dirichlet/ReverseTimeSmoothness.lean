module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime

/-!
# Reverse-time smoothness infrastructure

This module records smoothness preservation under the reverse-time map and
the coordinate-level smoothness facts used by the reverse-time Dirichlet
construction.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators Matrix.Norms.Elementwise

/-- The reverse-time map is smooth. -/
theorem contDiff_reverseTimeMap {d : ℕ} (r₁ : ℝ) :
    ContDiff ℝ ⊤ (reverseTimeMap r₁ : TimeVelocity d → TimeVelocity d) := by
  exact (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- A function smooth on a neighborhood of a set is differentiable at each
point of the set. -/
theorem IsSmoothOnNeighborhood.differentiableAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : Set E}
    (hf : IsSmoothOnNeighborhood f K) {x : E} (hx : x ∈ K) :
    DifferentiableAt ℝ f x := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  exact (hV.contDiffAt (hVopen.mem_nhds (hKV hx))).differentiableAt (by simp)

/-- Reverse-time pullback preserves smoothness on corresponding neighborhoods. -/
theorem IsSmoothOnNeighborhood.reverseTime
    {d : ℕ} {S K : Set (TimeVelocity d)} (r₁ : ℝ)
    {f : TimeVelocity d → ℝ}
    (hSK : reverseTimeMap r₁ '' S ⊆ K)
    (hf : IsSmoothOnNeighborhood f K) :
    IsSmoothOnNeighborhood (f ∘ reverseTimeMap r₁) S := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  refine ⟨reverseTimeMap r₁ ⁻¹' V,
    (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen, ?_, ?_⟩
  · intro z hz
    exact hKV (hSK ⟨z, hz, rfl⟩)
  · exact hV.comp
      ((contDiff_reverseTimeMap r₁).of_le (by exact_mod_cast le_top)).contDiffOn
      fun _ hz => hz

/-- Matrix-valued coefficient smoothness gives smoothness of each entry. -/
theorem IsSmoothOnNeighborhood.coefficientEntry
    {d : ℕ} {K : Set (TimeVelocity d)} (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (i j : Fin d) :
    IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2 i j) K := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  refine ⟨V, hVopen, hKV, ?_⟩
  have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
    exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV fun _ _ => Set.mem_univ _
  exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hrow fun _ _ => Set.mem_univ _

/-- The spatial slice derivative is the full derivative applied to a purely
spatial tangent vector. -/
theorem fderiv_spatialSlice_apply
    {d : ℕ} (a : CoefficientField d) (r : ℝ)
    (y v : PDE.Vec d) (i j : Fin d)
    (ha : DifferentiableAt ℝ
      (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) :
    (fderiv ℝ (fun x : PDE.Vec d => a r x i j) y) v =
      (fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) (0, v) := by
  have hslice : HasFDerivAt (fun x : PDE.Vec d => a r x i j)
      ((fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) y := by
    simpa only [Function.comp_def] using ha.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) r y)
  rw [hslice.fderiv]
  rfl

/-- Smooth matrix and drift fields give a smooth divergence-form drift entry. -/
theorem IsSmoothOnNeighborhood.divergenceDriftEntry
    {d : ℕ} {K : Set (TimeVelocity d)}
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) K)
    (j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j) K := by
  rcases ha with ⟨Va, hVaopen, hKVa, hVa⟩
  rcases hb with ⟨Vb, hVbopen, hKVb, hVb⟩
  refine ⟨Va ∩ Vb, hVaopen.inter hVbopen, fun z hz => ⟨hKVa hz, hKVb hz⟩, ?_⟩
  have hentry (i : Fin d) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => a z.1 z.2 i j) Va := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp
      ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hVa fun _ _ => Set.mem_univ _)
      fun _ _ => Set.mem_univ _
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
      scalarSpatialCoefficientDivergence a z j) Va := by
    have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
        ∑ i : Fin d,
          (fderiv ℝ (fun w : TimeVelocity d => a w.1 w.2 i j) z)
            (0, PDE.basisVec i)) Va := by
      apply ContDiffOn.sum
      intro i _
      exact ((hentry i).fderiv_of_isOpen hVaopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiffOn_const
    refine hsum.congr ?_
    intro z hz
    rcases z with ⟨r, y⟩
    simp only [scalarSpatialCoefficientDivergence]
    apply Finset.sum_congr rfl
    intro i _
    exact fderiv_spatialSlice_apply a r y (PDE.basisVec i) i j
      (((hentry i).contDiffAt (hVaopen.mem_nhds hz)).differentiableAt (by simp))
  have hbentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) Vb := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hVb fun _ _ => Set.mem_univ _
  exact (hdiv.mono Set.inter_subset_left).sub (hbentry.mono Set.inter_subset_right)

end HypoellipticAleksandrov.Parabolic.Dirichlet
