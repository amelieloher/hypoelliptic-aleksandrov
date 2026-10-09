module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates

/-!
# Iterated Fréchet derivatives through coordinate partials

The `k`-th Fréchet derivative of a smooth function on phase space is controlled by the
iterated coordinate partials `∂_{c₁} ⋯ ∂_{c_k}`:
`‖D^k F(y)‖ ≤ ∑ over words |∂_{c₁} ⋯ ∂_{c_k} F(y)|`.
This lets the derivative bounds of the flow kernel, stated for coordinate words, be used as the
`iteratedFDeriv` bounds required by `SmoothingKernelFamily`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- Iterated coordinate partials along a word; the head of the list is the outermost
derivative. -/
def wordPartial : List (Fin d ⊕ Fin d) → (EvolutionAmbientState d → ℝ) →
    EvolutionAmbientState d → ℝ
  | [], F => F
  | c :: l, F => coordPartial c (wordPartial l F)

theorem iteratedFDeriv_coordDir {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∀ (k : ℕ) (m : Fin k → Fin d ⊕ Fin d),
      (fun y => iteratedFDeriv ℝ k F y (fun i => coordDir (m i))) =
        wordPartial (List.ofFn m) F := by
  intro k
  induction k with
  | zero => intro m; funext y; simp [wordPartial]
  | succ k ih =>
    intro m
    funext y
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) y :=
      (hF.differentiable_iteratedFDeriv (m := k) (by
        exact_mod_cast (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k)))) y
    rw [hd.iteratedFDeriv_succ_apply_left']
    have := ih (fun i => m i.succ)
    have e : (fun i : Fin k => coordDir (m (Fin.succ i))) = Fin.tail (fun i => coordDir (m i)) :=
      rfl
    rw [← e, this, List.ofFn_succ]
    rfl

/-- The coordinate decomposition coefficients of a phase-space vector. -/
def coordCoef (x : EvolutionAmbientState d) : Fin d ⊕ Fin d → ℝ :=
  Sum.elim (fun j => x.1 j) (fun j => x.2 j)

theorem sum_coordCoef_smul (x : EvolutionAmbientState d) :
    ∑ c, coordCoef x c • coordDir c = x := by
  rw [Fintype.sum_sum_type]
  ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coordCoef, coordDir,
    Pi.single_apply]

theorem abs_coordCoef_le (x : EvolutionAmbientState d) (c : Fin d ⊕ Fin d) :
    |coordCoef x c| ≤ ‖x‖ := by
  rcases c with j | j
  · simp only [coordCoef, Sum.elim_inl, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm x.1 j).trans (le_max_left _ _)
  · simp only [coordCoef, Sum.elim_inr, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm x.2 j).trans (le_max_right _ _)

theorem norm_multilinear_le_sum {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => EvolutionAmbientState d) ℝ) :
    ‖A‖ ≤ ∑ m : Fin k → Fin d ⊕ Fin d, |A (fun i => coordDir (m i))| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun x => ?_
  have hx : x = fun i => ∑ c, coordCoef (x i) c • coordDir c :=
    funext fun i => (sum_coordCoef_smul (x i)).symm
  have hA : A x = ∑ r : Fin k → Fin d ⊕ Fin d,
      (∏ i, coordCoef (x i) (r i)) * A (fun i => coordDir (r i)) := by
    conv_lhs => rw [hx]
    refine (A.toMultilinearMap.map_sum (fun i c => coordCoef (x i) c • coordDir c)).trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    have := A.toMultilinearMap.map_smul_univ (fun i => coordCoef (x i) (r i))
      (fun i => coordDir (r i))
    simpa using this
  rw [hA, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => abs_coordCoef_le (x i) (r i))
    (abs_nonneg _)

theorem norm_iteratedFDeriv_le_sum {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (k : ℕ) (y : EvolutionAmbientState d) :
    ‖iteratedFDeriv ℝ k F y‖ ≤
      ∑ m : Fin k → Fin d ⊕ Fin d, |wordPartial (List.ofFn m) F y| := by
  refine (norm_multilinear_le_sum _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← iteratedFDeriv_coordDir hF k m]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
