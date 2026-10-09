module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FlowMoments
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.IteratedPartial
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel

/-!
# The Gaussian flow kernel as a smoothing kernel family

The Gaussian flow estimates: for `lam > 0`, the Gaussian kernel `flowKernel lam`
satisfies every field of `SmoothingKernelFamily`, so all statements of the smoothing estimates hold
for it.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real MeasureTheory Set

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem vecDir_eq_coordDir (δ : Fin d ⊕ Fin d) : vecDir δ = coordDir δ := by
  rcases δ with i | i <;> rfl

theorem iterPartial_eq_wordPartial (l : List (Fin d ⊕ Fin d))
    (F : EvolutionAmbientState d → ℝ) : iterPartial l F = wordPartial l F := by
  induction l with
  | nil => rfl
  | cons δ l ih =>
    funext y
    simp only [iterPartial, wordPartial, ih]
    unfold dirPartial coordPartial
    rw [vecDir_eq_coordDir]

theorem flowKernel_iteratedFDeriv_bound {lam : ℝ} (hl : 0 < lam) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      ‖iteratedFDeriv ℝ k (flowKernel lam h) y‖ ≤ C * (1 + ‖y‖) ^ k * flowKernel lam h y := by
  have hw : ∀ m : Fin k → Fin d ⊕ Fin d, ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      |wordPartial (List.ofFn m) (flowKernel lam h) y| ≤
        C * (1 + ‖y‖) ^ k * flowKernel lam h y := fun m => by
    obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl ha (List.ofFn m)
    refine ⟨C, fun h hah y => ?_⟩
    have := hC h hah y
    rwa [iterPartial_eq_wordPartial, List.length_ofFn] at this
  choose C hC using hw
  refine ⟨∑ m, |C m|, fun h hah y => ?_⟩
  have hh : 0 < h := ha.trans_le hah
  have hp := flowKernel_pos hl hh y
  refine (norm_iteratedFDeriv_le_sum (flowKernel_contDiff hl hh) k y).trans ?_
  calc ∑ m : Fin k → Fin d ⊕ Fin d, |wordPartial (List.ofFn m) (flowKernel lam h) y|
      ≤ ∑ m : Fin k → Fin d ⊕ Fin d, |C m| * ((1 + ‖y‖) ^ k * flowKernel lam h y) :=
        Finset.sum_le_sum fun m _ => by
          refine (hC m h hah y).trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ = (∑ m, |C m|) * (1 + ‖y‖) ^ k * flowKernel lam h y := by
        rw [← Finset.sum_mul, mul_assoc]

theorem gaussExp_half_le_one {ε : ℝ} (hε : 0 < ε) (y : EvolutionAmbientState d) :
    gaussExp (ε / 2) 0 (ε / 2) y ≤ 1 := by
  unfold gaussExp quadForm
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (y.2 i), sq_nonneg (y.1 i)]

theorem continuousOn_flowCoef {lam : ℝ} (hl : 0 < lam) :
    ContinuousOn (flowConst lam) (Set.Ioi 0) ∧ ContinuousOn (flowA lam) (Set.Ioi 0) ∧
      ContinuousOn (flowB lam) (Set.Ioi 0) ∧ ContinuousOn (flowC lam) (Set.Ioi 0) := by
  have hne : ∀ h ∈ (Set.Ioi (0 : ℝ)), h ≠ 0 := fun h hh => ne_of_gt hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold flowConst
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun h hh => ?_
    have := hne h hh; positivity
  · unfold flowA
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun h hh => ?_
    have := hne h hh; positivity
  · unfold flowB
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun h hh => ?_
    have := hne h hh; positivity
  · unfold flowC
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun h hh => ?_
    have := hne h hh; positivity

theorem flowKernel_jointContinuousOn {lam : ℝ} (hl : 0 < lam) :
    ContinuousOn (fun p : ℝ × EvolutionAmbientState d => flowKernel lam p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hg : Continuous (fun q : ℝ × ℝ × ℝ × EvolutionAmbientState d =>
      gaussExp q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    unfold gaussExp quadForm; fun_prop
  obtain ⟨h0, h1, h2, h3⟩ := continuousOn_flowCoef hl
  have hfst : MapsTo (fun p : ℝ × EvolutionAmbientState d => p.1) (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (Set.Ioi 0) := fun p hp => hp.1
  have e1 : ContinuousOn (fun p : ℝ × EvolutionAmbientState d => flowConst lam p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := h0.comp continuousOn_fst hfst
  have e2 : ContinuousOn (fun p : ℝ × EvolutionAmbientState d =>
      (flowA lam p.1, flowB lam p.1, flowC lam p.1, p.2)) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (h1.comp continuousOn_fst hfst).prodMk ((h2.comp continuousOn_fst hfst).prodMk
      ((h3.comp continuousOn_fst hfst).prodMk continuousOn_snd))
  have e3 := hg.comp_continuousOn e2
  have hc := (e1.pow d).mul e3
  exact hc.congr fun p hp => flowKernel_eq hl hp.1 p.2

/-- The Gaussian flow kernel `Φ_h` of the Gaussian flow as an abstract smoothing kernel family. -/
def flowKernelFamily {lam : ℝ} (hl : 0 < lam) : SmoothingKernelFamily d lam where
  kernel := flowKernel lam
  supConst := flowSupConstant d lam
  pos := fun hh y => flowKernel_pos hl hh y
  contDiff := fun hh => flowKernel_contDiff hl hh
  integral_eq_one := fun hh => integral_flowKernel hl hh
  le_sup := fun {h} hh y => by
    have := flowKernel_le hl hh y
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_neg hh.le]
    congr 2
    rw [show (2 * d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  hasDerivAt_heat := fun hh y => hasDerivAt_flowKernel hl hh y
  deriv_bound := fun k {K} hK hsub => by
    obtain ⟨a, ha, hle⟩ := SmoothingKernelFamily.exists_pos_le_of_isCompact hK hsub
    obtain ⟨C, hC⟩ := flowKernel_iteratedFDeriv_bound (d := d) hl ha k
    exact ⟨C, fun h hh y => hC h (hle h hh) y⟩
  weight_le := fun k {K} hK hsub => by
    obtain ⟨a, ha, hle⟩ := SmoothingKernelFamily.exists_pos_le_of_isCompact hK hsub
    obtain ⟨b, hb⟩ := hK.bddAbove
    obtain ⟨ε, M, hε, hM, hdom⟩ := flow_weighted_le_gaussian (d := d) hl ha (le_max_right b a) k
    refine ⟨M, fun h hh y => ?_⟩
    exact (hdom h (hle h hh) ((hb hh).trans (le_max_left _ _)) y).trans
      (mul_le_of_le_one_right hM (gaussExp_half_le_one hε y))
  weight_integrable := fun k {h} hh => integrable_pow_mul_flowKernel hl hh k
  joint := flowKernel_jointContinuousOn hl
  weight_dom := fun k {K} hK hsub => by
    obtain ⟨a, ha, hle⟩ := SmoothingKernelFamily.exists_pos_le_of_isCompact hK hsub
    obtain ⟨b, hb⟩ := hK.bddAbove
    obtain ⟨ε, M, hε, hM, hdom⟩ := flow_weighted_le_gaussian (d := d) hl ha (le_max_right b a) k
    refine ⟨fun z => M * gaussExp (ε / 2) 0 (ε / 2) z, M, ?_, ?_, fun z => ⟨?_, ?_⟩,
      fun h hh z => hdom h (hle h hh) ((hb hh).trans (le_max_left _ _)) z⟩
    · unfold gaussExp quadForm; fun_prop
    · exact (integrable_gaussExp (by positivity)
        (by unfold pairRes; norm_num; positivity)).const_mul M
    · exact mul_nonneg hM (Real.exp_pos _).le
    · exact mul_le_of_le_one_right hM (gaussExp_half_le_one hε z)
  weight_integral_le := fun k {K} hK hsub => by
    obtain ⟨a, ha, hle⟩ := SmoothingKernelFamily.exists_pos_le_of_isCompact hK hsub
    obtain ⟨b, hb⟩ := hK.bddAbove
    obtain ⟨ε, M, hε, hM, hdom⟩ := flow_weighted_le_gaussian (d := d) hl ha (le_max_right b a) k
    have hint : Integrable (gaussExp (ε / 2) 0 (ε / 2) : EvolutionAmbientState d → ℝ) :=
      integrable_gaussExp (by positivity) (by unfold pairRes; norm_num; positivity)
    refine ⟨M * ∫ y : EvolutionAmbientState d, gaussExp (ε / 2) 0 (ε / 2) y, fun h hh => ?_⟩
    have hh0 : 0 < h := hsub hh
    rw [← integral_const_mul]
    exact integral_mono (integrable_pow_mul_flowKernel hl hh0 k) (hint.const_mul M)
      fun y => hdom h (hle h hh) ((hb hh).trans (le_max_left _ _)) y

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
