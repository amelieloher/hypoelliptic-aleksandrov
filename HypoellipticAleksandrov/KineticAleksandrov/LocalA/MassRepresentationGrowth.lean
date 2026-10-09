module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportOrder
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

/-! # The actual growth barrier controls compact trace approximation errors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic SectionTwo TheoremA Evolution

/-- The native growth barrier, expressed in the physical coordinate order. -/
def massGrowthBarrier {d : ℕ} (Lam T : ℝ) (P : KineticPoint d) : ℝ :=
  growthBarrier (growthConstant d Lam (PDE.vecEuclideanNorm (identityDrift d 0)) 1) T
    (sectionTwoPoint P)

/-- Its physical product-coordinate representative is globally smooth. -/
theorem massGrowthBarrier_smooth {d : ℕ} (Lam T : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (massGrowthBarrier (d := d) Lam T ∘
      (KineticPoint.equivProd d).symm) := by
  unfold massGrowthBarrier growthBarrier radialSq sectionTwoPoint PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The growth barrier is strictly positive on every physical point. -/
theorem massGrowthBarrier_pos {d : ℕ} (Lam T : ℝ) (P : KineticPoint d) :
    0 < massGrowthBarrier Lam T P := growthBarrier_pos _ _ _

/-- The barrier dominates one and the physical position squared norm in the past. -/
theorem massGrowthBarrier_lower {d : ℕ} (Lam T : ℝ) (P : KineticPoint d)
    (hP : P.time ≤ T) : 1 + PDE.vecNormSq P.position ≤ massGrowthBarrier Lam T P := by
  have hC : 0 ≤ growthConstant d Lam (PDE.vecEuclideanNorm (identityDrift d 0)) 1 := by
    have hb0 := PDE.vecEuclideanNorm_nonneg (identityDrift d 0)
    unfold growthConstant
    positivity
  have h := one_add_radialSq_le_growthBarrier hC (p := sectionTwoPoint P) hP
  have hv := PDE.vecNormSq_nonneg P.velocity
  dsimp only [radialSq, sectionTwoPoint] at h
  change 1 + PDE.vecNormSq P.position ≤
    growthBarrier (growthConstant d Lam (PDE.vecEuclideanNorm (identityDrift d 0)) 1) T
      (sectionTwoPoint P)
  dsimp only [sectionTwoPoint]
  linarith only [h, hv]

/-- Smooth physical scalar factors commute with the actual operator. -/
theorem mass_forward_const_mul {d : ℕ} (B : CoefficientField d)
    {D : Set (KineticPoint d)} (hD : IsOpen D) (u : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D)) (c : ℝ) (P : KineticPoint d) (hP : P ∈ D) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => c * u Q) P =
      c * forwardKineticOperator (ofTimeVelocityCoefficient B) u P := by
  have hr := boundary_swapped_slice_regular hD hu (sectionTwoPoint P) hP
  rw [forwardKineticOperator_eq_lop_identity B (fun Q => c * u Q),
    forwardKineticOperator_eq_lop_identity B u]
  simpa only [viscousTransportedOperator_zero, lop] using!
    (viscousTransportedOperator_const_mul (B := zIndependentCoefficient B)
      (b := identityDrift d) (ε := 0) c hr)

/-- The actual smooth growth barrier is a physical supersolution. -/
theorem massGrowthBarrier_operator_nonpos {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (T : ℝ) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) (massGrowthBarrier Lam T) P ≤ 0 := by
  have h := viscousTransportedOperator_growthBarrier_le (ε := 0) zero_le_one
    (fun t y z => ((sectionTwoCoefficient_fullBounds lam Lam B hB).2.2 t y z).2)
    (identityDrift_bounds d).1 T (sectionTwoPoint P)
  rw [viscousTransportedOperator_zero] at h
  rw [forwardKineticOperator_eq_lop_identity]
  exact h.trans (neg_nonpos.mpr (growthBarrier_pos _ _ _).le)

/-- Weighted trace error propagates to the full closed strip, including its initial face. -/
theorem mass_weighted_trace_bound {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (a T : ℝ) (haT : a < T) (v₀ : PDE.Vec d) (R : ℝ)
    (u : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R))
    (he : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) u P = 0)
    (hc : ContinuousOn u (localClosedStrip a T v₀ R))
    (hb : ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htr : ∀ P ∈ localTrace a T v₀ R, u P ≤ ε * massGrowthBarrier Lam T P) :
    ∀ P ∈ localClosedStrip a T v₀ R, u P ≤ ε * massGrowthBarrier Lam T P := by
  let G := massGrowthBarrier (d := d) Lam T
  have hGs := massGrowthBarrier_smooth (d := d) Lam T
  have hmul : ContDiff ℝ (⊤ : ℕ∞)
      ((fun P => ε * G P) ∘ (KineticPoint.equivProd d).symm) := contDiff_const.mul hGs
  obtain ⟨M, hM⟩ := hb
  have hm := mass_boundedAbove_subsolution_comparison B hB a T haT v₀ R
    (fun P => u P - ε * G P) (hu.sub hmul.contDiffOn) (fun P hP => by
      rw [cone_forward_sub B (isOpen_localStrip a T v₀ R) u (fun Q => ε * G Q)
        hu hmul.contDiffOn P hP, he P hP,
        mass_forward_const_mul B (isOpen_localStrip a T v₀ R) G hGs.contDiffOn ε P hP]
      exact sub_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hε
        (massGrowthBarrier_operator_nonpos B hB T P)))
    (hc.sub (continuousOn_const.mul (boundary_probe_continuous G hGs).continuousOn))
    ⟨M, fun P hP => (sub_le_self _ (mul_nonneg hε (massGrowthBarrier_pos Lam T P).le)).trans
      (le_of_abs_le (hM P hP))⟩ 0 (fun P hP => sub_nonpos.mpr (htr P hP))
  intro P hP
  exact sub_nonpos.mp (hm P hP)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
