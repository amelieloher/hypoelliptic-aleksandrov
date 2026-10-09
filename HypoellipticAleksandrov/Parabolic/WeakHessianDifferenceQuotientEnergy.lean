module

public import HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
public import HypoellipticAleksandrov.Parabolic.WeakPrincipalCoercivity
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Weak Hessian difference-quotient energy foundations

This module records the integrability foundations for the fixed-cylinder weak
Hessian energy argument.  In particular, it keeps the ordered convention
`QH z j i` and the literal residual orientation
`QW + principal + drift + scalar = R`.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped ENNReal BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

private theorem memLp_mul_of_ae_bound
    {d : ℕ} {S : Set (TimeVelocity d)} {a f : TimeVelocity d → ℝ} {K : ℝ}
    (ha : AEStronglyMeasurable a (timeVelocityVolumeOn S))
    (hK : ∀ᵐ z ∂timeVelocityVolumeOn S, |a z| ≤ K)
    (hf : ParabolicMemLpOn S (2 : ℝ≥0∞) f) :
    ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z ↦ a z * f z) := by
  refine MemLp.of_le_mul (c := K) hf (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hK] with z hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)

private theorem lowerOrderSource_memLp
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (B : TimeVelocity d → PDE.Vec d) (C0 q R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (M : ℝ)
    (hBmeas : AEStronglyMeasurable B
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hCmeas : AEStronglyMeasurable C0
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hB : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d, |B z j| ≤ M)
    (hC : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, |C0 z| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z ↦ QG z j))
    (hR : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R) :
    ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z ↦ ∑ j : Fin d, B z j * QG z j) ∧
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
        (fun z ↦ C0 z * q z) ∧
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z ↦
        R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) := by
  have hBcomp (j : Fin d) : AEStronglyMeasurable (fun z ↦ B z j)
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) :=
    (continuous_apply j).comp_aestronglyMeasurable hBmeas
  have hSmeas : MeasurableSet (Set.Ioo s₀ s₁ ×ˢ O) :=
    measurableSet_Ioo.prod hO.measurableSet
  have hBbound (j : Fin d) : ∀ᵐ z ∂timeVelocityVolumeOn
      (Set.Ioo s₀ s₁ ×ˢ O), |B z j| ≤ M := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    exact hB z hz j
  have hBG (j : Fin d) : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z ↦ B z j * QG z j) :=
    memLp_mul_of_ae_bound (hBcomp j) (hBbound j) (hQG j)
  have hsum : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z ↦ ∑ j : Fin d, B z j * QG z j) :=
    memLp_finset_sum Finset.univ fun j _ ↦ hBG j
  have hCbound : ∀ᵐ z ∂timeVelocityVolumeOn
      (Set.Ioo s₀ s₁ ×ˢ O), |C0 z| ≤ M := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    exact hC z hz
  have hscalar := memLp_mul_of_ae_bound hCmeas hCbound hq
  exact ⟨hsum, hscalar, (hR.sub hsum).sub hscalar⟩

/-- The raw residual equation has the orientation needed by the time-energy
and principal-coercivity pairings.  This lemma is deliberately pointwise and
retains the ordered entry `QH z j i`. -/
private theorem residualEquation_reoriented
    {d : ℕ} {S : Set (TimeVelocity d)}
    (A : TimeVelocity d → PDE.Mat d)
    (B QG : TimeVelocity d → PDE.Vec d)
    (C0 q QW R : TimeVelocity d → ℝ)
    (QH : TimeVelocity d → PDE.Mat d)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) +
          (∑ j : Fin d, B z j * QG z j) + C0 z * q z = R z) :
    ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) =
        R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z := by
  filter_upwards [heq] with z hz
  linarith

/-- A separated smooth compactly supported multiplier is bounded on every
restricted spacetime carrier. -/
private theorem separated_multiplier_memLp_top_restrict
    {d : ℕ} (S : Set (TimeVelocity d))
    (a : ℝ → ℝ) (ha : Continuous a) (haCompact : HasCompactSupport a)
    (c : PDE.Vec d → ℝ) (hc : Continuous c) (hcCompact : HasCompactSupport c) :
    MemLp (fun z : TimeVelocity d => a z.1 * c z.2) ∞
      (timeVelocityVolumeOn S) := by
  have hcont : Continuous (fun z : TimeVelocity d => a z.1 * c z.2) :=
    (ha.comp continuous_fst).mul (hc.comp continuous_snd)
  have hcompact : HasCompactSupport (fun z : TimeVelocity d => a z.1 * c z.2) := by
    have hprod : IsCompact (tsupport a ×ˢ tsupport c) :=
      haCompact.isCompact.prod hcCompact.isCompact
    apply HasCompactSupport.of_support_subset_isCompact hprod
    intro z hz
    have ha0 : a z.1 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    have hc0 : c z.2 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact ⟨subset_tsupport a (Function.mem_support.mpr ha0),
      subset_tsupport c (Function.mem_support.mpr hc0)⟩
  exact (hcont.memLp_of_hasCompactSupport hcompact).restrict S

/-- The localized gradient divergence, including its time cutoff, belongs to
restricted `L²` under precisely the coordinatewise gradient and diagonal
Hessian hypotheses used by the time-energy identity. -/
private theorem localizedGradientDivergence_memLp
    {d : ℕ} (S : Set (TimeVelocity d))
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hQG : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QG z k))
    (hQHdiag : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QH z k k))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    ParabolicMemLpOn S 2 (fun z => ζ z.1 *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z) := by
  have hpartialCont (k : Fin d) : Continuous (spatialPartial k η) := by
    unfold spatialPartial
    simpa using (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpartialCompact (k : Fin d) : HasCompactSupport (spatialPartial k η) := by
    unfold spatialPartial
    simpa using hηCompact.fderiv_apply (𝕜 := ℝ) (PDE.basisVec k)
  have hηsqCompact : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηCompact.mul_right (f' := η)
  have hc₁ (k : Fin d) : MemLp (fun z : TimeVelocity d =>
      (-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) ∞
      (timeVelocityVolumeOn S) := by
    have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact (fun y => η y * spatialPartial k η y)
      (hη.continuous.mul (hpartialCont k)) hηCompact.mul_right
    convert hbase.const_smul (-2 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hc₂ : MemLp (fun z : TimeVelocity d =>
      (-1 : ℝ) * ζ z.1 * η z.2 ^ 2) ∞ (timeVelocityVolumeOn S) := by
    have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact (fun y => η y ^ 2) (hη.continuous.pow 2) hηsqCompact
    convert hbase.const_smul (-1 : ℝ) using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hs (k : Fin d) : ParabolicMemLpOn S 2 (fun z =>
      ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) * QG z k +
      ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QH z k k) :=
    by
      simpa only [Pi.add_def] using
        ((hc₁ k).mul' (hQG k)).add (hc₂.mul' (hQHdiag k))
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).mp
    (memLp_finset_sum Finset.univ fun k _ => hs k)
  simp only [WeakGradientTimeEnergy.localizedGradientDivergence]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The lower-order residual is integrable against the localized gradient
divergence by restricted `L² × L²` duality. -/
private theorem lowerOrderSource_localizedGradientDivergence_integrable
    {d : ℕ} {S : Set (TimeVelocity d)}
    (F : TimeVelocity d → ℝ)
    (hF : ParabolicMemLpOn S 2 F)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hQG : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QG z k))
    (hQHdiag : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QH z k k))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 * F z *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z) S volume := by
  have hD := localizedGradientDivergence_memLp S QG QH hQG hQHdiag
    η hη hηCompact ζ hζ hζCompact
  have hprod := hF.integrable_mul hD
  apply hprod.congr
  exact Filter.Eventually.of_forall fun z => by
    simp only [Pi.mul_apply]
    ring

/-- Pairing the reoriented residual equation with the localized divergence
gives the exact integrated decomposition.  The two summands are supplied
separately so that `integral_add` never relies on implicit integrability. -/
private theorem integrated_residual_pairing
    {d : ℕ} {S : Set (TimeVelocity d)}
    (A : TimeVelocity d → PDE.Mat d)
    (QW F : TimeVelocity d → ℝ)
    (QH : TimeVelocity d → PDE.Mat d)
    (D : TimeVelocity d → ℝ)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) = F z)
    (hIw : IntegrableOn (fun z => QW z * D z) S volume)
    (hIp : IntegrableOn (fun z =>
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) * D z) S volume)
    :
    (∫ z in S, QW z * D z ∂volume) +
        (∫ z in S, (∑ i : Fin d, ∑ j : Fin d,
          A z i j * QH z j i) * D z ∂volume) =
      ∫ z in S, F z * D z ∂volume := by
  rw [← integral_add hIw hIp]
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  rw [← add_mul, hz]

/-- The scalar sign calculation at the heart of the pre-Young estimate.  It
keeps the time identity, residual splitting, and principal lower bound as
separate named inputs, matching the three analytic lemmas that produce them. -/
private theorem preYoung_of_time_residual_principal
    (lam Cpr E G If It Iw Ip : ℝ)
    (htime : 2 * Iw = -It)
    (hresidual : Iw + Ip = If)
    (hprincipal : -Ip ≥ lam / 2 * E - Cpr * G) :
    lam / 2 * E ≤ Cpr * G + |If| + |It| / 2 := by
  have hIw : Iw = -It / 2 := by linarith
  have hIp : -Ip = Iw - If := by linarith
  have hraw : lam / 2 * E ≤ Cpr * G + Iw - If := by linarith
  have hIf : -If ≤ |If| := neg_le_abs If
  have hIt : -It / 2 ≤ |It| / 2 := by
    have h := neg_le_abs It
    linarith
  rw [hIw] at hraw
  linarith

/-- The square integral of an arbitrary-measure `L²` function is its squared
real `eLpNorm`.  No finiteness assumption on the ambient measure is needed. -/
private theorem integral_sq_eq_toReal_eLpNorm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f (2 : ℝ≥0∞) μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ => sq_nonneg _) _), ENNReal.toReal_ofNat,
    Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

/-- Scalar Young inequality with the coefficient used to absorb one diagonal
Hessian entry.  Its proof uses only positivity of `lam`, not a dimension
factor. -/
private theorem abs_mul_le_quarter_young (lam x y : ℝ) (hlam : 0 < lam) :
    |x| * |y| ≤ lam / 4 * y ^ 2 + 1 / lam * x ^ 2 := by
  have hs := sq_nonneg (2 * |x| - lam * |y|)
  have hmul : (|x| * |y| - lam / 4 * y ^ 2) * lam ≤ x ^ 2 := by
    rw [← sq_abs x, ← sq_abs y]
    nlinarith
  have hdiv := (le_div_iff₀ hlam).2 hmul
  rw [sub_le_iff_le_add] at hdiv
  simpa only [div_eq_mul_inv, one_mul, mul_one, add_comm, mul_comm] using hdiv

/-- The pointwise coordinate estimate for the two terms in the localized
gradient divergence.  The cutoff weights are retained on the absorbed
Hessian square and discarded only from the lower-order squares. -/
private theorem localizedGradientDivergence_coordinate_young
    (lam Keta ζ η F G H Dη : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hζnonneg : 0 ≤ ζ) (hζle : ζ ≤ 1)
    (hηnonneg : 0 ≤ η) (hηle : η ≤ 1) (hDη : |Dη| ≤ Keta) :
    |ζ * F * (2 * η * Dη * G + η ^ 2 * H)| ≤
      lam / 4 * (ζ * η ^ 2 * H ^ 2) + Keta * G ^ 2 +
        (Keta + 1 / lam) * F ^ 2 := by
  have hηabs : |η| ≤ 1 := by simpa [abs_of_nonneg hηnonneg] using hηle
  have hζabs : |ζ| ≤ 1 := by simpa [abs_of_nonneg hζnonneg] using hζle
  have hgradYoung : 2 * |F| * |G| ≤ F ^ 2 + G ^ 2 := by
    rw [← sq_abs F, ← sq_abs G]
    nlinarith [sq_nonneg (|F| - |G|)]
  have hgrad : |ζ * F * (2 * η * Dη * G)| ≤
      Keta * (F ^ 2 + G ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      |ζ| * |F| * (2 * |η| * |Dη| * |G|) ≤
          1 * |F| * (2 * 1 * Keta * |G|) := by gcongr
      _ = Keta * (2 * |F| * |G|) := by ring
      _ ≤ Keta * (F ^ 2 + G ^ 2) :=
        mul_le_mul_of_nonneg_left hgradYoung hKeta
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hweight : 0 ≤ ζ * η ^ 2 := mul_nonneg hζnonneg hηsq
  have hweight_le : ζ * η ^ 2 ≤ 1 := by nlinarith [sq_nonneg (η - 1)]
  have hhessYoung := abs_mul_le_quarter_young lam F H hlam
  have hhess : |ζ * F * (η ^ 2 * H)| ≤
      lam / 4 * (ζ * η ^ 2 * H ^ 2) + 1 / lam * F ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hζnonneg,
      abs_of_nonneg hηsq]
    calc
      ζ * |F| * (η ^ 2 * |H|) = (ζ * η ^ 2) * (|F| * |H|) := by ring
      _ ≤ (ζ * η ^ 2) * (lam / 4 * H ^ 2 + 1 / lam * F ^ 2) :=
        mul_le_mul_of_nonneg_left hhessYoung hweight
      _ ≤ lam / 4 * (ζ * η ^ 2 * H ^ 2) + 1 / lam * F ^ 2 := by
        rw [mul_add]
        have hdrop : (ζ * η ^ 2) * (1 / lam * F ^ 2) ≤ 1 / lam * F ^ 2 :=
          mul_le_of_le_one_left (mul_nonneg (by positivity) (sq_nonneg F)) hweight_le
        convert add_le_add_left hdrop (lam / 4 * (ζ * η ^ 2 * H ^ 2)) using 1 <;>
          ring
  calc
    |ζ * F * (2 * η * Dη * G + η ^ 2 * H)| ≤
        |ζ * F * (2 * η * Dη * G)| + |ζ * F * (η ^ 2 * H)| := by
      rw [mul_add]
      exact abs_add_le _ _
    _ ≤ Keta * (F ^ 2 + G ^ 2) +
        (lam / 4 * (ζ * η ^ 2 * H ^ 2) + 1 / lam * F ^ 2) :=
      add_le_add hgrad hhess
    _ = lam / 4 * (ζ * η ^ 2 * H ^ 2) + Keta * G ^ 2 +
        (Keta + 1 / lam) * F ^ 2 := by ring

/-- The lower-order pairing with an arbitrary restricted `L²` source.  The
diagonal Hessian expenditure is dominated by the full ordered Hessian energy;
no division by the dimension occurs, so the statement includes `d = 0`. -/
private theorem lowerOrder_localizedGradientDivergence_abs_le
    {d : ℕ} (lam Keta s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (F : TimeVelocity d → ℝ) (hF : ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 F)
    (QG : TimeVelocity d → PDE.Vec d)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j))
    (QH : TimeVelocity d → PDE.Mat d)
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QH z j i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ Keta)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζnonneg : ∀ r, 0 ≤ ζ r) (hζle : ∀ r, ζ r ≤ 1)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta) :
    |∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * F z *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume| ≤
      lam / 4 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 ∂volume) +
      Keta * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 +
      (d : ℝ) * (Keta + 1 / lam) *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, F z ^ 2 ∂volume) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let μ := timeVelocityVolumeOn S
  have hpair := lowerOrderSource_localizedGradientDivergence_integrable F hF
    QG QH hQG (fun i => hQH i i) η hη hηcompact ζ hζ hζcompact
  have hmem : ∀ᵐ z ∂μ, z ∈ S :=
    ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)
  have hQGsq : Integrable (fun z => ∑ j : Fin d, QG z j ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq
  have hQHsq : Integrable (fun z => ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun i _ => (hQH j i).integrable_sq
  have hweightMeas : AEStronglyMeasurable (fun z : TimeVelocity d =>
      ζ z.1 * η z.2 ^ 2) μ :=
    (hζ.continuous.comp continuous_fst).aestronglyMeasurable.mul
      ((hη.continuous.comp continuous_snd).aestronglyMeasurable.pow 2)
  have hweightedH : Integrable (fun z => ζ z.1 * η z.2 ^ 2 *
      ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) μ := by
    apply hQHsq.mono' (hweightMeas.mul hQHsq.aestronglyMeasurable)
    filter_upwards with z
    have hw0 : 0 ≤ ζ z.1 * η z.2 ^ 2 :=
      mul_nonneg (hζnonneg _) (sq_nonneg _)
    have hw1 : ζ z.1 * η z.2 ^ 2 ≤ 1 := by
      have := hηle z.2
      nlinarith [hηnonneg z.2, hζnonneg z.1, hζle z.1,
        sq_nonneg (η z.2 - 1)]
    change |ζ z.1 * η z.2 ^ 2 *
      (∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2)| ≤ _
    have hsum : 0 ≤ ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [abs_of_nonneg (mul_nonneg hw0 hsum)]
    exact mul_le_of_le_one_left
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _) hw1
  let Rhs : TimeVelocity d → ℝ := fun z =>
    lam / 4 * (ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) +
      Keta * ∑ j : Fin d, QG z j ^ 2 +
      (d : ℝ) * (Keta + 1 / lam) * F z ^ 2
  have hRhs : Integrable Rhs μ :=
    ((hweightedH.const_mul (lam / 4)).add (hQGsq.const_mul Keta)).add
      (hF.integrable_sq.const_mul ((d : ℝ) * (Keta + 1 / lam)))
  have hpoint : ∀ᵐ z ∂μ,
      |ζ z.1 * F z * WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z| ≤
        Rhs z := by
    filter_upwards [hmem] with z hz
    simp only [WeakGradientTimeEnergy.localizedGradientDivergence]
    have hneg : ζ z.1 * F z * -(∑ i : Fin d,
        (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)) =
        -(ζ z.1 * F z * ∑ i : Fin d,
          (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)) := by ring
    rw [hneg, abs_neg]
    calc
      |ζ z.1 * F z * ∑ i : Fin d,
          (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)| ≤
          ∑ i : Fin d, |ζ z.1 * F z *
            (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)| := by
        rw [Finset.mul_sum]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (lam / 4 * (ζ z.1 * η z.2 ^ 2 * QH z i i ^ 2) +
          Keta * QG z i ^ 2 + (Keta + 1 / lam) * F z ^ 2) :=
        Finset.sum_le_sum fun i _ => localizedGradientDivergence_coordinate_young
          lam Keta (ζ z.1) (η z.2) (F z) (QG z i) (QH z i i)
          (spatialPartial i η z.2) hlam hKeta (hζnonneg _) (hζle _)
          (hηnonneg _) (hηle _) (hηderiv z.2 hz.2 i)
      _ ≤ Rhs z := by
        dsimp [Rhs]
        have hdiag : (∑ i : Fin d, QH z i i ^ 2) ≤
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 := by
          exact Finset.sum_le_sum fun j _ => Finset.single_le_sum
            (fun i _ => sq_nonneg (QH z j i)) (Finset.mem_univ j)
        have hcoeff : 0 ≤ lam / 4 * (ζ z.1 * η z.2 ^ 2) :=
          mul_nonneg (by positivity) (mul_nonneg (hζnonneg _) (sq_nonneg _))
        have hdiagWeighted := mul_le_mul_of_nonneg_left hdiag hcoeff
        have hsumEq :
            (∑ i : Fin d, (lam / 4 * (ζ z.1 * η z.2 ^ 2 * QH z i i ^ 2) +
              Keta * QG z i ^ 2 + (Keta + 1 / lam) * F z ^ 2)) =
              (lam / 4 * (ζ z.1 * η z.2 ^ 2)) * (∑ i : Fin d, QH z i i ^ 2) +
                Keta * ∑ i : Fin d, QG z i ^ 2 +
                (d : ℝ) * (Keta + 1 / lam) * F z ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [Finset.mul_sum, nsmul_eq_mul]
          ring_nf
        rw [hsumEq]
        simpa only [mul_assoc] using
          add_le_add (add_le_add hdiagWeighted (le_refl _)) (le_refl _)
  have habsPair : Integrable (fun z => |ζ z.1 * F z *
      WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z|) μ :=
    hpair.norm
  calc
    |∫ z in S, ζ z.1 * F z *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume| ≤
        ∫ z, |ζ z.1 * F z *
          WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, Rhs z ∂μ := integral_mono_ae habsPair hRhs hpoint
    _ = lam / 4 * (∫ z in S, ζ z.1 * η z.2 ^ 2 *
          ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 ∂volume) +
        Keta * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2 μ).toReal ^ 2 +
        (d : ℝ) * (Keta + 1 / lam) * (∫ z in S, F z ^ 2 ∂volume) := by
      dsimp [Rhs]
      have hinner := integral_add (hweightedH.const_mul (lam / 4))
        (hQGsq.const_mul Keta)
      have houter := integral_add ((hweightedH.const_mul (lam / 4)).add
        (hQGsq.const_mul Keta))
        (hF.integrable_sq.const_mul ((d : ℝ) * (Keta + 1 / lam)))
      rw [show (∫ z, lam / 4 * (ζ z.1 * η z.2 ^ 2 *
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) +
          Keta * ∑ j : Fin d, QG z j ^ 2 +
          (d : ℝ) * (Keta + 1 / lam) * F z ^ 2 ∂μ) =
          (∫ z, lam / 4 * (ζ z.1 * η z.2 ^ 2 *
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) +
            Keta * ∑ j : Fin d, QG z j ^ 2 ∂μ) +
          ∫ z, (d : ℝ) * (Keta + 1 / lam) * F z ^ 2 ∂μ by
            simpa only [Pi.add_apply] using houter]
      rw [show (∫ z, lam / 4 * (ζ z.1 * η z.2 ^ 2 *
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) +
          Keta * ∑ j : Fin d, QG z j ^ 2 ∂μ) =
          (∫ z, lam / 4 * (ζ z.1 * η z.2 ^ 2 *
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) ∂μ) +
          ∫ z, Keta * ∑ j : Fin d, QG z j ^ 2 ∂μ by
            simpa only [Pi.add_apply] using hinner]
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq]
      simp_rw [integral_sq_eq_toReal_eLpNorm_sq _ (hQG _)]
      dsimp [μ, S]
    _ = _ := by simp only [μ, S]

/-- The elementary three-term square estimate, in the subtraction orientation
used by the lower-order source. -/
private theorem sub_sub_sq_le_three (x y z : ℝ) :
    (x - y - z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y - z)]

/-- Finite Cauchy--Schwarz in the scalar form needed for the drift sum. -/
private theorem fin_sum_sq_le_card_mul_sum_sq
    {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (∑ i, u i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, u i ^ 2 := by
  simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := u))

/-- The squared lower-order source is controlled by the prescribed restricted
`L²` bounds, without a finite-measure assumption on the cylinder. -/
private theorem lowerOrderSource_integral_sq_le
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (B : TimeVelocity d → PDE.Vec d) (C0 q R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (M N_R N_q : ℝ)
    (N_QG : Fin d → ℝ)
    (hBmeas : AEStronglyMeasurable B
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hCmeas : AEStronglyMeasurable C0
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hM : 0 ≤ M)
    (hB : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d, |B z j| ≤ M)
    (hC : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, |C0 z| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z ↦ QG z j))
    (hR : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R)
    (hRnorm : (eLpNorm R 2
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ≤ N_R)
    (hqnorm : (eLpNorm q 2
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ≤ N_q)
    (hQGnorm : ∀ j : Fin d, (eLpNorm (fun z ↦ QG z j) 2
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ≤ N_QG j) :
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) ^ 2 ∂volume) ≤
      3 * (N_R ^ 2 + M ^ 2 * N_q ^ 2 +
        (d : ℝ) * M ^ 2 * ∑ j : Fin d, N_QG j ^ 2) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let μ := timeVelocityVolumeOn S
  have hparts := lowerOrderSource_memLp s₀ s₁ O hO B C0 q R QG M
    hBmeas hCmeas hB hC hq hQG hR
  have hdrift := hparts.1
  have hscalar := hparts.2.1
  have hsource := hparts.2.2
  have hmem : ∀ᵐ z ∂μ, z ∈ S :=
    ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)
  have hdriftPoint : ∀ᵐ z ∂μ,
      (∑ j : Fin d, B z j * QG z j) ^ 2 ≤
        (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2 := by
    filter_upwards [hmem] with z hz
    calc
      (∑ j : Fin d, B z j * QG z j) ^ 2 ≤
          (d : ℝ) * ∑ j : Fin d, (B z j * QG z j) ^ 2 :=
        by simpa using
          (fin_sum_sq_le_card_mul_sum_sq (fun j : Fin d ↦ B z j * QG z j))
      _ ≤ (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2 := by
        have hterm (j : Fin d) : (B z j * QG z j) ^ 2 ≤
            M ^ 2 * QG z j ^ 2 := by
          have hsq : |B z j| ^ 2 ≤ M ^ 2 :=
            by simpa only [pow_two] using
              (mul_self_le_mul_self (abs_nonneg _) (hB z hz j))
          rw [mul_pow, ← sq_abs (B z j)]
          exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hterm j
        have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        convert mul_le_mul_of_nonneg_left hsum hd using 1
        all_goals simp only [Finset.mul_sum]
        all_goals ring_nf
  have hscalarPoint : ∀ᵐ z ∂μ,
      (C0 z * q z) ^ 2 ≤ M ^ 2 * q z ^ 2 := by
    filter_upwards [hmem] with z hz
    have hsq : |C0 z| ^ 2 ≤ M ^ 2 :=
      by simpa only [pow_two] using
        (mul_self_le_mul_self (abs_nonneg _) (hC z hz))
    rw [mul_pow, ← sq_abs (C0 z)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint : ∀ᵐ z ∂μ,
      (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) ^ 2 ≤
        3 * (R z ^ 2 + M ^ 2 * q z ^ 2 +
          (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2) := by
    filter_upwards [hdriftPoint, hscalarPoint] with z hd hs
    nlinarith [sub_sub_sq_le_three (R z) (∑ j : Fin d, B z j * QG z j)
      (C0 z * q z)]
  have hQGsq : Integrable (fun z ↦ ∑ j : Fin d, QG z j ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ ↦ (hQG j).integrable_sq
  have hright : Integrable (fun z ↦
      3 * (R z ^ 2 + M ^ 2 * q z ^ 2 +
        (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2)) μ :=
    (((hR.integrable_sq.add (hq.integrable_sq.const_mul (M ^ 2))).add
      (hQGsq.const_mul ((d : ℝ) * M ^ 2))).const_mul 3)
  calc
    (∫ z in S,
      (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) ^ 2 ∂volume) ≤
        ∫ z, 3 * (R z ^ 2 + M ^ 2 * q z ^ 2 +
          (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2) ∂μ :=
      integral_mono_ae hsource.integrable_sq hright hpoint
    _ = 3 * ((eLpNorm R 2 μ).toReal ^ 2 +
        M ^ 2 * (eLpNorm q 2 μ).toReal ^ 2 +
        (d : ℝ) * M ^ 2 * ∑ j : Fin d,
          (eLpNorm (fun z ↦ QG z j) 2 μ).toReal ^ 2) := by
      rw [integral_const_mul]
      congr 1
      dsimp [μ, S]
      change (∫ z, (((fun z ↦ R z ^ 2) + (fun z ↦ M ^ 2 * q z ^ 2)) +
        (fun z ↦ (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2)) z
          ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) = _
      calc
        (∫ z, R z ^ 2 + M ^ 2 * q z ^ 2 +
            (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2 ∂μ) =
            (∫ z, R z ^ 2 ∂μ) + (∫ z, M ^ 2 * q z ^ 2 ∂μ) +
              ∫ z, (d : ℝ) * M ^ 2 * ∑ j : Fin d, QG z j ^ 2 ∂μ := by
          have hinner := integral_add hR.integrable_sq
            (hq.integrable_sq.const_mul (M ^ 2))
          have houter := integral_add
            (hR.integrable_sq.add (hq.integrable_sq.const_mul (M ^ 2)))
            (hQGsq.const_mul ((d : ℝ) * M ^ 2))
          simpa only [Pi.add_apply, μ, S] using houter.trans
            (congrArg (fun x ↦ x + ∫ z, (d : ℝ) * M ^ 2 *
              ∑ j : Fin d, QG z j ^ 2 ∂μ) hinner)
        _ = (eLpNorm R 2 μ).toReal ^ 2 +
            M ^ 2 * (eLpNorm q 2 μ).toReal ^ 2 +
            (d : ℝ) * M ^ 2 * ∑ j : Fin d,
              (eLpNorm (fun z ↦ QG z j) 2 μ).toReal ^ 2 := by
          rw [integral_const_mul, integral_const_mul,
            integral_finset_sum Finset.univ fun j _ ↦ (hQG j).integrable_sq,
            integral_sq_eq_toReal_eLpNorm_sq R hR,
            integral_sq_eq_toReal_eLpNorm_sq q hq]
          simp_rw [integral_sq_eq_toReal_eLpNorm_sq _ (hQG _)]
          rfl
    _ ≤ 3 * (N_R ^ 2 + M ^ 2 * N_q ^ 2 +
        (d : ℝ) * M ^ 2 * ∑ j : Fin d, N_QG j ^ 2) := by
      have hNR : 0 ≤ N_R := le_trans ENNReal.toReal_nonneg hRnorm
      have hNq : 0 ≤ N_q := le_trans ENNReal.toReal_nonneg hqnorm
      have hNQG (j : Fin d) : 0 ≤ N_QG j :=
        le_trans ENNReal.toReal_nonneg (hQGnorm j)
      have hRsq : (eLpNorm R 2 μ).toReal ^ 2 ≤ N_R ^ 2 :=
        by simpa only [pow_two, μ, S] using
          (mul_self_le_mul_self ENNReal.toReal_nonneg hRnorm)
      have hqsq : (eLpNorm q 2 μ).toReal ^ 2 ≤ N_q ^ 2 :=
        by simpa only [pow_two, μ, S] using
          (mul_self_le_mul_self ENNReal.toReal_nonneg hqnorm)
      have hQGsqNorm : (∑ j : Fin d,
          (eLpNorm (fun z ↦ QG z j) 2 μ).toReal ^ 2) ≤
          ∑ j : Fin d, N_QG j ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ by
          simpa only [pow_two, μ, S] using
            (mul_self_le_mul_self ENNReal.toReal_nonneg (hQGnorm j))
      have hdM : 0 ≤ (d : ℝ) * M ^ 2 :=
        mul_nonneg (Nat.cast_nonneg d) (by
          simpa only [pow_two] using mul_nonneg hM hM)
      have hqmul := mul_le_mul_of_nonneg_left hqsq (sq_nonneg M)
      have hQGmul := mul_le_mul_of_nonneg_left hQGsqNorm hdM
      nlinarith

/-- The literal support-indicator gradient term is bounded by the sum of the
coordinatewise restricted `L²` energies. -/
private theorem principalSupportIndicatorGradientIntegral_le_eLpNorm_sq_sum
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d))
    (QG : TimeVelocity d → PDE.Vec d) (η : PDE.Vec d → ℝ)
    (ζ : ℝ → ℝ) (hζcont : Continuous ζ)
    (hζnonneg : ∀ r, 0 ≤ ζ r) (hζle : ∀ r, ζ r ≤ 1)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j)) :
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
        (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2 ∂volume) ≤
      ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 := by
  let μ := timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)
  have hsum : Integrable (fun z => ∑ j : Fin d, QG z j ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq
  have hleftMeas : AEStronglyMeasurable (fun z => ζ z.1 *
      (tsupport η).indicator (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2) μ := by
    classical
    have hsumMeas := hsum.aestronglyMeasurable
    have hindicatorMeas : AEStronglyMeasurable (fun z =>
        (tsupport η).indicator (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2) μ := by
      apply (hsumMeas.indicator
        (isClosed_closure.preimage continuous_snd).measurableSet).congr
      filter_upwards with z
      rw [Set.indicator_apply, Set.indicator_apply]
      rfl
    exact (hζcont.comp continuous_fst).aestronglyMeasurable.mul hindicatorMeas
  have hleft : Integrable (fun z => ζ z.1 *
      (tsupport η).indicator (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2) μ := by
    classical
    apply hsum.mono' hleftMeas
    filter_upwards with z
    simp only [Real.norm_eq_abs]
    rw [Set.indicator_apply]
    split_ifs with hz
    · rw [abs_of_nonneg]
      · exact mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => sq_nonneg _)
          (hζle _)
      · exact mul_nonneg (hζnonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    · simp only [mul_zero, abs_zero]
      exact Finset.sum_nonneg fun j _ => sq_nonneg _
  calc
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
        (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2 ∂volume) ≤
        ∫ z, ∑ j : Fin d, QG z j ^ 2 ∂μ := by
      apply integral_mono_ae hleft hsum
      classical
      filter_upwards with z
      rw [Set.indicator_apply]
      split_ifs with hz
      · exact mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => sq_nonneg _)
          (hζle _)
      · simp only [mul_zero]
        exact Finset.sum_nonneg fun j _ => sq_nonneg _
    _ = ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2 μ).toReal ^ 2 := by
      rw [integral_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq]
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_sq_eq_toReal_eLpNorm_sq _ (hQG j)

/-- A derivative bound needed only on the time interval controls the absolute
time-cutoff error, without a global derivative premise. -/
private theorem timeCutoffGradientIntegral_abs_div_two_le
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : MeasurableSet O)
    (QG : TimeVelocity d → PDE.Vec d) (η : PDE.Vec d → ℝ)
    (ζ : ℝ → ℝ) (hη : Continuous η) (hζ : ContDiff ℝ 2 ζ) (Kζ : ℝ)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hζderiv : ∀ r ∈ Set.Ioo s₀ s₁, |_root_.deriv ζ r| ≤ Kζ)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j)) :
    |∫ z in Set.Ioo s₀ s₁ ×ˢ O, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ j : Fin d, QG z j ^ 2 ∂volume| / 2 ≤
      Kζ / 2 * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 := by
  let μ := timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)
  have hsum : Integrable (fun z => ∑ j : Fin d, QG z j ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq
  have hmem : ∀ᵐ z ∂μ, z ∈ Set.Ioo s₀ s₁ ×ˢ O :=
    ae_restrict_mem (measurableSet_Ioo.prod hO)
  have hpoint : ∀ᵐ z ∂μ,
      |_root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, QG z j ^ 2| ≤
        Kζ * ∑ j : Fin d, QG z j ^ 2 := by
    filter_upwards [hmem] with z hz
    have hηsq : η z.2 ^ 2 ≤ 1 := by nlinarith [hηnonneg z.2, hηle z.2]
    have hKζ : 0 ≤ Kζ := le_trans (abs_nonneg _) (hζderiv z.1 hz.1)
    have hraw :
      |_root_.deriv ζ z.1| * η z.2 ^ 2 * ∑ j : Fin d, QG z j ^ 2 ≤
          Kζ * ∑ j : Fin d, QG z j ^ 2 := by
      calc
        |_root_.deriv ζ z.1| * η z.2 ^ 2 * ∑ j : Fin d, QG z j ^ 2 ≤
            Kζ * 1 * ∑ j : Fin d, QG z j ^ 2 := by
          gcongr
          exact hζderiv z.1 hz.1
        _ = Kζ * ∑ j : Fin d, QG z j ^ 2 := by ring
    have habssum : |∑ j : Fin d, QG z j ^ 2| = ∑ j : Fin d, QG z j ^ 2 :=
      abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (η z.2)), habssum]
    exact hraw
  have habsInt : Integrable (fun z => |_root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ j : Fin d, QG z j ^ 2|) μ := by
    have hderivCont : Continuous (_root_.deriv ζ) := by
      rw [← show (fun t => (fderiv ℝ ζ t : ℝ → ℝ) 1) = _root_.deriv ζ by
        funext t
        exact fderiv_apply_one_eq_deriv]
      exact (hζ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hleftMeas : AEStronglyMeasurable (fun z =>
        |_root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, QG z j ^ 2|) μ :=
      (((hderivCont.comp continuous_fst).aestronglyMeasurable.mul
        ((hη.comp continuous_snd).aestronglyMeasurable.pow 2)).mul
          hsum.aestronglyMeasurable).norm
    exact (hsum.const_mul Kζ).mono' hleftMeas (by
      filter_upwards [hpoint] with z hz
      simpa only [Real.norm_eq_abs, abs_abs] using hz)
  have hraw : |∫ z, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ j : Fin d, QG z j ^ 2 ∂μ| ≤
      Kζ * ∫ z, ∑ j : Fin d, QG z j ^ 2 ∂μ := by
    calc
      |∫ z, _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ j : Fin d, QG z j ^ 2 ∂μ| ≤
          ∫ z, |_root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ j : Fin d, QG z j ^ 2| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, Kζ * ∑ j : Fin d, QG z j ^ 2 ∂μ :=
        integral_mono_ae habsInt (hsum.const_mul Kζ) hpoint
      _ = Kζ * ∫ z, ∑ j : Fin d, QG z j ^ 2 ∂μ := by rw [integral_const_mul]
  rw [integral_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq] at hraw
  simp_rw [integral_sq_eq_toReal_eLpNorm_sq _ (hQG _)] at hraw
  nlinarith

/-- The weak time identity and weak principal coercivity estimate combine,
through the literal residual equation, into the pre-Young Hessian estimate. -/
private theorem weakHessian_preYoung
    {d : ℕ} (lam Lam M K : ℝ) (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d)
    (B : TimeVelocity d → PDE.Vec d) (C0 q QW R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hBmeas : AEStronglyMeasurable B (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hCmeas : AEStronglyMeasurable C0 (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hB : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d, |B z j| ≤ M)
    (hC : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, |C0 z| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQW : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 QW)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (hR : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R)
    (hq_time : HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW)
    (hq_velocity : ∀ j : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j))
    (hQG_velocity : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) i (fun z => QG z j) (fun z => QH z j i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ) (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁)
    (hζnonneg : ∀ r, 0 ≤ ζ r)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) +
        (∑ j : Fin d, B z j * QG z j) + C0 z * q z = R z) :
    lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 ∂volume) ≤
      principalCoercivityConstant d lam Lam M K *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2 ∂volume) +
      |∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume| +
      |∫ z in Set.Ioo s₀ s₁ ×ˢ O, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, QG z i ^ 2 ∂volume| / 2 := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let F : TimeVelocity d → ℝ := fun z =>
    R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z
  let D : TimeVelocity d → ℝ := fun z => ζ z.1 *
    WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
  have htime := WeakGradientTimeEnergy.weakGradient_timeEnergy s₀ s₁ O hO
    q QW QG QH hq hQW hQG (fun i => hQH i i) hq_time hq_velocity
    (fun i => hQG_velocity i i) η hη hηcompact hηsupport
    ζ hζ hζcompact hζsupport
  have hprincipal := weakPrincipalIntegrationByParts_coercive lam Lam M K s₀ s₁ O hO
    A q QG QH hAmeas hlam hlamLam hA hAlower hAupper hAderiv hq hQG hQH
    hq_velocity hQG_velocity η hη hηcompact hηsupport hηnonneg hηle hηderiv
    ζ hζ hζcompact hζsupport hζnonneg
  have hFlow := (lowerOrderSource_memLp s₀ s₁ O hO B C0 q R QG M
    hBmeas hCmeas hB hC hq hQG hR).2.2
  have hIf := lowerOrderSource_localizedGradientDivergence_integrable F hFlow
    QG QH hQG (fun i => hQH i i) η hη hηcompact ζ hζ hζcompact
  have hreoriented := residualEquation_reoriented A B QG C0 q QW R QH heq
  have hIp : IntegrableOn (fun z =>
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) * D z) S volume := by
    apply hprincipal.1.congr
    exact Filter.Eventually.of_forall fun z => by simp only [D]; ring
  have hres := integrated_residual_pairing A QW F QH D hreoriented
    (by
      apply htime.1.congr
      exact Filter.Eventually.of_forall fun z => by simp only [D]; ring) hIp
  have hm := preYoung_of_time_residual_principal lam
    (principalCoercivityConstant d lam Lam M K)
    (∫ z in S, ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 ∂volume)
    (∫ z in S, ζ z.1 * (tsupport η).indicator
      (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2 ∂volume)
    (∫ z in S, F z * D z ∂volume)
    (∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, QG z i ^ 2 ∂volume)
    (∫ z in S, QW z * D z ∂volume)
    (∫ z in S, (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) * D z ∂volume)
    (by
      calc
        2 * (∫ z in S, QW z * D z ∂volume) =
            2 * (∫ z in S, ζ z.1 * QW z *
              WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume) := by
                congr 1
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun z => by simp only [D]; ring
        _ = -(∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
              ∑ i : Fin d, QG z i ^ 2 ∂volume) := by
                simpa only [S] using htime.2.2)
    hres
    (by
      convert hprincipal.2.2.2 using 1
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by simp only [D]; ring)
  have hIfEq : (∫ z in S, F z * D z ∂volume) =
      ∫ z in S, ζ z.1 * F z *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by simp only [D]; ring
  rw [hIfEq] at hm
  simpa only [S, F] using hm

/-- The fixed-cylinder weak Hessian energy estimate obtained from the literal
residual equation. -/
theorem exists_weakHessian_energy_le_of_residual
    (d : ℕ)
    (lam Lam M Keta Kzeta : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hM : 0 ≤ M) (hKeta : 0 ≤ Keta) (hKzeta : 0 ≤ Kzeta) :
    ∃ Cenergy : ℝ, 0 ≤ Cenergy ∧
      ∀ (s₀ s₁ : ℝ)
        (O : Set (PDE.Vec d)) (_hO : IsOpen O)
        (A : TimeVelocity d → PDE.Mat d)
        (B : TimeVelocity d → PDE.Vec d)
        (C0 : TimeVelocity d → ℝ)
        (q QW R : TimeVelocity d → ℝ)
        (QG : TimeVelocity d → PDE.Vec d)
        (QH : TimeVelocity d → PDE.Mat d),
        AEStronglyMeasurable A
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        AEStronglyMeasurable B
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        AEStronglyMeasurable C0
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        (∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
          ContDiffOn ℝ 1 (fun y => A (r, y) i j) O) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          lam • (1 : PDE.Mat d) ≤ A z) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          A z ≤ Lam • (1 : PDE.Mat d)) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d,
          |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d,
          |B z j| ≤ M) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          |C0 z| ≤ M) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 QW →
        (∀ j : Fin d, ParabolicMemLpOn
          (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j)) →
        (∀ j i : Fin d, ParabolicMemLpOn
          (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i)) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R →
        HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW →
        (∀ j : Fin d, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j)) →
        (∀ j i : Fin d, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O) i
            (fun z => QG z j) (fun z => QH z j i)) →
        (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
          QW z +
                (∑ i : Fin d, ∑ j : Fin d,
                  A z i j * QH z j i) +
              (∑ j : Fin d, B z j * QG z j) +
            C0 z * q z = R z) →
        ∀ (η : PDE.Vec d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) η →
          HasCompactSupport η →
          tsupport η ⊆ O →
          (∀ y, 0 ≤ η y) →
          (∀ y, η y ≤ 1) →
          (∀ y ∈ O, ∀ i : Fin d,
            |spatialPartial i η y| ≤ Keta) →
        ∀ (ζ : ℝ → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ζ →
          HasCompactSupport ζ →
          tsupport ζ ⊆ Set.Ioo s₀ s₁ →
          (∀ r, 0 ≤ ζ r) →
          (∀ r, ζ r ≤ 1) →
          (∀ r ∈ Set.Ioo s₀ s₁,
            |_root_.deriv ζ r| ≤ Kzeta) →
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
            ζ z.1 * η z.2 ^ 2 *
              ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
            ∂volume) ≤
          Cenergy *
            ((ENNReal.toReal (eLpNorm q 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2 +
              (∑ j : Fin d, (ENNReal.toReal
                (eLpNorm (fun z => QG z j) 2
                  (timeVelocityVolumeOn
                    (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn
                  (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2) := by
  set Cbase := principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2 +
    3 * (d : ℝ) * (Keta + 1 / lam) * (1 + M ^ 2 + (d : ℝ) * M ^ 2) with hCbase
  refine ⟨4 / lam * Cbase, ?_, ?_⟩
  · have hCpr : 0 ≤ principalCoercivityConstant d lam Lam M Keta := by
      unfold principalCoercivityConstant
      positivity
    have hbase : 0 ≤ Cbase := by
      rw [hCbase]
      positivity
    positivity
  · intro s₀ s₁ O hO A B C0 q QW R QG QH hAmeas hBmeas hCmeas hA
      hAlower hAupper hAderiv hB hC hq hQW hQG hQH hR hq_time hq_velocity
      hQG_velocity heq η hη hηcompact hηsupport hηnonneg hηle hηderiv ζ hζ
      hζcompact hζsupport hζnonneg hζle hζderiv
    let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
    let μ := timeVelocityVolumeOn S
    set E := ∫ z in S, ζ z.1 * η z.2 ^ 2 *
      ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 ∂volume with hE
    set G := ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2 μ).toReal ^ 2 with hGdef
    set Nq := (eLpNorm q 2 μ).toReal ^ 2 with hNqdef
    set NR := (eLpNorm R 2 μ).toReal ^ 2 with hNRdef
    let F : TimeVelocity d → ℝ := fun z =>
      R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z
    have hpre := weakHessian_preYoung lam Lam M Keta s₀ s₁ O hO A B C0 q QW R
      QG QH hAmeas hBmeas hCmeas hlam hlamLam hA hAlower hAupper hAderiv hB hC
      hq hQW hQG hQH hR hq_time hq_velocity hQG_velocity η hη hηcompact
      hηsupport hηnonneg hηle hηderiv ζ hζ hζcompact hζsupport hζnonneg heq
    have hprincipal := principalSupportIndicatorGradientIntegral_le_eLpNorm_sq_sum
      s₀ s₁ O QG η ζ hζ.continuous hζnonneg hζle hQG
    have htime := timeCutoffGradientIntegral_abs_div_two_le s₀ s₁ O
      hO.measurableSet QG η ζ hη.continuous (hζ.of_le (show
        (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)) Kzeta
      hηnonneg hηle hζderiv hQG
    have hFlow := (lowerOrderSource_memLp s₀ s₁ O hO B C0 q R QG M
      hBmeas hCmeas hB hC hq hQG hR).2.2
    have hsource := lowerOrder_localizedGradientDivergence_abs_le lam Keta s₀ s₁
      O hO F hFlow QG hQG QH hQH η hη hηcompact hηnonneg hηle hηderiv
      ζ hζ hζcompact hζnonneg hζle hlam hKeta
    have hFsq := lowerOrderSource_integral_sq_le s₀ s₁ O hO B C0 q R QG M
      (eLpNorm R 2 μ).toReal (eLpNorm q 2 μ).toReal
      (fun j => (eLpNorm (fun z => QG z j) 2 μ).toReal)
      hBmeas hCmeas hM hB hC hq hQG hR (le_refl _) (le_refl _) (fun _ => le_refl _)
    rw [← hE] at hpre hsource
    rw [← hGdef] at hprincipal htime hsource
    rw [← hNRdef, ← hNqdef, ← hGdef] at hFsq
    have hG : 0 ≤ G := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hNq : 0 ≤ Nq := sq_nonneg _
    have hNR : 0 ≤ NR := sq_nonneg _
    have hCpr : 0 ≤ principalCoercivityConstant d lam Lam M Keta := by
      unfold principalCoercivityConstant
      positivity
    have hcoef : 0 ≤ (d : ℝ) * (Keta + 1 / lam) := by positivity
    have hquarter : lam / 4 * E ≤
        (principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2) * G +
          3 * (d : ℝ) * (Keta + 1 / lam) *
            (NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G) := by
      have hpweighted := mul_le_mul_of_nonneg_left hprincipal hCpr
      have hFweighted := mul_le_mul_of_nonneg_left hFsq hcoef
      dsimp [F, μ, S] at hpre hprincipal htime hsource hFsq ⊢
      linarith
    have hdom :
        (principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2) * G +
          3 * (d : ℝ) * (Keta + 1 / lam) *
            (NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G) ≤
          Cbase * (Nq + G + NR) := by
      have ha : 0 ≤ principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2 :=
        by positivity
      have hb : 0 ≤ 3 * (d : ℝ) * (Keta + 1 / lam) := by positivity
      have hGtotal : G ≤ Nq + G + NR := by linarith
      have hrest : NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G ≤
          (1 + M ^ 2 + (d : ℝ) * M ^ 2) * (Nq + G + NR) := by
        rw [← sub_nonneg]
        have : 0 ≤ Nq + G + M ^ 2 * G + (d : ℝ) * M ^ 2 * Nq +
            M ^ 2 * NR + (d : ℝ) * M ^ 2 * NR := by
          have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          exact add_nonneg
            (add_nonneg
              (add_nonneg
                (add_nonneg
                  (add_nonneg hNq hG) (mul_nonneg (sq_nonneg M) hG))
                  (mul_nonneg (mul_nonneg hd (sq_nonneg M)) hNq))
                (mul_nonneg (sq_nonneg M) hNR))
            (mul_nonneg (mul_nonneg hd (sq_nonneg M)) hNR)
        convert this using 1
        all_goals ring
      calc
        (principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2) * G +
            3 * (d : ℝ) * (Keta + 1 / lam) *
              (NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G) ≤
            (principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2) *
                (Nq + G + NR) +
              (3 * (d : ℝ) * (Keta + 1 / lam)) *
                ((1 + M ^ 2 + (d : ℝ) * M ^ 2) * (Nq + G + NR)) :=
          add_le_add (mul_le_mul_of_nonneg_left hGtotal ha)
            (mul_le_mul_of_nonneg_left hrest hb)
        _ = Cbase * (Nq + G + NR) := by
          rw [hCbase]
          ring
    have hscaled : E ≤ 4 / lam * Cbase * (Nq + G + NR) := by
      have := le_trans hquarter hdom
      have hdiv : E ≤ (Cbase * (Nq + G + NR)) / (lam / 4) :=
        (le_div_iff₀ (by positivity : 0 < lam / 4)).2 (by
          convert this using 1
          all_goals ring)
      have heqscale : (Cbase * (Nq + G + NR)) / (lam / 4) =
          4 / lam * Cbase * (Nq + G + NR) := by
        field_simp
      rwa [heqscale] at hdiv
    exact hscaled

end HypoellipticAleksandrov.Parabolic
