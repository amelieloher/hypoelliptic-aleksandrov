module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.SpatialPrincipalIntegrationByParts

/-!
# Smooth principal coercivity

This module derives the quantitative fixed-time principal coercivity estimate
from the exact localized integration-by-parts identity.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

/-- The constant in fixed-time principal coercivity. -/
def principalCoercivityConstant
    (d : ℕ) (lam Lam M K : ℝ) : ℝ :=
  2 * (d : ℝ) ^ 3 / lam * (M + Lam * K) ^ 2

private theorem contDiffOn_spatialPartial {d n : ℕ} {O : Set (PDE.Vec d)}
    (hO : IsOpen O) (i : Fin d) {f : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f O) :
    ContDiffOn ℝ n (spatialPartial i f) O := by
  exact (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

private theorem spatialSecond_comm {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (q : PDE.Vec d → ℝ) (hq : ContDiffOn ℝ 2 q O)
    (j k : Fin d) {y : PDE.Vec d} (hy : y ∈ O) :
    spatialSecond q j k y = spatialSecond q k j y := by
  have hqy := hq.contDiffAt (hO.mem_nhds hy)
  have hs := hqy.isSymmSndFDerivAt (by norm_num)
  have heval (a b : Fin d) :
      spatialPartial b (spatialPartial a q) y =
        ((fderiv ℝ (fderiv ℝ q) y) (PDE.basisVec b)) (PDE.basisVec a) := by
    unfold spatialPartial
    have hc : ContDiffAt ℝ 1 (fderiv ℝ q) y :=
      (hq.fderiv_of_isOpen hO (by norm_num)).contDiffAt (hO.mem_nhds hy)
    rw [fderiv_clm_apply (hc.differentiableAt (by norm_num))
      (differentiableAt_const (c := PDE.basisVec a))]
    have hb : fderiv ℝ (fun _ : PDE.Vec d => PDE.basisVec a) y = 0 := by
      exact fderiv_const_apply (𝕜 := ℝ) (c := PDE.basisVec a)
    rw [hb]
    simp
  rw [show spatialSecond q j k y = spatialPartial k (spatialPartial j q) y by rfl,
    show spatialSecond q k j y = spatialPartial j (spatialPartial k q) y by rfl,
    heval j k, heval k j]
  exact hs.eq (PDE.basisVec k) (PDE.basisVec j)

private theorem principal_lower_pointwise
    {d : ℕ} {lam : ℝ} {O : Set (PDE.Vec d)}
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    {y : PDE.Vec d} (hy : y ∈ O) :
    lam * (η y) ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2) ≤
      (η y) ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y) := by
  have hrow (k : Fin d) :
      lam * (∑ i, spatialSecond q k i y ^ 2) ≤
        ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y) := by
    simpa only [PDE.vecNormSq, PDE.vecDot, Matrix.mulVec, dotProduct,
      Finset.mul_sum, pow_two] using
      (vecDot_mulVec_lower_of_loewner (hAlower y hy)
        (fun i => spatialSecond q k i y))
  have hsum :
      lam * (∑ k, ∑ i, spatialSecond q k i y ^ 2) ≤
        ∑ k, ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hrow k
  calc
    lam * (η y) ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2) =
        (η y) ^ 2 * (lam * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) := by ring
    _ ≤ (η y) ^ 2 * (∑ k, ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg (η y))
    _ = (η y) ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem contDiff_of_local_compactSupport {d : ℕ} {O : Set (PDE.Vec d)}
    (hO : IsOpen O) (f : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 0 f O)
    (hfsupport : tsupport f ⊆ O) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ O
  · exact (hf.contDiffAt (hO.mem_nhds hy)).continuousAt
  · have hnot : y ∉ tsupport f := fun h => hy (hfsupport h)
    exact continuousAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hnot)

private theorem integrableOn_of_local_compactSupport {d : ℕ} {O : Set (PDE.Vec d)}
    (hO : IsOpen O) (f : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 0 f O)
    (hfcompact : HasCompactSupport f) (hfsupport : tsupport f ⊆ O) :
    IntegrableOn f O :=
  (contDiff_of_local_compactSupport hO f hf hfsupport).integrable_of_hasCompactSupport
    hfcompact |>.integrableOn

private theorem weighted_young
    {d : ℕ} (hd : 0 < d) {lam B C e H G : ℝ}
    (hlam : 0 < lam) (hB : 0 ≤ B) (hC : 0 < C) (he : 0 ≤ e) :
    B * e * |H| * |G| ≤
      (lam * B / (4 * C * (d : ℝ))) * (e ^ 2 * H ^ 2) +
        (B * C * (d : ℝ) / lam) * G ^ 2 := by
  have _he := he
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs := sq_nonneg
    (Real.sqrt (lam / (4 * C * (d : ℝ))) * (e * |H|) -
      Real.sqrt (C * (d : ℝ) / lam) * |G|)
  have h₁ : 0 ≤ lam / (4 * C * (d : ℝ)) := div_nonneg hlam.le (by positivity)
  have h₂ : 0 ≤ C * (d : ℝ) / lam := div_nonneg (by positivity) hlam.le
  have hs₁ : Real.sqrt (lam / (4 * C * (d : ℝ))) ^ 2 =
      lam / (4 * C * (d : ℝ)) :=
    Real.sq_sqrt h₁
  have hs₂ : Real.sqrt (C * (d : ℝ) / lam) ^ 2 = C * (d : ℝ) / lam :=
    Real.sq_sqrt h₂
  have hsqrt :
      Real.sqrt (lam / (4 * C * (d : ℝ))) *
          Real.sqrt (C * (d : ℝ) / lam) = 1 / 2 := by
    rw [← Real.sqrt_mul h₁]
    have : lam / (4 * C * (d : ℝ)) * (C * (d : ℝ) / lam) = 1 / 4 := by
      field_simp
    rw [this]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / 4 : ℝ) := Real.sqrt_nonneg _
    have hsqrt_sq : Real.sqrt (1 / 4 : ℝ) ^ 2 = 1 / 4 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  rw [sub_sq] at hs
  simp only [mul_pow, hs₁, hs₂, sq_abs] at hs
  have hcross :
      (Real.sqrt (lam / (4 * C * (d : ℝ))) * (e * |H|)) *
          (Real.sqrt (C * (d : ℝ) / lam) * |G|) =
        e * |H| * |G| / 2 := by
    calc
      _ = (Real.sqrt (lam / (4 * C * (d : ℝ))) *
          Real.sqrt (C * (d : ℝ) / lam)) * (e * |H| * |G|) := by ring
      _ = _ := by rw [hsqrt]; ring
  have hs' :
      0 ≤ lam / (4 * C * (d : ℝ)) * (e ^ 2 * H ^ 2) -
          e * |H| * |G| + C * (d : ℝ) / lam * G ^ 2 := by
    calc
      0 ≤ lam / (4 * C * (d : ℝ)) * (e ^ 2 * H ^ 2) -
          2 * (Real.sqrt (lam / (4 * C * (d : ℝ))) * (e * |H|)) *
            (Real.sqrt (C * (d : ℝ) / lam) * |G|) +
          C * (d : ℝ) / lam * G ^ 2 := hs
      _ = _ := by
        rw [mul_assoc 2, hcross]
        ring
  have hyoung : e * |H| * |G| ≤
      lam / (4 * C * (d : ℝ)) * (e ^ 2 * H ^ 2) +
        C * (d : ℝ) / lam * G ^ 2 := by
    linarith
  calc
    B * e * |H| * |G| = B * (e * |H| * |G|) := by ring
    _ ≤ B * (lam / (4 * C * (d : ℝ)) * (e ^ 2 * H ^ 2) +
        C * (d : ℝ) / lam * G ^ 2) := mul_le_mul_of_nonneg_left hyoung hB
    _ = _ := by ring

private theorem sum_abs_mul_abs_le_jk_k
    {d : ℕ} (hd : 0 < d) {lam B C e : ℝ}
    (H : Fin d → Fin d → ℝ) (G : Fin d → ℝ)
    (hlam : 0 < lam) (hB : 0 ≤ B) (hC : 0 < C) (he : 0 ≤ e) :
    B * e * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) ≤
      (lam * B / (4 * C)) * (e ^ 2 * (∑ j, ∑ k, H j k ^ 2)) +
        (B * C * (d : ℝ) ^ 3 / lam) * (∑ k, G k ^ 2) := by
  calc
    B * e * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) =
        ∑ _i : Fin d, ∑ j, ∑ k, B * e * |H j k| * |G k| := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ ∑ _i, ∑ j, ∑ k,
        ((lam * B / (4 * C * (d : ℝ))) * (e ^ 2 * H j k ^ 2) +
          (B * C * (d : ℝ) / lam) * G k ^ 2) := by
      exact Finset.sum_le_sum fun _i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ =>
          weighted_young hd hlam hB hC he (H := H j k) (G := G k)
    _ = (lam * B / (4 * C)) * (e ^ 2 * (∑ j, ∑ k, H j k ^ 2)) +
        (B * C * (d : ℝ) ^ 3 / lam) * (∑ k, G k ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      field_simp

private theorem sum_abs_mul_abs_le_ji_k
    {d : ℕ} (hd : 0 < d) {lam B C e : ℝ}
    (H : Fin d → Fin d → ℝ) (G : Fin d → ℝ)
    (hlam : 0 < lam) (hB : 0 ≤ B) (hC : 0 < C) (he : 0 ≤ e) :
    B * e * (∑ i, ∑ j, ∑ k, |H j i| * |G k|) ≤
      (lam * B / (4 * C)) * (e ^ 2 * (∑ j, ∑ i, H j i ^ 2)) +
        (B * C * (d : ℝ) ^ 3 / lam) * (∑ k, G k ^ 2) := by
  calc
    B * e * (∑ i, ∑ j, ∑ k, |H j i| * |G k|) =
        ∑ i, ∑ j, ∑ k, B * e * |H j i| * |G k| := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ ∑ i, ∑ j, ∑ k,
        ((lam * B / (4 * C * (d : ℝ))) * (e ^ 2 * H j i ^ 2) +
          (B * C * (d : ℝ) / lam) * G k ^ 2) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ =>
          weighted_young hd hlam hB hC he (H := H j i) (G := G k)
    _ = (lam * B / (4 * C)) * (e ^ 2 * (∑ j, ∑ i, H j i ^ 2)) +
        (B * C * (d : ℝ) ^ 3 / lam) * (∑ k, G k ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      field_simp

private theorem remainder_lower_pointwise
    {d : ℕ} (hd : 0 < d) {lam Lam M K : ℝ}
    {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hq : ContDiffOn ℝ 2 q O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hC : 0 < M + Lam * K)
    {y : PDE.Vec d} (hy : y ∈ O) :
    2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y))
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y) ≥
      -(lam / 2 * (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) +
        principalCoercivityConstant d lam Lam M K *
          (∑ k, spatialPartial k q y ^ 2)) := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hηsq_le : η y ^ 2 ≤ η y := by
    nlinarith [hηnonneg y, hηle y]
  have habsTriple (f : Fin d → Fin d → Fin d → ℝ) :
      |∑ i, ∑ j, ∑ k, f i j k| ≤ ∑ i, ∑ j, ∑ k, |f i j k| := by
    calc
      _ ≤ ∑ i, |∑ j, ∑ k, f i j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |∑ k, f i j k| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.abs_sum_le_sum_abs _ _
  let H : Fin d → Fin d → ℝ := fun j k => spatialSecond q j k y
  let G : Fin d → ℝ := fun k => spatialPartial k q y
  have hentry (i j : Fin d) : |A y i j| ≤ Lam :=
    abs_apply_le_of_loewner hlam (hAlower y hy) (hAupper y hy) i j
  have hcutSum :
      |∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j * G k * H j k| ≤
        Lam * K * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ k,
          |spatialPartial i η y * A y i j * G k * H j k| := habsTriple _
      _ ≤ ∑ _i : Fin d, ∑ j, ∑ k,
          Lam * K * (|H j k| * |G k|) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, abs_mul, abs_mul]
            have hp : |spatialPartial i η y| * |A y i j| ≤ K * Lam :=
              mul_le_mul (hηderiv y hy i) (hentry i j) (abs_nonneg _) hK
            have hpG := mul_le_mul_of_nonneg_right hp (abs_nonneg (G k))
            have hpGH := mul_le_mul_of_nonneg_right hpG (abs_nonneg (H j k))
            nlinarith
      _ = _ := by simp only [Finset.mul_sum]
  have haiSum :
      |∑ i, ∑ j, ∑ k, spatialPartial i (fun x => A x i j) y * G k * H j k| ≤
        M * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ k,
          |spatialPartial i (fun x => A x i j) y * G k * H j k| := habsTriple _
      _ ≤ ∑ _i : Fin d, ∑ j, ∑ k, M * (|H j k| * |G k|) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, abs_mul]
            have hp := mul_le_mul_of_nonneg_right (hAderiv y hy i j i) (abs_nonneg (G k))
            have hp' := mul_le_mul_of_nonneg_right hp (abs_nonneg (H j k))
            nlinarith
      _ = _ := by simp only [Finset.mul_sum]
  have hakSum :
      |∑ i, ∑ j, ∑ k, spatialPartial k (fun x => A x i j) y * H j i * G k| ≤
        M * (∑ i, ∑ j, ∑ k, |H j i| * |G k|) := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ k,
          |spatialPartial k (fun x => A x i j) y * H j i * G k| := habsTriple _
      _ ≤ ∑ i, ∑ j, ∑ k, M * (|H j i| * |G k|) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, abs_mul]
            have hp := mul_le_mul_of_nonneg_right (hAderiv y hy i j k) (abs_nonneg (H j i))
            have hp' := mul_le_mul_of_nonneg_right hp (abs_nonneg (G k))
            nlinarith
      _ = _ := by simp only [Finset.mul_sum]
  have hcutRaw :
      |2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
          G k * H j k))| ≤
        (2 * Lam * K) * η y *
          (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg (hηnonneg y)]
    have hscale : 0 ≤ 2 * η y := mul_nonneg (by norm_num) (hηnonneg y)
    have hscaled := mul_le_mul_of_nonneg_left hcutSum hscale
    convert hscaled using 1 <;> ring
  have haiRaw :
      |η y ^ 2 * (∑ i, ∑ j, ∑ k,
          spatialPartial i (fun x => A x i j) y * G k * H j k)| ≤
        M * η y * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (η y))]
    calc
      _ ≤ η y ^ 2 * (M * (∑ _i : Fin d, ∑ j, ∑ k,
          |H j k| * |G k|)) := mul_le_mul_of_nonneg_left haiSum (sq_nonneg (η y))
      _ = (M * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|)) * η y ^ 2 := by ring
      _ ≤ (M * (∑ _i : Fin d, ∑ j, ∑ k, |H j k| * |G k|)) * η y := by
        exact mul_le_mul_of_nonneg_left hηsq_le (mul_nonneg hM (by positivity))
      _ = _ := by ring
  have hakRaw :
      |η y ^ 2 * (∑ i, ∑ j, ∑ k,
          spatialPartial k (fun x => A x i j) y * H j i * G k)| ≤
        M * η y * (∑ i, ∑ j, ∑ k, |H j i| * |G k|) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (η y))]
    calc
      _ ≤ η y ^ 2 * (M * (∑ i, ∑ j, ∑ k,
          |H j i| * |G k|)) := mul_le_mul_of_nonneg_left hakSum (sq_nonneg (η y))
      _ = (M * (∑ i, ∑ j, ∑ k, |H j i| * |G k|)) * η y ^ 2 := by ring
      _ ≤ (M * (∑ i, ∑ j, ∑ k, |H j i| * |G k|)) * η y := by
        exact mul_le_mul_of_nonneg_left hηsq_le (mul_nonneg hM (by positivity))
      _ = _ := by ring
  have hB0 : 0 ≤ 2 * Lam * K := by positivity
  have hcutYoung := sum_abs_mul_abs_le_jk_k hd H G hlam hB0 hC (hηnonneg y)
    (B := 2 * Lam * K)
  have haiYoung := sum_abs_mul_abs_le_jk_k hd H G hlam hM hC (hηnonneg y)
    (B := M)
  have hakYoung := sum_abs_mul_abs_le_ji_k hd H G hlam hM hC (hηnonneg y)
    (B := M)
  have hsymm (j k : Fin d) : H j k = spatialSecond q k j y := by
    exact spatialSecond_comm hO q hq j k hy
  have hsymmSq : ∑ j, ∑ k, H j k ^ 2 = ∑ k, ∑ i, spatialSecond q k i y ^ 2 := by
    calc
      _ = ∑ j, ∑ k, spatialSecond q k j y ^ 2 := by simp_rw [hsymm]
      _ = _ := Finset.sum_comm
  have hjiSq : ∑ j, ∑ i, H j i ^ 2 = ∑ k, ∑ i, spatialSecond q k i y ^ 2 := by
    rfl
  dsimp [H, G] at hcutRaw haiRaw hakRaw hcutYoung haiYoung hakYoung hsymmSq hjiSq
  rw [hsymmSq] at hcutYoung haiYoung
  rw [hjiSq] at hakYoung
  have hcutLower := neg_abs_le (2 * (η y * (∑ i, ∑ j, ∑ k,
    spatialPartial i η y * A y i j * spatialPartial k q y * spatialSecond q j k y)))
  have haiLower := neg_abs_le (η y ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
      spatialSecond q j k y))
  have hakUpper := le_abs_self (η y ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
      spatialPartial k q y))
  have hcombined :
      |2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
          spatialPartial k q y * spatialSecond q j k y))| +
        |η y ^ 2 * (∑ i, ∑ j, ∑ k,
          spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
            spatialSecond q j k y)| +
        |η y ^ 2 * (∑ i, ∑ j, ∑ k,
          spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
            spatialPartial k q y)| ≤
        (lam * (2 * Lam * K) / (4 * (M + Lam * K)) +
          lam * M / (4 * (M + Lam * K)) +
          lam * M / (4 * (M + Lam * K))) *
            (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) +
        ((2 * Lam * K) * (M + Lam * K) * (d : ℝ) ^ 3 / lam +
          M * (M + Lam * K) * (d : ℝ) ^ 3 / lam +
          M * (M + Lam * K) * (d : ℝ) ^ 3 / lam) *
            (∑ k, spatialPartial k q y ^ 2) := by
    linarith
  have hbudget :
      (lam * (2 * Lam * K) / (4 * (M + Lam * K)) +
          lam * M / (4 * (M + Lam * K)) +
          lam * M / (4 * (M + Lam * K))) *
            (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) +
        ((2 * Lam * K) * (M + Lam * K) * (d : ℝ) ^ 3 / lam +
          M * (M + Lam * K) * (d : ℝ) ^ 3 / lam +
          M * (M + Lam * K) * (d : ℝ) ^ 3 / lam) *
            (∑ k, spatialPartial k q y ^ 2) =
        lam / 2 * (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) +
          2 * (d : ℝ) ^ 3 / lam * (M + Lam * K) ^ 2 *
            (∑ k, spatialPartial k q y ^ 2) := by
    field_simp [ne_of_gt hlam, ne_of_gt hC]
    ring
  dsimp [principalCoercivityConstant]
  rw [hbudget] at hcombined
  linarith

private theorem principal_remainder_lower_pointwise_on_support
    {d : ℕ} (lam Lam M K : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (_hA : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A y i j) O)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hq : ContDiffOn ℝ 3 q O)
    (_hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (_hηcompact : HasCompactSupport η)
    (_hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    {y : PDE.Vec d} (hy : y ∈ O) :
    η y ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y)
      + 2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y))
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y) ≥
      lam / 2 * (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) -
        principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator (fun z => ∑ k, spatialPartial k q z ^ 2) y := by
  by_cases hd : 0 < d
  · by_cases hys : y ∈ tsupport η
    · have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
      let i0 : Fin d := ⟨0, hd⟩
      have hM : 0 ≤ M := le_trans (abs_nonneg _)
        (hAderiv y hy i0 i0 i0)
      have hK : 0 ≤ K := le_trans (abs_nonneg _) (hηderiv y hy i0)
      have hCnonneg : 0 ≤ M + Lam * K := add_nonneg hM (mul_nonneg hLam.le hK)
      have hp := principal_lower_pointwise A q η hAlower hy
      by_cases hCzero : M + Lam * K = 0
      · have hMzero : M = 0 := by
          nlinarith [mul_nonneg hLam.le hK]
        have hKzero : K = 0 := by
          have : Lam * K = 0 := by nlinarith
          exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hLam)
        have hηderivZero (i : Fin d) : spatialPartial i η y = 0 := by
          have := hηderiv y hy i
          rw [hKzero] at this
          exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
        have hAderivZero (i j k : Fin d) :
            spatialPartial k (fun x => A x i j) y = 0 := by
          have := hAderiv y hy i j k
          rw [hMzero] at this
          exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
        rw [Set.indicator_of_mem hys]
        simp_rw [hηderivZero, hAderivZero]
        simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero, sub_zero]
        dsimp [principalCoercivityConstant]
        rw [hMzero, hKzero]
        norm_num
        have henergy : 0 ≤ η y ^ 2 *
            (∑ k, ∑ i, spatialSecond q k i y ^ 2) := by positivity
        have hp' : lam * (η y ^ 2 *
            (∑ k, ∑ i, spatialSecond q k i y ^ 2)) ≤
            η y ^ 2 * (∑ i, ∑ j, ∑ k,
              A y i j * spatialSecond q k i y * spatialSecond q k j y) := by
          simpa only [mul_assoc] using hp
        have hhalf : lam / 2 * (η y ^ 2 *
            (∑ k, ∑ i, spatialSecond q k i y ^ 2)) ≤
            lam * (η y ^ 2 *
              (∑ k, ∑ i, spatialSecond q k i y ^ 2)) := by
          nlinarith
        exact hhalf.trans hp'
      · have hC : 0 < M + Lam * K := lt_of_le_of_ne hCnonneg (Ne.symm hCzero)
        have hr := remainder_lower_pointwise hd hO A q η hlam hlamLam hAlower hAupper
          hAderiv (hq.of_le (by norm_num)) hηnonneg hηle hηderiv hM hK hC hy
        rw [Set.indicator_of_mem hys]
        linarith
    · have hηzero : η y = 0 := by
        by_contra hne
        exact hys (subset_closure hne)
      have hηpartialZero (i : Fin d) : spatialPartial i η y = 0 := by
        unfold spatialPartial
        rw [fderiv_of_notMem_tsupport ℝ hys]
        simp
      rw [Set.indicator_of_notMem hys]
      simp_rw [hηzero, hηpartialZero]
      norm_num
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    simp

private theorem integrableOn_weighted_spatialSecond_sq
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (q η : PDE.Vec d → ℝ) (hq : ContDiffOn ℝ 3 q O)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O) :
    IntegrableOn (fun y => η y ^ 2 *
      (∑ k, ∑ i, spatialSecond q k i y ^ 2)) O := by
  have hqsecond (k i : Fin d) : ContDiffOn ℝ 0 (spatialSecond q k i) O :=
    (contDiffOn_spatialPartial hO i
      (contDiffOn_spatialPartial hO k hq)).of_le (by norm_num)
  have hsum : ContDiffOn ℝ 0
      (fun y => ∑ k, ∑ i, spatialSecond q k i y ^ 2) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun k _ =>
        ContDiffOn.sum (s := Finset.univ) fun i _ => (hqsecond k i).pow 2)
  have hη0 : ContDiffOn ℝ 0 η O := hη.contDiffOn.of_le (by simp)
  have hcompact2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηcompact.mul_left
  have hsupport2 : tsupport (fun y => η y ^ 2) ⊆ O :=
    (by simpa [pow_two] using tsupport_mul_subset_left.trans hηsupport)
  exact integrableOn_of_local_compactSupport hO _ ((hη0.pow 2).mul hsum)
    hcompact2.mul_right (tsupport_mul_subset_left.trans hsupport2)

private theorem integrableOn_spatialPartial_sq_tsupport
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (q η : PDE.Vec d → ℝ) (hq : ContDiffOn ℝ 3 q O)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O) :
    IntegrableOn (fun y => ∑ k, spatialPartial k q y ^ 2) (tsupport η) := by
  have hqp (k : Fin d) : ContDiffOn ℝ 0 (spatialPartial k q) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hq.of_le (by norm_num))
  have hsum : ContDiffOn ℝ 0 (fun y => ∑ k, spatialPartial k q y ^ 2) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun k _ => (hqp k).pow 2)
  exact (hsum.continuousOn.mono hηsupport).integrableOn_compact hηcompact

private theorem integrableOn_principal_remainder_identity_side
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hA : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A y i j) O)
    (hq : ContDiffOn ℝ 3 q O)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O) :
    IntegrableOn (fun y =>
      η y ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y)
      + 2 * η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y)
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y)) O := by
  have hsum {f : Fin d → Fin d → Fin d → PDE.Vec d → ℝ}
      (hf : ∀ i j k, ContDiffOn ℝ 0 (f i j k) O) :
      ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k, f i j k y) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun i _ =>
        ContDiffOn.sum (s := Finset.univ) fun j _ =>
          ContDiffOn.sum (s := Finset.univ) fun k _ => hf i j k)
  have hη0 : ContDiffOn ℝ 0 η O := hη.contDiffOn.of_le (by simp)
  have hηp (i : Fin d) : ContDiffOn ℝ 0 (spatialPartial i η) O :=
    contDiffOn_spatialPartial (n := 0) hO i (hη.contDiffOn.of_le (by simp))
  have hqp (k : Fin d) : ContDiffOn ℝ 0 (spatialPartial k q) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hq.of_le (by norm_num))
  have hqsecond (j k : Fin d) : ContDiffOn ℝ 0 (spatialSecond q j k) O :=
    contDiffOn_spatialPartial (n := 0) hO k
      (contDiffOn_spatialPartial (n := 1) hO j (hq.of_le (by norm_num)))
  have hA0 (i j : Fin d) : ContDiffOn ℝ 0 (fun y => A y i j) O :=
    (hA i j).of_le (by norm_num)
  have hAp (i j k : Fin d) :
      ContDiffOn ℝ 0 (spatialPartial k (fun x => A x i j)) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hA i j)
  have hprincipal : ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k,
      A y i j * spatialSecond q k i y * spatialSecond q k j y) O :=
    hsum fun i j k => ((hA0 i j).mul (hqsecond k i)).mul (hqsecond k j)
  have hcutoff : ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k,
      spatialPartial i η y * A y i j * spatialPartial k q y *
        spatialSecond q j k y) O :=
    hsum fun i j k => (((hηp i).mul (hA0 i j)).mul (hqp k)).mul (hqsecond j k)
  have hAi : ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k,
      spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
        spatialSecond q j k y) O :=
    hsum fun i j k => ((hAp i j i).mul (hqp k)).mul (hqsecond j k)
  have hAk : ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
        spatialPartial k q y) O :=
    hsum fun i j k => ((hAp i j k).mul (hqsecond j i)).mul (hqp k)
  let R : PDE.Vec d → ℝ := fun y =>
    η y * (η y * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y)
      + 2 * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y)
      + η y * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y))
  have hR : ContDiffOn ℝ 0 R O := by
    exact hη0.mul (((hη0.mul hprincipal).add (contDiffOn_const.mul hcutoff)).add
      (hη0.mul hAi) |>.sub (hη0.mul hAk))
  have hReq : R = fun y =>
      η y ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y)
      + 2 * η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y)
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y) := by
    funext y
    dsimp [R]
    ring
  rw [← hReq]
  exact integrableOn_of_local_compactSupport hO R hR hηcompact.mul_right
    (tsupport_mul_subset_left.trans hηsupport)

/-- Quantitative fixed-time coercivity of the negative localized principal
pairing, modulo the gradient remainder on the cutoff's topological support. -/
theorem smoothPrincipalIntegrationByParts_coercive
    {d : ℕ} (lam Lam M K : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A y i j) O)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hq : ContDiffOn ℝ 3 q O)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y)
    (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d,
      |spatialPartial i η y| ≤ K) :
    -(∫ y in O,
        (∑ i, ∑ j, A y i j * spatialSecond q j i y) *
          (-∑ k,
            (2 * η y * spatialPartial k η y * spatialPartial k q y +
              η y ^ 2 * spatialSecond q k k y)) ∂volume) ≥
      lam / 2 *
        (∫ y in O, η y ^ 2 *
          (∑ k, ∑ i, spatialSecond q k i y ^ 2) ∂volume)
      - principalCoercivityConstant d lam Lam M K *
        (∫ y in tsupport η,
          ∑ k, spatialPartial k q y ^ 2 ∂volume) := by
  let L : PDE.Vec d → ℝ := fun y =>
    η y ^ 2 * (∑ i, ∑ j, ∑ k,
      A y i j * spatialSecond q k i y * spatialSecond q k j y)
    + 2 * η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
      spatialPartial k q y * spatialSecond q j k y)
    + η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
        spatialSecond q j k y)
    - η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
        spatialPartial k q y)
  let E : PDE.Vec d → ℝ := fun y =>
    η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)
  let G : PDE.Vec d → ℝ := fun y => ∑ k, spatialPartial k q y ^ 2
  have hLint : IntegrableOn L O := by
    exact integrableOn_principal_remainder_identity_side hO A q η hA hq hη
      hηcompact hηsupport
  have hEint : IntegrableOn E O :=
    integrableOn_weighted_spatialSecond_sq hO q η hq hη hηcompact hηsupport
  have hGint : IntegrableOn G (tsupport η) :=
    integrableOn_spatialPartial_sq_tsupport hO q η hq hηcompact hηsupport
  have hGindicator : IntegrableOn ((tsupport η).indicator G) O := by
    exact (hGint.integrable_indicator (isClosed_tsupport η).measurableSet).integrableOn
  have hrightInt : IntegrableOn (fun y => lam / 2 * E y -
      principalCoercivityConstant d lam Lam M K * (tsupport η).indicator G y) O :=
    (hEint.const_mul _).sub (hGindicator.const_mul _)
  have hpoint : ∀ᵐ y ∂(volume.restrict O),
      lam / 2 * E y - principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator G y ≤ L y := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
    dsimp [L, E, G]
    simpa only [mul_assoc] using
      (principal_remainder_lower_pointwise_on_support lam Lam M K O hO A q η
        hlam hlamLam hA hAlower hAupper hAderiv hq hη hηcompact hηsupport
        hηnonneg hηle hηderiv hy)
  have hmono := integral_mono_ae hrightInt hLint hpoint
  have hindicatorIntegral :
      (∫ y in O, (tsupport η).indicator G y ∂volume) = ∫ y in tsupport η, G y ∂volume := by
    rw [MeasureTheory.setIntegral_indicator (isClosed_tsupport η).measurableSet]
    rw [inter_eq_right.mpr hηsupport]
  have hrightIntegral :
      (∫ y in O, lam / 2 * E y - principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator G y ∂volume) =
        lam / 2 * (∫ y in O, E y ∂volume) -
          principalCoercivityConstant d lam Lam M K *
            (∫ y in tsupport η, G y ∂volume) := by
    rw [integral_sub (hEint.const_mul _) (hGindicator.const_mul _),
      integral_const_mul, integral_const_mul, hindicatorIntegral]
  have hη0 : ContDiffOn ℝ 0 η O := hη.contDiffOn.of_le (by simp)
  have hηp (i : Fin d) : ContDiffOn ℝ 0 (spatialPartial i η) O :=
    contDiffOn_spatialPartial (n := 0) hO i (hη.contDiffOn.of_le (by simp))
  have hqp (k : Fin d) : ContDiffOn ℝ 0 (spatialPartial k q) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hq.of_le (by norm_num))
  have hqsecond (j k : Fin d) : ContDiffOn ℝ 0 (spatialSecond q j k) O :=
    contDiffOn_spatialPartial (n := 0) hO k
      (contDiffOn_spatialPartial (n := 1) hO j (hq.of_le (by norm_num)))
  have hA0 (i j : Fin d) : ContDiffOn ℝ 0 (fun y => A y i j) O :=
    (hA i j).of_le (by norm_num)
  have hAp (i j k : Fin d) : ContDiffOn ℝ 0
      (spatialPartial k (fun x => A x i j)) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hA i j)
  have htriple {f : Fin d → Fin d → Fin d → PDE.Vec d → ℝ}
      (hf : ∀ i j k, ContDiffOn ℝ 0 (f i j k) O) :
      ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k, f i j k y) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun i _ =>
        ContDiffOn.sum (s := Finset.univ) fun j _ =>
          ContDiffOn.sum (s := Finset.univ) fun k _ => hf i j k)
  have hcompact2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηcompact.mul_left
  have hsupport2 : tsupport (fun y => η y ^ 2) ⊆ O :=
    (by simpa [pow_two] using tsupport_mul_subset_left.trans hηsupport)
  let P : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
    A y i j * spatialSecond q k i y * spatialSecond q k j y)
  let C : PDE.Vec d → ℝ := fun y => η y * (∑ i, ∑ j, ∑ k,
    spatialPartial i η y * A y i j * spatialPartial k q y * spatialSecond q j k y)
  let I : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
      spatialSecond q j k y)
  let J : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
        spatialPartial k q y)
  have hP : IntegrableOn P O := by
    apply integrableOn_of_local_compactSupport hO P
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hA0 i j).mul (hqsecond k i)).mul (hqsecond k j))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have hC : IntegrableOn C O := by
    apply integrableOn_of_local_compactSupport hO C
    · exact hη0.mul (htriple fun i j k =>
        (((hηp i).mul (hA0 i j)).mul (hqp k)).mul (hqsecond j k))
    · exact hηcompact.mul_right
    · exact tsupport_mul_subset_left.trans hηsupport
  have hI : IntegrableOn I O := by
    apply integrableOn_of_local_compactSupport hO I
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hAp i j i).mul (hqp k)).mul (hqsecond j k))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have hJ : IntegrableOn J O := by
    apply integrableOn_of_local_compactSupport hO J
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hAp i j k).mul (hqsecond j i)).mul (hqp k))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have hLintSplit : (∫ y in O, L y ∂volume) =
      (∫ y in O, P y ∂volume) + 2 * (∫ y in O, C y ∂volume) +
        (∫ y in O, I y ∂volume) - (∫ y in O, J y ∂volume) := by
    change (∫ y, L y ∂(volume.restrict O)) = _
    have hLC : L = fun y => P y + 2 * C y + I y - J y := by
      funext y
      dsimp [L, P, C, I, J]
      ring
    rw [hLC]
    change (∫ y, (((P + fun z => 2 * C z) + I) - J) y ∂(volume.restrict O)) = _
    have hsumI : (∫ y, ((P + fun z => 2 * C z) + I) y ∂(volume.restrict O)) =
        (∫ y, (P + fun z => 2 * C z) y ∂(volume.restrict O)) +
          ∫ y, I y ∂(volume.restrict O) := by
      simpa only [Pi.add_apply] using integral_add (hP.add (hC.const_mul 2)) hI
    have hsumC : (∫ y, (P + fun z => 2 * C z) y ∂(volume.restrict O)) =
        (∫ y, P y ∂(volume.restrict O)) +
          ∫ y, 2 * C y ∂(volume.restrict O) := by
      simpa only [Pi.add_apply] using integral_add hP (hC.const_mul 2)
    calc
      _ = (∫ y, ((P + fun z => 2 * C z) + I) y ∂(volume.restrict O)) -
          ∫ y, J y ∂(volume.restrict O) :=
        integral_sub ((hP.add (hC.const_mul 2)).add hI) hJ
      _ = ((∫ y, (P + fun z => 2 * C z) y ∂(volume.restrict O)) +
          ∫ y, I y ∂(volume.restrict O)) -
          ∫ y, J y ∂(volume.restrict O) := by rw [hsumI]
      _ = _ := by
        rw [hsumC, integral_const_mul]
  have hibp := smoothPrincipalIntegrationByParts O hO A q η hA hq hη hηcompact hηsupport
  have hnegIdentity :
      -(∫ y in O,
        (∑ i, ∑ j, A y i j * spatialSecond q j i y) *
          (-∑ k, (2 * η y * spatialPartial k η y * spatialPartial k q y +
            η y ^ 2 * spatialSecond q k k y)) ∂volume) = ∫ y in O, L y ∂volume := by
    rw [hLintSplit]
    dsimp [P, C, I, J]
    linarith
  rw [hnegIdentity, ← hrightIntegral]
  exact hmono
