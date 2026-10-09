module

public import HypoellipticAleksandrov.Parabolic.LocalCompactSupportIntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Smooth principal integration by parts

This module proves the fixed-time, localized principal integration-by-parts
identity used in the smooth difference-quotient argument.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology

namespace HypoellipticAleksandrov.Parabolic

private theorem contDiffOn_spatialPartial {d n : ℕ} {O : Set (PDE.Vec d)}
    (hO : IsOpen O) (i : Fin d) {f : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f O) :
    ContDiffOn ℝ n (spatialPartial i f) O := by
  exact (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

private theorem spatialPartial_mul {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (i : Fin d) {f g : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    {y : PDE.Vec d} (hy : y ∈ O) :
    spatialPartial i (fun x => f x * g x) y =
      spatialPartial i f y * g y + f y * spatialPartial i g y := by
  rw [spatialPartial, fderiv_fun_mul
    ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))
    ((hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))]
  simp [spatialPartial]
  ring

private theorem spatialPartial_sq_mul {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (i : Fin d) {f g : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    {y : PDE.Vec d} (hy : y ∈ O) :
    spatialPartial i (fun x => f x ^ 2 * g x) y =
      2 * f y * spatialPartial i f y * g y + f y ^ 2 * spatialPartial i g y := by
  rw [show (fun x => f x ^ 2 * g x) = fun x => (f x * f x) * g x by funext x; ring]
  rw [spatialPartial_mul hO i (hf.mul hf) hg hy,
    spatialPartial_mul hO i hf hf hy]
  ring

private theorem spatialThird_comm {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (q : PDE.Vec d → ℝ) (hq : ContDiffOn ℝ 3 q O)
    (i j k : Fin d) {y : PDE.Vec d} (hy : y ∈ O) :
    spatialPartial k (spatialSecond q j i) y =
      spatialPartial i (spatialSecond q j k) y := by
  have hj : ContDiffOn ℝ 2 (spatialPartial j q) O :=
    contDiffOn_spatialPartial hO j hq
  have hjy := hj.contDiffAt (hO.mem_nhds hy)
  have hs := hjy.isSymmSndFDerivAt (by norm_num)
  have heval (a b : Fin d) :
      spatialPartial b (spatialPartial a (spatialPartial j q)) y =
        ((fderiv ℝ (fderiv ℝ (spatialPartial j q)) y) (PDE.basisVec b))
          (PDE.basisVec a) := by
    let r := spatialPartial j q
    change spatialPartial b (spatialPartial a r) y =
      ((fderiv ℝ (fderiv ℝ r) y) (PDE.basisVec b)) (PDE.basisVec a)
    unfold spatialPartial
    have hc : ContDiffAt ℝ 1 (fderiv ℝ (spatialPartial j q)) y :=
      (hj.fderiv_of_isOpen hO (by norm_num)).contDiffAt (hO.mem_nhds hy)
    change (fderiv ℝ (fun y => (fderiv ℝ (spatialPartial j q) y)
      (PDE.basisVec a)) y) (PDE.basisVec b) = _
    rw [fderiv_clm_apply
      (hc.differentiableAt (by norm_num))
      (differentiableAt_const (c := PDE.basisVec a))]
    have hb : fderiv ℝ (fun _ : PDE.Vec d => PDE.basisVec a) y = 0 := by
      exact fderiv_const_apply (𝕜 := ℝ) (c := PDE.basisVec a)
    rw [hb]
    change _ = ((fderiv ℝ (fderiv ℝ (spatialPartial j q)) y)
      (PDE.basisVec b)) (PDE.basisVec a)
    simp
  rw [show spatialPartial k (spatialSecond q j i) y =
      spatialPartial k (spatialPartial i (spatialPartial j q)) y by rfl,
    show spatialPartial i (spatialSecond q j k) y =
      spatialPartial i (spatialPartial k (spatialPartial j q)) y by rfl,
    heval i k, heval k i]
  exact hs.eq (PDE.basisVec k) (PDE.basisVec i)

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

/-- Exact fixed-time principal integration-by-parts identity with the
negative localized gradient divergence. -/
theorem smoothPrincipalIntegrationByParts
    {d : ℕ} (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hA : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A y i j) O)
    (hq : ContDiffOn ℝ 3 q O)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O) :
    (∫ y in O,
      (∑ i, ∑ j, A y i j * spatialSecond q j i y) *
        (-∑ k, (2 * η y * spatialPartial k η y * spatialPartial k q y +
          η y ^ 2 * spatialSecond q k k y)) ∂volume) =
      -(∫ y in O, η y ^ 2 *
        (∑ i, ∑ j, ∑ k, A y i j * spatialSecond q k i y *
          spatialSecond q k j y) ∂volume)
      - 2 * (∫ y in O, η y *
        (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
          spatialPartial k q y * spatialSecond q j k y) ∂volume)
      - (∫ y in O, η y ^ 2 *
        (∑ i, ∑ j, ∑ k,
          spatialPartial i (fun x => A x i j) y *
            spatialPartial k q y * spatialSecond q j k y) ∂volume)
      + (∫ y in O, η y ^ 2 *
        (∑ i, ∑ j, ∑ k,
          spatialPartial k (fun x => A x i j) y *
            spatialSecond q j i y * spatialPartial k q y) ∂volume) := by
  have hq1 : ContDiffOn ℝ 1 q O := hq.of_le (by norm_num)
  have hη1 : ContDiffOn ℝ 1 η O := hη.contDiffOn.of_le (by simp)
  have hqp (i : Fin d) : ContDiffOn ℝ 1 (spatialPartial i q) O :=
    contDiffOn_spatialPartial hO i (hq.of_le (by norm_num))
  have hqsecond (j i : Fin d) : ContDiffOn ℝ 1 (spatialSecond q j i) O := by
    exact contDiffOn_spatialPartial hO i
      (contDiffOn_spatialPartial hO j hq)
  have hηp (i : Fin d) : ContDiffOn ℝ 0 (spatialPartial i η) O :=
    contDiffOn_spatialPartial hO i (hη.contDiffOn.of_le (by simp))
  have hcompact2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa [pow_two] using! hηcompact.mul_left
  have hsupport2 : tsupport (fun y => η y ^ 2) ⊆ O :=
    (by simpa [pow_two] using (tsupport_mul_subset_left.trans hηsupport))
  have hibp (i j k : Fin d) :
      (∫ y in O, (A y i j * spatialSecond q j i y) *
        (-(2 * η y * spatialPartial k η y * spatialPartial k q y +
          η y ^ 2 * spatialSecond q k k y)) ∂volume) =
        -(∫ y in O, η y ^ 2 * A y i j * spatialSecond q k i y *
            spatialSecond q k j y ∂volume)
        - 2 * (∫ y in O, η y * spatialPartial i η y * A y i j *
            spatialPartial k q y * spatialSecond q j k y ∂volume)
        - (∫ y in O, η y ^ 2 * spatialPartial i (fun x => A x i j) y *
            spatialPartial k q y * spatialSecond q j k y ∂volume)
        + (∫ y in O, η y ^ 2 * spatialPartial k (fun x => A x i j) y *
            spatialSecond q j i y * spatialPartial k q y ∂volume) := by
    let F : PDE.Vec d → ℝ := fun y => A y i j * spatialSecond q j i y
    let G : PDE.Vec d → ℝ := fun y => η y ^ 2 * spatialPartial k q y
    have hF : ContDiffOn ℝ 1 F O := (hA i j).mul (hqsecond j i)
    have hG : ContDiffOn ℝ 1 G O := by
      simpa [G, pow_two] using (hη1.mul hη1).mul (hqp k)
    have hGcompact : HasCompactSupport G := hcompact2.mul_right
    have hGsupport : tsupport G ⊆ O := tsupport_mul_subset_left.trans hsupport2
    have hfirst := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
      O hO k F G hF hG hGcompact hGsupport
    have hGderiv (y : PDE.Vec d) (hy : y ∈ O) :
        spatialPartial k G y =
          2 * η y * spatialPartial k η y * spatialPartial k q y +
            η y ^ 2 * spatialSecond q k k y := by
      exact spatialPartial_sq_mul hO k hη1 (hqp k) hy
    have hFderiv (y : PDE.Vec d) (hy : y ∈ O) :
        spatialPartial k F y =
          spatialPartial k (fun x => A x i j) y * spatialSecond q j i y +
            A y i j * spatialPartial i (spatialSecond q j k) y := by
      rw [spatialPartial_mul hO k (hA i j) (hqsecond j i) hy,
        spatialThird_comm hO q hq i j k hy]
    have hfirst' :
        (∫ y in O, F y * (-(spatialPartial k G y)) ∂volume) =
          ∫ y in O, spatialPartial k F y * G y ∂volume := by
      calc
        _ = -(∫ y in O, F y * spatialPartial k G y ∂volume) := by
          rw [← integral_neg]
          apply setIntegral_congr_fun hO.measurableSet
          intro y _
          ring
        _ = _ := by linarith
    rw [setIntegral_congr_fun hO.measurableSet (fun y hy => by rw [hGderiv y hy])] at hfirst'
    let L : PDE.Vec d → ℝ := fun y => η y ^ 2 * A y i j * spatialPartial k q y
    let R : PDE.Vec d → ℝ := spatialSecond q j k
    have hL : ContDiffOn ℝ 1 L O := by
      simpa [L, pow_two] using ((hη1.mul hη1).mul (hA i j)).mul (hqp k)
    have hR : ContDiffOn ℝ 1 R O := hqsecond j k
    have hLcompact : HasCompactSupport L := hcompact2.mul_right.mul_right
    have hLsupport : tsupport L ⊆ O :=
      tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans hsupport2)
    have hsecond := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_left
      O hO i L R hL hR hLcompact hLsupport
    have hLderiv (y : PDE.Vec d) (hy : y ∈ O) :
        spatialPartial i L y =
          2 * η y * spatialPartial i η y * A y i j * spatialPartial k q y +
          η y ^ 2 * spatialPartial i (fun x => A x i j) y * spatialPartial k q y +
          η y ^ 2 * A y i j * spatialSecond q k i y := by
      dsimp [L]
      rw [show (fun y => η y ^ 2 * A y i j * spatialPartial k q y) =
          fun y => (η y * η y * A y i j) * spatialPartial k q y by funext x; ring,
        spatialPartial_mul hO i ((hη1.mul hη1).mul (hA i j)) (hqp k) hy,
        spatialPartial_mul hO i (hη1.mul hη1) (hA i j) hy,
        spatialPartial_mul hO i hη1 hη1 hy]
      change _ = _ + _ + η y ^ 2 * A y i j * spatialPartial i (spatialPartial k q) y
      ring
    have hsecond' :
        (∫ y in O, L y * spatialPartial i R y ∂volume) =
          -(∫ y in O,
            (2 * η y * spatialPartial i η y * A y i j * spatialPartial k q y +
             η y ^ 2 * spatialPartial i (fun x => A x i j) y * spatialPartial k q y +
             η y ^ 2 * A y i j * spatialSecond q k i y) * R y ∂volume) := by
      rw [hsecond]
      congr 1
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      change spatialPartial i L y * R y = _
      rw [hLderiv y hy]
    dsimp [F, G, L, R] at hfirst' hsecond
    have hfirst'' :
        (∫ y in O, A y i j * spatialSecond q j i y *
          -(2 * η y * spatialPartial k η y * spatialPartial k q y +
            η y ^ 2 * spatialSecond q k k y) ∂volume) =
          ∫ y in O,
            (spatialPartial k (fun x => A x i j) y * spatialSecond q j i y +
             A y i j * spatialPartial i (spatialSecond q j k) y) *
              (η y ^ 2 * spatialPartial k q y) ∂volume := by
      rw [hfirst']
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      change spatialPartial k F y * G y = _
      rw [hFderiv y hy]
    let U : PDE.Vec d → ℝ := fun y =>
      η y * (2 * spatialPartial i η y * A y i j * spatialPartial k q y * R y)
    let V : PDE.Vec d → ℝ := fun y =>
      η y ^ 2 * spatialPartial i (fun x => A x i j) y * spatialPartial k q y * R y
    let W : PDE.Vec d → ℝ := fun y =>
      η y ^ 2 * A y i j * spatialSecond q k i y * R y
    have hAi : ContDiffOn ℝ 0 (spatialPartial i (fun x => A x i j)) O :=
      contDiffOn_spatialPartial hO i (hA i j)
    have hη0 : ContDiffOn ℝ 0 η O := hη1.of_le (by norm_num)
    have hA0 : ContDiffOn ℝ 0 (fun y => A y i j) O := (hA i j).of_le (by norm_num)
    have hqp0 : ContDiffOn ℝ 0 (spatialPartial k q) O := (hqp k).of_le (by norm_num)
    have hqki0 : ContDiffOn ℝ 0 (spatialSecond q k i) O :=
      (hqsecond k i).of_le (by norm_num)
    have hR0 : ContDiffOn ℝ 0 R O := hR.of_le (by norm_num)
    have hU : IntegrableOn U O := by
      apply integrableOn_of_local_compactSupport hO U
      · simpa [U] using hη0.mul
          (((((contDiffOn_const.mul (hηp i)).mul hA0).mul hqp0).mul hR0))
      · exact hηcompact.mul_right
      · exact tsupport_mul_subset_left.trans hηsupport
    have hV : IntegrableOn V O := by
      apply integrableOn_of_local_compactSupport hO V
      · simpa [V, pow_two] using
          (((((hη1.of_le (by norm_num)).mul (hη1.of_le (by norm_num))).mul hAi).mul
            ((hqp k).of_le (by norm_num))).mul (hR.of_le (by norm_num)))
      · exact hcompact2.mul_right.mul_right.mul_right
      · exact tsupport_mul_subset_left.trans
          (tsupport_mul_subset_left.trans
            (tsupport_mul_subset_left.trans hsupport2))
    have hW : IntegrableOn W O := by
      apply integrableOn_of_local_compactSupport hO W
      · simpa [W, pow_two] using
          (((((hη0.mul hη0).mul hA0).mul hqki0).mul hR0))
      · exact hcompact2.mul_right.mul_right.mul_right
      · exact tsupport_mul_subset_left.trans
          (tsupport_mul_subset_left.trans
            (tsupport_mul_subset_left.trans hsupport2))
    have combine :
        (∫ y in O, L y * spatialPartial i R y ∂volume) =
          -((∫ y in O, U y ∂volume) + (∫ y in O, V y ∂volume) +
            (∫ y in O, W y ∂volume)) := by
      rw [hsecond']
      congr 1
      calc
        _ = ∫ y in O, (U y + V y) + W y ∂volume := by
          apply setIntegral_congr_fun hO.measurableSet
          intro y _
          simp only [U, V, W]
          ring
        _ = _ := by
          change (∫ y, ((U + V) + W) y ∂(volume.restrict O)) = _
          calc
            _ = (∫ y, (U + V) y ∂(volume.restrict O)) +
                ∫ y, W y ∂(volume.restrict O) :=
              integral_add (hU.add hV) hW
            _ = _ := by
              rw [show (∫ y, (U + V) y ∂(volume.restrict O)) =
                  (∫ y, U y ∂(volume.restrict O)) +
                    ∫ y, V y ∂(volume.restrict O) from integral_add hU hV]
    let P : PDE.Vec d → ℝ := fun y =>
      η y ^ 2 * spatialPartial k (fun x => A x i j) y *
        spatialSecond q j i y * spatialPartial k q y
    let Q : PDE.Vec d → ℝ := fun y =>
      L y * spatialPartial i R y
    have hAk : ContDiffOn ℝ 0 (spatialPartial k (fun x => A x i j)) O :=
      contDiffOn_spatialPartial hO k (hA i j)
    have hP : IntegrableOn P O := by
      apply integrableOn_of_local_compactSupport hO P
      · simpa [P, pow_two] using
          ((((hη0.mul hη0).mul hAk).mul ((hqsecond j i).of_le (by norm_num))).mul hqp0)
      · exact hcompact2.mul_right.mul_right.mul_right
      · exact tsupport_mul_subset_left.trans
          (tsupport_mul_subset_left.trans
            (tsupport_mul_subset_left.trans hsupport2))
    have hRi : ContDiffOn ℝ 0 (spatialPartial i R) O :=
      contDiffOn_spatialPartial hO i hR
    have hQ : IntegrableOn Q O := by
      apply integrableOn_of_local_compactSupport hO Q
      · exact hL.of_le (by norm_num) |>.mul hRi
      · exact hLcompact.mul_right
      · exact tsupport_mul_subset_left.trans hLsupport
    have hfirstSplit :
        (∫ y in O, A y i j * spatialSecond q j i y *
          -(2 * η y * spatialPartial k η y * spatialPartial k q y +
            η y ^ 2 * spatialSecond q k k y) ∂volume) =
          (∫ y in O, P y ∂volume) + ∫ y in O, Q y ∂volume := by
      rw [hfirst'']
      calc
        _ = ∫ y in O, P y + Q y ∂volume := by
          apply setIntegral_congr_fun hO.measurableSet
          intro y _
          simp only [P, Q, L, R]
          ring
        _ = _ := integral_add hP hQ
    dsimp [P, Q, U, V, W, L, R] at hfirstSplit combine
    have hsymmInt :
        (∫ y in O, η y ^ 2 * A y i j * spatialSecond q k i y *
          spatialSecond q j k y ∂volume) =
        ∫ y in O, η y ^ 2 * A y i j * spatialSecond q k i y *
          spatialSecond q k j y ∂volume := by
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      dsimp
      rw [spatialSecond_comm hO q (hq.of_le (by norm_num)) j k hy]
    have htwo :
        (∫ y in O, η y * spatialPartial i η y * A y i j * spatialPartial k q y *
          spatialSecond q j k y * 2 ∂volume) =
        2 * ∫ y in O, η y * spatialPartial i η y * A y i j * spatialPartial k q y *
          spatialSecond q j k y ∂volume := by
      calc
        _ = ∫ y in O, 2 * (η y * spatialPartial i η y * A y i j *
            spatialPartial k q y * spatialSecond q j k y) ∂volume := by
          apply setIntegral_congr_fun hO.measurableSet
          intro y _
          ring
        _ = _ := integral_const_mul 2 _
    ring_nf at hfirstSplit combine ⊢
    linarith [hsymmInt, htwo]
  -- Distribute the finite sums and use the preceding scalar identity.
  have hηmul (f : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 0 f O) :
      IntegrableOn (fun y => η y * f y) O := by
    apply integrableOn_of_local_compactSupport hO _
    · exact (hη1.of_le (by norm_num)).mul hf
    · exact hηcompact.mul_right
    · exact tsupport_mul_subset_left.trans hηsupport
  have hη2mul (f : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 0 f O) :
      IntegrableOn (fun y => η y ^ 2 * f y) O := by
    apply integrableOn_of_local_compactSupport hO _
    · simpa [pow_two] using
        ((hη1.of_le (by norm_num)).mul (hη1.of_le (by norm_num))).mul hf
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have integral_triple (f : Fin d → Fin d → Fin d → PDE.Vec d → ℝ)
      (hf : ∀ i j k, IntegrableOn (f i j k) O) :
      (∫ y in O, ∑ i, ∑ j, ∑ k, f i j k y ∂volume) =
        ∑ i, ∑ j, ∑ k, ∫ y in O, f i j k y ∂volume := by
    rw [integral_finset_sum]
    · congr 1
      funext i
      rw [integral_finset_sum]
      · congr 1
        funext j
        rw [integral_finset_sum]
        exact fun k _ => hf i j k
      · exact fun j _ => integrable_finset_sum _ (fun k _ => hf i j k)
    · exact fun i _ => integrable_finset_sum _ (fun j _ =>
        integrable_finset_sum _ (fun k _ => hf i j k))
  let fl : Fin d → Fin d → Fin d → PDE.Vec d → ℝ := fun i j k y =>
    η y * (A y i j * spatialSecond q j i y *
      (-(2 * spatialPartial k η y * spatialPartial k q y +
        η y * spatialSecond q k k y)))
  let fh : Fin d → Fin d → Fin d → PDE.Vec d → ℝ := fun i j k y =>
    η y ^ 2 * (A y i j * spatialSecond q k i y * spatialSecond q k j y)
  let fc : Fin d → Fin d → Fin d → PDE.Vec d → ℝ := fun i j k y =>
    η y * (spatialPartial i η y * A y i j * spatialPartial k q y *
      spatialSecond q j k y)
  let fiA : Fin d → Fin d → Fin d → PDE.Vec d → ℝ := fun i j k y =>
    η y ^ 2 * (spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
      spatialSecond q j k y)
  let fkA : Fin d → Fin d → Fin d → PDE.Vec d → ℝ := fun i j k y =>
    η y ^ 2 * (spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
      spatialPartial k q y)
  have hfl (i j k : Fin d) : IntegrableOn (fl i j k) O := by
    have hf0 : ContDiffOn ℝ 0 (fun y =>
        A y i j * spatialSecond q j i y *
          (-(2 * spatialPartial k η y * spatialPartial k q y +
            η y * spatialSecond q k k y))) O := by
      exact (((hA i j).of_le (by norm_num)).mul ((hqsecond j i).of_le (by norm_num))).mul
        ((((contDiffOn_const.mul (hηp k)).mul ((hqp k).of_le (by norm_num))).add
          ((hη1.of_le (by norm_num)).mul ((hqsecond k k).of_le (by norm_num)))).neg)
    exact hηmul _ hf0
  have hfh (i j k : Fin d) : IntegrableOn (fh i j k) O := by
    apply hη2mul
    exact (((hA i j).of_le (by norm_num)).mul ((hqsecond k i).of_le (by norm_num))).mul
      ((hqsecond k j).of_le (by norm_num))
  have hfc (i j k : Fin d) : IntegrableOn (fc i j k) O := by
    apply hηmul
    exact ((((hηp i).mul ((hA i j).of_le (by norm_num))).mul
      ((hqp k).of_le (by norm_num))).mul ((hqsecond j k).of_le (by norm_num)))
  have hfiA (i j k : Fin d) : IntegrableOn (fiA i j k) O := by
    apply hη2mul
    exact (((contDiffOn_spatialPartial hO i (hA i j)).mul
      ((hqp k).of_le (by norm_num))).mul ((hqsecond j k).of_le (by norm_num)))
  have hfkA (i j k : Fin d) : IntegrableOn (fkA i j k) O := by
    apply hη2mul
    exact (((contDiffOn_spatialPartial hO k (hA i j)).mul
      ((hqsecond j i).of_le (by norm_num))).mul ((hqp k).of_le (by norm_num)))
  calc
    _ = ∫ y in O, ∑ i, ∑ j, ∑ k, fl i j k y ∂volume := by
      apply setIntegral_congr_fun hO.measurableSet
      intro y _
      simp only [fl, Finset.sum_mul]
      ring_nf
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring_nf
    _ = ∑ i, ∑ j, ∑ k, ∫ y in O, fl i j k y ∂volume :=
      integral_triple fl hfl
    _ = ∑ i, ∑ j, ∑ k,
        (-(∫ y in O, fh i j k y ∂volume) -
          2 * (∫ y in O, fc i j k y ∂volume) -
          (∫ y in O, fiA i j k y ∂volume) +
          (∫ y in O, fkA i j k y ∂volume)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [show (∫ y in O, fl i j k y ∂volume) =
          ∫ y in O, A y i j * spatialSecond q j i y *
            (-(2 * η y * spatialPartial k η y * spatialPartial k q y +
              η y ^ 2 * spatialSecond q k k y)) ∂volume by
        apply setIntegral_congr_fun hO.measurableSet
        intro y _
        simp only [fl]
        ring]
      rw [hibp i j k]
      simp only [fh, fc, fiA, fkA]
      ring_nf
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.mul_sum]
      simp_rw [← Finset.mul_sum]
      rw [← integral_triple fh hfh, ← integral_triple fc hfc,
        ← integral_triple fiA hfiA, ← integral_triple fkA hfkA]
      have eh : (∫ y in O, ∑ i, ∑ j, ∑ k, fh i j k y ∂volume) =
          ∫ y in O, η y ^ 2 * (∑ i, ∑ j, ∑ k,
            A y i j * spatialSecond q k i y * spatialSecond q k j y) ∂volume := by
        apply setIntegral_congr_fun hO.measurableSet
        intro y _
        simp only [fh, Finset.mul_sum]
      have ec : (∫ y in O, ∑ i, ∑ j, ∑ k, fc i j k y ∂volume) =
          ∫ y in O, η y * (∑ i, ∑ j, ∑ k,
            spatialPartial i η y * A y i j * spatialPartial k q y *
              spatialSecond q j k y) ∂volume := by
        apply setIntegral_congr_fun hO.measurableSet
        intro y _
        simp only [fc, Finset.mul_sum]
      have ei : (∫ y in O, ∑ i, ∑ j, ∑ k, fiA i j k y ∂volume) =
          ∫ y in O, η y ^ 2 * (∑ i, ∑ j, ∑ k,
            spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
              spatialSecond q j k y) ∂volume := by
        apply setIntegral_congr_fun hO.measurableSet
        intro y _
        simp only [fiA, Finset.mul_sum]
      have ek : (∫ y in O, ∑ i, ∑ j, ∑ k, fkA i j k y ∂volume) =
          ∫ y in O, η y ^ 2 * (∑ i, ∑ j, ∑ k,
            spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
              spatialPartial k q y) ∂volume := by
        apply setIntegral_congr_fun hO.measurableSet
        intro y _
        simp only [fkA, Finset.mul_sum]
      rw [eh, ec, ei, ek]

end HypoellipticAleksandrov.Parabolic
