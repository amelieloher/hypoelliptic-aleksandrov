module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackEndpoint
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Physical scaling for the source-aware local parabolic Harnack estimate

This module transports the normalized one-box estimate to every positive
physical radius, retaining its compact carrier and raw inhomogeneous source.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Set

private def parabolicAffineHomeomorph
    {d : ℕ} (t0 : ℝ) (v0 : PDE.Vec d) (s : ℝ) (hs : 0 < s) :
    TimeVelocity d ≃ₜ TimeVelocity d where
  toEquiv :=
    { toFun := parabolicAffine t0 v0 s
      invFun := fun z ↦ ((z.1 - t0) / s ^ 2, s⁻¹ • (z.2 - v0))
      left_inv := by
        intro z
        apply Prod.ext
        · change (t0 + s ^ 2 * z.1 - t0) / s ^ 2 = z.1
          field_simp [hs.ne']; ring
        · ext i
          change s⁻¹ * (v0 i + s * z.2 i - v0 i) = z.2 i
          field_simp [hs.ne']; ring
      right_inv := by
        rintro ⟨t, v⟩
        apply Prod.ext
        · change t0 + s ^ 2 * ((t - t0) / s ^ 2) = t
          field_simp [hs.ne']; ring
        · ext i
          change v0 i + s * (s⁻¹ * (v i - v0 i)) = v i
          field_simp [hs.ne']; ring }
  continuous_toFun := (contDiff_infty_parabolicAffine t0 v0 s).continuous
  continuous_invFun := by
    fun_prop

private theorem isCompact_parabolicAffine_preimage
    {d : ℕ} {t0 s : ℝ} {v0 : PDE.Vec d} (hs : 0 < s)
    {K : Set (TimeVelocity d)} (hK : IsCompact K) :
    IsCompact (parabolicAffine t0 v0 s ⁻¹' K) := by
  change IsCompact ((parabolicAffineHomeomorph t0 v0 s hs) ⁻¹' K)
  exact (parabolicAffineHomeomorph t0 v0 s hs).isCompact_preimage.mpr hK

private theorem parabolicAffine_image_preimage_eq
    {d : ℕ} {t0 s : ℝ} {v0 : PDE.Vec d} (hs : 0 < s)
    (K : Set (TimeVelocity d)) :
    parabolicAffine t0 v0 s '' (parabolicAffine t0 v0 s ⁻¹' K) = K := by
  change (parabolicAffineHomeomorph t0 v0 s hs : TimeVelocity d → TimeVelocity d) ''
    ((parabolicAffineHomeomorph t0 v0 s hs : TimeVelocity d → TimeVelocity d) ⁻¹' K) = K
  exact Set.image_preimage_eq _ (parabolicAffineHomeomorph t0 v0 s hs).surjective

private theorem normalized_target_velocity
    {d : ℕ} {r : ℝ} {v v0 : PDE.Vec d} (hr : 0 < r)
    (hv : v ∈ velocityCube v0 (r / 2)) :
    (2 / r) • (v - v0) ∈ velocityCube (0 : PDE.Vec d) 1 := by
  intro i
  have hvi := hv i
  have hscale : 0 < 2 / r := div_pos (by norm_num) hr
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, sub_zero]
  rw [abs_mul, abs_of_pos hscale]
  calc
    (2 / r) * |v i - v0 i| < (2 / r) * (r / 2) :=
      mul_lt_mul_of_pos_left hvi hscale
    _ = 1 := by field_simp [hr.ne']

private theorem physical_target_from_normalized_velocity
    {d : ℕ} {r : ℝ} {v v0 : PDE.Vec d} (hr : 0 < r) :
    v0 + (r / 2) • ((2 / r) • (v - v0)) = v := by
  ext i
  change v0 i + (r / 2) * ((2 / r) * (v i - v0 i)) = v i
  field_simp [hr.ne']
  ring

/-- The normalized source-aware local Harnack estimate at every positive
physical radius, with the same constants and physical source norm. -/
theorem exists_source_local_parabolic_harnack
    (d : Nat) (hd : 1 <= d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam <= Lam) :
    ∃ hBox C : Real, 0 < hBox ∧ hBox <= 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity d)) (B : CoefficientField d)
        (q F : TimeVelocity d -> Real) (t0 : Real) (v0 : PDE.Vec d) (r : Real),
        0 < r -> IsCompact K -> K ⊆ U -> IsOpen U ->
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ K ->
        IsContinuousCoefficientOn B U -> ContDiffOn Real 2 q U ->
        ContinuousOn F U -> IsNonnegativeOn q K ->
        HasLowerEllipticityOn lam B K -> HasUpperEllipticityOn Lam B K ->
        (∀ x ∈ K, parabolicOperator B q x = F x) ->
        ∀ v : PDE.Vec d, v ∈ velocityCube v0 (r / 2) ->
          hBox * q (t0, v0) <= q (t0 + r ^ 2, v) +
            C * r ^ ((d : Real) / ((d : Real) + 1)) *
              parabolicLpNormOn d F K := by
  obtain ⟨hBox, C, hhBox0, hhBox1, hC, hnormalized⟩ :=
    exists_source_local_parabolic_harnack_nonnegative d hd lam hlam Lam hlamLam
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F t0 v0 r hr hK hKU hU hbox hB hq hF hnonneg hlower hupper heq v hv
  let s : ℝ := r / 2
  let a : TimeVelocity d → TimeVelocity d := parabolicAffine (t0 - r ^ 2) v0 s
  let KHat : Set (TimeVelocity d) := a ⁻¹' K
  let UHat : Set (TimeVelocity d) := a ⁻¹' U
  let BHat : CoefficientField d := pullbackCoefficient B (t0 - r ^ 2) v0 s
  let qHat : TimeVelocity d → ℝ := pullbackScalar q (t0 - r ^ 2) v0 s
  let FHat : TimeVelocity d → ℝ := fun z ↦ s ^ 2 * F (a z)
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hmapK : MapsTo a KHat K := mapsTo_preimage _ _
  have hmapU : MapsTo a UHat U := mapsTo_preimage _ _
  have hKHat : IsCompact KHat := by
    dsimp [KHat, a]
    exact isCompact_parabolicAffine_preimage hs hK
  have hUHat : IsOpen UHat := by
    dsimp [UHat, a]
    exact hU.preimage (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous
  have hboxHat : parabolicClosedBox 2 2 0 0 ⊆ KHat := by
    intro z hz
    change a z ∈ K
    apply hbox
    have hz' : z ∈ parabolicAffine (t0 - r ^ 2) v0 (r / 2) ⁻¹'
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 := by
      rw [parabolicAffine_preimage_localHarnackClosedBox hr]
      exact hz
    simpa [s] using hz'
  have hBHat : IsContinuousCoefficientOn BHat UHat := by
    exact hB.pullback hmapU
  have hqHat : ContDiffOn ℝ 2 qHat UHat := by
    exact ContDiffOn.pullbackScalar hq hmapU
  have hFHat : ContinuousOn FHat UHat := by
    exact continuousOn_const.mul
      (hF.comp (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous.continuousOn hmapU)
  have hnonnegHat : IsNonnegativeOn qHat KHat := by
    exact hnonneg.pullbackScalar hmapK
  have hlowerHat : HasLowerEllipticityOn lam BHat KHat := by
    exact hlower.pullback hmapK
  have hupperHat : HasUpperEllipticityOn Lam BHat KHat := by
    exact hupper.pullback hmapK
  have heqHat : ∀ z ∈ KHat, parabolicOperator BHat qHat z = FHat z := by
    intro z hz
    have hzU : z ∈ UHat := by
      change a z ∈ U
      exact hKU (hmapK hz)
    rw [parabolicOperator_pullbackScalar
      (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmapU hzU))]
    change s ^ 2 * parabolicOperator B q (a z) = s ^ 2 * F (a z)
    rw [heq (a z) (hmapK hz)]
  let w : PDE.Vec d := (2 / r) • (v - v0)
  have hw : w ∈ velocityCube (0 : PDE.Vec d) 1 := by
    exact normalized_target_velocity hr hv
  have hphysical : v0 + (r / 2) • w = v := by
    exact physical_target_from_normalized_velocity hr
  have hKHatUHat : KHat ⊆ UHat := by
    exact Set.preimage_mono hKU
  have hnormalizedOut := hnormalized KHat UHat BHat qHat FHat hKHat hKHatUHat hUHat hboxHat
    hBHat hqHat hFHat hnonnegHat hlowerHat hupperHat heqHat w hw
  have hsource : qHat (4, (0 : PDE.Vec d)) = q (t0, v0) := by
    dsimp [qHat, s]
    rw [parabolicAffine_localHarnack_source]
  have hterminal : qHat (8, w) = q (t0 + r ^ 2, v) := by
    dsimp [qHat, s]
    rw [parabolicAffine_localHarnack_terminal, hphysical]
  have hnorm : parabolicLpNormOn d FHat KHat =
      s ^ ((d : Real) / ((d : Real) + 1)) * parabolicLpNormOn d F K := by
    rw [parabolicLpNormOn_pullback (t0 - r ^ 2) v0 hs F KHat]
    rw [show parabolicAffine (t0 - r ^ 2) v0 s '' KHat = K by
      dsimp [KHat, a]
      exact parabolicAffine_image_preimage_eq hs K]
  let p : ℝ := (d : Real) / ((d : Real) + 1)
  have hp : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscale : s ^ p ≤ r ^ p := by
    exact Real.rpow_le_rpow hs.le (by dsimp [s]; linarith) hp
  have hnormnonneg : 0 ≤ parabolicLpNormOn d F K := ENNReal.toReal_nonneg
  have herror : C * (s ^ p * parabolicLpNormOn d F K) ≤
      C * r ^ p * parabolicLpNormOn d F K := by
    calc
      C * (s ^ p * parabolicLpNormOn d F K) =
          C * s ^ p * parabolicLpNormOn d F K := by ring
      _ ≤ C * r ^ p * parabolicLpNormOn d F K := by
        gcongr
  calc
    hBox * q (t0, v0) = hBox * qHat (4, (0 : PDE.Vec d)) := by rw [hsource]
    _ ≤ qHat (8, w) + C * parabolicLpNormOn d FHat KHat := hnormalizedOut
    _ = q (t0 + r ^ 2, v) + C * (s ^ p * parabolicLpNormOn d F K) := by
      rw [hterminal, hnorm]
    _ ≤ q (t0 + r ^ 2, v) + C * r ^ p * parabolicLpNormOn d F K := by
      linarith

end HypoellipticAleksandrov.Parabolic
