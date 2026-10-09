module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeInteriorGeometry
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentativeUnique
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeInteriorCoefficientMajorant
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliTimeDerivative
public import HypoellipticAleksandrov.Parabolic.ParabolicW12TimeReflection

/-!
# Original-time local L2 strong jets

This file reflects the interior reverse-time weak Hessian and time derivative
back to the original-time cylinder.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set IsReverseTimeVariationalEnergySolution
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- A supplied global original-time value representative admits a local
anisotropic `L²` weak jet satisfying the literal original-time equation. -/
theorem exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ s₀ s₁ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hr₀s₀ : r₀ < s₀)
    (hs₀s₁ : s₀ < s₁)
    (hs₁r₁ : s₁ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O)
    (hOnonempty : O.Nonempty)
    (hOcompact : IsCompact (closure O))
    (hOΩ : closure O ⊆ Ω)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (w : TimeVelocity d → ℝ)
    (hwmem : MemLp w (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    ∃ J : ParabolicW12Function d
        (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞),
      J.toFun =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w ∧
      ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
        J.timeDeriv z +
              (∑ i : Fin d, ∑ j : Fin d,
                a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d,
              b z.1 z.2 j * J.velocityGrad z j) +
          c z.1 z.2 * J.toFun z =
        F z.1 z.2 := by
  obtain ⟨Kη, η, Kχ, χ, τ₀, τ₁, τ₂, τ₃, hχΩ, rfl, rfl, rfl, rfl,
      hτ₀, hτ₀τ₁, hτ₁τ₂, hτ₂τ₃, hτ₃⟩ :=
    exists_originalTimeInteriorCaccioppoliGeometry
      r₀ s₀ s₁ r₁ hr₀s₀ hs₀s₁ hs₁r₁ hΩ hOcompact hOΩ
  obtain ⟨δ, hδ, hcarrier, hpredecessor⟩ :=
    exists_gradientCoord_representatives_hessian_timeDerivative_uniform_interior_caccioppoli
        hd r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOnonempty subset_closure η χ
  obtain ⟨M, hM, hA, hB, hBD, hq, hqD, hfD⟩ :=
    exists_reverseTimeInteriorCoefficientMajorant r₀ r₁ χ δ hcarrier
      a b c F haSmooth hbSmooth hcSmooth hFSmooth
  obtain ⟨C_cac, hC_cac, hrun⟩ :=
    hpredecessor _ _ _ _ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃
      lam Lam M hlam hlamLam hM
  obtain ⟨G, hG, H, hHmem, hHweak, _hHbound, U, hU, hUslice, hUweak,
      hWmem, hWweak⟩ :=
    hrun a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu
  let Q : Set (TimeVelocity d) := Set.Ioo (r₁ - s₁) (r₁ - s₀) ×ˢ O
  let W : TimeVelocity d → ℝ := fun z =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
    (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
    reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
    reverseTimeScalarCoefficient r₁ F z.1 z.2
  have htime : Set.Ioo (r₁ - s₁) (r₁ - s₀) ⊆
      reverseTimeOpenInterval (r₁ - r₀) := by
    intro τ hτ
    exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
      hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
  have hOΩ' : O ⊆ Ω := subset_closure.trans hOΩ
  have hQglobal : Q ⊆ reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω :=
    Set.prod_mono htime hOΩ'
  have hUlocal : ParabolicMemLpOn Q (2 : ℝ≥0∞) U :=
    hU.mono_measure (Measure.restrict_mono_set volume hQglobal)
  have hGlocal : ∀ j, ParabolicMemLpOn Q (2 : ℝ≥0∞) (G j) := fun j =>
    (hG j).mono_measure (Measure.restrict_mono_set volume hQglobal)
  let Jrev : ParabolicW12Function d Q (2 : ℝ≥0∞) :=
    { toFun := U
      timeDeriv := W
      velocityGrad := fun z j => G j z
      velocityHessian := H
      memLp := hUlocal
      timeDeriv_memLp := hWmem
      velocityGrad_memLp := hGlocal
      velocityHessian_memLp := hHmem
      hasWeakTimeDeriv := hWweak
      hasWeakVelocityPartialDeriv := hUweak
      hasWeakVelocitySecondPartialDeriv := hHweak }
  have hQmeas : MeasurableSet Q := measurableSet_Ioo.prod hOopen.measurableSet
  have hQreflect : reverseTimeMap r₁ ⁻¹' Q = Set.Ioo s₀ s₁ ×ˢ O := by
    simpa only [Q] using reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ s₀ s₁ O
  let Jreflected := Jrev.timeReflect r₁ hQmeas
  let J : ParabolicW12Function d (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) :=
    { toFun := fun z => U (reverseTimeMap r₁ z)
      timeDeriv := fun z => -W (reverseTimeMap r₁ z)
      velocityGrad := fun z j => G j (reverseTimeMap r₁ z)
      velocityHessian := fun z => H (reverseTimeMap r₁ z)
      memLp := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.memLp
      timeDeriv_memLp := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.timeDeriv_memLp
      velocityGrad_memLp := by
        intro i
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.velocityGrad_memLp i
      velocityHessian_memLp := by
        intro i j
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.velocityHessian_memLp i j
      hasWeakTimeDeriv := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.hasWeakTimeDeriv
      hasWeakVelocityPartialDeriv := by
        intro i
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.hasWeakVelocityPartialDeriv i
      hasWeakVelocitySecondPartialDeriv := by
        intro i j
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect] using
          Jreflected.hasWeakVelocitySecondPartialDeriv i j }
  refine ⟨J, ?_, ?_⟩
  · have hUreflectMem : MemLp (fun z => U (reverseTimeMap r₁ z)) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) := by
      have hglobal := reverseTimeMap_measurePreserving_restrict (d := d) r₁
        (U := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)
        ((measurableSet_Ioo.prod hΩ.measurableSet))
      have hglobalSet : reverseTimeMap r₁ ⁻¹'
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω) =
          Set.Ioo r₀ r₁ ×ˢ Ω := by
        simpa only [reverseTimeOpenInterval, sub_self] using
          reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ r₀ r₁ Ω
      simpa only [Function.comp_def, hglobalSet] using hU.comp_measurePreserving hglobal
    have hUreflectSlice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => U (reverseTimeMap r₁ (r, y))) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y := by
      have hreflection : MeasurePreserving (fun r : ℝ => r₁ - r)
          (volume : Measure ℝ) volume := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
            (Measure.measurePreserving_neg (volume : Measure ℝ))
      have hpreimage : (fun r : ℝ => r₁ - r) ⁻¹' Set.Ioo 0 (r₁ - r₀) =
          Set.Ioo r₀ r₁ := by
        rw [preimage_const_sub_Ioo]
        congr 1 <;> ring
      have htimeReflect : MeasurePreserving (fun r : ℝ => r₁ - r)
          (volume.restrict (Set.Ioo r₀ r₁)) (reverseTimeVolume (r₁ - r₀)) := by
        rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpreimage]
        exact hreflection.restrict_preimage isOpen_Ioo.measurableSet
      filter_upwards [htimeReflect.quasiMeasurePreserving.ae hUslice] with r hr
      simpa only [reverseTimeMap_apply] using hr.1
    have hUw := originalTimeL2V_value_product_representative_ae_eq
      r₀ r₁ hΩ u (fun z => U (reverseTimeMap r₁ z)) w
      hUreflectMem.aemeasurable hwmem.aemeasurable hUreflectSlice hwslice
    have hlocal : (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w :=
      hUw.filter_mono (ae_mono (Measure.restrict_mono_set volume (by
        exact Set.prod_mono
          (Set.Ioo_subset_Ioo hr₀s₀.le hs₁r₁.le) hOΩ')))
    change (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
      timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w
    exact hlocal
  · filter_upwards [] with z
    change -W (reverseTimeMap r₁ z) +
          (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * H (reverseTimeMap r₁ z) j i) +
        (∑ j : Fin d, b z.1 z.2 j * G j (reverseTimeMap r₁ z)) +
      c z.1 z.2 * U (reverseTimeMap r₁ z) = F z.1 z.2
    simp only [W, reverseTimeMap_apply, reverseTimeCoefficient,
      reverseTimeVectorCoefficient, reverseTimeScalarCoefficient, sub_sub_cancel]
    ring

/-- A supplied reverse-time variational solution has one global original-time
value representative admitting compatible local anisotropic `L²` weak jets. -/
theorem exists_originalTimeValueRepresentative_localL2StrongJets
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∃ w : TimeVelocity d → ℝ,
      MemLp w (2 : ℝ≥0∞)
          (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y) ∧
      ∀ (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)),
        r₀ < s₀ →
        s₀ < s₁ →
        s₁ < r₁ →
        IsOpen O →
        O.Nonempty →
        IsCompact (closure O) →
        closure O ⊆ Ω →
        ∃ J : ParabolicW12Function d
            (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞),
          J.toFun =ᵐ[
            timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w ∧
          ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
            J.timeDeriv z +
                  (∑ i : Fin d, ∑ j : Fin d,
                    a z.1 z.2 i j * J.velocityHessian z j i) +
                (∑ j : Fin d,
                  b z.1 z.2 j * J.velocityGrad z j) +
              c z.1 z.2 * J.toFun z =
            F z.1 z.2 := by
  obtain ⟨w, hwmem, hwslice⟩ :=
    exists_originalTimeL2V_value_product_representative r₀ r₁ hΩ u
  refine ⟨w, hwmem, hwslice, ?_⟩
  intro s₀ s₁ O hr₀s₀ hs₀s₁ hs₁r₁ hOopen hOnonempty hOcompact hOΩ
  exact exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    hd r₀ s₀ s₁ r₁ h₀₁ hr₀s₀ hs₀s₁ hs₁r₁ hΩ hΩbounded
    hOopen hOnonempty hOcompact hOΩ lam Lam hlam hlamLam a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial u g hdu hu
    w hwmem hwslice

end HypoellipticAleksandrov.Parabolic.Dirichlet
