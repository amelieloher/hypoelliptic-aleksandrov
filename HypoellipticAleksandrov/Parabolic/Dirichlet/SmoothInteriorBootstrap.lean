/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalC12Representative
public import HypoellipticAleksandrov.Parabolic.ContDiffTwoAEGluing
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.Parabolic.ScalarJetPointGermCongruence
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentativeUnique

/-!
# Smooth interior bootstrap

This module glues local classical representatives of the supplied reverse-time
variational solution into one original-time representative on the full open
time--velocity cylinder. The representative is scalar `C¹,²`, satisfies the
original-time equation pointwise, and retains the selected local weak jets
almost everywhere.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set MeasureTheory
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

noncomputable section

/-- The supplied variational solution has one original-time representative
that is scalar `C¹,²` in the full interior, satisfies the original-time PDE
pointwise, and retains the selected local weak jets almost everywhere. -/
theorem exists_smoothInteriorBootstrap
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
      IsScalarC12On w (Set.Ioo r₀ r₁ ×ˢ Ω) ∧
      (∀ z ∈ Set.Ioo r₀ r₁ ×ˢ Ω,
        scalarTimeDerivative w z +
              (∑ i : Fin d, ∑ j : Fin d,
                a z.1 z.2 i j * scalarSpatialHessian w z i j) +
            (∑ j : Fin d,
              b z.1 z.2 j * scalarSpatialGradient w z j) +
          c z.1 z.2 * w z = F z.1 z.2) ∧
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
          scalarTimeDerivative w =ᵐ[
            timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] J.timeDeriv ∧
          (∀ j : Fin d,
            (fun z => scalarSpatialGradient w z j) =ᵐ[
              timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)]
              fun z => J.velocityGrad z j) ∧
          ∀ i j : Fin d,
            (fun z => scalarSpatialHessian w z i j) =ᵐ[
              timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)]
              fun z => J.velocityHessian z j i := by
  classical
  obtain ⟨w₀, hw₀mem, hw₀slice, hw₀local⟩ :=
    exists_originalTimeValueRepresentative_localL2StrongJets hd r₀ r₁ h₀₁
      hΩ hΩbounded lam Lam hlam hlamLam a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hUpper hcNonpos initial u g hdu hu
  let Q : Set (TimeVelocity d) := Set.Ioo r₀ r₁ ×ˢ Ω
  have hQopen : IsOpen Q := isOpen_Ioo.prod hΩ
  have hlocal : ∀ z : Q, ∃ (V : Set (TimeVelocity d)) (v : TimeVelocity d → ℝ),
      IsOpen V ∧ (z : TimeVelocity d) ∈ V ∧ V ⊆ Q ∧ ContDiff ℝ 2 v ∧
      v =ᵐ[timeVelocityVolumeOn V] w₀ ∧
      ∀ x ∈ V,
        scalarTimeDerivative v x +
              (∑ i : Fin d, ∑ j : Fin d,
                a x.1 x.2 i j * scalarSpatialHessian v x i j) +
            (∑ j : Fin d, b x.1 x.2 j * scalarSpatialGradient v x j) +
          c x.1 x.2 * v x = F x.1 x.2 := by
    intro z
    have hztime := z.property.1
    have hzspace := z.property.2
    obtain ⟨hzlo, hzhi⟩ := hztime
    let q₀ : ℝ := (r₀ + (z : TimeVelocity d).1) / 2
    let s₀ : ℝ := (q₀ + (z : TimeVelocity d).1) / 2
    let q₁ : ℝ := ((z : TimeVelocity d).1 + r₁) / 2
    let s₁ : ℝ := ((z : TimeVelocity d).1 + q₁) / 2
    have hrq₀ : r₀ < q₀ := by dsimp [q₀]; linarith
    have hq₀s₀ : q₀ < s₀ := by dsimp [s₀, q₀]; linarith
    have hs₀z : s₀ < (z : TimeVelocity d).1 := by dsimp [s₀, q₀]; linarith
    have hz_s₁ : (z : TimeVelocity d).1 < s₁ := by dsimp [s₁, q₁]; linarith
    have hs₁q₁ : s₁ < q₁ := by dsimp [s₁, q₁]; linarith
    have hq₁r : q₁ < r₁ := by dsimp [q₁]; linarith
    have hsingleton : ({(z : TimeVelocity d).2} : Set (PDE.Vec d)) ⊆ Ω := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hzspace
    obtain ⟨O₀, hO₀open, hzO₀, hO₀Ω, hO₀compact⟩ :=
      exists_open_between_and_isCompact_closure
        (isCompact_singleton : IsCompact ({(z : TimeVelocity d).2} : Set (PDE.Vec d)))
        hΩ hsingleton
    have hsingletonO₀ : ({(z : TimeVelocity d).2} : Set (PDE.Vec d)) ⊆ O₀ := hzO₀
    obtain ⟨O, hOopen, hzO, hOO₀, hOcompact⟩ :=
      exists_open_between_and_isCompact_closure
        (isCompact_singleton : IsCompact ({(z : TimeVelocity d).2} : Set (PDE.Vec d)))
        hO₀open hsingletonO₀
    have hO₀ne : O₀.Nonempty :=
      ⟨(z : TimeVelocity d).2, hzO₀ (Set.mem_singleton _)⟩
    have hOne : O.Nonempty :=
      ⟨(z : TimeVelocity d).2, hzO (Set.mem_singleton _)⟩
    obtain ⟨J, rho, hrho, v, hJw, hSsub, hvC2, hvC12, hvw, ht, hg, hh, hpde⟩ :=
      exists_localC12Representative_of_valueRepresentative hd
        r₀ q₀ s₀ s₁ q₁ r₁ h₀₁ hrq₀ hq₀s₀
        (hs₀z.trans hz_s₁) hs₁q₁ hq₁r hΩ hΩbounded
        hO₀open hO₀ne hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
        lam Lam hlam hlamLam a b c haSmooth hbSmooth hcSmooth hLower hUpper hcNonpos
        F hFSmooth initial u g hdu hu w₀ hw₀mem hw₀slice
    let V := Metric.thickening rho (Set.Icc s₀ s₁ ×ˢ closure O)
    have hzTarget : (z : TimeVelocity d) ∈ Set.Icc s₀ s₁ ×ˢ closure O :=
      ⟨⟨hs₀z.le, hz_s₁.le⟩, subset_closure (hzO (Set.mem_singleton _))⟩
    have hzV : (z : TimeVelocity d) ∈ V := Metric.self_subset_thickening hrho _ hzTarget
    refine ⟨V, v, Metric.isOpen_thickening, hzV, ?_, hvC2, hvw, hpde⟩
    exact hSsub.trans (Set.prod_mono (Set.Ioo_subset_Ioo hrq₀.le hq₁r.le)
      (fun y hy => hO₀Ω (subset_closure hy)))
  choose V v hVopen hzV hVQ hvC2 hvAE hpde using hlocal
  obtain ⟨w, hwC2, hww₀, hwv⟩ :=
    exists_contDiffOn_two_gluing V v hVopen hzV hVQ hvC2 hvAE
  have hwC12 : IsScalarC12On w Q :=
    isScalarC12On_of_isOpen_contDiffOn_two hQopen hwC2
  have hwmem : MemLp w (2 : ℝ≥0∞) (timeVelocityVolumeOn Q) :=
    hw₀mem.ae_eq hww₀.symm
  have hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y := by
    have hprod : (volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω) =
        timeVelocityVolumeOn Q := by
      rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
      simpa only [Q, PDE.volumeOn] using Measure.prod_restrict
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure (PDE.Vec d)))
          (Set.Ioo r₀ r₁) Ω
    have hcurry := Measure.ae_ae_eq_curry_of_prod (hprod ▸ hww₀)
    filter_upwards [hcurry, hw₀slice] with r hraw hs
    exact hraw.trans hs
  have hpdeGlobal : ∀ z ∈ Q,
      scalarTimeDerivative w z +
            (∑ i : Fin d, ∑ j : Fin d,
              a z.1 z.2 i j * scalarSpatialHessian w z i j) +
          (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient w z j) +
        c z.1 z.2 * w z = F z.1 z.2 := by
    intro z hz
    let zQ : Q := ⟨z, hz⟩
    have hEq : w =ᶠ[nhds z] v zQ :=
      (hVopen zQ).eventually_mem (hzV zQ) |>.mono (fun _ hy => hwv zQ hy)
    have hwAt : ContDiffAt ℝ 2 w z := hwC2.contDiffAt (hQopen.mem_nhds hz)
    obtain ⟨ht, hg, hh⟩ := scalarJet_eqAt_of_eventuallyEq hwAt (hvC2 zQ).contDiffAt hEq
    have hvval : w z = v zQ z := hEq.eq_of_nhds
    simpa [ht, hg, hh, hvval] using hpde zQ z (hzV zQ)
  refine ⟨w, hwmem, hwslice, hwC12, hpdeGlobal, ?_⟩
  intro s₀ s₁ O hr₀s₀ hs₀s₁ hs₁r₁ hOopen hOne hOcompact hOΩ
  let q₀ : ℝ := (r₀ + s₀) / 2
  let q₁ : ℝ := (s₁ + r₁) / 2
  have hrq₀ : r₀ < q₀ := by dsimp [q₀]; linarith
  have hq₀s₀ : q₀ < s₀ := by dsimp [q₀]; linarith
  have hs₁q₁ : s₁ < q₁ := by dsimp [q₁]; linarith
  have hq₁r : q₁ < r₁ := by dsimp [q₁]; linarith
  obtain ⟨O₀, hO₀open, hOO₀, hO₀Ω, hO₀compact⟩ :=
    exists_open_between_and_isCompact_closure hOcompact hΩ hOΩ
  have hO₀ne : O₀.Nonempty := hOne.mono (subset_closure.trans hOO₀)
  obtain ⟨Jouter, rho, hrho, vloc, hJw₀, hSsub, hvlocC2, hvlocC12,
      hvlocw₀, htloc, hgloc, hhloc, hpdeloc⟩ :=
    exists_localC12Representative_of_valueRepresentative hd
      r₀ q₀ s₀ s₁ q₁ r₁ h₀₁ hrq₀ hq₀s₀ hs₀s₁
      hs₁q₁ hq₁r hΩ hΩbounded hO₀open hO₀ne hO₀compact hO₀Ω
      hOopen hOne hOcompact hOO₀ lam Lam hlam hlamLam a b c haSmooth hbSmooth
      hcSmooth hLower hUpper hcNonpos F hFSmooth initial u g hdu hu w₀ hw₀mem hw₀slice
  let B : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  have hBQ : B ⊆ Q := Set.prod_mono (Set.Ioo_subset_Ioo hr₀s₀.le hs₁r₁.le)
    (fun y hy => hOΩ (subset_closure hy))
  have hBS : B ⊆ Metric.thickening rho (Set.Icc s₀ s₁ ×ˢ closure O) := by
    intro z hz
    exact Metric.self_subset_thickening hrho _
      ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
  let J := Jouter.restrict (hBS.trans hSsub)
  have hwvloc : EqOn w vloc B := by
    have hae : w =ᵐ[timeVelocityVolumeOn B] vloc :=
      (hww₀.filter_mono (ae_mono (Measure.restrict_mono_set volume hBQ))).trans
        (hvlocw₀.filter_mono (ae_mono (Measure.restrict_mono_set volume hBS))).symm
    rw [timeVelocityVolumeOn] at hae
    exact Measure.eqOn_open_of_ae_eq hae (isOpen_Ioo.prod hOopen)
      (hwC12.continuousOn.mono hBQ) (hvlocC2.continuous.continuousOn)
  have hjetAE : ∀ᵐ z ∂timeVelocityVolumeOn B,
      scalarTimeDerivative w z = scalarTimeDerivative vloc z ∧
      scalarSpatialGradient w z = scalarSpatialGradient vloc z ∧
      scalarSpatialHessian w z = scalarSpatialHessian vloc z := by
    filter_upwards [ae_restrict_mem (isOpen_Ioo.prod hOopen).measurableSet] with z hz
    have hevent : w =ᶠ[nhds z] vloc :=
      (isOpen_Ioo.prod hOopen).eventually_mem hz |>.mono (fun _ hy => hwvloc hy)
    exact scalarJet_eqAt_of_eventuallyEq
      (hwC2.contDiffAt (hQopen.mem_nhds (hBQ hz))) hvlocC2.contDiffAt hevent
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · exact (hJw₀.filter_mono (ae_mono (Measure.restrict_mono_set volume (hBS.trans hSsub)))).trans
      (hww₀.filter_mono (ae_mono (Measure.restrict_mono_set volume hBQ))).symm
  · filter_upwards [hjetAE, htloc.filter_mono
        (ae_mono (Measure.restrict_mono_set volume hBS))] with z hz hzt
    exact hz.1.trans hzt
  · intro j
    filter_upwards [hjetAE, (hgloc j).filter_mono
        (ae_mono (Measure.restrict_mono_set volume hBS))] with z hz hzg
    exact congrFun hz.2.1 j |>.trans hzg
  · intro i j
    filter_upwards [hjetAE, (hhloc i j).filter_mono
        (ae_mono (Measure.restrict_mono_set volume hBS))] with z hz hzh
    exact congrFun (congrFun hz.2.2 i) j |>.trans hzh

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
