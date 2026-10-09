module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierUniformLimit
public import HypoellipticAleksandrov.Parabolic.WeakRepresentativeLocalization
public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Localized jets for weak-solution mollifier convergence

This module packages the concrete cutoff localization of a selected local
parabolic weak jet.  It derives compact-uniform convergence of its literal
global mollifications to a supplied continuous representative.  No equation,
coefficient, residual, sign, or kernel-localization assertion is made here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- A selected local parabolic weak jet together with its concrete compactly
supported global cutoff extension around a compact carrier. -/
structure LocalizedParabolicJet
    (d : Nat) (U K : Set (TimeVelocity d)) (u : TimeVelocity d → Real) where
  V : Set (TimeVelocity d)
  W : Set (TimeVelocity d)
  w : ParabolicW12Function d W (parabolicExponent d)
  b : TimeVelocity d → Real
  g : ParabolicW12Function d Set.univ (parabolicExponent d)
  V_open : IsOpen V
  V_closure_compact : IsCompact (closure V)
  K_subset_V : K ⊆ V
  W_open : IsOpen W
  W_closure_compact : IsCompact (closure W)
  closure_V_subset_W : closure V ⊆ W
  closure_W_subset_U : closure W ⊆ U
  w_ae_eq_u : w.toFun =ᵐ[timeVelocityVolumeOn W] u
  b_smooth : ContDiff Real (⊤ : ℕ∞) b
  b_compact : HasCompactSupport b
  b_tsupport_subset_W : tsupport b ⊆ W
  b_one_near_closure_V : ∀ᶠ z in 𝓝ˢ (closure V), b z = 1
  g_is_cutoff :
    g = w.mulContDiffHasCompactSupport_univ
      (by simp [parabolicExponent]) b_smooth b_compact W_open b_tsupport_subset_W
  g_toFun_eq_near_closure_V : g.toFun =ᶠ[𝓝ˢ (closure V)] w.toFun
  g_timeDeriv_eq_near_closure_V : g.timeDeriv =ᶠ[𝓝ˢ (closure V)] w.timeDeriv
  g_velocityGrad_eq_near_closure_V :
    g.velocityGrad =ᶠ[𝓝ˢ (closure V)] w.velocityGrad
  g_velocityHessian_eq_near_closure_V :
    g.velocityHessian =ᶠ[𝓝ˢ (closure V)] w.velocityHessian

namespace LocalizedParabolicJet

/-- The selected cutoff jet agrees with its local jet on an open plateau that
contains the closure of the compact carrier. -/
theorem exists_open_plateau
    {d : Nat} {U K : Set (TimeVelocity d)} {u : TimeVelocity d → Real}
    (J : LocalizedParabolicJet d U K u) :
    ∃ O : Set (TimeVelocity d),
      IsOpen O ∧ closure J.V ⊆ O ∧ O ⊆ J.W ∧
      EqOn J.g.toFun J.w.toFun O ∧
      EqOn J.g.timeDeriv J.w.timeDeriv O ∧
      EqOn J.g.velocityGrad J.w.velocityGrad O ∧
      EqOn J.g.velocityHessian J.w.velocityHessian O := by
  obtain ⟨Ob, hObOpen, hclosureOb, hbOb⟩ :=
    eventually_nhdsSet_iff_exists.mp J.b_one_near_closure_V
  obtain ⟨OtoFun, hOtoFunOpen, hclosureOtoFun, hgOtoFun⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_toFun_eq_near_closure_V
  obtain ⟨Otime, hOtimeOpen, hclosureOtime, hgOtime⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_timeDeriv_eq_near_closure_V
  obtain ⟨Ograd, hOgradOpen, hclosureOgrad, hgOgrad⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_velocityGrad_eq_near_closure_V
  obtain ⟨Ohessian, hOhessianOpen, hclosureOhessian, hgOhessian⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_velocityHessian_eq_near_closure_V
  let O := Ob ∩ (OtoFun ∩ (Otime ∩ (Ograd ∩ Ohessian)))
  refine ⟨O, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hObOpen.inter (hOtoFunOpen.inter
      (hOtimeOpen.inter (hOgradOpen.inter hOhessianOpen)))
  · intro z hz
    exact ⟨hclosureOb hz, hclosureOtoFun hz,
      hclosureOtime hz, hclosureOgrad hz, hclosureOhessian hz⟩
  · intro z hz
    have hbz : J.b z = 1 := hbOb z hz.1
    have hsupport : z ∈ Function.support J.b := by
      change J.b z ≠ 0
      rw [hbz]
      exact one_ne_zero
    exact J.b_tsupport_subset_W (subset_tsupport (f := J.b) hsupport)
  · intro z hz
    exact hgOtoFun z hz.2.1
  · intro z hz
    exact hgOtime z hz.2.2.1
  · intro z hz
    exact hgOgrad z hz.2.2.2.1
  · intro z hz
    exact hgOhessian z hz.2.2.2.2

end LocalizedParabolicJet

namespace ParabolicW12Loc

/-- A local parabolic weak function has a concrete cutoff jet whose literal
mollifications converge uniformly on a compact carrier to any supplied
continuous representative of its restricted-volume almost-everywhere class. -/
theorem exists_localizedJet_mollifications_tendstoUniformlyOn
    (d : Nat) (hd : 1 ≤ d)
    {U K : Set (TimeVelocity d)} {u q : TimeVelocity d → Real}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : ParabolicW12Loc U (parabolicExponent d) u)
    (hq : ContinuousOn q U)
    (hqu : q =ᵐ[timeVelocityVolumeOn U] u) :
    ∃ J : LocalizedParabolicJet d U K u,
      TendstoUniformlyOn
        (fun n z =>
          parabolicConvolution J.g.toFun (parabolicMollifier d n) z)
        q atTop K := by
  obtain ⟨V, hVOpen, hKV, hclosureVU, hVCompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWOpen, hWCompact, hclosureVW, hclosureWU⟩ :=
    exists_open_compact_closure_collar hU hVOpen hVCompact hclosureVU
  obtain ⟨w, hwu⟩ :=
    hu.exists_parabolicW12Function hWOpen hWCompact hclosureWU
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]
  obtain ⟨b, hbSmooth, hbCompact, hbOne, hbW, htoFun, htime, hgrad, hhessian⟩ :=
    exists_smooth_compact_cutoff_mul_eventuallyEq_jet hVCompact hWOpen hWCompact
      hclosureVW w hp
  let J : LocalizedParabolicJet d U K u :=
    { V := V
      W := W
      w := w
      b := b
      g := w.mulContDiffHasCompactSupport_univ
        (by simp [parabolicExponent]) hbSmooth hbCompact hWOpen hbW
      V_open := hVOpen
      V_closure_compact := hVCompact
      K_subset_V := hKV
      W_open := hWOpen
      W_closure_compact := hWCompact
      closure_V_subset_W := hclosureVW
      closure_W_subset_U := hclosureWU
      w_ae_eq_u := hwu
      b_smooth := hbSmooth
      b_compact := hbCompact
      b_tsupport_subset_W := hbW
      b_one_near_closure_V := hbOne
      g_is_cutoff := by rfl
      g_toFun_eq_near_closure_V := by
        simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! htoFun
      g_timeDeriv_eq_near_closure_V := by
        simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! htime
      g_velocityGrad_eq_near_closure_V := by
        simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! hgrad
      g_velocityHessian_eq_near_closure_V := by
        simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! hhessian }
  have hJCompact : HasCompactSupport J.g.toFun := by
    change IsCompact (tsupport J.g.toFun)
    refine IsCompact.of_isClosed_subset J.b_compact (isClosed_tsupport (f := J.g.toFun)) ?_
    rw [J.g_is_cutoff]
    simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ_toFun] using
      (tsupport_mul_subset_left (f := J.b) (g := J.w.toFun))
  obtain ⟨r, hrContinuous, hrUniform, hrg⟩ :=
    J.g.exists_continuousOn_tendstoUniformlyOn_ae_eq_toFun_parabolicConvolution
      hd hJCompact (closure J.V) J.V_closure_compact
  obtain ⟨O, hOOpen, hclosureVO, hOW, hgwo, -, -, -⟩ := J.exists_open_plateau
  have hrgV : r =ᵐ[timeVelocityVolumeOn J.V] J.g.toFun :=
    hrg.filter_mono <| ae_mono <|
      Measure.restrict_mono_set volume subset_closure
  have hgwV : J.g.toFun =ᵐ[timeVelocityVolumeOn J.V] J.w.toFun := by
    filter_upwards [ae_restrict_mem J.V_open.measurableSet] with z hzV
    exact hgwo (hclosureVO (subset_closure hzV))
  have hVW : J.V ⊆ J.W := subset_closure.trans J.closure_V_subset_W
  have hwuV : J.w.toFun =ᵐ[timeVelocityVolumeOn J.V] u :=
    J.w_ae_eq_u.filter_mono <| ae_mono <|
      Measure.restrict_mono_set volume hVW
  have hVU : J.V ⊆ U :=
    subset_closure.trans (J.closure_V_subset_W.trans
      (subset_closure.trans J.closure_W_subset_U))
  have hquV : q =ᵐ[timeVelocityVolumeOn J.V] u :=
    hqu.filter_mono <| ae_mono <|
      Measure.restrict_mono_set volume hVU
  have hrquV : r =ᵐ[timeVelocityVolumeOn J.V] q :=
    (hrgV.trans hgwV).trans (hwuV.trans hquV.symm)
  have hrq : EqOn r q J.V :=
    Measure.eqOn_open_of_ae_eq hrquV J.V_open
      (hrContinuous.mono subset_closure) (hq.mono hVU)
  refine ⟨J, ?_⟩
  exact (hrUniform.mono (J.K_subset_V.trans subset_closure)).congr_right
    fun z hzK => hrq (J.K_subset_V hzK)

end ParabolicW12Loc

end HypoellipticAleksandrov.Parabolic
