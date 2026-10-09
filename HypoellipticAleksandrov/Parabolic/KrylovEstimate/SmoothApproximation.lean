module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.CompactScalarJet
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.UniformConvolution
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothDerivatives

/-! # Uniform approximation of the anisotropic scalar jet -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Filter Set
open scoped Topology

/-- Smooth functions approximate all selected scalar derivatives on interior compact sets. -/
theorem exists_smooth_scalar_jet_close
    {N : ℕ} {V K : Set (TimeVelocity N)} (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (q : TimeVelocity N → ℝ) (hq : IsScalarC12On q V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TimeVelocity N → ℝ, ContDiff ℝ 2 w ∧
      ∀ z ∈ K,
        |w z - q z| ≤ ε ∧
        |scalarTimeDerivative w z - scalarTimeDerivative q z| ≤ ε ∧
        (∀ i : Fin N, |scalarSpatialGradient w z i -
          scalarSpatialGradient q z i| ≤ ε) ∧
        (∀ i j : Fin N, |scalarSpatialHessian w z i j -
          scalarSpatialHessian q z i j| ≤ ε) := by
  obtain ⟨W, hv, hvc, ht, htc, hg, hh, ev, et, eg, eh⟩ :=
    exists_compact_continuous_scalar_jet hV hK hKV q hq
  have av := eventually_uniform_parabolicConvolution_close W.toFun hv hvc hε
  have atime := eventually_uniform_parabolicConvolution_close W.timeDeriv ht htc hε
  have ag : ∀ᶠ n in atTop, ∀ i : Fin N, ∀ z,
      |parabolicConvolution (fun y => W.velocityGrad y i) (parabolicMollifier N n) z -
        W.velocityGrad z i| ≤ ε := by
    rw [eventually_all]
    exact fun i => eventually_uniform_parabolicConvolution_close _ (hg i).1 (hg i).2 hε
  have ah : ∀ᶠ n in atTop, ∀ i j : Fin N, ∀ z,
      |parabolicConvolution (fun y => W.velocityHessian y i j)
        (parabolicMollifier N n) z - W.velocityHessian z i j| ≤ ε := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact fun j => eventually_uniform_parabolicConvolution_close _ (hh i j).1 (hh i j).2 hε
  obtain ⟨n, hn⟩ := (av.and (atime.and (ag.and ah))).exists
  let w := parabolicConvolution W.toFun (parabolicMollifier N n)
  have hs := W.contDiff_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have hw : ContDiff ℝ 2 w := hs.of_le (by simp)
  have dt := W.timeDerivative_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have dg := W.velocityGradient_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have dh := W.velocityHessian_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  refine ⟨w, hw, fun z hz => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← ev hz]
    exact hn.1 z
  · rw [scalarTimeDerivative_eq_timeDerivative w hw z, ← et hz]
    change |timeDerivative (parabolicConvolution W.toFun _) z - W.timeDeriv z| ≤ ε
    rw [dt]
    exact hn.2.1 z
  · intro i
    rw [scalarSpatialGradient_eq_velocityGradient w hw z, ← eg hz]
    change |velocityGradient (parabolicConvolution W.toFun _) z i - W.velocityGrad z i| ≤ ε
    rw [congrFun (dg i) z]
    exact hn.2.2.1 i z
  · intro i j
    rw [scalarSpatialHessian_eq_velocityHessian w hw z, ← eh hz]
    change |velocityHessian (parabolicConvolution W.toFun _) z i j -
      W.velocityHessian z i j| ≤ ε
    rw [congrFun (dh i j) z]
    exact hn.2.2.2 i j z

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
