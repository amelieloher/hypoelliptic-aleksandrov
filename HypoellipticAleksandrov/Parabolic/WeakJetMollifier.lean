module

public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import Mathlib.Analysis.Convolution

/-!
# Convolution of selected parabolic weak jets

This module smooths a global selected weak jet by right convolution against one
smooth compactly supported scalar kernel.  It records only the selected time,
velocity-gradient, and ordered velocity-Hessian commutations.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped Convolution ENNReal Topology

/-- Right convolution on time--velocity space against its literal product volume. -/
noncomputable def parabolicConvolution {d : Nat}
    (f rho : TimeVelocity d -> Real) : TimeVelocity d -> Real :=
  f ⋆[ContinuousLinearMap.mul Real Real, (volume : Measure (TimeVelocity d))] rho

/-- Right parabolic convolution of compactly supported functions has compact support. -/
theorem hasCompactSupport_parabolicConvolution
    {d : Nat} {f rho : TimeVelocity d -> Real}
    (hf : HasCompactSupport f) (hrho : HasCompactSupport rho) :
    HasCompactSupport (parabolicConvolution f rho) := by
  simpa only [parabolicConvolution] using
    hf.convolution (L := ContinuousLinearMap.mul Real Real) hrho

private theorem contDiff_translatedKernel {d : Nat} {rho : TimeVelocity d -> Real}
    (hrho : ContDiff Real (⊤ : ℕ∞) rho) (z : TimeVelocity d) :
    ContDiff Real (⊤ : ℕ∞) (fun y => rho (z - y)) := by
  simpa only [Function.comp_def, id_eq, Homeomorph.coe_subLeft] using
    hrho.comp (contDiff_const.sub contDiff_id)

private theorem hasCompactSupport_translatedKernel {d : Nat} {rho : TimeVelocity d -> Real}
    (hrho : HasCompactSupport rho) (z : TimeVelocity d) :
    HasCompactSupport (fun y => rho (z - y)) := by
  simpa only [Function.comp_def, id_eq, Homeomorph.coe_subLeft] using
    hrho.comp_homeomorph (Homeomorph.subLeft z)

private theorem fderiv_translatedKernel_apply {d : Nat} {rho : TimeVelocity d -> Real}
    (hrho : ContDiff Real (⊤ : ℕ∞) rho) (z y q : TimeVelocity d) :
    fderiv Real (fun x => rho (z - x)) y q = -fderiv Real rho (z - y) q := by
  have hmap : HasFDerivAt (fun x : TimeVelocity d => z - x)
      (-ContinuousLinearMap.id Real (TimeVelocity d)) y := by
    simpa only [sub_eq_add_neg, Pi.neg_apply, id_eq] using ((hasFDerivAt_id y).neg.const_add z)
  have hcomp := (hrho.differentiable (by simp) (z - y)).hasFDerivAt.comp y hmap
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, map_neg] using
    congrArg (fun L : TimeVelocity d →L[Real] Real => L q) hcomp.fderiv

private theorem fderiv_parabolicConvolution_eq {d : Nat}
    {u du rho : TimeVelocity d -> Real}
    {D : (TimeVelocity d -> Real) -> TimeVelocity d -> Real} (q : TimeVelocity d)
    (hweak : forall phi : TimeVelocity d -> Real,
      ContDiff Real (⊤ : ℕ∞) phi ->
      HasCompactSupport phi ->
      (∫ y, u y * D phi y) = -∫ y, du y * phi y)
    (hD : forall (z y : TimeVelocity d),
      D (fun x => rho (z - x)) y = -fderiv Real rho (z - y) q)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduLoc : LocallyIntegrable du (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) (z : TimeVelocity d) :
    fderiv Real (parabolicConvolution u rho) z q = parabolicConvolution du rho z := by
  let _ : LocallyIntegrable du (volume : Measure (TimeVelocity d)) := hduLoc
  let phi : TimeVelocity d -> Real := fun y => rho (z - y)
  have hphi : ContDiff Real (⊤ : ℕ∞) phi := contDiff_translatedKernel hrho z
  have hphiCompact : HasCompactSupport phi := hasCompactSupport_translatedKernel hrhoCompact z
  have hraw := hweak phi hphi hphiCompact
  have hleft : (∫ y, u y * D phi y) =
      -(∫ y, u y * fderiv Real rho (z - y) q) := by
    calc
      (∫ y, u y * D phi y) =
          ∫ y, -(u y * fderiv Real rho (z - y) q) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hD z y]
        ring
      _ = -(∫ y, u y * fderiv Real rho (z - y) q) := by
        rw [integral_neg]
  have hright : (∫ y, du y * phi y) = parabolicConvolution du rho z := by
    calc
      (∫ y, du y * phi y) = ∫ y, du y * rho (z - y) := by
        apply integral_congr_ae
        filter_upwards with y
        rfl
      _ = parabolicConvolution du rho z := by
        symm
        exact convolution_def (ContinuousLinearMap.mul Real Real)
  have hconv := hrhoCompact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul Real Real) huLoc (hrho.of_le (by simp)) z
  calc
    fderiv Real (parabolicConvolution u rho) z q =
        ((u ⋆[ContinuousLinearMap.precompR (TimeVelocity d)
          (ContinuousLinearMap.mul Real Real),
          (volume : Measure (TimeVelocity d))] fderiv Real rho) z) q := by
      simpa only [parabolicConvolution] using
        congrArg (fun L : TimeVelocity d →L[Real] Real => L q) hconv.fderiv
    _ = (u ⋆[ContinuousLinearMap.mul Real Real, (volume : Measure (TimeVelocity d))]
        fun a => fderiv Real rho a q) z := by
      exact convolution_precompR_apply (ContinuousLinearMap.mul Real Real) huLoc
        (hrhoCompact.fderiv Real) (hrho.continuous_fderiv (by simp)) z q
    _ = ∫ y, u y * fderiv Real rho (z - y) q := by
      exact convolution_def (ContinuousLinearMap.mul Real Real)
    _ = -(-(∫ y, u y * fderiv Real rho (z - y) q)) := by ring
    _ = -(∫ y, u y * D phi y) := by rw [hleft]
    _ = ∫ y, du y * phi y := by simp only [hraw, neg_neg]
    _ = parabolicConvolution du rho z := hright

/-- Convolution by a smooth compactly supported kernel is globally smooth. -/
theorem contDiff_parabolicConvolution
    {d : Nat} {f rho : TimeVelocity d -> Real}
    (hf : LocallyIntegrable f (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    ContDiff Real (⊤ : ℕ∞) (parabolicConvolution f rho) := by
  simpa only [parabolicConvolution] using
    hrhoCompact.contDiff_convolution_right (ContinuousLinearMap.mul Real Real) hf hrho

/-- Right convolution commutes with the selected global weak time derivative. -/
theorem timeDerivative_parabolicConvolution
    {d : Nat} {u du rho : TimeVelocity d -> Real}
    (hu : HasWeakTimeDerivOn Set.univ u du)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduLoc : LocallyIntegrable du (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    timeDerivative (parabolicConvolution u rho) = parabolicConvolution du rho := by
  funext z
  unfold timeDerivative
  apply fderiv_parabolicConvolution_eq (u := u) (du := du) (rho := rho) (1, 0)
    (D := timeDerivative) ?_ ?_ huLoc hduLoc hrho hrhoCompact z
  · intro phi hphi hphiCompact
    simpa only [Measure.restrict_univ] using hu phi hphi hphiCompact (Set.subset_univ _)
  · intro x y
    simpa only [timeDerivative] using fderiv_translatedKernel_apply hrho x y (1, 0)

/-- Right convolution commutes with every selected global weak velocity derivative. -/
theorem velocityGradient_parabolicConvolution
    {d : Nat} {u dui rho : TimeVelocity d -> Real} {i : Fin d}
    (hu : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduiLoc : LocallyIntegrable dui (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    (fun z => velocityGradient (parabolicConvolution u rho) z i) =
      parabolicConvolution dui rho := by
  funext z
  unfold velocityGradient
  apply fderiv_parabolicConvolution_eq (u := u) (du := dui) (rho := rho)
    (0, Pi.single i 1) (D := fun f z => velocityGradient f z i) ?_ ?_ huLoc hduiLoc hrho
      hrhoCompact z
  · intro phi hphi hphiCompact
    simpa only [Measure.restrict_univ] using hu phi hphi hphiCompact (Set.subset_univ _)
  · intro x y
    simpa only [velocityGradient] using
      fderiv_translatedKernel_apply hrho x y (0, Pi.single i 1)

private theorem fderiv_velocityGradient_apply {d : Nat} {f : TimeVelocity d -> Real}
    (hf : ContDiff Real 2 f) (z qi qj : TimeVelocity d) :
    fderiv Real (fun x => fderiv Real f x qi) z qj =
      fderiv Real (fderiv Real f) z qj qi := by
  have hderiv : DifferentiableAt Real (fderiv Real f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hderiv (differentiableAt_const (c := qi))]
  simp

private theorem velocityHessian_eq_fderiv_velocityGradient {d : Nat}
    {f : TimeVelocity d -> Real} {i j : Fin d} (hf : ContDiff Real 2 f)
    (z : TimeVelocity d) :
    velocityHessian f z i j =
      fderiv Real (fun x => velocityGradient f x i) z (0, Pi.single j 1) := by
  let qi : TimeVelocity d := (0, Pi.single i 1)
  let qj : TimeVelocity d := (0, Pi.single j 1)
  calc
    velocityHessian f z i j = velocityHessian f z j i := by
      exact (congrFun (congrFun (velocityHessian_isSymm hf z).eq i) j).symm
    _ = fderiv Real (fun x => fderiv Real f x qi) z qj := by
      exact (fderiv_velocityGradient_apply hf z qi qj).symm
    _ = fderiv Real (fun x => velocityGradient f x i) z (0, Pi.single j 1) := by
      rfl

/-- Right convolution commutes with the ordered selected global velocity Hessian. -/
theorem velocityHessian_parabolicConvolution
    {d : Nat} {u dui duij rho : TimeVelocity d -> Real} {i j : Fin d}
    (hui : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huij : HasWeakVelocityPartialDerivOn Set.univ j dui duij)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduiLoc : LocallyIntegrable dui (volume : Measure (TimeVelocity d)))
    (hduijLoc : LocallyIntegrable duij (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    (fun z => velocityHessian (parabolicConvolution u rho) z i j) =
      parabolicConvolution duij rho := by
  have hfirst := velocityGradient_parabolicConvolution hui huLoc hduiLoc hrho hrhoCompact
  have hsecond := velocityGradient_parabolicConvolution huij hduiLoc hduijLoc hrho hrhoCompact
  funext z
  rw [velocityHessian_eq_fderiv_velocityGradient
    ((contDiff_parabolicConvolution huLoc hrho hrhoCompact).of_le
      (WithTop.coe_le_coe.mpr le_top))]
  rw [hfirst]
  exact congrFun hsecond z

namespace ParabolicW12Function

/-- The convolution of a global selected jet value is smooth. -/
theorem contDiff_convolution {d : Nat} {p : ENNReal}
    (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    ContDiff Real (⊤ : ℕ∞) (parabolicConvolution w.toFun rho) := by
  apply contDiff_parabolicConvolution (rho := rho) ?_ hrho hrhoCompact
  exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with its time representative. -/
theorem timeDerivative_convolution {d : Nat} {p : ENNReal}
    (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    timeDerivative (parabolicConvolution w.toFun rho) = parabolicConvolution w.timeDeriv rho := by
  apply timeDerivative_parabolicConvolution w.hasWeakTimeDeriv ?_ ?_ hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp (w.timeDeriv_memLp.locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with each velocity gradient. -/
theorem velocityGradient_convolution {d : Nat} {p : ENNReal}
    (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) (i : Fin d) :
    (fun z => velocityGradient (parabolicConvolution w.toFun rho) z i) =
      parabolicConvolution (fun y => w.velocityGrad y i) rho := by
  apply velocityGradient_parabolicConvolution (w.hasWeakVelocityPartialDeriv i) ?_ ?_
    hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityGrad_memLp i).locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with its ordered velocity Hessian. -/
theorem velocityHessian_convolution {d : Nat} {p : ENNReal}
    (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) (i j : Fin d) :
    (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
        (parabolicConvolution w.toFun rho) z i j) =
      parabolicConvolution (fun y => w.velocityHessian y i j) rho := by
  apply velocityHessian_parabolicConvolution
    (w.hasWeakVelocityPartialDeriv i) (w.hasWeakVelocitySecondPartialDeriv i j) ?_ ?_ ?_
    hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityHessian_memLp i j).locallyIntegrableOn hp)

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
