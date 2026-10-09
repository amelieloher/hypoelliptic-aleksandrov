module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # Vanishing localized source for the one-block Gaussian comparison -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The globally smooth glued Gaussian is smooth near every set. -/
theorem gaussianBarrier_isSmoothNear {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (E : Set (KineticPoint d)) :
    IsSmoothNear (gaussianBarrier lam Lam H h L ell tminus sblock x v) E := by
  refine ⟨univ, isOpen_univ, subset_univ E, ?_⟩
  exact (contDiff_raw_gaussianBarrier hlam hh Lam H L ell tminus sblock hx hv).contDiffOn

/-- Initial-strip comparison and the multiplied sign annihilate the localized source. -/
theorem gaussianBarrier_localizedSource_zero {d : ℕ} {lam h R : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hR : 0 < R) (Lam H L ell tminus sblock : ℝ)
    (hLam : lam ≤ Lam) (hH : 0 ≤ H) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (u : KineticPoint d → ℝ)
    (hinit : ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ R),
      P.time - tminus - sblock ≤ 0 →
      gaussianBarrier lam Lam H h L ell tminus sblock x v P ≤ u P) :
    localizedSource A (gaussianBarrier lam Lam H h L ell tminus sblock x v) u
      =ᵐ[volume.restrict (backwardCylinder
        ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ R)] 0 := by
  let S := {P : KineticPoint d | 0 < P.time - tminus - sblock ∧
    P.time - tminus - sblock ≤ h}
  have ht : Continuous (fun P : KineticPoint d => P.time - tminus - sblock) :=
    (continuous_time.sub continuous_const).sub continuous_const
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const ht).measurableSet.inter
      (isClosed_le ht continuous_const).measurableSet
  have hs := (ae_restrict_iff' hS).mp
    (gaussianBarrier_sign hlam hh Lam H L ell tminus sblock hLam hH hell A hA
      hx hv hkin hLip)
  let Q := backwardCylinder
    (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d) R
  have hQ : MeasurableSet Q := (isOpen_backwardCylinder _ R hR).measurableSet
  filter_upwards [hs.filter_mono (ae_restrict_le (μ := volume) (s := Q)),
    ae_restrict_mem hQ] with P hsign hP
  by_cases hp : u P < gaussianBarrier lam Lam H h L ell tminus sblock x v P
  · have hc := subset_closure hP
    have hpositive : 0 < P.time - tminus - sblock := by
      by_contra hn
      exact (not_lt_of_ge (hinit P hc (le_of_not_gt hn))) hp
    have hupper := (closure_backwardCylinder_bounds
      (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d)
      hR hc).2.1
    have hmem : P ∈ S := ⟨hpositive, by change P.time ≤ tminus + sblock + h at hupper
                                        linarith only [hupper]⟩
    have hnonpos := (hsign hmem).1.trans (hsign hmem).2
    rw [localizedSource, Set.indicator_of_mem (show P ∈ {Q | u Q <
      gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
    exact max_eq_right hnonpos
  · rw [localizedSource, Set.indicator_of_notMem (show P ∉ {Q | u Q <
      gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.Holder
