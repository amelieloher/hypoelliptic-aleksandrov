module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationSource

/-! # Position cutoffs for solutions defined only on a kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Parabolic Evolution
open scoped Topology

/-- The position cutoff uses the cylinder's actual free-transport frame. -/
def localPositionCutoff {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (P : KineticPoint d) : ℝ := χ (relativePosition Z₀ P)

/-- The local solution multiplied by a position cutoff, with no extension assumption. -/
def localCutoffSolution {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ := localPositionCutoff Z₀ χ P * u P

/-- Free-transport relative position is smooth on the physical product carrier. -/
theorem contDiff_relativePosition_native {d : ℕ} (Z₀ : KineticPoint d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (relativePosition Z₀ ∘ (KineticPoint.equivProd d).symm) :=
  (contDiff_snd.fst.sub contDiff_const).sub
    ((contDiff_fst.sub contDiff_const).smul contDiff_const)

/-- A smooth position cutoff is smooth in physical product coordinates. -/
theorem contDiff_localPositionCutoff {d : ℕ} (Z₀ : KineticPoint d)
    {χ : PDE.Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (localPositionCutoff Z₀ χ ∘ (KineticPoint.equivProd d).symm) :=
  hχ.comp (contDiff_relativePosition_native Z₀)

/-- Strict position membership and closed velocity membership give outer closure membership. -/
theorem local_closed_strip_mem_outer {d : ℕ} (Z₀ Q : KineticPoint d)
    {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time ≤ a) (hT : T ≤ Z₀.time + R ^ 2)
    (hQ : Q ∈ localClosedStrip a T Z₀.velocity R)
    (hx : relativePosition Z₀ Q ∈ PDE.euclideanBall 0 (R ^ 3)) :
    Q ∈ closure (forwardCylinder Z₀ R hR) := by
  rw [comparison_closure_forwardCylinder_eq]
  refine ⟨⟨ha.trans hQ.1, hQ.2.1.trans hT⟩,
    PDE.euclideanBall_subset_euclideanClosedBall _ _ hx, ?_⟩
  change PDE.vecNormSq (Q.velocity - Z₀.velocity - 0) ≤ R ^ 2
  have hv := (closure_minimal (PDE.euclideanBall_subset_euclideanClosedBall _ _)
    (PDE.isClosed_euclideanClosedBall Z₀.velocity R)) hQ.2.2
  change PDE.vecNormSq (Q.velocity - Z₀.velocity) ≤ R ^ 2 at hv
  simpa only [sub_zero] using hv

/-- The cutoff solution is smooth inside the whole velocity strip. -/
theorem localCutoffSolution_contDiffOn {d : ℕ} (Z₀ : KineticPoint d)
    {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time < a) (hT : T < Z₀.time + R ^ 2)
    (u : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' forwardCylinder Z₀ R hR))
    (χ : PDE.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (localCutoffSolution Z₀ χ u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T Z₀.velocity R) := by
  rintro q ⟨P, hP, rfl⟩
  by_cases hx : relativePosition Z₀ P ∈ tsupport χ
  · have hp : P ∈ forwardCylinder Z₀ R hR :=
      ⟨ha.trans hP.1, hP.2.1.trans hT, hP.2.2, hs hx⟩
    have hopen : IsOpen ((KineticPoint.equivProd d) '' forwardCylinder Z₀ R hR) :=
      (KineticPoint.homeomorphProd d).isOpenMap _ (isOpen_forwardCylinder Z₀ R hR)
    exact ((contDiff_localPositionCutoff Z₀ hχ).contDiffAt.mul
      (hu.contDiffAt (hopen.mem_nhds ⟨P, hp, rfl⟩))).contDiffWithinAt
  · have he : χ =ᶠ[𝓝 (relativePosition Z₀ P)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hx
    have hrel := (contDiff_relativePosition_native Z₀).continuous.continuousAt
      (x := (KineticPoint.equivProd d) P)
    have hz : (localCutoffSolution Z₀ χ u ∘ (KineticPoint.equivProd d).symm) =ᶠ[
        𝓝 ((KineticPoint.equivProd d) P)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hrel.eventually he] with q hq
      change χ (relativePosition Z₀ ((KineticPoint.equivProd d).symm q)) *
        u ((KineticPoint.equivProd d).symm q) = 0
      change χ (relativePosition Z₀ ((KineticPoint.equivProd d).symm q)) = 0 at hq
      rw [hq, zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

/-- The original closed-cylinder continuity gives closed-strip continuity after cutoff. -/
theorem localCutoffSolution_continuousOn {d : ℕ} (Z₀ : KineticPoint d)
    {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time ≤ a) (hT : T ≤ Z₀.time + R ^ 2)
    (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (χ : PDE.Vec d → ℝ) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) :
    ContinuousOn (localCutoffSolution Z₀ χ u) (localClosedStrip a T Z₀.velocity R) := by
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  intro P hP
  by_cases hx : relativePosition Z₀ P ∈ tsupport χ
  · have hp := local_closed_strip_mem_outer Z₀ P hR ha hT hP (hs hx)
    have hmem : closure (forwardCylinder Z₀ R hR) ∈
        𝓝[localClosedStrip a T Z₀.velocity R] P := by
      have hpos := hrel.continuousAt.preimage_mem_nhds
        ((PDE.isOpen_euclideanBall 0 (R ^ 3)).mem_nhds (hs hx))
      apply mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds hpos)
        self_mem_nhdsWithin)
      intro Q hQ
      exact local_closed_strip_mem_outer Z₀ Q hR ha hT hQ.2 hQ.1
    exact (hχ.comp hrel).continuousAt.continuousWithinAt.mul
      ((hu P hp).mono_of_mem_nhdsWithin hmem)
  · have he : χ =ᶠ[𝓝 (relativePosition Z₀ P)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hx
    have hz : localCutoffSolution Z₀ χ u =ᶠ[𝓝 P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hrel.continuousAt.eventually he] with Q hQ
      change χ (relativePosition Z₀ Q) * u Q = 0
      change χ (relativePosition Z₀ Q) = 0 at hQ
      rw [hQ, zero_mul]
    exact (continuousAt_const.congr_of_eventuallyEq hz).continuousWithinAt

/-- A cutoff with zero position germ has zero classical operator, even for arbitrary data. -/
theorem localCutoffSolution_operator_zero {d : ℕ} (Z₀ P : KineticPoint d)
    (A : FullKineticCoefficient d) (χ : PDE.Vec d → ℝ) (u : KineticPoint d → ℝ)
    (hx : relativePosition Z₀ P ∉ tsupport χ) :
    forwardKineticOperator A (localCutoffSolution Z₀ χ u) P = 0 := by
  have he : χ =ᶠ[𝓝 (relativePosition Z₀ P)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hpoint : χ (relativePosition Z₀ P) = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  have htime : (fun t => localCutoffSolution Z₀ χ u ⟨t, P.position, P.velocity⟩) =ᶠ[
      𝓝 P.time] (fun _ => (0 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => P.position - Z₀.position -
        (t - Z₀.time) • Z₀.velocity) :=
      continuous_const.sub ((continuous_id.sub continuous_const).smul continuous_const)
    filter_upwards [hc.continuousAt.eventually he] with t ht
    change χ (P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity) = 0 at ht
    change χ (P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity) *
      u ⟨t, P.position, P.velocity⟩ = 0
    rw [ht, zero_mul]
  have hpos : (fun x => localCutoffSolution Z₀ χ u ⟨P.time, x, P.velocity⟩) =ᶠ[
      𝓝 P.position] (fun _ => (0 : ℝ)) := by
    have hc : Continuous (fun x : PDE.Vec d => x - Z₀.position -
        (P.time - Z₀.time) • Z₀.velocity) :=
      (continuous_id.sub continuous_const).sub continuous_const
    filter_upwards [hc.continuousAt.eventually he] with x hx'
    change χ (x - Z₀.position - (P.time - Z₀.time) • Z₀.velocity) = 0 at hx'
    change χ (x - Z₀.position - (P.time - Z₀.time) • Z₀.velocity) *
      u ⟨P.time, x, P.velocity⟩ = 0
    rw [hx', zero_mul]
  have ht : kineticTimeDerivative (localCutoffSolution Z₀ χ u) P = 0 := by
    exact htime.deriv_eq.trans (deriv_const _ _)
  have hg : kineticPositionGradient (localCutoffSolution Z₀ χ u) P = 0 := by
    ext i
    change fderiv ℝ (fun x => localCutoffSolution Z₀ χ u ⟨P.time, x, P.velocity⟩)
      P.position (PDE.basisVec i) = 0
    rw [hpos.fderiv_eq]
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i))
      (hasFDerivAt_const (0 : ℝ) P.position).fderiv
  have hvel : (fun v => localCutoffSolution Z₀ χ u ⟨P.time, P.position, v⟩) =
      (fun _ => (0 : ℝ)) := by
    funext v
    change χ (relativePosition Z₀ P) * u ⟨P.time, P.position, v⟩ = 0
    rw [hpoint, zero_mul]
  have hh : kineticVelocityHessian (localCutoffSolution Z₀ χ u) P = 0 := by
    rw [kineticVelocityHessian_eq_sliceHessian, hvel]
    have hgrad : (fun y : PDE.Vec d => PDE.classicalGradient (fun _ => (0 : ℝ)) y) =
        (fun _ => (0 : PDE.Vec d)) := by
      funext y
      ext k
      rw [PDE.classicalGradient_apply, fderiv_const_apply]
      rfl
    ext i j
    change fderiv ℝ (fun y => PDE.classicalGradient (fun _ => (0 : ℝ)) y)
      P.velocity (PDE.basisVec i) j = 0
    rw [hgrad, fderiv_const_apply]
    rfl
  rw [forwardKineticOperator_apply, ht, hg, hh]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    matrixContraction, add_zero, Matrix.zero_apply]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
