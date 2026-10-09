module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BallEvolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation

/-! # Uniform quadratic comparison for smooth compact sources

The bound depends on the source supremum, rather than its distance to the boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov Parabolic Evolution Set
open scoped Topology

/-- The stationary moving-domain convention recovers exactly the given ball. -/
theorem boundedSource_stationary_domain {d : ℕ} (c : PDE.Vec d) (R t : ℝ) :
    movingDomain (PDE.euclideanBall c R) (fun _ => 0) t = PDE.euclideanBall c R := by
  ext y
  rw [mem_movingDomain_iff]
  simp only [sub_zero]

/-- Smooth compact sources bounded by one satisfy the uniform quadratic comparison. -/
theorem duhamel_smooth_le_boundedSourceQuadratic
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 0 < d)
    {c : PDE.Vec d} {R : ℝ} (hR : 0 < R) {lam Lam m Lb : ℝ}
    (hlam : 0 < lam) (hm : 0 < m)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (hb : IsSmoothDrift b)
    (hbounds : HasTransportBounds m Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall c R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) (fun _ => 0)
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (hgn : ∀ p, 0 ≤ g p) (hgb : ∀ p, g p ≤ 1)
    (T : ℝ) (hs : tsupport g ⊆
      evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T)
    (p : KineticPoint d)
    (hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T) :
    duhamelPotential K T g p ≤ boundedSourceQuadratic c R lam p := by
  have hΩ := LocalA.localBall_admissible c hR
  have hΩm := (PDE.isOpen_euclideanBall c R).measurableSet
  have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec d)) := continuous_const
  let W := duhamelPotential K T g
  let Q := boundedSourceQuadratic c R lam
  have hWc := continuousOn_duhamelPotential hΩ hΩm hγ B b S K hreal
    g hgn hg hc hgs T hs
  have hWs := duhamelPotential_contDiffOn hH hΩ hΩm hγ B b S K hreal
    hB hBs hb g hgn hg hc hgs T hs hlam hm hell hbounds.2
  have hWe := duhamelPotential_source_equation hH hΩ hΩm hγ B b S K hreal
    hB hBs hb g hgn hg hc hgs T hs hlam hm hell hbounds.2
  have hU := (isOpen_duhamelCylinder (PDE.isOpen_euclideanBall c R) hγ T).preimage
    (evolutionHomeomorph d).continuous
  have hreg : ∀ q ∈ evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T,
      IsSliceRegularAt W q := by
    intro q hq
    apply boundedSource_sliceRegular_of_smooth
    have hqm : (evolutionHomeomorph d).symm q ∈
        evolutionHomeomorph d ⁻¹'
          evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T := by
      simpa using hq
    exact hWs.contDiffAt (hU.mem_nhds hqm)
  have hslab : movingClosedSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T ⊆
      evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T :=
    fun q hq => ⟨hq.2.1, hq.2.2⟩
  have hactive : movingActiveSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T ⊆
      evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T :=
    fun q hq => ⟨hq.2.1, hq.2.2⟩
  have hQn : ∀ q ∈ movingClosedSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T,
      0 ≤ Q q := by
    intro q hq
    apply boundedSourceQuadratic_nonneg hlam c R
    simpa only [boundedSource_stationary_domain] using hq.2.2
  have hmax := growth_comparison (PDE.isOpen_euclideanBall c R) hγ hlam hell hbounds.1
    (le_refl 0) zero_le_one (a := p.time) (T := T) (u := fun q => W q - Q q)
    ?_ ?_ ?_ ?_ ?_ ?_ p ⟨le_rfl, hp.1, hp.2⟩
  · exact sub_nonpos.mp hmax
  · refine ⟨T - p.time, fun q hq => ?_⟩
    have hw := (duhamelPotential_nonneg_le K T g hgn 1 zero_le_one hgb q hq.2.1).2
    dsimp only [W, Q]
    have hqn := hQn q hq
    dsimp only [Q] at hqn
    linarith only [hw, hqn, hq.1]
  · exact (hWc.mono hslab).sub (continuous_boundedSourceQuadratic c R lam).continuousOn
  · intro q hq
    exact (hreg q (hactive hq)).sub (isSliceRegularAt_boundedSourceQuadratic c R lam q)
  · intro q hq
    rw [viscousTransportedOperator_sub (hreg q (hactive hq))
      (isSliceRegularAt_boundedSourceQuadratic c R lam q)]
    have hw : viscousTransportedOperator B b 0 W q = -g q := by
      rw [viscousTransportedOperator_zero]
      exact hWe q (hactive hq)
    have hqv := viscousTransportedOperator_boundedSourceQuadratic_le hd hlam B hell b c R q
    change 0 ≤ viscousTransportedOperator B b 0 W q -
      viscousTransportedOperator B b 0 Q q
    rw [hw]
    exact sub_nonneg.mpr (hqv.trans (neg_le_neg (hgb q)))
  · intro q hq ht
    have hw := duhamelPotential_eq_zero_of_terminal_le K T g q ht.ge
    change W q - Q q ≤ 0
    dsimp only [W]
    rw [hw, zero_sub]
    exact neg_nonpos.mpr (hQn q hq)
  · intro q hq hfront
    have hnot : q.position ∉ movingDomain (PDE.euclideanBall c R) (fun _ => 0) q.time :=
      ((isOpen_movingDomain_of_isAdmissibleEvolutionDomain (fun _ => 0) hΩ q.time
        ).frontier_eq ▸ hfront).2
    have hw := duhamelPotential_eq_zero_of_not_mem K T g q hnot
    change W q - Q q ≤ 0
    dsimp only [W]
    rw [hw, zero_sub]
    exact neg_nonpos.mpr (hQn q hq)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
