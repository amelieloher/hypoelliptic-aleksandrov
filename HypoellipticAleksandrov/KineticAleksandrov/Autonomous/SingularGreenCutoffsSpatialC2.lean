module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsTerminalC2
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Derived Green identity for actual compact C² spatial tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory

/-- Compact C² spatial tests obey the actual full-space Green identity.
Size and operator bounds are derived, and no Green identity is assumed. -/
theorem fullspace_green_spatial_compact_c2
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) p =
      F (p.position, p.velocity) - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity) := by
  let f := fun q : Point => F (q.position, q.velocity)
  let π := fun x : EvolutionVec 1 => (diffusedCoord 1 x, transportedCoord 1 x)
  let fraw := fun x : EvolutionVec 1 => F (π x)
  have hπ : Continuous π :=
    (diffusedCoord 1).continuous.prodMk (transportedCoord 1).continuous
  have hfraw : ContDiff ℝ 2 fraw := hF.comp
    ((diffusedCoord 1).contDiff.prodMk (transportedCoord 1).contDiff)
  have hfeq : f ∘ evolutionHomeomorph 1 = fraw := by
    funext x
    simp [f, fraw, π, evolutionHomeomorph, KineticPoint.homeomorphProd,
      KineticPoint.isometryEquivProd, KineticPoint.equivProd]
    rfl
  let H := fun x : EvolutionAmbientState 1 =>
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f ⟨0, x.1, x.2⟩
  let x0 := fun x : EvolutionAmbientState 1 => (evolutionProdCLE 1).symm (0, x)
  have hx0 : Continuous x0 :=
    (evolutionProdCLE 1).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hHeq : H = (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) fraw)
      ∘ x0 := by
    funext x
    have hh := transportedOperator_comp (B := evolutionCoefficient A.a)
      (b := identityDrift 1) (u := f) (x := x0 x) (by rw [hfeq]; exact hfraw.contDiffAt)
    rw [hfeq] at hh
    have hx : evolutionHomeomorph 1 (x0 x) = ⟨0, x.1, x.2⟩ := by
      simp [x0, evolutionHomeomorph, KineticPoint.homeomorphProd,
        KineticPoint.isometryEquivProd, KineticPoint.equivProd]
      rfl
    rw [hx] at hh
    exact hh.symm
  have hHc : Continuous H := by
    rw [hHeq]
    exact (continuous_transportedOperator_c2 A hfraw).comp hx0
  have hHk : HasCompactSupport H := by
    apply hc.of_isClosed_subset (isClosed_tsupport H)
    apply closure_minimal ?_ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    have hnx : x0 x ∉ tsupport fraw := by
      intro hh
      have hhit := tsupport_comp_subset_preimage F hπ hh
      apply hn
      change π (x0 x) ∈ tsupport F at hhit
      have hpx : π (x0 x) = x := by
        have hh := (evolutionProdCLE 1).apply_symm_apply (0, x)
        exact congrArg Prod.snd hh
      rwa [hpx] at hhit
    have hz := transportedOperator_eq_zero_of_notMem_tsupport hnx
      (evolutionCoefficient A.a) (identityDrift 1)
    exact hx (by rw [hHeq]; exact hz)
  have hstation (q : Point) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f q =
        H (q.position, q.velocity) := by
    have ht (z : Point) : kineticTimeDerivative f z = 0 := by
      change deriv (fun _ : ℝ => F (z.position, z.velocity)) z.time = 0
      exact deriv_const z.time (F (z.position, z.velocity))
    dsimp only [H]
    rw [transportedForwardOperator_apply, transportedForwardOperator_apply, ht, ht]
    rfl
  obtain ⟨M, hMb⟩ := hHc.bounded_above_of_compact_support hHk
  obtain ⟨C, -, hCb⟩ := F.exists_bound
  exact fullspace_green_terminal_c2 hH hlam hLam A E hE T f
    (by rw [hfeq]; exact hfraw) C (max M 0) (le_max_right _ _) (fun q => hCb _)
    (fun q => by
      rw [hstation]
      simpa only [Real.norm_eq_abs] using (hMb (q.position, q.velocity)).trans
        (le_max_left M 0)) F (hc.uniformContinuous_of_continuous hF.continuous)
    (fun _ _ => rfl) p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
