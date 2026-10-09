module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Anisotropic regularity from joint interior smoothness -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Set
open Evolution Parabolic
open scoped Topology
variable {d : ℕ}

/-- Joint smoothness in packed Euclidean coordinates supplies the full kinetic C112 API. -/
theorem isKineticC112On_of_contDiffOn {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' D)) : IsKineticC112On u D := by
  let e := evolutionHomeomorph d
  let U := e ⁻¹' D
  let f := u ∘ e
  have hU : IsOpen U := hD.preimage e.continuous
  have hx : ∀ p ∈ D, e.symm p ∈ U := fun p hp => by simpa [U] using hp
  have hs : ∀ x ∈ U, ContDiffAt ℝ 2 f x :=
    fun x hx => (hu.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hd : ∀ x ∈ U, DifferentiableAt ℝ f x :=
    fun x hx => (hs x hx).differentiableAt (by norm_num)
  have hj : ∀ v : EvolutionVec d,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) U :=
    fun v => (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hjj : ∀ v w : EvolutionVec d,
      ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) U :=
    fun v w => (((hj v).fderiv_of_isOpen (m := 0) hU (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hc : ContinuousOn e.symm D := e.symm.continuous.continuousOn
  have hm : MapsTo e.symm D U := hx
  have hslice : ∀ p ∈ D, IsSliceRegularAt u p := by
    intro p hp
    apply IsSliceRegularAt.of_contDiffAt
    have h := (hs (e.symm p) (hx p hp)).comp
      (p.time, p.position, p.velocity) (evolutionProdCLE d).symm.contDiff.contDiffAt
    have heq : (fun q => f ((evolutionProdCLE d).symm q)) = rawLift u := by
      funext q
      simp [f, e, evolutionHomeomorph, rawLift, KineticPoint.homeomorphProd,
        KineticPoint.isometryEquivProd, KineticPoint.equivProd]
      rfl
    change ContDiffAt ℝ 2 (fun q => f ((evolutionProdCLE d).symm q))
      (p.time, p.position, p.velocity) at h
    rw [heq] at h
    exact h
  refine ⟨?_, fun p hp => (hslice p hp).time,
    fun p hp => (hslice p hp).position.of_le (by norm_num),
    fun p hp => (hslice p hp).velocity, ?_, ?_, ?_, ?_⟩
  · simpa [f, e, Function.comp_def] using
      hu.continuousOn.comp hc hm
  · apply ((hj basisT).continuousOn.comp hc hm).congr
    intro p hp
    simpa [f, e] using kineticTimeDerivative_comp (hd _ (hx p hp))
  · apply continuousOn_pi.mpr
    intro i
    apply ((hj (basisV i)).continuousOn.comp hc hm).congr
    intro p hp
    simpa [f, e] using kineticPositionGradient_comp (hd _ (hx p hp)) i
  · apply continuousOn_pi.mpr
    intro i
    apply ((hj (basisZ i)).continuousOn.comp hc hm).congr
    intro p hp
    simpa [f, e] using kineticVelocityGradient_comp (hd _ (hx p hp)) i
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply ((hjj (basisZ j) (basisZ i)).comp hc hm).congr
    intro p hp
    simpa [f, e] using kineticVelocityHessian_comp (hs _ (hx p hp)) i j

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
