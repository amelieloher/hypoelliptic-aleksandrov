module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomySemigroup
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyAction

/-! # The bounded Borel semigroup in physical position-velocity order -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The coordinate exchange is an actual linear equivalence of bounded Borel carriers. -/
def physicalBorelEquiv : BoundedBorel (EvolutionAmbientState 1) ≃ₗ[ℝ]
    BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) where
  toFun F := terminalStateDatum (physicalTerminalDatum F)
  invFun G := G.pullback (fun x => fullspaceState 0 x.swap)
    ((measurable_fullspaceState 0).comp measurable_swap)
  left_inv F := by apply BoundedBorel.ext; intro x; rfl
  right_inv G := by apply BoundedBorel.ext; intro x; rfl
  map_add' F G := by apply BoundedBorel.ext; intro x; rfl
  map_smul' c F := by apply BoundedBorel.ext; intro x; rfl

/-- The same supplied semigroup, conjugated to physical state order `(X,v)`. -/
def fullSpacePhysicalSemigroup (E : FullSpaceEvolution) (t : NNReal) :
    BoundedBorel (EvolutionAmbientState 1) →ₗ[ℝ] BoundedBorel (EvolutionAmbientState 1) :=
  physicalBorelEquiv.symm.toLinearMap.comp
    ((fullSpaceSemigroup E t).comp physicalBorelEquiv.toLinearMap)

/-- Physical-coordinate semigroup composition holds for every bounded Borel function. -/
theorem fullSpacePhysicalSemigroup_add {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (t s : NNReal) :
    fullSpacePhysicalSemigroup E (t + s) =
      (fullSpacePhysicalSemigroup E t).comp (fullSpacePhysicalSemigroup E s) := by
  apply LinearMap.ext
  intro F
  change physicalBorelEquiv.symm (fullSpaceSemigroup E (t + s) (physicalBorelEquiv F)) =
    physicalBorelEquiv.symm (fullSpaceSemigroup E t
      (physicalBorelEquiv (physicalBorelEquiv.symm
        (fullSpaceSemigroup E s (physicalBorelEquiv F)))))
  rw [fullSpaceSemigroup_add A E hE, physicalBorelEquiv.apply_symm_apply]
  rfl

/-- The physical semigroup and the literal kernel action are the same function. -/
theorem fullSpacePhysicalSemigroup_eq_action {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (t : NNReal) (F : BoundedBorel (EvolutionAmbientState 1)) (x : EvolutionAmbientState 1) :
    fullSpacePhysicalSemigroup E t F x = fullSpaceAction E F ⟨t, x.1, x.2⟩ := by
  rw [fullSpaceAction_eq_zeroTime A E hE F _ t.coe_nonneg]
  let p := fullspaceState 0 x.swap
  change E.1 0 t t.coe_nonneg (terminalStateDatum (physicalTerminalDatum F)) p = _
  exact (hE.2.1 0 t t.coe_nonneg p (terminalStateDatum (physicalTerminalDatum F))).trans
    (integral_master_eq_fiber E.2 autonomousWholeDomain_measurable 0 t t.coe_nonneg p
      (physicalTerminalDatum F) (physicalTerminalDatum F).measurable).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
