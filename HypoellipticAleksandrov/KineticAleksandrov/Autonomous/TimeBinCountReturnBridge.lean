module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometry

/-! # Scalar-to-ambient bridge for the full source return-time conclusion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov

/-- Repack the scalar return comparison without changing its constant or data quantifiers. -/
theorem return_time_ambient_of_scalar
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (F : BoundedBorel (EvolutionAmbientState 1)), (∀ p, 0 ≤ F p) →
      ∀ (t s : NNReal) (z : Z), 0 < (t : ℝ) →
        2 * (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ 3 * (t : ℝ) →
        |z.2| ≤ Real.sqrt (t : ℝ) →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        fullSpaceAction E F ⟨t, fun _ => z.1, fun _ => z.2⟩ ≤
          C * fullSpaceAction E F ⟨s, fun _ => z.1, fun _ => z.2⟩ := by
  obtain ⟨C, hC, h⟩ := hReturn
  refine ⟨C, hC, ?_⟩
  intro A F hF t s z ht hs hs1 hv
  let G : BoundedBorel Z := F.pullback physicalState (by unfold physicalState; fun_prop)
  have he : scalarTerminalDatum G = F := by
    apply BoundedBorel.ext
    intro w
    change F (fun _ => w.1 0, fun _ => w.2 0) = F w
    have hw : (fun _ => w.1 0, fun _ => w.2 0) = w := by
      apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    rw [hw]
  have hh := h A G (fun w => hF (physicalState w)) t s z.1 z.2 ht hs hs1 hv
  simpa only [S, he, point] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
