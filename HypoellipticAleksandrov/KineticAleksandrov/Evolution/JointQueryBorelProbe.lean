module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelTerminalEstimate
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelRational
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure

/-! # Measurable extensions of fixed-terminal classical probes

The extension is zero outside the past cylinder and for inadmissible terminal data.
It is used only to form countable measurable upper-time approximations, never as a
solution of an off-domain or reversed-time evolution problem.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set


/-- A measurable countable family of functions can be evaluated at a measurable mesh index
and at the actual query point. -/
theorem measurable_mesh_query_lookup {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (j : ℕ) (v : ℤ → KineticPoint n → ℝ)
    (hv : ∀ k, Measurable (v k)) :
    Measurable (fun q : EvolutionQuery Ω γ =>
      v (terminalTimeMeshIndex j q.1.2.1) (evolutionQueryPoint q)) := by
  have hm : Measurable (fun z : ℤ × KineticPoint n => v z.1 z.2) :=
    measurable_from_prod_countable_right hv
  exact hm.comp (((measurable_terminalTimeMeshIndex j).comp
    (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))).prodMk
    continuous_evolutionQueryPoint.measurable)


/-- Evaluating a countable measurable family at a measurable index is measurable. -/
theorem measurable_countable_lookup {X : Type*} [MeasurableSpace X]
    (I : X → ℤ) (v : ℤ → X → ℝ) (hv : ∀ k, Measurable (v k)) (hI : Measurable I) :
    Measurable (fun x => v (I x) x) := by
  have hLookup : Measurable (fun z : ℤ × X => v z.1 z.2) :=
    measurable_from_prod_countable_right hv
  exact hLookup.comp (hI.prodMk measurable_id)

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- A fixed terminal probe solution, extended by zero outside its past closed cylinder.
For a datum not supported in the terminal fiber the auxiliary function is zero. -/
def extendedTerminalProbe (n : ℕ) (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hEx : ClassicalTerminalExistence Ω γ B b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) : KineticPoint n → ℝ := by
  classical
  exact if hF : IsSmoothCompactTerminalDatum Ω γ τ F then
    (evolutionPastClosedCylinder Ω γ τ).indicator (hEx τ F hF).choose
  else 0

/-- The auxiliary fixed-terminal extension is Borel measurable. -/
theorem measurable_extendedTerminalProbe
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (extendedTerminalProbe n Ω γ B b hEx τ F) := by
  classical
  unfold extendedTerminalProbe
  split_ifs with hF
  · have hu := (hEx τ F hF).choose_spec.1
    have hs : IsClosed (evolutionPastClosedCylinder Ω γ τ) :=
      (isClosed_le continuous_time continuous_const).inter
        (isClosed_setOf_mem_closure_movingDomain hγ.1)
    exact hu.2.1.measurable_piecewise continuousOn_const hs.measurableSet
  · exact measurable_const

/-- On a valid earlier source the extension is exactly the terminal integral operator. -/
theorem extendedTerminalProbe_eq_operator
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    extendedTerminalProbe n Ω γ B b hEx τ F
      ⟨σ, p.1.1, p.1.2⟩ = P₀ σ τ hστ (terminalStateDatum F) p := by
  rw [extendedTerminalProbe, dite_eq_left hF,
    indicator_of_mem (mk_mem_evolutionPastClosedCylinder hστ p), terminalOperators_apply_smooth]
  exact (terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    σ τ hστ p F hF _ (hEx τ F hF).choose_spec.1).symm

/-- The upper-time countable probe approximation is measurable on valid queries. -/
theorem measurable_upper_terminal_probe
    (j : ℕ) (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (fun q : EvolutionQuery Ω γ =>
      extendedTerminalProbe n Ω γ B b hEx
        (terminalTimeMesh j q.1.2.1) F (evolutionQueryPoint q)) := by
  exact measurable_mesh_query_lookup j
    (fun k => extendedTerminalProbe n Ω γ B b hEx ((k : ℝ) / ((j : ℝ) + 1)) F)
    (fun k => measurable_extendedTerminalProbe n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx ((k : ℝ) / ((j : ℝ) + 1)) F)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
