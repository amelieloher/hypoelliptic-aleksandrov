module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelSlice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Jointly measurable integrals of compact time-state probes -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology

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

local notation "μT" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Integrating a smooth compact graph-supported time-state probe against the terminal
measure at its own terminal time is jointly Borel measurable. -/
theorem measurable_joint_terminal_probe
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ {z : ℝ × EvolutionAmbientState n |
      z.2 ∈ evolutionStateSet Ω γ z.1}) :
    Measurable (fun q : EvolutionQuery Ω γ => ∫ x, Φ (q.1.2.1, x) ∂(μT q)) := by
  let A (j : ℕ) (q : EvolutionQuery Ω γ) := validTerminalProbeIntegral n Ω γ μT
    (jointTerminalProbeSlice Φ (terminalTimeMesh j q.1.2.1)) q
  have hA (j : ℕ) : Measurable (A j) := by
    apply measurable_countable_lookup
      (fun q : EvolutionQuery Ω γ => terminalTimeMeshIndex j q.1.2.1)
      (fun k q => validTerminalProbeIntegral n Ω γ μT
        (jointTerminalProbeSlice Φ ((k : ℝ) / ((j : ℝ) + 1))) q)
    · intro k
      obtain ⟨hr, hcompact⟩ := jointTerminalProbeSlice_regular Φ hΦ hc
        ((k : ℝ) / ((j : ℝ) + 1))
      exact measurable_valid_terminal_probe n hn lam Lam m L_b
        hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
        hb_smooth hb_lipschitz hb_coercive hEx _ hr hcompact
    · exact (measurable_terminalTimeMeshIndex j).comp
        (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
  apply measurable_of_tendsto_metrizable hA
  apply tendsto_pi_nhds.mpr
  intro q
  have : IsFiniteMeasure (μT q) := ⟨(terminalMeasure_spec n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q).1.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨C, _, hC⟩ := Φ.exists_bound
  have hlim := tendsto_integral_of_dominated_convergence (μ := μT q)
    (F := fun j x => Φ (terminalTimeMesh j q.1.2.1, x))
    (f := fun x => Φ (q.1.2.1, x)) (fun _ => C)
    (fun j => (Φ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC (terminalTimeMesh j q.1.2.1, x))
    (Eventually.of_forall fun x => hΦ.continuous.continuousAt.tendsto.comp
      ((tendsto_terminalTimeMesh q.1.2.1).prodMk_nhds tendsto_const_nhds))
  have hnear := (tendsto_terminalTimeMesh q.1.2.1).eventually
    (eventually_jointTerminalProbeSlice_admissible
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) Φ hΦ hc hs q.1.2.1)
  apply hlim.congr'
  filter_upwards [hnear] with j hj
  exact (ite_eq_left hj).symm

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
