module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Smooth interior representatives of vanishing-viscosity sequences -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder

/-- A smooth representative of the zero-source weak equation satisfies the equation
pointwise in the original kinetic coordinates. -/
theorem transportedForwardOperator_eq_zero_of_smooth_weak {n : ℕ}
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) {U : Set (KineticPoint n)} (hU : IsOpen U)
    {u V : KineticPoint n → ℝ}
    (hu : IsKineticWeakTransportedSolution B b U u (fun _ => 0))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U)) (hrep : u =ᵐ[volume.restrict U] V) :
    ∀ p ∈ U, transportedForwardOperator B b V p = 0 := by
  have hw : IsKineticWeakTransportedSolution B b U V (fun _ => 0) := by
    refine ⟨(locallyIntegrableOn_congr hrep).mp hu.1, ?_⟩
    intro ψ hψ hc hs
    have he := hu.2 ψ hψ hc hs
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hrep] with p hp
    rw [hp]
  have hp := (isWeakTransportedSolution_comp_iff B b U V (fun _ => 0)).mpr hw
  have hP := (evolutionHomeomorph n).continuous.isOpen_preimage U hU
  have hreg : IsWeakRegularizedSolution B b 0 (evolutionHomeomorph n ⁻¹' U)
      (V ∘ evolutionHomeomorph n) (fun _ => 0) := by
    simpa only [IsWeakRegularizedSolution, IsWeakTransportedSolution,
      IsDistributionalSolution, regularizedAdjoint, transportedAdjoint,
      Function.comp_def, zero_mul, add_zero, sub_zero] using hp
  have he := regularizedOperator_eq_zero_of_smooth_weak hP hB hBs hb 0 hV hreg
  intro p hpin
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by simpa [x] using hpin
  have heq := he x hx
  rw [regularizedOperator_comp 0 ((hV.contDiffAt (hP.mem_nhds hx)).of_le (by simp)),
    zero_mul, add_zero] at heq
  simpa [x] using heq

/-- Interior compactness retains all integrable tests as well as a smooth representative.
Boundary extension is handled separately by uniform trace estimates. -/
theorem exists_smooth_viscosity_sequence_limit
    (hH : HormanderHypoellipticityStatement)
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (C : ℝ) (hC : 0 ≤ C)
    (v : ℕ → KineticPoint n → ℝ)
    (hv : ∀ j : ℕ, IsClassicalViscousTerminalSolution Ω γ B b (1 / ((j : ℝ) + 1)) τ F (v j))
    (hb : ∀ j, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |v j p| ≤ C) :
    ∃ (u V : KineticPoint n → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧
      AEStronglyMeasurable u (volume.restrict (evolutionPastOpenCylinder Ω γ τ)) ∧
      (∀ᵐ p ∂volume.restrict (evolutionPastOpenCylinder Ω γ τ), |u p| ≤ C) ∧
      (∀ ψ : KineticPoint n → ℝ,
        IntegrableOn ψ (evolutionPastOpenCylinder Ω γ τ) volume →
        Tendsto (fun j => ∫ p in evolutionPastOpenCylinder Ω γ τ, v (ν j) p * ψ p)
          atTop (𝓝 (∫ p in evolutionPastOpenCylinder Ω γ τ, u p * ψ p))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
        (evolutionHomeomorph n ⁻¹' evolutionPastOpenCylinder Ω γ τ) ∧
      u =ᵐ[volume.restrict (evolutionPastOpenCylinder Ω γ τ)] V ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, |V p| ≤ C) ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, transportedForwardOperator B b V p = 0) := by
  let : SecondCountableTopology (KineticPoint n) :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  let U := evolutionPastOpenCylinder Ω γ τ
  have hU := isOpen_evolutionPastOpenCylinder
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 τ
  have hUS : U ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  have hva : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U) := fun j =>
    (((hv j).2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
  have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v j p| ≤ C := fun j => by
    filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
    exact hb j p (hUS hp)
  obtain ⟨u, ν, hν, hua, hub, hlim⟩ := exists_sigmaFinite_bounded_weak_subsequence
    (volume.restrict U) v C hC hva hba
  have hε : Tendsto (fun j => 1 / ((ν j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hν.tendsto_atTop
  have hw := weak_transport_equation_of_vanishing_viscosity n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
    hb_lipschitz hb_coercive τ (fun j => 1 / ((ν j : ℝ) + 1))
    (fun j => by positivity) hε (fun j => v (ν j)) u C hC
    (fun j => classical_viscous_terminalSolution_isWeak
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hB_smooth hB_symm hb_smooth (hv (ν j)))
    (fun j => hba (ν j)) hua hub hlim
  obtain ⟨V, hV, hrep⟩ := exists_smooth_kinetic_representative hH hlam hB_smooth hB_ell
    hb_smooth hm hb_coercive U hU u hw
  have hc : ContinuousOn V U := by
    have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
      (fun p hp => by simpa using hp)
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
  refine ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, ?_, ?_⟩
  · have hh := bounded_weak_limit_abs_sub_le_on_open U U hU Subset.rfl
      (fun j => v (ν j)) u V C 0 C (fun j => hva (ν j)) (fun j => hba (ν j))
      hua hub hlim hc hrep (fun j p hp => by simpa using hb (ν j) p (hUS hp))
    simpa only [sub_zero] using hh
  · exact transportedForwardOperator_eq_zero_of_smooth_weak hB_smooth hB_symm
      hb_smooth hU hw hV hrep

end HypoellipticAleksandrov.KineticAleksandrov
