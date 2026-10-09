module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalPatch
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationBarriersTraces
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import Mathlib.Tactic.Linarith

/-! # Classical terminal solutions conditional on viscous existence

The additional premise is the existence of bounded classical viscous terminal solutions
on the moving domains.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set Filter MeasureTheory Evolution Classical
open scoped Topology MatrixOrder

/-- Existence of a classical terminal solution, derived from viscous existence.  Hörmander's
hypoellipticity theorem and viscous existence are explicit hypotheses. -/
theorem exists_classical_terminalSolution_of_viscous
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
    (hvisc : ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
      IsSmoothCompactTerminalDatum Ω γ τ F → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (C : ℝ), 0 ≤ C → (∀ q, |F q| ≤ C) →
      ∃ u : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
        (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
        (∀ v : KineticPoint n → ℝ,
          IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
            EqOn v u (evolutionPastClosedCylinder Ω γ τ)))
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
  let : SecondCountableTopology (KineticPoint n) :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  obtain ⟨C, hC, hFC⟩ := F.exists_bound
  let family (ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}) :=
    (hvisc τ F hF ε.1 ε.2.1 ε.2.2 C hC hFC).choose
  have hfamily (ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}) :=
    (hvisc τ F hF ε.1 ε.2.1 ε.2.2 C hC hFC).choose_spec
  let seqε (j : ℕ) : {ε : ℝ // 0 < ε ∧ ε ≤ 1} :=
    ⟨1 / ((j : ℝ) + 1), by
      constructor
      · positivity
      · exact (div_le_one (by positivity)).mpr (by
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith)⟩
  let v := fun j => family (seqε j)
  let w := family ⟨1, one_pos, le_rfl⟩
  have hw : IsClassicalViscousTerminalSolution Ω γ B b 1 τ F w := (hfamily _).1
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  let U := evolutionPastOpenCylinder Ω γ τ
  let S := evolutionPastClosedCylinder Ω γ τ
  have hU := isOpen_evolutionPastOpenCylinder hΩo hγ.1 τ
  have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  obtain ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, hVC, hVE⟩ :=
    exists_smooth_viscosity_sequence_limit hH n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
      hb_lipschitz hb_coercive τ F C hC v
      (fun j => (hfamily (seqε j)).1) (fun j => (hfamily (seqε j)).2.1)
  have hva : ∀ j, AEStronglyMeasurable (v (ν j)) (volume.restrict U) := fun j =>
    (((hfamily (seqε (ν j))).1.2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
  have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v (ν j) p| ≤ C := fun j => by
    filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
    exact (hfamily (seqε (ν j))).2.1 p (hUS hp)
  have hcV : ContinuousOn V U := by
    have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
      (fun p hp => by simpa using hp)
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
  have ht := uniform_viscous_boundary_traces hΩ hγ hlam hB_ell hb_lipschitz τ F hF
    family (fun ε => (hfamily ε).1)
  have htrace : ∀ p ∈ S, p ∉ U → ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p ∈ O ∧
        ∀ q ∈ O ∩ U, |V q - w p| ≤ η := by
    intro p hp hpi η hη
    have hfaces : p ∈ evolutionTerminalClosure Ω γ τ ∨
        p ∈ evolutionLateralFrontier Ω γ τ := by
      by_cases he : p.time = τ
      · exact Or.inl ⟨he, by simpa only [← he] using hp.2⟩
      · right
        refine ⟨hp.1, ?_⟩
        rw [(isOpen_movingDomain hΩo p.time).frontier_eq]
        refine ⟨hp.2, ?_⟩
        intro hi
        exact hpi ⟨lt_of_le_of_ne hp.1 he, hi⟩
    rcases hfaces with hterm | hlat
    · obtain ⟨O, hO, hpO, hbO⟩ := ht.1 p hterm η hη
      refine ⟨O, hO, hpO, ?_⟩
      have hh := bounded_weak_limit_abs_sub_le_on_open U (O ∩ U) (hO.inter hU)
        inter_subset_right (fun j => v (ν j)) u V C
        (F (p.position, p.velocity)) η hva hba hua hub hlim hcV hrep
        (fun j q hq => hbO (seqε (ν j)) q ⟨hq.1, hUS hq.2⟩)
      simpa only [hw.2.2.2.2.1 p hterm] using hh
    · obtain ⟨O, hO, hpO, hbO⟩ := ht.2 p hlat η hη
      refine ⟨O, hO, hpO, ?_⟩
      have hh := bounded_weak_limit_abs_sub_le_on_open U (O ∩ U) (hO.inter hU)
        inter_subset_right (fun j => v (ν j)) u V C 0 η hva hba hua hub hlim hcV hrep
        (fun j q hq => by
          simpa only [sub_zero] using (hbO (seqε (ν j)) q ⟨hq.1, hUS hq.2⟩))
      simpa only [hw.2.2.2.2.2 p hlat] using hh
  let candidate := fun p => if p ∈ U then V p else w p
  have hgerm : ∀ p ∈ U, candidate =ᶠ[𝓝 p] V := by
    intro p hp
    filter_upwards [hU.mem_nhds hp] with q hq
    change (if q ∈ U then V q else w q) = V q
    exact ite_eq_left (show q ∈ U from hq)
  have hclass : IsClassicalTerminalSolution Ω γ B b τ F candidate := by
    refine ⟨⟨C, hC, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      by_cases hi : p ∈ U
      · simpa only [candidate, ite_eq_left hi] using hVC p hi
      · simpa only [candidate, ite_eq_right hi] using (hfamily ⟨1, one_pos, le_rfl⟩).2.1 p hp
    · exact continuousOn_interior_patch U S hU hUS V w hcV hw.2.1 htrace
    · rw [evolutionPastInteriorRaw_eq_image]
      apply contDiffOn_comp_evolutionHomeomorph_iff.mp
      apply hV.congr
      intro x hx
      change (if evolutionHomeomorph n x ∈ U then _ else _) = _
      exact ite_eq_left (show evolutionHomeomorph n x ∈ U from hx)
    · intro p hp
      have he := viscousTransportedOperator_congr_germ B b 0 (hgerm p hp)
      simpa only [viscousTransportedOperator_zero, hVE p hp] using he
    · intro p hp
      have hi : p ∉ U := fun h => (ne_of_lt h.1) hp.1
      simpa only [candidate, ite_eq_right hi] using hw.2.2.2.2.1 p hp
    · intro p hp
      have hf := hp.2
      rw [(isOpen_movingDomain hΩo p.time).frontier_eq] at hf
      have hi : p ∉ U := fun h => hf.2 h.2
      simpa only [candidate, ite_eq_right hi] using hw.2.2.2.2.2 p hp
  have hzero := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F candidate).mpr hclass
  refine ⟨candidate, hclass, ?_, ?_⟩
  · intro D hD hFD
    have _hD := hD
    exact classical_abs_le_const hΩo hγ.1 hlam hB_ell hb_lipschitz
      le_rfl zero_le_one hzero hFD
  · intro z hz
    exact classical_unique hΩo hγ.1 hlam hB_ell hb_lipschitz le_rfl zero_le_one
      ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F z).mpr hz) hzero

end HypoellipticAleksandrov.KineticAleksandrov
