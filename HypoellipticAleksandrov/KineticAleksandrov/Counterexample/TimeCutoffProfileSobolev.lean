module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeak
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Local Sobolev regularity of the selected flattened profile -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory
open scoped ENNReal

/-- Concatenation of the native position and velocity weak jets in the standard chart. -/
def spatialPackedGradient {d : ℕ} (gx gv : XV d → PDE.Vec d)
    (x : PDE.Vec (d + d)) : PDE.Vec (d + d) :=
  Fin.addCases (gx (spatialCoordinateCLE d x)) (gv (spatialCoordinateCLE d x))

/-- Native weak first jets supply the full weak gradient in the existing Sobolev chart. -/
theorem weakGradient_spatialCoordinate {d : ℕ} (D : Set (PDE.Vec (d + d)))
    (u : XV d → ℝ) (gx gv : XV d → PDE.Vec d)
    (hweak : ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, u q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, u q * dv test q i) = -(∫ q, gv q i * test q))) :
    PDE.HasWeakGradientOn D (fun x => u (spatialCoordinateCLE d x))
      (spatialPackedGradient gx gv) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [spatialPackedGradient, Fin.addCases_left]
    apply weakPartial_on_of_global
    intro test ht hs
    exact weak_directional_spatialCoordinate u (fun q => gx q j)
      (PDE.basisVec j, 0) (PDE.basisVec (Fin.castAdd d j))
      (spatialCoordinate_basis_position j)
      (fun test ht hs => (hweak test (ht.of_le (by simp)) hs).1 j) test ht hs
  · simp only [spatialPackedGradient, Fin.addCases_right]
    apply weakPartial_on_of_global
    intro test ht hs
    exact weak_directional_spatialCoordinate u (fun q => gv q j)
      (0, PDE.basisVec j) (PDE.basisVec (Fin.natAdd d j))
      (spatialCoordinate_basis_velocity j)
      (fun test ht hs => (hweak test (ht.of_le (by simp)) hs).2 j) test ht hs

/-- Compact bounds and measurability imply finite-exponent membership after chart pullback. -/
theorem memLp_spatialCoordinate_of_compact_bound {d : ℕ} {D : Set (PDE.Vec (d + d))}
    (hD : PDE.IsOpenBoundedConvexDomain D) (f : XV d → ℝ) (hf : Measurable f)
    (hb : ∀ K : Set (XV d), IsCompact K → ∃ C : ℝ, ∀ q ∈ K, ‖f q‖ ≤ C)
    (p : ℝ≥0∞) : PDE.MemLpOn D p (fun x => f (spatialCoordinateCLE d x)) := by
  have : IsFiniteMeasure (PDE.volumeOn D) :=
    hD.isBoundedDomain.isFiniteMeasure_volumeOn
  have hK : IsCompact (spatialCoordinateCLE d '' closure D) :=
    hD.isBoundedDomain.isBounded.isCompact_closure.image (spatialCoordinateCLE d).continuous
  obtain ⟨C, hC⟩ := hb _ hK
  apply MemLp.of_bound
    (hf.comp (spatialCoordinateCLE d).continuous.measurable).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hD.isOpen.measurableSet] with x hx
  exact hC _ ⟨x, subset_closure hx, rfl⟩

/-- The complete upstream source theorem discharges all local Sobolev hypotheses for
its selected value and first jets, including on neighborhoods of the origin. -/
def flatProfileW1p_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D) :
    PDE.W1pFunction D 2 := by
  obtain ⟨hc, hx, hv, _, hb, _, _, _, _, hw, _, _⟩ := hflat hd ha ha1 h r hr
  refine ⟨fun x => selectedFlatProfile h r (spatialCoordinateCLE d x),
    spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r),
    ?_, ?_, weakGradient_spatialCoordinate D _ _ _ (fun t ht hs =>
      ⟨(hw t ht hs).1, (hw t ht hs).2.1⟩)⟩
  · apply memLp_spatialCoordinate_of_compact_bound hD _ hc.measurable
    intro K hK
    obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
    exact ⟨C, fun q hq => hC ⟨q, hq, rfl⟩⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [spatialPackedGradient, Fin.addCases_left]
      apply memLp_spatialCoordinate_of_compact_bound hD _ (measurable_pi_iff.mp hx j)
      intro K hK
      obtain ⟨M, _, hM⟩ := hb K hK
      exact ⟨M, fun q hq => (norm_le_pi_norm _ j).trans (hM q hq).1⟩
    · simp only [spatialPackedGradient, Fin.addCases_right]
      apply memLp_spatialCoordinate_of_compact_bound hD _ (measurable_pi_iff.mp hv j)
      intro K hK
      obtain ⟨M, _, hM⟩ := hb K hK
      exact ⟨M, fun q hq => (norm_le_pi_norm _ j).trans (hM q hq).2.1⟩

/-- The same upstream representatives also give the weak velocity derivatives of the
velocity jet in the packed chart; mixed position derivatives are not required. -/
theorem weak_velocityJet_spatialCoordinate_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (D : Set (PDE.Vec (d + d))) (i k : Fin d) :
    PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => flatProfileVelocityJet h r (spatialCoordinateCLE d x) k)
      (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hw, _, _⟩ := hflat hd ha ha1 h r hr
  apply weakPartial_on_of_global
  intro test ht hs
  apply weak_directional_spatialCoordinate (fun q => flatProfileVelocityJet h r q k)
    (fun q => flatProfileHessian h r q i k) (0, PDE.basisVec i)
    (PDE.basisVec (Fin.natAdd d i)) (spatialCoordinate_basis_velocity i) _ test ht hs
  intro test ht hs
  apply weak_first_jet_of_second (selectedFlatProfile h r) _ _
    (0, PDE.basisVec k) (0, PDE.basisVec i) _ _ test ht hs
  · intro test ht hs
    exact (hw test (ht.of_le (by simp)) hs).2.1 k
  · intro test ht hs
    have he := (hw test (ht.of_le (by simp)) hs).2.2 i k
    simpa only [dvv, dv, PDE.basisVec,
      smooth_test_second_swap test (ht.of_le (by simp))] using! he

/-- Compact Hessian bounds discharge the finite norm hypothesis of the second chain rule. -/
theorem memLp_flatProfileHessian_spatialCoordinate_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (i k : Fin d) (p : ℝ≥0∞) :
    PDE.MemLpOn D p (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
  obtain ⟨_, _, _, hm, hb, _, _, _, _, _, _, _⟩ := hflat hd ha ha1 h r hr
  apply memLp_spatialCoordinate_of_compact_bound hD _ (hm i k)
  intro K hK
  obtain ⟨M, _, hM⟩ := hb K hK
  exact ⟨M, fun q hq => by simpa only [Real.norm_eq_abs] using (hM q hq).2.2 i k⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
