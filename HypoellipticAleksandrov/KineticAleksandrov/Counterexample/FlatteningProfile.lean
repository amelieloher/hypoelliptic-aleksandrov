module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSource
import Mathlib.Tactic.Ring

/-! # The complete flattened-profile conditions

The representatives below use the jointly selected witnesses of the profile statement.
The proposition records the full conclusion proved in `FlatteningSourceProfile`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The literal flattening of the selected profile. -/
noncomputable def selectedFlatProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) : XV d → ℝ :=
  flatProfile (profileFunction h) flatteningPsi flatteningOffset alpha r

/-- The position derivative representative obtained by the scalar chain rule. -/
noncomputable def flatProfilePositionJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (q : XV d) : PDE.Vec d :=
  fun i => -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
    profilePositionJet h q i

/-- The velocity derivative representative obtained by the scalar chain rule. -/
noncomputable def flatProfileVelocityJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (q : XV d) : PDE.Vec d :=
  fun i => -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
    profileVelocityJet h q i

/-- The second velocity derivative, including the rank-one chain-rule term. -/
noncomputable def flatProfileHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (q : XV d) : PDE.Mat d :=
  fun i k =>
    -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profileHessian h q i k -
    Real.rpow r (-alpha) *
      deriv (deriv flatteningPsi) (profileFunction h q / Real.rpow r alpha) *
      profileVelocityJet h q i * profileVelocityJet h q k

/-- The selected literal flattened profile is continuous. -/
theorem continuous_selectedFlatProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) :
    Continuous (selectedFlatProfile h r) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  unfold selectedFlatProfile flatProfile
  exact continuous_const.sub (continuous_const.mul
    (contDiff_flatteningPsi.continuous.comp (hH.div_const _)))

/-- The ordinary first chain rule at a differentiability point of the unflattened profile. -/
theorem fderiv_flatProfile {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hH : DifferentiableAt ℝ H q) :
    fderiv ℝ (flatProfile H flatteningPsi flatteningOffset alpha r) q =
      (-deriv flatteningPsi (H q / Real.rpow r alpha)) • fderiv ℝ H q := by
  let a := Real.rpow r alpha
  have ha : a ≠ 0 := (Real.rpow_pos_of_pos hr alpha).ne'
  have hin : HasFDerivAt (fun z => H z / a) (a⁻¹ • fderiv ℝ H q) q := by
    simpa only [div_eq_mul_inv, mul_comm] using hH.hasFDerivAt.const_mul a⁻¹
  have hp : DifferentiableAt ℝ flatteningPsi (H q / a) :=
    (contDiff_flatteningPsi.differentiable (by simp)).differentiableAt
  have hout := hp.hasDerivAt.comp_hasFDerivAt q hin
  have hu := (hout.const_mul a).const_sub (1 - flatteningOffset * a)
  have he := hu.fderiv
  change fderiv ℝ (flatProfile H flatteningPsi flatteningOffset alpha r) q = _ at he
  rw [he]
  simp only [smul_smul]
  rw [← neg_smul]
  congr 1
  dsimp [a] at ha ⊢
  field_simp

/-- Entrywise contraction expands the rank-one term of the flattening chain rule. -/
theorem contraction_flattening_identity {d : ℕ} (A B : PDE.Mat d)
    (w : PDE.Vec d) (s t : ℝ) :
    matrixContraction A (fun i k => -s * B i k - t * w i * w k) =
      -s * matrixContraction A B - t * PDE.vecDot (A.mulVec w) w := by
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The explicit weak representatives satisfy the source equation algebraically almost everywhere.
This conclusion alone does not establish that they are derivatives of the flattened profile. -/
theorem flatProfile_representatives_source {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) :
    ∀ᵐ q ∂volume,
      PDE.vecDot q.2 (flatProfilePositionJet h r q) -
        matrixContraction (profileMatrix h q) (flatProfileHessian h r q) =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  have hEq := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJets := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hEq, hJets] with q hq hj
  unfold flatProfilePositionJet flatProfileHessian
  rw [contraction_flattening_identity]
  unfold flatSource
  rw [← hj.2.1, hq]
  have hdot (s : ℝ) :
      PDE.vecDot q.2 (fun i => -s * profilePositionJet h q i) =
        -s * PDE.vecDot q.2 (profilePositionJet h q) := by
    unfold PDE.vecDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot]
  ring

/-- All explicit flattened derivative representatives are measurable. -/
theorem measurable_flatProfile_jets {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) :
    Measurable (flatProfilePositionJet h r) ∧ Measurable (flatProfileVelocityJet h r) ∧
      (∀ i k, Measurable (fun q => flatProfileHessian h r q i k)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hmx := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.1
  have hmv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.1
  have hmh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpsi : Continuous (deriv flatteningPsi) := by
    rw [funext deriv_flatteningPsi]
    exact contDiff_flatteningSlope.continuous
  have hpsi2 : Continuous (deriv (deriv flatteningPsi)) := by
    rw [funext deriv_flatteningPsi]
    exact contDiff_flatteningSlope.continuous_deriv (by simp)
  have harg := hH.measurable.div_const (Real.rpow r alpha)
  have hs := (hpsi.measurable.comp harg).neg
  have ht : Measurable (fun q : XV d => Real.rpow r (-alpha) *
      deriv (deriv flatteningPsi) (profileFunction h q / Real.rpow r alpha)) :=
    measurable_const.mul (hpsi2.measurable.comp harg)
  refine ⟨?_, ?_, ?_⟩
  · apply Measurable.of_eval
    intro i
    exact hs.mul ((measurable_pi_apply i).comp hmx)
  · apply Measurable.of_eval
    intro i
    exact hs.mul ((measurable_pi_apply i).comp hmv)
  · intro i k
    exact (hs.mul (hmh i k)).sub
      ((ht.mul ((measurable_pi_apply i).comp hmv)).mul ((measurable_pi_apply k).comp hmv))

/-- The complete weak flattened-profile conclusion required by the mollification lane. -/
def FlatProfileSourceStatement {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) : Prop :=
  let u := selectedFlatProfile h r
  let gx := flatProfilePositionJet h r
  let gv := flatProfileVelocityJet h r
  let hess := flatProfileHessian h r
  Continuous u ∧
  Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
  (∀ K : Set (XV d), IsCompact K →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K,
      ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
  (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
  (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
  (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
  (∀ᵐ q ∂volume, gx q = dx u q ∧ gv q = dv u q ∧ hess q = dvv u q) ∧
  (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
    (∀ i, (∫ q, u q * dx test q i) = -(∫ q, gx q i * test q)) ∧
    (∀ i, (∫ q, u q * dv test q i) = -(∫ q, gv q i * test q)) ∧
    (∀ i k, (∫ q, u q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
  (∀ᵐ q ∂volume,
    PDE.vecDot q.2 (gx q) - matrixContraction (profileMatrix h q) (hess q) =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q) ∧
  (∀ᵐ q ∂volume, statOp (profileMatrix h) u q =
    flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
