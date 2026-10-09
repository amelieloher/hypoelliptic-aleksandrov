module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenDensityTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Main
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI

/-!
# Theorem 1.1: uniform finite-horizon density bound on the reflected cylinder

Companion paper, proof of Theorem 1.1.  After reflection (case W), let `Q = 𝒬_R(-t₀,-x₀,v₀)` be the
forward cylinder `forwardCylinder (kineticReflection P₀) R hR`, let `P ∈ Q`, let `S_P < R²` be the
remaining time and `q = p/(p-1)`, `p > 2d+1`.  The whole-space Green measure `Γ_P` from the unit
point mass at `P`, restricted to `Q` and written in absolute time, has a Lebesgue density `G_P` with
`‖G_P‖_{L^q(Q)} ≤ C S_P^{(1-2d(q-1))/q} ≤ C R^{2-(4d+2)/p}`, `C = C(d,λ,Λ,p)`.

The theorem is **conditional** (distinct name `..._of_slabFourierBounds`): its only premise besides
the source data is `hbounds`, the family-level conclusion of Lemma 5.1 (the premise of
`Green.green_density_of_slab_marginals`, with the structural constants `C_γ, c` fixed before the
coefficient and uniform over the Section 2 coefficients of case (W) with realizing `(S,K)`).  It is
discharged by Lemma 5.1.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- The case-W starting state `(v,z) = (V,X)` of a kinetic point `P = (σ,X,V)`. -/
def kineticStartState (d : ℕ) (P : KineticPoint d) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) P.time :=
  ⟨(P.velocity, P.position), by
    rw [evolutionStateSet, movingDomain_wholeSpace]
    exact ⟨mem_univ _, mem_univ _⟩⟩

/-- The remaining time `S_P = s₀ + R² - s` of a point `P = (s,X,v)` in a forward cylinder
with bottom time `s₀ = Z₀.time`. -/
def remainingTime {d : ℕ} (Z₀ P : KineticPoint d) (R : ℝ) : ℝ := Z₀.time + R ^ 2 - P.time

/-- Forward cylinders are open, hence measurable. -/
theorem measurableSet_forwardCylinder' {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    MeasurableSet (forwardCylinder Z₀ R hR) := by
  have ht : Continuous (@KineticPoint.time d) := continuous_time
  have hv : Continuous (@KineticPoint.velocity d) := continuous_velocity
  have hrel : Continuous (fun P : KineticPoint d => relativePosition Z₀ P) :=
    ((continuous_position.sub continuous_const).sub
      ((ht.sub continuous_const).smul continuous_const))
  exact ((isOpen_lt continuous_const ht).inter ((isOpen_lt ht continuous_const).inter
    (((PDE.isOpen_euclideanBall Z₀.velocity R).preimage hv).inter
      ((PDE.isOpen_euclideanBall (0 : PDE.Vec d) (R ^ 3)).preimage hrel)))).measurableSet

/-- Exponent algebra: with `q = p/(p-1)` and `p > 2d+1`, `S^{δ_q/q} ≤ (R²)^{δ_q/q} = R^{2-(4d+2)/p}`
for `0 ≤ S ≤ R²`. -/
theorem greenDelta_rpow_le {d : ℕ} {p S R : ℝ} (hp : 2 * (d : ℝ) + 1 < p) (hS : 0 ≤ S)
    (hSR : S ≤ R ^ 2) (hR : 0 < R) :
    S ^ ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1))) ≤
      R ^ (2 - (4 * (d : ℝ) + 2) / p) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have he : (1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1)) = (p - 1 - 2 * d) / p := by
    field_simp
    ring
  have h2 : 2 - (4 * (d : ℝ) + 2) / p = 2 * ((p - 1 - 2 * d) / p) := by
    field_simp
    ring
  have hnn : 0 ≤ (p - 1 - 2 * d) / p := div_nonneg (by linarith) hp0.le
  rw [he, h2, Real.rpow_mul hR.le]
  calc S ^ ((p - 1 - 2 * (d : ℝ)) / p) ≤ (R ^ 2) ^ ((p - 1 - 2 * (d : ℝ)) / p) :=
        Real.rpow_le_rpow hS hSR hnn
    _ = (R ^ (2 : ℝ)) ^ ((p - 1 - 2 * (d : ℝ)) / p) := by
        rw [Real.rpow_two]

/-- **Conditional Theorem 1.1.**  See the module docstring.  The premise `hbounds`
is the conclusion of Lemma 5.1 for all case-W coefficients and realizing `(S,K)`, with
structural constants `C_γ, c` fixed first; `C = greenConstant d (p/(p-1)) C_γ` depends only on
`d, λ, Λ, p`. -/
theorem green_density_bound_of_slabFourierBounds {d : ℕ} (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (A : CoefficientField d),
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient (kineticReflectedCoefficient A)) (identityDrift d) S K →
      ∀ P ∈ forwardCylinder (kineticReflection P₀) R hR,
      ∀ ΓP : Measure (ElapsedTime (ENNReal.ofReal (remainingTime (kineticReflection P₀) P R)) ×
          EvolutionAmbientState d),
        IsGreenMeasure K P.time (ENNReal.ofReal (remainingTime (kineticReflection P₀) P R))
          (Measure.dirac (kineticStartState d P)) ΓP →
      ∃ G : KineticPoint d → ℝ≥0∞, Measurable G ∧
        (ΓP.map (greenKineticPoint d P.time)).restrict
            (forwardCylinder (kineticReflection P₀) R hR) =
          (volume.restrict (forwardCylinder (kineticReflection P₀) R hR)).withDensity G ∧
        eLpNorm G (ENNReal.ofReal (p / (p - 1)))
            (volume.restrict (forwardCylinder (kineticReflection P₀) R hR)) ≤
          ENNReal.ofReal (C * remainingTime (kineticReflection P₀) P R ^
            ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1)))) ∧
        C * remainingTime (kineticReflection P₀) P R ^
            ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1))) ≤
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) := by
  obtain ⟨Cγ, c, hb⟩ := hbounds
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hq : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ hp1]
    linarith
  have hqd : p / (p - 1) < 1 + 1 / (2 * (d : ℝ)) := by
    have h : p / (p - 1) = 1 + 1 / (p - 1) := by field_simp; ring
    rw [h]
    have : 1 / (p - 1) < 1 / (2 * (d : ℝ)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  refine ⟨((greenConstant d (p / (p - 1)) Cγ : ℝ≥0) : ℝ), NNReal.coe_nonneg _, ?_⟩
  intro P₀ R hR A hsm hsymm hlo hhi S K hreal P hP ΓP hΓP
  have hP' := (mem_forwardCylinder_iff _ _ _ hR).1 hP
  have hSP : 0 < remainingTime (kineticReflection P₀) P R := by
    unfold remainingTime
    linarith [hP'.2.1]
  have hSR : remainingTime (kineticReflection P₀) P R < R ^ 2 := by
    unfold remainingTime
    linarith [hP'.1]
  have hset := (caseW_sourceSetting hlam hLam hsm hsymm hlo hhi).1
  let μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) P.time) :=
    Measure.dirac (kineticStartState d P)
  have hΓ := greenMeasure_spec K P.time ⊤ (by simp) μ
  have hbd := hb _ hset S K hreal P.time μ _ hΓ
  obtain ⟨G₀, hG₀m, hΓP', hnorm⟩ := green_density_of_slab_marginals Cγ c K P.time μ _ hΓ hbd
    hq hqd hSP ΓP hΓP
  obtain ⟨hGm, hGden, hGnorm⟩ := greenKineticPoint_density P.time _ ΓP G₀ hG₀m hΓP'
    (measurableSet_forwardCylinder' (kineticReflection P₀) R hR)
  refine ⟨_, hGm, hGden, ?_, ?_⟩
  · refine (hGnorm _).trans (hnorm.trans (le_of_eq ?_))
    have hμ : μ Set.univ = 1 := measure_univ
    rw [hμ, mul_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    rfl
  · exact mul_le_mul_of_nonneg_left
      (greenDelta_rpow_le hp hSP.le hSR.le hR) (NNReal.coe_nonneg _)

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
