module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusConjugacy
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW

/-! # Source-smooth operator conjugacy in the transported carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA

/-- The local normalized scalar diffusion on the full coefficient carrier. -/
def Clock.normalizedCoefficient (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point) :
    FullKineticCoefficient 1 := fun s y _ _ _ => c.diffusion a e s (y 0)

/-- The local normalized scalar transport on the drift carrier. -/
def Clock.normalizedDrift (c : Clock) : PDE.Vec 1 → PDE.Vec 1 :=
  fun y _ => c.drift (y 0)

/-- Exact field-order identification with the Section Two operator. -/
theorem Clock.normalizedOperator_eq_transport (c : Clock) (a : ℝ → ℝ → ℝ)
    (e q : Point) (h : Point → ℝ) :
    c.normalizedOperator a e h q =
      transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
        (h ∘ sectionTwoPoint) (sectionTwoPoint q) := by
  simp only [Clock.normalizedOperator, transportedForwardOperator, Clock.normalizedCoefficient,
    Clock.normalizedDrift, fullKineticCoefficientAt, sectionTwoPoint,
    matrixContraction, PDE.vecDot, Fin.sum_univ_one]
  rfl

/-- The source conjugacy for every function smooth on the normalized open velocity strip. -/
theorem Clock.conjugacy (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point) (h : Point → ℝ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive})
    (p : Point) (hp : p.velocity 0 ∈ c.active) :
    forwardScalarOperator a (h ∘ c.map e) p =
      |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
        transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
          (h ∘ sectionTwoPoint) (sectionTwoPoint (c.map e p)) := by
  have hopen : IsOpen {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} :=
    isOpen_Ioo.preimage (continuous_apply 2)
  have hmem : scalarCoordinates (c.map e p) ∈
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} :=
    (c.mem_active_iff (p.velocity 0)).mp hp
  have hlocal : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates (c.map e p)) :=
    ((hh _ hmem).contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  rw [← c.normalizedOperator_eq_transport a e (c.map e p) h]
  exact c.conjugacy_at a e p h hp hlocal

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
