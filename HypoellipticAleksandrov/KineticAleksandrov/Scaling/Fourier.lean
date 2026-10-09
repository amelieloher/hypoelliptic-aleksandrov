module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Unique
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.EllipticityScaling

/-!
# Fourier projections under an affine change of variables (companion paper, (2.12))

Since `z' - z = a (τ' - τ) w + e (Z' - Z)`, the Fourier projection of the original kernel at
frequency `ξ` is the constant phase `exp (-i a (τ' - τ) ξ · w)` times the affine image of the
Fourier projection of the rescaled kernel at frequency `e ξ`.  The affine image and the
constant phase preserve total variation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

theorem vecDot_sub_right {d : ℕ} (x y z : PDE.Vec d) :
    PDE.vecDot x (y - z) = PDE.vecDot x y - PDE.vecDot x z := by
  simp only [PDE.vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem vecDot_smul_right {d : ℕ} (c : ℝ) (x y : PDE.Vec d) :
    PDE.vecDot x (c • y) = c * PDE.vecDot x y := by
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum]

namespace KineticAffineScaling

variable {d : ℕ} {Φ : KineticAffineScaling d} {Ω Ω' : Set (PDE.Vec d)}
  {γ γ' : ℝ → PDE.Vec d}

/-- The affine change of the diffused coordinate as a measurable equivalence. -/
def positionEquiv (Φ : KineticAffineScaling d) : PDE.Vec d ≃ᵐ PDE.Vec d :=
  Φ.positionHomeo.toMeasurableEquiv

@[simp] theorem positionEquiv_apply (Φ : KineticAffineScaling d) (Y : PDE.Vec d) :
    Φ.positionEquiv Y = Φ.position Y := rfl

/-- The constant phase `exp (-i a (τ' - τ) ξ · w)` of the source's Lemma 2.5. -/
def fourierShiftPhase (Φ : KineticAffineScaling d) (τ τ' : ℝ) (ξ : PDE.Vec d) : ℂ :=
  Complex.exp (-Complex.I * ((Φ.a * (τ' - τ) * PDE.vecDot ξ Φ.w : ℝ) : ℂ))

theorem norm_fourierShiftPhase (Φ : KineticAffineScaling d) (τ τ' : ℝ) (ξ : PDE.Vec d) :
    ‖Φ.fourierShiftPhase τ τ' ξ‖ = 1 := by
  simp [fourierShiftPhase, Complex.norm_exp, Complex.mul_re]

/-- Pointwise phase identity: the original phase is the constant phase times the rescaled
phase at frequency `e ξ`. -/
theorem fourierPhase_comp (Φ : KineticAffineScaling d) (τ τ' : ℝ) (ξ Z : PDE.Vec d)
    (x : EvolutionAmbientState d) :
    fourierPhase ξ (Φ.transport τ Z) x =
      Φ.fourierShiftPhase τ τ' ξ *
        fourierPhase (Φ.e • ξ) Z ((Φ.ambientEquiv τ').symm x) := by
  unfold fourierPhase fourierShiftPhase
  rw [← Complex.exp_add]
  congr 1
  have hdiff : Φ.transportInv τ' x.2 - Z =
      Φ.e⁻¹ • ((x.2 - Φ.transport τ Z) - (Φ.a * τ' - Φ.a * τ) • Φ.w) := by
    have hZ : Z = Φ.transportInv τ (Φ.transport τ Z) := (Φ.transportInv_transport τ Z).symm
    conv_lhs => rw [hZ]
    unfold transportInv transport
    rw [← smul_sub]
    congr 1
    module
  have hreal : PDE.vecDot (Φ.e • ξ) (Φ.transportInv τ' x.2 - Z) =
      PDE.vecDot ξ (x.2 - Φ.transport τ Z) - Φ.a * (τ' - τ) * PDE.vecDot ξ Φ.w := by
    rw [hdiff, vecDot_smul_left, vecDot_smul_right, vecDot_sub_right, vecDot_smul_right,
      ← mul_assoc, mul_inv_cancel₀ Φ.e_pos.ne', one_mul]
    ring
  simp only [ambientEquiv_symm_apply]
  rw [hreal]
  push_cast
  ring

/-- **Fourier projections** (companion paper, Lemma 2.5).  If `ν` is the Fourier projection
of `K` at the original query `Φ q'` and frequency `ξ`, and `ν'` that of the pushed-forward
kernel at `q'` and frequency `e ξ`, then
`ν E = exp (-i a (τ' - τ) ξ · w) · ν' (Φ⁻¹ E)` for every Borel set `E`. -/
theorem isFourierProjection_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (q' : EvolutionQuery Ω' γ') (ξ : PDE.Vec d) (ν ν' : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K (queryMap h q') ξ ν)
    (hν' : IsFourierProjection (pushKernel h K) q' (Φ.e • ξ) ν')
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    ν E = Φ.fourierShiftPhase q'.1.1 q'.1.2.1 ξ * ν' (Φ.position ⁻¹' E) := by
  have hE' : MeasurableSet (Φ.position ⁻¹' E) := Φ.positionEquiv.measurable hE
  rw [hν E hE, hν' _ hE', pushKernel_master_apply, setIntegral_map_equiv]
  have hset : (Φ.ambientEquiv q'.1.2.1).symm ⁻¹' ((Φ.position ⁻¹' E) ×ˢ (univ : Set (PDE.Vec d))) =
      E ×ˢ (univ : Set (PDE.Vec d)) := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, and_true, ambientEquiv_symm_apply,
      Φ.position_positionInv]
  rw [hset, ← integral_const_mul]
  refine setIntegral_congr_fun (hE.prod MeasurableSet.univ) fun x _ => ?_
  exact Φ.fourierPhase_comp q'.1.1 q'.1.2.1 ξ q'.1.2.2.2 x

/-- **Total variation** (companion paper, (2.12)): under the hypotheses of
`isFourierProjection_pushKernel`, `‖ν‖_TV = ‖ν'‖_TV`. -/
theorem totalVariation_fourier_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ')
    (K : MovingFiberKernel Ω γ) (q' : EvolutionQuery Ω' γ') (ξ : PDE.Vec d)
    (ν ν' : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K (queryMap h q') ξ ν)
    (hν' : IsFourierProjection (pushKernel h K) q' (Φ.e • ξ) ν') :
    totalVariationNorm ν = totalVariationNorm ν' := by
  have hmap : ν = Φ.fourierShiftPhase q'.1.1 q'.1.2.1 ξ • ν'.map Φ.positionEquiv := by
    apply VectorMeasure.ext
    intro E hE
    rw [isFourierProjection_pushKernel h K q' ξ ν ν' hν hν' E hE,
      smul_apply, VectorMeasure.map_apply _ Φ.positionEquiv.measurable hE]
    rfl
  unfold totalVariationNorm
  rw [hmap, VectorMeasure.variation_smul, Measure.smul_apply,
    variation_map_equiv_univ Φ.positionEquiv ν']
  have : ‖Φ.fourierShiftPhase q'.1.1 q'.1.2.1 ξ‖₊ = 1 := by
    rw [← NNReal.coe_inj]
    exact Φ.norm_fourierShiftPhase _ _ _
  rw [this, one_smul]

/-- **Fourier projections of any two realizations** (companion paper, Lemma 2.5 and
(2.12)): for realizations `(S, K)` of the original problem and `(S', K')` of the rescaled
one, the Fourier projections `ν` of `K` (at `Φ q'`, frequency `ξ`) and `ν'` of `K'` (at `q'`,
frequency `e ξ`) satisfy `ν E = exp (-i a (τ' - τ) ξ · w) · ν' (Φ⁻¹ E)` and have equal total
variation. -/
theorem realizes_fourier_tv (h : Φ.MapsDomain Ω γ Ω' γ')
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hΩ' : IsAdmissibleEvolutionDomain Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    {S' : TerminalOperatorFamily Ω' γ'} {K' : MovingFiberKernel Ω' γ'}
    (hreal' : RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') (Φ.coefficient B) (Φ.drift b) S' K')
    (q' : EvolutionQuery Ω' γ') (ξ : PDE.Vec d) (ν ν' : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K (queryMap h q') ξ ν)
    (hν' : IsFourierProjection K' q' (Φ.e • ξ) ν') :
    (∀ E : Set (PDE.Vec d), MeasurableSet E →
      ν E = Φ.fourierShiftPhase q'.1.1 q'.1.2.1 ξ * ν' (Φ.position ⁻¹' E)) ∧
      totalVariationNorm ν = totalVariationNorm ν' := by
  have hK := (realizes_unique_pushKernel h hΩ hγ hΩ' hreal hreal').1
  subst hK
  exact ⟨fun E hE => isFourierProjection_pushKernel h K q' ξ ν ν' hν hν' E hE,
    totalVariation_fourier_pushKernel h K q' ξ ν ν' hν hν'⟩

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
