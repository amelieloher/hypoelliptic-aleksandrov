module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExitCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureSupersolutions

/-! # A single exponential velocity-face estimate without coefficient derivatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal

/-- One velocity face has the exponential early-exit estimate supplied by its literal
classical supersolution. Parameters are internal algebraic data, not analytic inputs. -/
theorem reconstruction_early_face_exponential_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : sMinus ≤ e.1.time) (theta k beta face d : ℝ) (_hk : 0 ≤ k)
    (hbeta : beta ^ 2 = k ^ 2)
    (hface : ∀ v ∈ Icc H.lo H.hi, beta * (v - face) ≤ 0)
    (hd : beta * (e.1.velocity 0 - face) ≤ -k * d) :
    stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 = face ∧ p.time ≤ sMinus + theta} ≤
        ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) := by
  let c := Lam * k ^ 2
  let b := sMinus + theta
  let phi := reconstructionExponentialPlane (-c) beta (c * b - beta * face)
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  have hc : 0 ≤ c := mul_nonneg hLam0.le (sq_nonneg k)
  have hp (p : Point) : phi p = Real.exp (c * (b - p.time) + beta * (p.velocity 0 - face)) := by
    dsimp only [phi, reconstructionExponentialPlane]
    congr 1
    ring
  have hpos (p : Point) : 0 < phi p := by rw [hp]; exact Real.exp_pos _
  have hop (p : Point) : forwardScalarOperator A.a phi p =
      (A.a (p.position 0) (p.velocity 0) - Lam) * k ^ 2 * phi p := by
    rw [reconstructionExponentialPlane_operator, hbeta]
    dsimp only [c]
    ring
  have hpn (p : Point) (ht : e.1.time ≤ p.time) (hv : p.velocity 0 ∈ Icc H.lo H.hi) :
      phi p ≤ Real.exp (c * theta) := by
    rw [hp]
    apply Real.exp_le_exp.mpr
    have hf := hface (p.velocity 0) hv
    have hh : b - p.time ≤ theta := by dsimp only [b]; linarith
    have hh' := mul_le_mul_of_nonneg_left hh hc
    linarith
  have hbound : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ H.carrier → |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M := by
    refine ⟨(1 + c) * Real.exp (c * theta), fun p ht _ hv => ?_⟩
    have hv' : p.velocity 0 ∈ Icc H.lo H.hi := ⟨hv.1.le, hv.2.le⟩
    have hpb := hpn p ht hv'
    have ha := A.bounds (p.position 0) (p.velocity 0)
    have ha0 : 0 ≤ A.a (p.position 0) (p.velocity 0) := hlam.le.trans ha.1
    have hpb0 := (hpos p).le
    constructor
    · rw [abs_of_nonneg hpb0]
      nlinarith [Real.exp_pos (c * theta)]
    · rw [hop, abs_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr ha.2),
        abs_of_nonneg (sq_nonneg k), abs_of_nonneg hpb0]
      have h1 : -(A.a (p.position 0) (p.velocity 0) - Lam) * k ^ 2 ≤ c := by
        dsimp only [c]
        nlinarith [sq_nonneg k]
      have hh := mul_le_mul h1 hpb hpb0 hc
      nlinarith [Real.exp_pos (c * theta)]
  have hB : MeasurableSet {p : Point | p.velocity 0 = face ∧ p.time ≤ b} :=
    (isClosed_eq ((continuous_apply 0).comp continuous_velocity)
      continuous_const).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hmass := stripExitOfRealization_le_supersolution hH hlam hLam A H E hE T e phi
    (reconstructionExponentialPlane_smooth _ _ _) hbound
    (fun p _ _ => by
      rw [hop]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (A.bounds _ _).2) (sq_nonneg k))
        (hpos p).le)
    (fun p _ _ _ => (hpos p).le) _ hB
    (fun p hp' _ _ _ => by
      rw [hp, hp'.1, sub_self, mul_zero, add_zero]
      exact Real.one_le_exp_iff.mpr (mul_nonneg hc (sub_nonneg.mpr hp'.2)))
  apply hmass.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hp]
  apply Real.exp_le_exp.mpr
  have ht : b - e.1.time ≤ theta := by dsimp only [b]; linarith
  have hh := mul_le_mul_of_nonneg_left ht hc
  dsimp only [c] at hh ⊢
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
