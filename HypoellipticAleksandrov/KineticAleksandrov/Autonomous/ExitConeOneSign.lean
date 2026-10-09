module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone

/-! # The literal lower cone bound on a one-sign velocity interval -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The endpoint minimum is the allowed lower speed on a one-sign open interval. -/
theorem reconstruction_interval_one_sign_min_le (H : Interval) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) (hsign : ∀ v ∈ H.carrier, 0 < sgn * v)
    (v : ℝ) (hv : v ∈ H.carrier) : min |H.lo| |H.hi| ≤ sgn * v := by
  rcases hsgn with rfl | rfl
  · have hm := hsign ((H.lo + H.hi) / 2) (by
      change H.lo < (H.lo + H.hi) / 2 ∧ (H.lo + H.hi) / 2 < H.hi
      constructor <;> linarith [H.ordered])
    have hhi : 0 < H.hi := by linarith [H.ordered]
    have hlo : 0 ≤ H.lo := by
      by_contra hn
      have hh := hsign (H.lo / 2) (by
        change H.lo < H.lo / 2 ∧ H.lo / 2 < H.hi
        constructor <;> linarith)
      linarith
    rw [one_mul]
    exact (min_le_left _ _).trans (by rw [abs_of_nonneg hlo]; exact hv.1.le)
  · have hm := hsign ((H.lo + H.hi) / 2) (by
      change H.lo < (H.lo + H.hi) / 2 ∧ (H.lo + H.hi) / 2 < H.hi
      constructor <;> linarith [H.ordered])
    have hlo : H.lo < 0 := by linarith [H.ordered]
    have hhi : H.hi ≤ 0 := by
      by_contra hn
      have hh := hsign (H.hi / 2) (by
        change H.lo < H.hi / 2 ∧ H.hi / 2 < H.hi
        constructor <;> linarith)
      linarith
    rw [neg_one_mul]
    exact (min_le_right _ _).trans (by
      rw [abs_of_nonpos hhi]
      exact neg_le_neg hv.2.le)

/-- Both finite-horizon measures satisfy the one-sign lower physical cone bound. -/
theorem strip_one_sign_cone_ae_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hsign : ∀ v ∈ H.carrier, 0 < sgn * v) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      min |H.lo| |H.hi| * (p.time - e.1.time) ≤ sgn * (p.position 0 - e.1.position 0)) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      min |H.lo| |H.hi| * (p.time - e.1.time) ≤ sgn * (p.position 0 - e.1.position 0) := by
  let m := min |H.lo| |H.hi|
  have hh := reconstruction_transport_cone_ae hH hlam hLam A H E hE T e m (-sgn)
    (sgn * e.1.position 0 - m * e.1.time)
    (by dsimp only [reconstructionConeCoordinate]; ring)
    (fun v hv => by
      have h := reconstruction_interval_one_sign_min_le H sgn hsgn hsign v hv
      dsimp only [m]
      nlinarith)
  constructor
  · filter_upwards [hh.1] with p hp
    dsimp only [reconstructionConeCoordinate] at hp
    nlinarith
  · filter_upwards [hh.2] with p hp
    dsimp only [reconstructionConeCoordinate] at hp
    nlinarith

/-- The one-sign lower cone holds for actual Green measures at every horizon. -/
theorem strip_one_sign_cone_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hsign : ∀ v ∈ H.carrier, 0 < sgn * v) (T : WithTop ℝ) (e : StripPole H T) :
    stripGreenOfKernel H E.2 T e
      {p | sgn * (p.position 0 - e.1.position 0) <
        min |H.lo| |H.hi| * (p.time - e.1.time)} = 0 := by
  have hf (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
      stripGreenOfKernel H E.2 T e {p | sgn * (p.position 0 - e.1.position 0) <
        min |H.lo| |H.hi| * (p.time - e.1.time)} = 0 := by
    have hh := (strip_one_sign_cone_ae_of_realization hH hlam hLam A H E hE
      sgn hsgn hsign T e).2
    rw [ae_iff] at hh
    simpa only [not_le] using hh
  cases T with
  | coe T => exact hf T e
  | top =>
    apply reconstruction_green_infinite_zero_of_finite H E e
    · exact (isOpen_lt
        (continuous_const.mul (((continuous_apply 0).comp continuous_position).sub
          continuous_const))
        (continuous_const.mul (continuous_time.sub continuous_const))).measurableSet
    · intro T hT
      exact hf T _

/-- The canonical Green family has the source's one-sign lower cone. -/
theorem strip_one_sign_cone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hsign : ∀ v ∈ H.carrier, 0 < sgn * v) (T : WithTop ℝ) (e : StripPole H T) :
    stripGreen hH hLE hlam hLam A H T e
      {p | sgn * (p.position 0 - e.1.position 0) <
        min |H.lo| |H.hi| * (p.time - e.1.time)} = 0 :=
  strip_one_sign_cone_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) sgn hsgn hsign T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
