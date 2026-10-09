module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign

/-! # Future-time and one-sign cone support of the actual infinite exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Any almost-everywhere property shared by all finite exits passes to the infinite exit. -/
theorem stripInfiniteExit_ae_of_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (P : Point → Prop)
    (hP : ∀ T : ℝ, ∀ ht : e.1.time < T,
      ∀ᵐ p ∂stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T ht), P p) :
    ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e, P p := by
  let t (n : ℕ) := e.1.time + (n : ℝ) + 1
  have ht (n : ℕ) : e.1.time < t n := by
    dsimp only [t]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn (n : ℕ) : ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e,
      p.time < t n → P p := by
    apply (ae_restrict_iff'
      (isOpen_lt continuous_time continuous_const).measurableSet).mp
    rw [stripInfiniteExit_restrict_finite hH hLE hlam hLam A H e (t n) (ht n)
      (t n) le_rfl]
    exact ae_restrict_of_ae (hP (t n) (ht n))
  filter_upwards [ae_all_iff.mpr hn] with p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
  apply hp n
  dsimp only [t]
  linarith

/-- Infinite exits occur at or after the pole and at an actual interval endpoint. -/
theorem stripInfiniteExit_ae_future_faces
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e,
      e.1.time ≤ p.time ∧ (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi) := by
  have ht : ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e, e.1.time ≤ p.time := by
    apply stripInfiniteExit_ae_of_finite hH hLE hlam hLam A H e
    intro T ht
    exact (stripExitOfRealization_ae_closed_future hH hlam hLam A H _
      (stripEvolution_spec hH hLE hlam hLam A H) T (stripPoleFinite H e T ht)).mono
        (fun _ hp => hp.1)
  have hf : ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e, p ∈ stripInfiniteFace H := by
    rw [ae_iff]
    exact stripInfiniteExit_compl_face hH hLE hlam hLam A H e
  filter_upwards [ht, hf] with p ht hf
  exact ⟨ht, hf⟩

/-- The source's lower one-sign cone also holds for the infinite exit measure. -/
theorem stripInfiniteExit_ae_one_sign_cone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hsign : ∀ v ∈ H.carrier, 0 < sgn * v) :
    ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e,
      min |H.lo| |H.hi| * (p.time - e.1.time) ≤ sgn * (p.position 0 - e.1.position 0) := by
  apply stripInfiniteExit_ae_of_finite hH hLE hlam hLam A H e
  intro T ht
  exact (strip_one_sign_cone_ae_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) sgn hsgn hsign T
      (stripPoleFinite H e T ht)).1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
