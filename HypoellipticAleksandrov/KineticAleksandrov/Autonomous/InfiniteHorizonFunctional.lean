module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonValues

/-! # Unique positive boundary functional determined by the actual infinite Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped CompactlySupported

/-- The actual homogeneous values extend to exactly one positive contraction functional
on all compactly supported continuous exit data. -/
theorem existsUnique_infiniteBoundaryFunctional
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    ∃! ℓ : C_c(stripInfiniteFace H, ℝ) →ₚ[ℝ] ℝ,
      (∀ (f : C_c(stripInfiniteFace H, ℝ)) (c : ℝ), 0 ≤ c →
        (∀ p, |f p| ≤ c) → |ℓ f| ≤ c) ∧
      ∀ f : exitProbeSubmodule, ℓ (infiniteExitProbeCcLinear H f) = infiniteExitProbeValueLinear
        hH hLE hlam hLam A H e f := by
  obtain ⟨ℓ, hbd, hagree⟩ := exists_positive_extension_of_dense (infiniteExitProbeCcLinear H)
    (infiniteExitProbeValueLinear hH hLE hlam hLam A H e)
    (infiniteExitProbeValueLinear_bound hH hLE hlam hLam A H e)
    (infiniteExitProbeValueLinear_nonneg hH hLE hlam hLam A H e)
    (infiniteExitProbeCc_sq H) (infiniteExitProbeCc_dense H)
  refine ⟨ℓ, ⟨hbd, hagree⟩, fun k hk => ?_⟩
  have hlin : k.toLinearMap = ℓ.toLinearMap :=
    eq_of_bounded_of_dense (infiniteExitProbeCcLinear H) k.toLinearMap ℓ.toLinearMap
      hk.1 hbd (fun f => (hk.2 f).trans (hagree f).symm) (infiniteExitProbeCc_dense H)
  exact PositiveLinearMap.ext (fun f => LinearMap.congr_fun hlin f)

/-- The strip boundary functional is chosen only from its proved unique characterization. -/
def infiniteBoundaryFunctional
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    C_c(stripInfiniteFace H, ℝ) →ₚ[ℝ] ℝ :=
  (existsUnique_infiniteBoundaryFunctional hH hLE hlam hLam A H e).exists.choose

/-- Full contraction and smooth-probe characterization of the unique boundary functional. -/
theorem infiniteBoundaryFunctional_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    (∀ (f : C_c(stripInfiniteFace H, ℝ)) (c : ℝ), 0 ≤ c → (∀ p, |f p| ≤ c) →
      |infiniteBoundaryFunctional hH hLE hlam hLam A H e f| ≤ c) ∧
    ∀ f : exitProbeSubmodule, infiniteBoundaryFunctional hH hLE hlam hLam A H e
      (infiniteExitProbeCcLinear H f) = infiniteExitProbeValueLinear hH hLE hlam hLam A H e f :=
  (existsUnique_infiniteBoundaryFunctional hH hLE hlam hLam A H e).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
