module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionLinearity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalProbe

/-! # Smooth compact physical probes and their actual trace restrictions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic
open scoped CompactlySupported

/-- Ambient smooth compact probes in exactly the stipulated physical product coordinates. -/
def boundaryProbeSubmodule (d : ℕ) : Submodule ℝ (ℝ × PDE.Vec d × PDE.Vec d → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun _c _f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

/-- The literal physical function represented by an ambient product probe. -/
def boundaryProbePhysical {d : ℕ} (f : boundaryProbeSubmodule d) : KineticPoint d → ℝ :=
  f.1 ∘ KineticPoint.equivProd d

/-- Every probe has the full stipulated smoothness, continuity and compact support. -/
theorem boundaryProbePhysical_regular {d : ℕ} (f : boundaryProbeSubmodule d) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryProbePhysical f ∘ (KineticPoint.equivProd d).symm) ∧
      Continuous (boundaryProbePhysical f) ∧ HasCompactSupport (boundaryProbePhysical f) := by
  have heq : boundaryProbePhysical f ∘ (KineticPoint.equivProd d).symm = f.1 := by
    funext q
    exact congrArg f.1 ((KineticPoint.equivProd d).apply_symm_apply q)
  refine ⟨by rw [heq]; exact f.2.1, ?_, ?_⟩
  · exact f.2.1.continuous.comp (KineticPoint.homeomorphProd d).continuous
  · exact f.2.2.comp_homeomorph (KineticPoint.homeomorphProd d)

/-- A probe restricts to a genuine compactly supported continuous function on the full trace. -/
def boundaryProbeCc {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (f : boundaryProbeSubmodule d) : C_c(localTrace a T v₀ R, ℝ) where
  toFun P := boundaryProbePhysical f P.1
  continuous_toFun := (boundaryProbePhysical_regular f).2.1.comp continuous_subtype_val
  hasCompactSupport' := (boundaryProbePhysical_regular f).2.2.comp_isClosedEmbedding
    (isClosed_localTrace a T v₀ R).isClosedEmbedding_subtypeVal

/-- Trace restriction is linear before any functional or measure is selected. -/
def boundaryProbeCcLinear {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    boundaryProbeSubmodule d →ₗ[ℝ] C_c(localTrace a T v₀ R, ℝ) where
  toFun := boundaryProbeCc a T v₀ R
  map_add' f g := by ext P; rfl
  map_smul' c f := by ext P; rfl

/-- Products of a probe with itself supply squares in the dense trace range. -/
theorem boundaryProbeCc_sq {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (f : boundaryProbeSubmodule d) :
    ∃ g : boundaryProbeSubmodule d,
      boundaryProbeCcLinear a T v₀ R g =
        boundaryProbeCcLinear a T v₀ R f * boundaryProbeCcLinear a T v₀ R f := by
  refine ⟨⟨fun x => f.1 x * f.1 x, f.2.1.mul f.2.1, f.2.2.mul_left⟩, ?_⟩
  ext P
  rfl

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Actual homogeneous reconstruction values form a linear functional on smooth probes. -/
def boundaryProbeValueLinear (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    boundaryProbeSubmodule d →ₗ[ℝ] ℝ where
  toFun f := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 (boundaryProbePhysical f) P.1
  map_add' f g := ballBoundarySolution_add hH hLE hd hlam hLam B hB v₀ hR _ _ _ _
    (boundaryProbePhysical_regular f).1 (boundaryProbePhysical_regular g).1
    (boundaryProbePhysical_regular f).2.2 (boundaryProbePhysical_regular g).2.2 P.1
  map_smul' c f := ballBoundarySolution_const_mul hH hLE hd hlam hLam B hB v₀ hR _ _ c _
    (boundaryProbePhysical_regular f).1 P.1

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
