module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantKinetic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # From the source Green measures to the localised Aleksandrov estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
local notation "Q" => forwardCylinder Z₀ R hR
local notation "μQ" => volume.restrict Q

/-- The Green-measure argument needs only continuous, pointwise positive diffusion. -/
theorem kinetic_abp_abstract_of_continuous
    (A : FullKineticCoefficient d)
    (hAcont : ContinuousOn (fun P : KineticPoint d => A P.time P.position P.velocity) Q)
    (hApos : ∀ P ∈ Q, (A P.time P.position P.velocity).PosSemidef)
    (q : ℝ) (hq : 1 < q) (K : ℝ) (hK : 0 < K)
    (Γ : KineticPoint d → Measure (KineticPoint d))
    (hpotential : ∀ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)) →
      HasCompactSupport g → tsupport g ⊆ Q → (∀ P, 0 ≤ g P) →
      IsKineticC112On (fun P => ∫ z, g z ∂Γ P) Q ∧
      (∀ P ∈ Q, 0 ≤ ∫ z, g z ∂Γ P) ∧
      (∀ P ∈ Q, forwardKineticOperator A (fun P => ∫ z, g z ∂Γ P) P = -g P))
    (hdensity : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      Γ P = (μQ).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal q) μQ).toReal ≤ K ∧ MemLp G (ENNReal.ofReal q) μQ)
    (u g₀ : KineticPoint d → ℝ)
    (hcont : ContinuousOn u (closure Q)) (hreg : IsKineticC112On u Q)
    (hg₀0 : ∀ P ∈ Q, 0 ≤ g₀ P)
    (hLp : MemLp g₀ (ENNReal.ofReal (q / (q - 1))) μQ)
    (hsub : ∀ᵐ P ∂μQ, -g₀ P ≤ forwardKineticOperator A u P) :
    ∀ P ∈ closure Q, u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
      K * (eLpNorm ({P | 0 < u P}.indicator g₀)
        (ENNReal.ofReal (q / (q - 1))) μQ).toReal := by
  let : IsFiniteMeasureOnCompacts (volume : Measure (KineticPoint d)) :=
    Measure.IsFiniteMeasureOnCompacts.map
      (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))
      (KineticPoint.homeomorphProd d).symm
  let p := q / (q - 1)
  have hpq : q.HolderConjugate p := Real.HolderConjugate.conjExponent hq
  have hp : 1 < p := hpq.symm.lt
  have hQ := isOpen_forwardCylinder Z₀ R hR
  let F := {P | 0 < u P}.indicator g₀
  have hFeq : (Q ∩ {P | 0 < u P}).indicator g₀ =ᵐ[μQ] F := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    simp only [indicator,mem_inter_iff,mem_ofPred_eq,hP,true_and,F]
  have hFs : MeasurableSet (Q ∩ {P | 0 < u P}) :=
    (hreg.continuousOn.isOpen_inter_preimage hQ isOpen_Ioi).measurableSet
  have hFp : MemLp F (ENNReal.ofReal p) μQ := (hLp.indicator hFs).ae_eq hFeq
  let N := (eLpNorm F (ENNReal.ofReal p) μQ).toReal
  let M := sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR)
  have hinterior : ∀ P ∈ Q, u P ≤ M + K * N := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ζ hζ
    let ε := ζ / 4
    let η := ζ / (4 * (K + 1))
    have hε : 0 < ε := by positivity
    have hη : 0 < η := div_pos hζ (by positivity)
    have hbudget : K * η ≤ ζ / 4 := by
      dsimp only [η]
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith only [hK.le,hζ.le]
    obtain ⟨τ,hτ,hboundary⟩ := comparison_exit_boundary_approx Z₀ R hR u hcont hε
    obtain ⟨a,ha,hexhaust⟩ := innerCylinder_exhaustion Z₀ R hR P hP
    let δ := min (R ^ 2 / 4) (min τ a / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδlt : δ < R ^ 2 / 2 := by
      have hd : δ ≤ R ^ 2 / 4 := min_le_left _ _
      nlinarith [sq_pos_of_pos hR]
    have hδτ : δ < τ := by
      have h1 : δ ≤ min τ a / 2 := min_le_right _ _
      have h2 := min_le_left τ a
      linarith only [h1,h2,hτ]
    have hδa : δ < a := by
      have h1 : δ ≤ min τ a / 2 := min_le_right _ _
      have h2 := min_le_right τ a
      linarith only [h1,h2,ha]
    obtain ⟨hdef,hdef0,_,hdom⟩ := abp_defect_cutoff hQ.measurableSet A u g₀
      hreg hAcont hg₀0 hsub ε hε
    have hcut := abpPositiveCutoff_spec hε
    obtain ⟨g,hgs,hgc,hgQ,hg0,hmajor,hgnorm⟩ := exists_smooth_majorant_kinetic hQ
      (isCompact_closure_innerCylinder Z₀ R hR δ hδ0 hδlt)
      (closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt)
      (h := fun P => abpPositiveCutoff ε (u P) * max (-forwardKineticOperator A u P) 0)
      (F := F) ((hcut.1.continuous.comp_continuousOn hreg.continuousOn).mul hdef)
      (fun P _ => mul_nonneg (hcut.2.1 _).1 (hdef0 P))
      (hdom.mono fun _ h => h.2) (ENNReal.one_le_ofReal.mpr hp.le)
      ENNReal.ofReal_ne_top hη
    have hgc' : Continuous g := by
      have he : (fun P : KineticPoint d =>
          g ((KineticPoint.equivProd d).symm ((KineticPoint.homeomorphProd d) P))) = g := by
        funext P
        exact congrArg g ((KineticPoint.equivProd d).symm_apply_apply P)
      rw [← he]
      exact hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous
    have hgp : MemLp g (ENNReal.ofReal p) μQ :=
      (hgc'.memLp_of_hasCompactSupport hgc).mono_measure Measure.restrict_le_self
    have hgN : (eLpNorm g (ENNReal.ofReal p) μQ).toReal ≤ N + η := by
      have hn := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hFp.eLpNorm_ne_top,ENNReal.ofReal_ne_top⟩) hgnorm
      rw [ENNReal.toReal_add hFp.eLpNorm_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hη.le] at hn
      exact hn
    obtain ⟨hW,hW0,hWop⟩ := hpotential g hgs hgc hgQ hg0
    have hcompare := abp_potential_comparison Z₀ R hR A u
      (fun P => ∫ z, g z ∂Γ P) g hreg hW hW0 hWop hApos δ hδ0 hδlt ε hε
      hmajor (M + ε) (hboundary δ hδ0 hδlt hδτ) P (hexhaust δ hδ0 hδlt hδa)
    obtain ⟨G,hG,hG0,hΓ,hGnorm,hGq⟩ := hdensity P hP
    have hWbound := abp_potential_holder μQ (Γ P) G g hpq hG hG0
      (Filter.Eventually.of_forall hg0) hΓ hGq hgp hGnorm
    have hb : (∫ z, g z ∂Γ P) ≤ K * (N + η) :=
      hWbound.trans (mul_le_mul_of_nonneg_left hgN hK.le)
    dsimp only [ε] at hcompare
    nlinarith only [hcompare,hb,hbudget,hζ]
  exact le_on_closure hinterior hcont continuousOn_const

/-- Source proposition Proposition 6.2, including its local smooth ellipticity conditions. -/
theorem kinetic_abp_abstract
    (A : FullKineticCoefficient d) (lam Lam : ℝ) (hlam : 0 < lam)
    (hA : ∀ P ∈ Q, lam • (1 : PDE.Mat d) ≤ A P.time P.position P.velocity ∧
      A P.time P.position P.velocity ≤ Lam • (1 : PDE.Mat d))
    (hsymm : ∀ P ∈ Q, (A P.time P.position P.velocity).IsSymm)
    (hsmooth : ∃ D : Set (KineticPoint d), IsOpen D ∧ closure Q ⊆ D ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × (PDE.Vec d × PDE.Vec d) => A z.1 z.2.1 z.2.2)
        ((KineticPoint.equivProd d).symm ⁻¹' D))
    (q : ℝ) (hq : 1 < q) (K : ℝ) (hK : 0 < K)
    (Γ : KineticPoint d → Measure (KineticPoint d))
    (hpotential : ∀ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)) →
      HasCompactSupport g → tsupport g ⊆ Q → (∀ P, 0 ≤ g P) →
      IsKineticC112On (fun P => ∫ z, g z ∂Γ P) Q ∧
      (∀ P ∈ Q, 0 ≤ ∫ z, g z ∂Γ P) ∧
      (∀ P ∈ Q, forwardKineticOperator A (fun P => ∫ z, g z ∂Γ P) P = -g P))
    (hdensity : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      Γ P = (μQ).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal q) μQ).toReal ≤ K ∧ MemLp G (ENNReal.ofReal q) μQ)
    (u g₀ : KineticPoint d → ℝ)
    (hcont : ContinuousOn u (closure Q)) (hreg : IsKineticC112On u Q)
    (hg₀ : Measurable g₀) (hg₀0 : ∀ P ∈ Q, 0 ≤ g₀ P)
    (hLp : MemLp g₀ (ENNReal.ofReal (q / (q - 1))) μQ)
    (hsub : ∀ᵐ P ∂μQ, -g₀ P ≤ forwardKineticOperator A u P) :
    ∀ P ∈ closure Q, u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
      K * (eLpNorm ({P | 0 < u P}.indicator g₀)
        (ENNReal.ofReal (q / (q - 1))) μQ).toReal := by
  obtain ⟨D,_,hQD,hsm⟩ := hsmooth
  have hcontA : ContinuousOn (fun P : KineticPoint d => A P.time P.position P.velocity) Q := by
    apply hsm.continuousOn.comp (KineticPoint.homeomorphProd d).continuous.continuousOn
    intro P hP
    change (KineticPoint.equivProd d).symm ((KineticPoint.equivProd d) P) ∈ D
    rw [Equiv.symm_apply_apply]
    exact hQD (subset_closure hP)
  exact kinetic_abp_abstract_of_continuous Z₀ R hR A hcontA
    (fun P hP => (HypoellipticAleksandrov.posDef_of_loewner_lower hlam (hA P hP).1).posSemidef)
    q hq K hK Γ hpotential hdensity u g₀ hcont hreg hg₀0 hLp hsub

end HypoellipticAleksandrov.KineticAleksandrov
