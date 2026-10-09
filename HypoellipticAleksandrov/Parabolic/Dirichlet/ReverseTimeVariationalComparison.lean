module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentativeAlgebra
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePositivePartOrder
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase

/-! # Weak comparison for reverse-time variational energy solutions -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance comparisonModule {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) := MeasureTheory.Lp.instModule

private theorem comparison_scalar_energy
    (g₁ g₂ B₁ B₂ Bw Bp S₁ S₂ G V lam K : ℝ)
    (h₁ : g₁ + B₁ = S₁) (h₂ : g₂ + B₂ = S₂)
    (hBsub : B₁ - B₂ = Bw) (hBpos : Bw = Bp) (hS : S₁ - S₂ ≤ 0)
    (hG : (lam / 2) * G - K * V ≤ Bp) :
    2 * (g₁ - g₂) + lam * G ≤ 2 * K * V := by
  linarith

private theorem comparison_energy_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT u g hd ⟨t, ht⟩)‖ ^ 2 -
      ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT u g hd
        ⟨0, ⟨le_rfl, hT.le⟩⟩)‖ ^ 2 =
      2 * ∫ r in Ioc 0 t, (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T := by
  exact reverseTimeHilbertRepresentative_posPart_norm_sq_increment hΩ T hT u g hd
    0 t ⟨le_rfl, hT.le⟩ ht ht.1

private theorem comparison_initialTrace_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u₁ u₂ : ReverseTimeL2V hΩ T) (g₁ g₂ : ReverseTimeL2VStar hΩ T)
    (hd₁ : HasGelfandWeakTimeDerivative hΩ T hT u₁ g₁)
    (hd₂ : HasGelfandWeakTimeDerivative hΩ T hT u₂ g₂)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT (u₁-u₂) (g₁-g₂)) :
    reverseTimeInitialTrace hΩ T hT (u₁-u₂) (g₁-g₂) hd =
      reverseTimeInitialTrace hΩ T hT u₁ g₁ hd₁ -
        reverseTimeInitialTrace hΩ T hT u₂ g₂ hd₂ := by
  have hr := reverseTimeHilbertRepresentative_sub_eq hΩ T hT
    u₁ g₁ hd₁ u₂ g₂ hd₂ hd
  have he := congrArg (fun Q : C(Icc 0 T, PDE.ScalarLp Ω (2 : ℝ≥0∞)) =>
    Q ⟨0,⟨le_rfl,hT.le⟩⟩) hr
  convert he using 1 <;> rfl

private def comparisonClamp (T r : ℝ) := min T (max 0 r)

private theorem comparisonClamp_mem {T : ℝ} (hT : 0 < T) (r : ℝ) :
    comparisonClamp T r ∈ Icc 0 T := by
  exact ⟨le_min hT.le (le_max_left _ _), min_le_left _ _⟩

private theorem comparisonClamp_eq {T r : ℝ} (hr : r ∈ Icc 0 T) :
    comparisonClamp T r = r := by
  simp only [comparisonClamp, max_eq_right hr.1, min_eq_right hr.2]

private theorem comparisonClamp_continuous (T : ℝ) : Continuous (comparisonClamp T) :=
  continuous_const.min (continuous_const.max continuous_id)

private theorem comparison_clamped_energy_zero
    {E : Type*} [NormedAddCommGroup E] [Lattice E] [Norm E]
    {T : ℝ} (hT : 0 < T) (W : C(Icc 0 T, E))
    (hW0 : ‖W ⟨0,⟨le_rfl,hT.le⟩⟩‖ = 0) :
    ‖W ⟨comparisonClamp T 0, comparisonClamp_mem hT 0⟩‖^2 = 0 := by
  have hh : (⟨comparisonClamp T 0,comparisonClamp_mem hT 0⟩ : Icc 0 T) =
      ⟨0,⟨le_rfl,hT.le⟩⟩ := Subtype.ext (comparisonClamp_eq ⟨le_rfl,hT.le⟩)
  rw [hh, hW0]
  norm_num

private theorem comparison_posPart_clamped_energy_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hT : 0 < T)
    (W : C(Icc 0 T, PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hW0 : Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
    ‖Lp.posPart (W ⟨comparisonClamp T 0, comparisonClamp_mem hT 0⟩)‖^2 = 0 := by
  exact comparison_clamped_energy_zero hT
    ⟨fun q => Lp.posPart (W q), Lp.continuous_posPart.comp W.continuous⟩
    (by change ‖Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩)‖ = 0; rw [hW0, norm_zero])

private theorem comparison_setIntegral_eq
    (f : ℝ → ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ r in Ioc 0 t, f r ∂reverseTimeVolume T) = ∫ r in Ioc 0 t, f r := by
  rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact inter_eq_left.mpr (Ioc_subset_Icc_self.trans fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)

private theorem comparison_value_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (w : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT w g) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ r in Ioc 0 t, ‖valueCLM hΩ (h10PositivePart hΩ (w r))‖ ^ 2
      ∂reverseTimeVolume T) =
    ∫ r in Ioc 0 t, ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd
      ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖ ^ 2 := by
  let W := reverseTimeHilbertRepresentative hΩ T hT w g hd
  have hW := (reverseTimeHilbertRepresentative_spec hΩ T hT w g hd).1
  calc
    _ = ∫ r in Ioc 0 t, ‖Lp.posPart (W
        ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖ ^ 2
        ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hW,
        ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with r hWr hr
      have hrcc : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
      have hWr' : W ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩ =
          valueCLM hΩ (w r) := by simpa only [comparisonClamp_eq hrcc] using hWr hr
      rw [hWr', ← valueCLM_h10PositivePart]
    _ = _ := comparison_setIntegral_eq _ ht

private theorem comparison_posPart_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (w : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT w g) (K : ℝ) (hK : 0 ≤ K)
    (hrate : ∀ᵐ τ ∂reverseTimeVolume T,
      2 * (g τ) (h10PositivePart hΩ (w τ)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2 * 0 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2)
    (hW0 : Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd
      ⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
    ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd ⟨t,ht⟩) = 0 := by
  let W := reverseTimeHilbertRepresentative hΩ T hT w g hd
  let E : ℝ → ℝ := fun t => ‖Lp.posPart
    (W ⟨comparisonClamp T t, comparisonClamp_mem hT t⟩)‖^2
  have hEc : ContinuousOn E (Icc 0 T) :=
    (((Lp.continuous_posPart.comp W.continuous).norm.pow 2).comp
      ((comparisonClamp_continuous T).subtype_mk _)).continuousOn
  have hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t := fun _ _ => sq_nonneg _
  have hE0 : E 0 = 0 := by
    exact comparison_posPart_clamped_energy_zero hT W hW0
  have hEle : ∀ t ∈ Icc 0 T, E t ≤ (2*K) * ∫ r in Ioc 0 t, E r := by
    intro t ht
    have hi := comparison_energy_increment hΩ T hT w g hd t ht
    have hpair : Integrable (fun r => (g r) (h10PositivePart hΩ (w r)))
        (reverseTimeVolume T) :=
      (integrable_reverseTimeDualPairing hΩ T (reverseTimePositivePart hΩ T w) g).congr (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
        rw [hr])
    have hm := (Lp.memLp (reverseTimePositivePart hΩ T w)).continuousLinearMap_comp
      (valueCLM hΩ)
    have hv : Integrable (fun r => ‖valueCLM hΩ (h10PositivePart hΩ (w r))‖^2)
        (reverseTimeVolume T) :=
      ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).congr (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
        rw [hr])
    have hint : (∫ r in Ioc 0 t, 2 * (g r) (h10PositivePart hΩ (w r))
        ∂reverseTimeVolume T) ≤
        ∫ r in Ioc 0 t, 2*K*‖valueCLM hΩ (h10PositivePart hΩ (w r))‖^2
          ∂reverseTimeVolume T :=
      setIntegral_mono_ae_restrict (hpair.const_mul 2).integrableOn
      (hv.const_mul (2*K)).integrableOn (ae_restrict_of_ae (by
        filter_upwards [hrate] with r hr
        simpa only [mul_zero, add_zero] using hr))
    rw [integral_const_mul, integral_const_mul] at hint
    have hval := comparison_value_integral hΩ T hT w g hd t ht
    have hh : (⟨comparisonClamp T t,comparisonClamp_mem hT t⟩ : Icc 0 T) =
        ⟨t,ht⟩ := Subtype.ext (comparisonClamp_eq ht)
    dsimp only [E]
    rw [hW0, norm_zero, zero_pow (by norm_num), sub_zero] at hi
    have hbound : ‖Lp.posPart (W ⟨t,ht⟩)‖^2 ≤
        2*K * ∫ r in Ioc 0 t, ‖Lp.posPart
          (W ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖^2 := by
      dsimp only [W]
      rw [← hval]
      linarith
    calc
      _ = ‖Lp.posPart (W ⟨t,ht⟩)‖^2 :=
        congrArg (fun q : Icc 0 T => ‖Lp.posPart (W q)‖^2) hh
      _ ≤ _ := hbound
  have hz := eq_zero_on_Icc_of_nonneg_le_mul_integral hT
    (mul_nonneg (by norm_num) hK) E hEc hEn hE0 hEle
  intro t ht
  have hh : (⟨comparisonClamp T t,comparisonClamp_mem hT t⟩ : Icc 0 T) =
      ⟨t,ht⟩ := Subtype.ext (comparisonClamp_eq ht)
  have hs : ‖Lp.posPart (W ⟨t,ht⟩)‖^2 = 0 := by
    simpa only [E, hh] using hz t ht
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (Lp.posPart (W ⟨t,ht⟩))]

private theorem comparison_ae_rate
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F₁ F₂ : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₁Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₁ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₂Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₂ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (hF₂leF₁ : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      F₂ z.1 z.2 ≤ F₁ z.1 z.2)
    (initial₁ initial₂ : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u₁ : ReverseTimeL2V hΩ (r₁-r₀)) (g₁ : ReverseTimeL2VStar hΩ (r₁-r₀))
    (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₁ g₁)
    (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁)
    (u₂ : ReverseTimeL2V hΩ (r₁-r₀)) (g₂ : ReverseTimeL2VStar hΩ (r₁-r₀))
    (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₂ g₂)
    (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * ((g₁-g₂) τ) (h10PositivePart hΩ ((u₁-u₂) τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 := by
  obtain ⟨K,hK,hGard⟩ := reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  refine ⟨K,hK,?_⟩
  rcases hu₁ with ⟨_,heq₁⟩
  rcases hu₂ with ⟨_,heq₂⟩
  filter_upwards [heq₁,heq₂,Lp.coeFn_sub u₁ u₂,Lp.coeFn_sub g₁ g₂,
    ae_restrict_mem measurableSet_Ioo] with τ heq₁τ heq₂τ huτ hgτ hτ
  have hτcc : τ ∈ Icc 0 (r₁-r₀) := ⟨hτ.1.le,hτ.2.le⟩
  let w := u₁ τ-u₂ τ
  let wp := h10PositivePart hΩ w
  let f₁ := reverseTimeSourceSlice r₁ τ F₁
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₁ hF₁Smooth τ hτcc)
  let f₂ := reverseTimeSourceSlice r₁ τ F₂
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₂ hF₂Smooth τ hτcc)
  have hs : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y := by
    filter_upwards [coeFn_reverseTimeSourceSlice r₁ τ F₁ _,
      coeFn_reverseTimeSourceSlice r₁ τ F₂ _,ae_restrict_mem hΩ.measurableSet]
      with y h1 h2 hy
    rw [h1,h2]
    exact hF₂leF₁ (r₁-τ,y) ⟨⟨by linarith [h₀₁,hτ.2],by linarith [hτ.1]⟩,
      subset_closure hy⟩
  have hS := reverseTimeSourceFunctional_sub_nonpos_of_ae_le hΩ f₁ f₂ hs w
  have e₁ : (g₁ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp =
      reverseTimeSourceFunctional hΩ f₁ wp := heq₁τ hτ wp
  have e₂ : (g₂ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
      reverseTimeSourceFunctional hΩ f₂ wp := heq₂τ hτ wp
  let B := reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth ⟨τ,hτcc⟩
  have hB : reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp -
      reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
      reverseTimeSpatialForm hΩ r₁ τ a b c w wp := by
    have hm := congrArg (fun q : H10HilbertGraphDual hΩ => q wp)
      (B.map_sub (u₁ τ) (u₂ τ))
    simpa only [B,reverseTimeSpatialFormOperator_apply,ContinuousLinearMap.sub_apply,w]
      using hm.symm
  have hBp := reverseTimeSpatialForm_apply_positivePart_eq hΩ r₁ τ a b c w
  have hG := hGard τ hτcc wp
  rw [huτ,hgτ]
  change 2*((g₁ τ) wp-(g₂ τ) wp)+lam*‖gradientCLM hΩ wp‖^2 ≤
    2*K*‖valueCLM hΩ wp‖^2
  exact comparison_scalar_energy _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ hB hBp hS hG

/-- Reverse-time variational comparison: ordered initial data and the original-source
orientation `F₂ ≤ F₁` imply spatial almost-everywhere order at every closed time. -/
theorem reverseTimeVariationalEnergySolution_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F₁ F₂ : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₁Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₁ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₂Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₂ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (hF₂leF₁ : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      F₂ z.1 z.2 ≤ F₁ z.1 z.2)
    (initial₁ initial₂ : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, initial₁ y ≤ initial₂ y)
    (u₁ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₁ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₁ g₁)
    (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁)
    (u₂ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₂ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₂ g₂)
    (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₁ g₁ hdu₁ ⟨τ, hτ⟩ y ≤
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₂ g₂ hdu₂ ⟨τ, hτ⟩ y := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let hd : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) hT
      (u₁ - u₂) (g₁ - g₂) := by
    change HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
      (u₁ - u₂) (g₁ - g₂)
    simpa [sub_eq_add_neg] using hdu₁.add (hdu₂.smul (-1 : ℝ))
  obtain ⟨K,hK,hrate⟩ := comparison_ae_rate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F₁ F₂ haSmooth hbSmooth hcSmooth hF₁Smooth hF₂Smooth hLower hcNonpos
    hF₂leF₁ initial₁ initial₂ u₁ g₁ hdu₁ hu₁ u₂ g₂ hdu₂ hu₂
  let wd : ReverseTimeL2V hΩ (r₁-r₀) := u₁-u₂
  let gd : ReverseTimeL2VStar hΩ (r₁-r₀) := g₁-g₂
  let hdd : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) hT wd gd := hd
  have hrate' : ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * (gd τ) (h10PositivePart hΩ (wd τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 := by
    simpa only [wd, gd] using hrate
  let W := reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT wd gd hdd
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁-r₀) hT
    u₁ g₁ hdu₁ u₂ g₂ hdu₂ hd
  have hW0 : Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩) = 0 := by
    have ht1 := hu₁.1
    have ht2 := hu₂.1
    change Lp.posPart (reverseTimeInitialTrace hΩ (r₁-r₀) hT (u₁-u₂) (g₁-g₂) hd) = 0
    have htrace := comparison_initialTrace_sub hΩ (r₁-r₀) hT
      u₁ u₂ g₁ g₂ hdu₁ hdu₂ hd
    rw [htrace, ht1, ht2]
    apply Lp.ext
    filter_upwards [Lp.coeFn_posPart (initial₁-initial₂), Lp.coeFn_sub initial₁ initial₂,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω), hinitial]
      with y hp hs hz hi
    rw [hp, hs, hz]
    simp only [Pi.sub_apply]
    exact max_eq_right (sub_nonpos.mpr hi)
  intro τ hτ
  have hrate0 : ∀ᵐ r ∂reverseTimeVolume (r₁-r₀),
      2 * (gd r) (h10PositivePart hΩ (wd r)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 * 0 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 := by
    filter_upwards [hrate'] with r hr
    have hg : 0 ≤ lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa only [mul_zero, add_zero] using (show
      2 * (gd r) (h10PositivePart hΩ (wd r)) ≤
        2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 by linarith)
  have hp := comparison_posPart_zero hΩ (r₁-r₀) hT wd gd hdd K hK hrate0 hW0 τ hτ
  have hw : ∀ᵐ y ∂PDE.volumeOn Ω, W ⟨τ,hτ⟩ y ≤ 0 := by
    filter_upwards [Lp.ext_iff.mp hp, Lp.coeFn_posPart (W ⟨τ,hτ⟩),
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω)] with y hy hpy hz
    rw [hpy, hz] at hy
    exact max_eq_right_iff.mp hy
  have hrepW : W = reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ -
      reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ := by
    dsimp only [W, wd, gd, hdd]
    exact hrep
  rw [hrepW] at hw
  filter_upwards [hw, Lp.coeFn_sub
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩)
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩)] with y hy hsy
  change ((reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩ -
    reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩) y) ≤ 0 at hy
  rw [hsy] at hy
  exact sub_nonpos.mp hy

end HypoellipticAleksandrov.Parabolic.Dirichlet
