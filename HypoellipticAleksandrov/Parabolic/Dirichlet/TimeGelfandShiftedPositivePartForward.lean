module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport

/-! # Forward Steklov shifted-positive-part energy estimate -/
@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem forward_shifted_rate_continuous
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0) {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Continuous (shiftedPositivePartEnergyRate hΩ hΩb M N
      (fun s ↦ reverseTimeForwardSteklov T h u s)
      (fun s ↦ reverseTimeForwardSteklov T h g s)) := by
  have hx := continuous_reverseTimeForwardSteklov T h hh u
  have hy := continuous_reverseTimeForwardSteklov T h hh g
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp (hx.prodMk hk)
  exact (hy.clm_apply hp).sub (continuous_const.mul
    ((spatialMassCLM hΩb).continuous.comp ((valueCLM hΩ).continuous.comp hp)))

private theorem forward_shifted_halfEnergy_continuous
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    {h : ℝ} (hh : 0 < h) (u : ReverseTimeL2V hΩ T) :
    Continuous (fun t ↦ shiftedPositivePartHalfEnergy hΩ
      (reverseTimeForwardSteklov T h u t) (reverseTimeAffineThreshold M N t)) := by
  have hx := continuous_reverseTimeForwardSteklov T h hh u
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp (hx.prodMk hk)
  have hc := (continuous_const : Continuous (fun _ : ℝ ↦ (1 / 2 : ℝ))).mul
    ((continuous_norm.comp ((valueCLM hΩ).continuous.comp hp)).pow 2)
  convert hc using 1
  funext t
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def, shiftedPositivePartHalfEnergy,
    valueCLM_h10ShiftedPositivePart]

private theorem hasDerivAt_forward_shifted_halfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b t : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hb : b + h ≤ T) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ shiftedPositivePartHalfEnergy hΩ
      (reverseTimeForwardSteklov T h u s) (reverseTimeAffineThreshold M N s))
      (shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t) t := by
  exact hasDerivAt_shiftedPositivePartHalfEnergy hΩ hΩb M N _
    (continuous_reverseTimeForwardSteklov T h hh u) _ t (by linarith [ha, ht.1])
    (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hd hh
      (by linarith [ha, ht.1]) (by linarith [hb, ht.2]))

/-- Half-energy identity underlying the forward fixed-window formula. -/
theorem reverseTimeForwardSteklov_shiftedPositivePart_halfEnergy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b + h ≤ T) :
    shiftedPositivePartHalfEnergy hΩ (reverseTimeForwardSteklov T h u b)
        (reverseTimeAffineThreshold M N b) -
      shiftedPositivePartHalfEnergy hΩ (reverseTimeForwardSteklov T h u a)
        (reverseTimeAffineThreshold M N a) =
      ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (forward_shifted_halfEnergy_continuous hΩ T M N hh u).continuousOn
    (fun t ht ↦ hasDerivAt_forward_shifted_halfEnergy hΩ hΩb T hT M N u g hd
      hh ha hb ht)
    ((forward_shifted_rate_continuous hΩ hΩb T M N hh u g).intervalIntegrable a b)
  rw [← hFTC, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

end HypoellipticAleksandrov.Parabolic.Dirichlet
