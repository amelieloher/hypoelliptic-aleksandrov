module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePartForward
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePartBackward

/-! # Shifted-positive-part reverse-time Steklov energy identities -/
@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Fixed-window forward Steklov shifted-positive-part energy identity. -/
theorem reverseTimeForwardSteklov_shiftedPositivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b + h ≤ T) :
    shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeForwardSteklov T h u t) b -
      shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeForwardSteklov T h u t) a =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t := by
  rw [← reverseTimeForwardSteklov_shiftedPositivePart_halfEnergy_identity hΩ
    hΩb T hT M N u g hd hh ha hab hb]
  simp only [shiftedPositivePartEnergy, shiftedPositivePartHalfEnergy,
    valueCLM_h10ShiftedPositivePart]
  ring

/-- Fixed-window backward Steklov shifted-positive-part energy identity. -/
theorem reverseTimeBackwardSteklov_shiftedPositivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a - h) (hab : a ≤ b) (hb : b ≤ T) :
    shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeBackwardSteklov T h u t) b -
      shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeBackwardSteklov T h u t) a =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeBackwardSteklov T h u s)
        (fun s ↦ reverseTimeBackwardSteklov T h g s) t := by
  rw [← reverseTimeBackwardSteklov_shiftedPositivePart_halfEnergy_identity hΩ
    hΩb T hT M N u g hd hh ha hab hb]
  simp only [shiftedPositivePartEnergy, shiftedPositivePartHalfEnergy,
    valueCLM_h10ShiftedPositivePart]
  ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
