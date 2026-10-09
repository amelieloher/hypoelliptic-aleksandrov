module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactInteriorH1ToH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1PositivePartContinuity
public import PDEFoundation.Sobolev.H1.ZeroBoundaryLimit

/-!
# The order-ideal property of H¹₀

An `H¹` representative lying almost everywhere between zero and an `H¹₀`
representative inherits a representative-level `H¹₀` certificate.
-/

@[expose] public section

namespace PDE.H1Function

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- An `H¹` representative lying almost everywhere between zero and an
`H¹₀` representative has a representative-level `H¹₀` certificate. -/
theorem exists_h10Function_of_ae_nonneg_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.H10Function Ω) (z : PDE.H1Function Ω)
    (hz : ∀ᵐ x ∂(PDE.volumeOn Ω),
      0 ≤ z.toFun x ∧ z.toFun x ≤ u.toH1Function.toFun x) :
    ∃ w : PDE.H10Function Ω, w.toH1Function = z := by
  classical
  let a : ℕ → PDE.H1Function Ω := fun n =>
    (PDE.H10Function.ofContDiff hΩ (u.approx_smooth n)
      (u.approx_hasCompactSupport n) (u.approx_support_subset n)).toH1Function
  obtain ⟨zpos, hzposFun, hzposGrad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hΩ z 0 (by norm_num)
  have hzposFunAE : zpos.toFun =ᵐ[PDE.volumeOn Ω] z.toFun := by
    filter_upwards [hz] with x hx
    rw [hzposFun]
    simp only [sub_zero, max_eq_left hx.1]
  have hzposGradAE : ∀ i : Fin d,
      (fun x => zpos.grad x i) =ᵐ[PDE.volumeOn Ω] (fun x => z.grad x i) := by
    intro i
    filter_upwards [hz, grad_ae_zero_on_zero_set_of_isOpen hΩ z] with x hx hzero
    rw [hzposGrad]
    simp only [indicator_apply, mem_setOf_eq]
    by_cases hzx : 0 < z.toFun x
    · simp [hzx]
    · have hz0 : z.toFun x = 0 := le_antisymm (not_lt.mp hzx) hx.1
      simp [hzx, congrFun (hzero hz0) i]
  have huNonneg : ∀ᵐ x ∂(PDE.volumeOn Ω), 0 ≤ u.toH1Function.toFun x := by
    filter_upwards [hz] with x hx
    exact hx.1.trans hx.2
  have huPosGradAE : ∀ i : Fin d,
      (fun x => {y | 0 < u.toH1Function.toFun y}.indicator
        u.toH1Function.grad x i) =ᵐ[PDE.volumeOn Ω]
        (fun x => u.toH1Function.grad x i) := by
    intro i
    filter_upwards [huNonneg,
      grad_ae_zero_on_zero_set_of_isOpen hΩ u.toH1Function] with x hx hzero
    simp only [indicator_apply, mem_setOf_eq]
    by_cases hux : 0 < u.toH1Function.toFun x
    · simp [hux]
    · have hu0 := le_antisymm (not_lt.mp hux) hx
      simp [hux, congrFun (hzero hu0) i]
  have haVal : Tendsto
      (fun n => eLpNorm ((a n).toFun - u.toH1Function.toFun)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    simpa only [a, PDE.H10Function.ofContDiff_toFun, Pi.sub_def] using u.tendsto_approx
  have haGrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (a n).grad x i - u.toH1Function.grad x i)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    intro i
    simpa only [a, PDE.H10Function.ofContDiff_grad] using u.tendsto_approx_grad i
  choose p hpFun hpGrad using fun n =>
    exists_h1PositivePartSubConst_of_isOpen hΩ (a n) 0 (by norm_num)
  have hpConv := tendsto_positivePart_of_tendsto_eLpNorm hΩ a u.toH1Function haVal haGrad
  let b : ℕ → PDE.H1Function Ω := fun n => zpos - p n
  let b₀ : PDE.H1Function Ω := zpos - u.toH1Function
  have hbVal : Tendsto
      (fun n => eLpNorm ((b n).toFun - b₀.toFun)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    refine hpConv.1.congr' (Filter.Eventually.of_forall fun n => ?_)
    symm
    change eLpNorm (fun x => (b n).toFun x - b₀.toFun x)
      2 (PDE.volumeOn Ω) = _
    rw [PDE.eLpNorm_sub_swap]
    apply eLpNorm_congr_ae
    filter_upwards [huNonneg] with x hux
    simp only [b, b₀, sub_toFun, hpFun, Pi.sub_apply]
    rw [max_eq_left hux]
    abel
  have hbGrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (b n).grad x i - b₀.grad x i)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    intro i
    refine (hpConv.2 i).congr' (Filter.Eventually.of_forall fun n => ?_)
    symm
    rw [PDE.eLpNorm_sub_swap]
    apply eLpNorm_congr_ae
    filter_upwards [huPosGradAE i] with x hux
    simp only [b, b₀, sub_grad, hpGrad, Pi.sub_apply]
    rw [hux]
    abel
  choose q hqFun hqGrad using fun n =>
    exists_h1PositivePartSubConst_of_isOpen hΩ (b n) 0 (by norm_num)
  obtain ⟨q₀, hq₀Fun, hq₀Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hΩ b₀ 0 (by norm_num)
  have hqConv := tendsto_positivePart_of_tendsto_eLpNorm hΩ b b₀ hbVal hbGrad
  have hb₀Nonpos : ∀ᵐ x ∂(PDE.volumeOn Ω), b₀.toFun x ≤ 0 := by
    filter_upwards [hz, hzposFunAE] with x hx hzx
    simp only [b₀, sub_toFun]
    rw [hzx]
    exact sub_nonpos.mpr hx.2
  let F : ℕ → PDE.H1Function Ω := fun n => zpos - q n
  have hFmem : ∀ n, PDE.MemH10 Ω (F n).toFun := by
    intro n
    let K : Set (PDE.Vec d) := tsupport (u.approx n)
    have hFzero : ∀ᵐ x ∂(PDE.volumeOn Ω), x ∉ K → (F n).toFun x = 0 := by
      filter_upwards with x
      intro hx
      have hax : (a n).toFun x = 0 := by
        simp only [a, PDE.H10Function.ofContDiff_toFun, Pi.sub_def]
        exact image_eq_zero_of_notMem_tsupport hx
      have hpx : (p n).toFun x = 0 := by
        rw [hpFun]
        simp [hax]
      simp only [F, sub_toFun, hqFun, b]
      rw [hpx]
      have hzposNonneg : 0 ≤ zpos.toFun x := by
        rw [hzposFun]
        exact le_max_right _ _
      simp only [sub_zero, max_eq_left hzposNonneg, sub_self]
    obtain ⟨w, hw⟩ := exists_h10Function_of_ae_zero_outside_compact hΩ (F n) K
      (u.approx_hasCompactSupport n).isCompact (u.approx_support_subset n) hFzero
    exact ⟨w, congrArg PDE.H1Function.toFun hw⟩
  have hFVal : Tendsto
      (fun n => eLpNorm (fun x => z.toFun x - (F n).toFun x)
        2 (PDE.volumeOn Ω)) atTop (nhds 0) := by
    refine hqConv.1.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [hzposFunAE, hb₀Nonpos] with x hzfun hbzero
    simp only [F, sub_toFun, hqFun, Pi.sub_apply]
    rw [← hzfun, max_eq_right hbzero]
    abel
  have hFGrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => z.grad x i - (F n).grad x i)
        2 (PDE.volumeOn Ω)) atTop (nhds 0) := by
    intro i
    refine (hqConv.2 i).congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [hzposGradAE i, hb₀Nonpos] with x hzgrad hbzero
    simp only [F, sub_grad, hqGrad, Pi.sub_apply]
    rw [← hzgrad]
    simp [indicator_apply, not_lt.mpr hbzero]
  obtain ⟨w, hw⟩ := PDE.memH10_of_tendsto_H1 hΩ z F hFmem hFVal hFGrad
  have hwFun : w.toH1Function.toFun =ᵐ[PDE.volumeOn Ω] z.toFun :=
    Filter.Eventually.of_forall fun x => congrFun hw x
  have hwGrad : ∀ i : Fin d,
      (fun x => w.toH1Function.grad x i) =ᵐ[PDE.volumeOn Ω]
        (fun x => z.grad x i) := by
    intro i
    have hwWeak := w.toH1Function.hasWeakGradient i
    rw [hw] at hwWeak
    exact PDE.HasWeakPartialDerivOn.ae_eq hΩ
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 i).locallyIntegrable (by norm_num)))
      hwWeak (z.hasWeakGradient i)
  exact ⟨PDE.H10Function.copyToH1Function_of_ae_eq w z hwFun hwGrad, rfl⟩

end PDE.H1Function
