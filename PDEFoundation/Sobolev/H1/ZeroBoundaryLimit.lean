module

public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Closure of representative-level `H¹₀` under `H¹` limits

The LIH-compatible predicate `MemH10 U` is closed under coordinatewise
`L²(volumeOn U)` convergence of both a representative and its selected weak
gradient.  The proof keeps the approximation data explicit: it diagonalizes
the supported smooth approximations supplied by the sequence of `H¹₀`
witnesses and packages the resulting sequence as an `H10Function` witness
for the limit.

Only openness is used, namely for uniqueness of locally integrable weak
derivatives.  No boundedness or geometric regularity of the domain is needed
for this closure statement.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory Topology

/-- Commuting the two arguments of a pointwise difference does not change its
`Lᵖ` extended norm. -/
theorem eLpNorm_sub_swap {d : ℕ} {μ : Measure (Vec d)}
    (a b : Vec d → ℝ) {p : ℝ≥0∞} :
    eLpNorm (fun x => a x - b x) p μ =
      eLpNorm (fun x => b x - a x) p μ := by
  rw [show (fun x => a x - b x) = -(fun x => b x - a x) from by
    funext x
    simp only [Pi.neg_apply]
    ring, eLpNorm_neg]

/-- **`H¹₀(U)` is closed under representative-level `H¹` limits.**

If an `H¹` representative is the coordinatewise `L²(volumeOn U)` limit of
representatives admitting supported smooth `H¹₀` approximations, then its
chosen representative belongs to `MemH10 U`. -/
theorem memH10_of_tendsto_H1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (f : H1Function U) (F : ℕ → H1Function U)
    (hmem : ∀ n, MemH10 U (F n).toFun)
    (hfun : Tendsto
      (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x)
        2 (volumeOn U))
      atTop (nhds 0))
    (hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => f.grad x i - (F n).grad x i)
        2 (volumeOn U))
      atTop (nhds 0)) :
    MemH10 U f.toFun := by
  classical
  set μU : Measure (Vec d) := volumeOn U with hμU
  choose W hW using hmem
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hbridge : ∀ n (i : Fin d),
      (fun x => (W n).toH1Function.grad x i) =ᵐ[μU]
        (fun x => (F n).grad x i) := by
    intro n i
    have hw := (W n).toH1Function.hasWeakGradient i
    rw [hW n] at hw
    exact HasWeakPartialDerivOn.ae_eq hU (hloc _ i) (hloc _ i) hw
      ((F n).hasWeakGradient i)
  set ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹ with hε
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simp only [hε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_tendsto : Tendsto ε atTop (nhds 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero).comp (tendsto_add_atTop_nat 1)
  have hex : ∀ n, ∃ k,
      eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x)
          2 μU < ε n ∧
      ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n := by
    intro n
    have e1 : ∀ᶠ k in atTop,
        eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x)
            2 μU < ε n :=
      (W n).tendsto_approx.eventually_lt_const (hε_pos n)
    have e2 : ∀ i : Fin d, ∀ᶠ k in atTop,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      fun i => ((W n).tendsto_approx_grad i).eventually_lt_const (hε_pos n)
    have e2' : ∀ᶠ k in atTop, ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      Filter.eventually_all.2 e2
    exact (e1.and e2').exists
  choose k hk using hex
  set ψ : ℕ → Vec d → ℝ := fun n => (W n).approx (k n) with hψ
  have htf : Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x)
        2 μU) atTop (nhds 0) := by
    refine hfun.congr (fun n => ?_)
    rw [eLpNorm_sub_swap ((W n).toH1Function.toFun) (f.toFun), hW n]
  have hfun_bound : Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU)
      atTop (nhds 0) := by
    simpa using hε_tendsto.add htf
  have hgi : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i)
        2 μU) atTop (nhds 0) := by
    intro i
    refine (hgrad i).congr (fun n => ?_)
    rw [eLpNorm_sub_swap (fun x => (W n).toH1Function.grad x i)
      (fun x => f.grad x i)]
    exact eLpNorm_congr_ae (by
      filter_upwards [hbridge n i] with x hx
      rw [hx])
  have hgrad_bound : ∀ i : Fin d, Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU)
      atTop (nhds 0) := by
    intro i
    simpa using hε_tendsto.add (hgi i)
  refine ⟨{ toH1Function := f
            approx := ψ
            approx_smooth := fun n => (W n).approx_smooth (k n)
            approx_hasCompactSupport := fun n => (W n).approx_hasCompactSupport (k n)
            approx_support_subset := fun n => (W n).approx_support_subset (k n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfun_bound
      (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => ψ n x - f.toFun x) =
          (fun x => ψ n x - (W n).toH1Function.toFun x) +
            (fun x => (W n).toH1Function.toFun x - f.toFun x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt (hk n).1) le_rfl
  · intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hgrad_bound i) (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - f.grad x i) =
          (fun x => (fderiv ℝ (ψ n) x) (basisVec i) -
            (W n).toH1Function.grad x i) +
            (fun x => (W n).toH1Function.grad x i - f.grad x i) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt ((hk n).2 i)) le_rfl

end PDE
