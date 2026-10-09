module

public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Extension by zero for `H¹₀`

This module proves the literal extension-by-zero operation along an inclusion
of open domains.  It is formulated on the native `Vec d` carrier and on the
representative-level `H1Function`/`H10Function` interfaces shared with the
application repositories.

## Main definitions

- `H10Function.zeroExtendToH1`: the `H¹(U)` core of the zero extension.
- `H10Function.zeroExtend`: the same operation with its supported smooth
  approximation retained explicitly.

## Main results

- `H10Function.zeroExtend_toFun` and `H10Function.zeroExtend_grad` identify
  the value and chosen weak gradient with their literal indicators on `V`.

The proof does not use a trace characterization.  The approximating smooth
functions already have support inside `V`, so they are also valid zero-boundary
approximants on `U`; integration by parts passes to the limit through the
explicit `L²` convergence fields.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ}

/-! ## Local measure and pairing lemmas -/

/-- Restricting restricted volume to a measurable subset of its domain. -/
private theorem restrict_restrict_of_subset {U V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    (volume.restrict U).restrict V = volume.restrict V := by
  rw [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVU]

/-- Zero extension from a measurable subdomain preserves scalar `L²` membership. -/
theorem memL2On_indicator_of_subset {U V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} (hu : MemL2On V u) :
    MemL2On U (Set.indicator V u) := by
  refine (memLp_indicator_iff_restrict hV).2 ?_
  rw [restrict_restrict_of_subset hV hVU]
  exact hu

private theorem indicator_coord (V : Set (Vec d)) (f : Vec d → Vec d) (i : Fin d) :
    (fun x => Set.indicator V f x i) = Set.indicator V (fun x => f x i) := by
  funext x
  by_cases hx : x ∈ V
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem indicator_mul_right (V : Set (Vec d)) (f g : Vec d → ℝ) (x : Vec d) :
    Set.indicator V f x * g x = Set.indicator V (fun y => f y * g y) x := by
  by_cases hx : x ∈ V
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem tendsto_setIntegral_mul_of_eLpNorm_sub_tendsto
    {V : Set (Vec d)} {g f : Vec d → ℝ} {F : ℕ → Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict V))
    (hf : MemLp f 2 (volume.restrict V))
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict V))
    (hlim : Tendsto
      (fun n => eLpNorm (fun x => F n x - f x) 2 (volume.restrict V))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in V, F n x * g x ∂volume)
      atTop (nhds (∫ x in V, f x * g x ∂volume)) := by
  set μ := volume.restrict V with hμdef
  have hFn_int : ∀ n, Integrable (fun x => F n x * g x) μ := by
    intro n
    simpa using! (hF n).integrable_mul hg
  have hL1_bound : ∀ n,
      eLpNorm (fun x => (F n x - f x) * g x) 1 μ ≤
        eLpNorm (fun x => F n x - f x) 2 μ * eLpNorm g 2 μ := by
    intro n
    have hd_meas : AEStronglyMeasurable (fun x => F n x - f x) μ :=
      ((hF n).sub hf).aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
        (μ := μ) (p := (2 : ENNReal)) (q := (2 : ENNReal)) (r := (1 : ENNReal))
        (fun a b : ℝ => a * b) 1 continuous_mul hd_meas hg_meas
        (Eventually.of_forall fun x => by simp))
  have hgtop : eLpNorm g 2 μ ≠ ⊤ := hg.eLpNorm_lt_top.ne
  have hL1 :
      Tendsto
        (fun n => eLpNorm (fun x => (F n x - f x) * g x) 1 μ)
        atTop (nhds 0) := by
    have hscaled :
        Tendsto
          (fun n => eLpNorm (fun x => F n x - f x) 2 μ * eLpNorm g 2 μ)
          atTop (nhds 0) := by
      have h := ENNReal.Tendsto.mul_const hlim (Or.inr hgtop)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hscaled (fun _ => zero_le) hL1_bound
  have hL1' :
      Tendsto
        (fun n => eLpNorm (fun x => F n x * g x - f x * g x) 1 μ)
        atTop (nhds 0) := by
    have hfun :
        (fun n => eLpNorm (fun x => F n x * g x - f x * g x) 1 μ) =
          fun n => eLpNorm (fun x => (F n x - f x) * g x) 1 μ := by
      funext n
      congr 1
      funext x
      ring
    rw [hfun]
    exact hL1
  exact tendsto_integral_of_L1' (μ := μ)
    (fun x => f x * g x) (Eventually.of_forall hFn_int) hL1'

private theorem approx_eq_zero_off {V : Set (Vec d)} (u : H10Function V) (n : ℕ)
    {x : Vec d} (hx : x ∉ V) : u.approx n x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hmem => hx (u.approx_support_subset n hmem))

private theorem approx_fderiv_eq_zero_off {V : Set (Vec d)} (u : H10Function V) (n : ℕ)
    {x : Vec d} (hx : x ∉ V) (i : Fin d) :
    (fderiv ℝ (u.approx n) x) (basisVec i) = 0 := by
  have hx' : x ∉ tsupport (fderiv ℝ (u.approx n)) := fun hmem =>
    hx (u.approx_support_subset n (tsupport_fderiv_subset ℝ hmem))
  rw [image_eq_zero_of_notMem_tsupport hx']
  rfl

private theorem setIntegral_eq_of_zero_off {U V : Set (Vec d)} (hVU : V ⊆ U)
    {h : Vec d → ℝ} (hzero : ∀ x, x ∉ V → h x = 0) :
    ∫ x in V, h x ∂volume = ∫ x in U, h x ∂volume := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun hxV => hx (hVU hxV)))]

/-! ## The extension operations -/

namespace H10Function

/-- Extend an `H¹₀(V)` representative by literal zero to the larger open
domain `U`.  The companion `H10Function.zeroExtend` retains the approximation
data certifying the zero boundary condition on `U`. -/
noncomputable def zeroExtendToH1 {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) : H1Function U where
  toFun := Set.indicator V u.toH1Function.toFun
  grad := Set.indicator V u.toH1Function.grad
  memL2 := memL2On_indicator_of_subset hV.measurableSet hVU u.toH1Function.memL2
  gradMemL2 := by
    intro i
    rw [indicator_coord V u.toH1Function.grad i]
    exact memL2On_indicator_of_subset hV.measurableSet hVU
      (u.toH1Function.gradMemL2 i)
  hasWeakGradient := by
    intro i φ hφ hφc hφs
    set gphi : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i) with hgphi
    have hφ_cont : Continuous φ := hφ.continuous
    have hgphi_cont : Continuous gphi := by
      simpa [hgphi] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hgphi_supp : HasCompactSupport gphi := by
      simpa [hgphi] using hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hφ_memV : MemLp φ 2 (volume.restrict V) :=
      (hφ_cont.memLp_of_hasCompactSupport hφc).restrict V
    have hgphi_memV : MemLp gphi 2 (volume.restrict V) :=
      (hgphi_cont.memLp_of_hasCompactSupport hgphi_supp).restrict V
    have happrox_memV : ∀ n, MemLp (u.approx n) 2 (volume.restrict V) :=
      fun n =>
        ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
          (u.approx_hasCompactSupport n)).restrict V
    have happroxd_memV : ∀ n,
        MemLp (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2
          (volume.restrict V) := by
      intro n
      have hcont : Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
        simpa using
          ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
      have hsupp : HasCompactSupport
          (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
        simpa using
          (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact (hcont.memLp_of_hasCompactSupport hsupp).restrict V
    have hAtend :
        Tendsto (fun n => ∫ x in V, u.approx n x * gphi x ∂volume)
          atTop (nhds (∫ x in V, u.toH1Function.toFun x * gphi x ∂volume)) :=
      tendsto_setIntegral_mul_of_eLpNorm_sub_tendsto hgphi_memV
        u.toH1Function.memL2 happrox_memV u.tendsto_approx
    have hBtend :
        Tendsto
          (fun n => ∫ x in V, (fderiv ℝ (u.approx n) x) (basisVec i) * φ x ∂volume)
          atTop (nhds (∫ x in V, u.toH1Function.grad x i * φ x ∂volume)) :=
      tendsto_setIntegral_mul_of_eLpNorm_sub_tendsto hφ_memV
        (u.toH1Function.gradMemL2 i) happroxd_memV (u.tendsto_approx_grad i)
    have hAB : ∀ n,
        (∫ x in V, u.approx n x * gphi x ∂volume) =
          -∫ x in V, (fderiv ℝ (u.approx n) x) (basisVec i) * φ x ∂volume := by
      intro n
      have hAU :
          (∫ x in V, u.approx n x * gphi x ∂volume) =
            ∫ x in U, u.approx n x * gphi x ∂volume :=
        setIntegral_eq_of_zero_off hVU
          (fun x hx => by rw [approx_eq_zero_off u n hx, zero_mul])
      have hBU :
          (∫ x in V, (fderiv ℝ (u.approx n) x) (basisVec i) * φ x ∂volume) =
            ∫ x in U, (fderiv ℝ (u.approx n) x) (basisVec i) * φ x ∂volume :=
        setIntegral_eq_of_zero_off hVU
          (fun x hx => by rw [approx_fderiv_eq_zero_off u n hx i, zero_mul])
      have hIBP :=
        (HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
          ((u.approx_smooth n).of_le (by simp))) φ hφ hφc hφs
      rw [hAU, hBU]
      exact hIBP
    have hAtend' :
        Tendsto (fun n => ∫ x in V, u.approx n x * gphi x ∂volume)
          atTop (nhds (-∫ x in V, u.toH1Function.grad x i * φ x ∂volume)) := by
      rw [show (fun n => ∫ x in V, u.approx n x * gphi x ∂volume) =
          fun n => -∫ x in V, (fderiv ℝ (u.approx n) x) (basisVec i) * φ x ∂volume
        from funext hAB]
      exact hBtend.neg
    have hkey :
        (∫ x in V, u.toH1Function.toFun x * gphi x ∂volume) =
          -∫ x in V, u.toH1Function.grad x i * φ x ∂volume :=
      tendsto_nhds_unique hAtend hAtend'
    calc
      ∫ x in U, Set.indicator V u.toH1Function.toFun x *
          (fderiv ℝ φ x) (basisVec i) ∂volume =
          ∫ x in U, Set.indicator V (fun y => u.toH1Function.toFun y * gphi y) x
            ∂volume := by
              refine setIntegral_congr_fun hU.measurableSet ?_
              intro x _
              exact indicator_mul_right V u.toH1Function.toFun gphi x
      _ = ∫ x in V, u.toH1Function.toFun x * gphi x ∂volume := by
            rw [setIntegral_indicator hV.measurableSet,
              Set.inter_eq_self_of_subset_right hVU]
      _ = -∫ x in V, u.toH1Function.grad x i * φ x ∂volume := hkey
      _ = -∫ x in U, Set.indicator V (fun y => u.toH1Function.grad y i * φ y) x
            ∂volume := by
              rw [setIntegral_indicator hV.measurableSet,
                Set.inter_eq_self_of_subset_right hVU]
      _ = -∫ x in U, Set.indicator V u.toH1Function.grad x i * φ x ∂volume := by
              congr 1
              refine setIntegral_congr_fun hU.measurableSet ?_
              intro x _
              by_cases hx : x ∈ V
              · simp [Set.indicator_of_mem hx]
              · simp [Set.indicator_of_notMem hx]

@[simp]
theorem zeroExtendToH1_toFun {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) :
    (u.zeroExtendToH1 hU hV hVU).toFun =
      Set.indicator V u.toH1Function.toFun :=
  rfl

@[simp]
theorem zeroExtendToH1_grad {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) :
    (u.zeroExtendToH1 hU hV hVU).grad =
      Set.indicator V u.toH1Function.grad :=
  rfl

/-- Extend an `H¹₀(V)` function by literal zero to the larger open domain `U`.
The original smooth compactly supported approximants remain valid, because
their supports are already contained in `V ⊆ U`. -/
noncomputable def zeroExtend {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) : H10Function U where
  toH1Function := u.zeroExtendToH1 hU hV hVU
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := fun n => (u.approx_support_subset n).trans hVU
  tendsto_approx := by
    have hfun :
        (fun n => eLpNorm (fun x => u.approx n x -
          (u.zeroExtendToH1 hU hV hVU).toFun x) 2 (volume.restrict U)) =
          fun n => eLpNorm (fun x => u.approx n x - u.toH1Function.toFun x) 2
            (volume.restrict V) := by
      funext n
      have heq :
          (fun x => u.approx n x - (u.zeroExtendToH1 hU hV hVU).toFun x) =
            Set.indicator V (fun x => u.approx n x - u.toH1Function.toFun x) := by
        funext x
        by_cases hx : x ∈ V
        · simp [zeroExtendToH1_toFun, Set.indicator_of_mem hx]
        · simp [zeroExtendToH1_toFun, Set.indicator_of_notMem hx,
            approx_eq_zero_off u n hx]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hV.measurableSet,
        restrict_restrict_of_subset hV.measurableSet hVU]
    rw [hfun]
    exact u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    have hfun :
        (fun n => eLpNorm
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) -
            (u.zeroExtendToH1 hU hV hVU).grad x i) 2
          (volume.restrict U)) =
          fun n => eLpNorm
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) -
              u.toH1Function.grad x i) 2 (volume.restrict V) := by
      funext n
      have heq :
          (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) -
            (u.zeroExtendToH1 hU hV hVU).grad x i) =
            Set.indicator V (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) -
              u.toH1Function.grad x i) := by
        funext x
        by_cases hx : x ∈ V
        · simp [zeroExtendToH1_grad, Set.indicator_of_mem hx]
        · simp [zeroExtendToH1_grad, Set.indicator_of_notMem hx,
            approx_fderiv_eq_zero_off u n hx i]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hV.measurableSet,
        restrict_restrict_of_subset hV.measurableSet hVU]
    rw [hfun]
    exact u.tendsto_approx_grad i

@[simp]
theorem zeroExtend_toFun {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) :
    (u.zeroExtend hU hV hVU).toH1Function.toFun =
      Set.indicator V u.toH1Function.toFun :=
  rfl

@[simp]
theorem zeroExtend_grad {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (u : H10Function V) :
    (u.zeroExtend hU hV hVU).toH1Function.grad =
      Set.indicator V u.toH1Function.grad :=
  rfl

end H10Function

end PDE
