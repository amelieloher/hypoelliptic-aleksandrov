module

public import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.Parabolic.Operator
public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierLocalization
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Residual-bearing mollification of local weak parabolic equations

This file globalizes a cutoff selected weak jet and mollifies it on a compact
strict collar.  The resulting smooth functions satisfy the pointwise forward
equation with their explicit coefficient--Hessian commutator residual.  No
claim of residual decay or of a homogeneous classical equation is made here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := by
  simp [parabolicExponent]

/-- A compact carrier, relatively compact open plateau, and ambient open
weak-equation domain. -/
def IsStrictMollificationCollar {d : Nat}
    (K V U : Set (TimeVelocity d)) : Prop :=
  IsCompact K ∧ IsOpen U ∧ IsOpen V ∧ IsCompact (closure V) ∧
    K ⊆ V ∧ closure V ⊆ U

/-- A compact subset of an open time--velocity set has a strict collar. -/
theorem exists_strictMollificationCollar
    {d : Nat} {K U : Set (TimeVelocity d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsStrictMollificationCollar K V U := by
  obtain ⟨V, hV, hKV, hVU, hVCompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  exact ⟨V, hK, hU, hV, hVCompact, hKV, hVU⟩

/-- The value obtained by right-convolving a global selected weak jet. -/
noncomputable def parabolicMollifiedValue
    {d : Nat} {p : ENNReal}
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → Real :=
  parabolicConvolution g.toFun (parabolicMollifier d n)

/-- The matrix made by right-convolving the selected velocity Hessian entries. -/
noncomputable def parabolicMollifiedHessian
    {d : Nat} {p : ENNReal}
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → PDE.Mat d :=
  fun z i j => parabolicConvolution
    (fun y => g.velocityHessian y i j) (parabolicMollifier d n) z

/-- The explicit coefficient--Hessian residual of this mollification. -/
noncomputable def weakEquationMollificationResidual
    {d : Nat} {p : ENNReal} (Aext : CoefficientField d)
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → Real :=
  fun z =>
    parabolicConvolution
      (fun y => matrixContraction (coefficientAt Aext y) (g.velocityHessian y))
      (parabolicMollifier d n) z -
    matrixContraction
      (coefficientAt (parabolicMollifyCoefficient Aext n) z)
      (parabolicMollifiedHessian g n z)

/-- Unfolding lemma for the selected-jet value mollification. -/
@[simp] theorem parabolicMollifiedValue_apply
    {d : Nat} {p : ENNReal} (g : ParabolicW12Function d Set.univ p)
    (n : Nat) :
    parabolicMollifiedValue g n =
      parabolicConvolution g.toFun (parabolicMollifier d n) := rfl

/-- A mollified global selected jet value is smooth at every finite order. -/
theorem contDiff_parabolicMollifiedValue
    {d : Nat} {p : ENNReal} (g : ParabolicW12Function d Set.univ p)
    (hp : 1 ≤ p) (n : Nat) :
    ContDiff Real (↑(⊤ : ℕ∞)) (parabolicMollifiedValue g n) := by
  simpa only [parabolicMollifiedValue] using
    g.contDiff_convolution hp (parabolicMollifier d n)
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)

/-- Time differentiation commutes with this global selected-jet mollification. -/
theorem timeDerivative_parabolicMollifiedValue
    {d : Nat} {p : ENNReal} (g : ParabolicW12Function d Set.univ p)
    (hp : 1 ≤ p) (n : Nat) :
    timeDerivative (parabolicMollifiedValue g n) =
      parabolicConvolution g.timeDeriv (parabolicMollifier d n) := by
  simpa only [parabolicMollifiedValue] using
    g.timeDerivative_convolution hp (parabolicMollifier d n)
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)

/-- The velocity Hessian commutes entrywise with this global selected-jet
mollification. -/
theorem velocityHessian_parabolicMollifiedValue
    {d : Nat} {p : ENNReal} (g : ParabolicW12Function d Set.univ p)
    (hp : 1 ≤ p) (n : Nat) :
    velocityHessian (parabolicMollifiedValue g n) =
      parabolicMollifiedHessian g n := by
  funext z
  ext i j
  exact congrFun
    (g.velocityHessian_convolution hp (parabolicMollifier d n)
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n) i j) z

private theorem ae_on_subset
    {d : Nat} {P : TimeVelocity d → Prop} {S T : Set (TimeVelocity d)}
    (h : ∀ᵐ z ∂timeVelocityVolumeOn T, P z) (hST : S ⊆ T) :
    ∀ᵐ z ∂timeVelocityVolumeOn S, P z :=
  h.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hST

private theorem parabolicConvolution_eq_of_ae_eq_on_support
    {d : Nat} {f g rho : TimeVelocity d → Real} {O : Set (TimeVelocity d)}
    (hO : MeasurableSet O) (z : TimeVelocity d)
    (hsupport : {y | rho (z - y) ≠ 0} ⊆ O)
    (heq : f =ᵐ[timeVelocityVolumeOn O] g) :
    parabolicConvolution f rho z = parabolicConvolution g rho z := by
  change (∫ y, f y * rho (z - y)) = ∫ y, g y * rho (z - y)
  apply integral_congr_ae
  have heq' : ∀ᵐ y ∂volume, y ∈ O → f y = g y := by
    change ∀ᵐ y ∂volume.restrict O, f y = g y at heq
    exact (ae_restrict_iff' hO).mp heq
  filter_upwards [heq'] with y hy
  by_cases hyO : y ∈ O
  · rw [hy hyO]
  · have hzero : rho (z - y) = 0 := by
      by_contra hne
      exact hyO (hsupport hne)
    simp [hzero]

private theorem parabolicConvolution_nonneg_of_ae_nonneg_on_support
    {d : Nat} {f rho : TimeVelocity d → Real} {O : Set (TimeVelocity d)}
    (hO : MeasurableSet O) (z : TimeVelocity d)
    (hsupport : {y | rho (z - y) ≠ 0} ⊆ O)
    (hnonneg : ∀ᵐ y ∂timeVelocityVolumeOn O, 0 ≤ f y)
    (hrho : ∀ y, 0 ≤ rho y) :
    0 ≤ parabolicConvolution f rho z := by
  change 0 ≤ ∫ y, f y * rho (z - y)
  apply integral_nonneg_of_ae
  have hnonneg' : ∀ᵐ y ∂volume, y ∈ O → 0 ≤ f y := by
    change ∀ᵐ y ∂volume.restrict O, 0 ≤ f y at hnonneg
    exact (ae_restrict_iff' hO).mp hnonneg
  filter_upwards [hnonneg'] with y hy
  change 0 ≤ f y * rho (z - y)
  by_cases hyO : y ∈ O
  · exact mul_nonneg (hy hyO) (hrho (z - y))
  · have hzero : rho (z - y) = 0 := by
      by_contra hne
      exact hyO (hsupport hne)
    simp [hzero]

private theorem exists_cutoff_global_jet_on_plateau
    {d : Nat} {A Aext : CoefficientField d}
    {u : TimeVelocity d → Real} {K V U : Set (TimeVelocity d)}
    (hK : IsCompact K) (hV : IsOpen V) (hVCompact : IsCompact (closure V))
    (hKV : K ⊆ V) (hVU : closure V ⊆ U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u) :
    ∃ g : ParabolicW12Function d Set.univ (parabolicExponent d),
      ∃ O : Set (TimeVelocity d), IsOpen O ∧ K ⊆ O ∧ O ⊆ V ∧
        g.toFun =ᵐ[timeVelocityVolumeOn O] u ∧
        g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
          fun z => matrixContraction (coefficientAt Aext z) (g.velocityHessian z) := by
  have hVU' : V ⊆ U := subset_closure.trans hVU
  obtain ⟨w, hwu, hweq⟩ := hWeak V hV hVCompact hVU
  obtain ⟨b, hb, hbCompact, hbOne, hbV, hvalue, htime, _hgrad, hhess⟩ :=
    exists_smooth_compact_cutoff_mul_eventuallyEq_jet hK hV hVCompact hKV w
      (parabolicExponent_one_le d)
  let g : ParabolicW12Function d Set.univ (parabolicExponent d) :=
    w.mulContDiffHasCompactSupport_univ (parabolicExponent_one_le d) hb hbCompact hV hbV
  have hgvalue : g.toFun =ᶠ[𝓝ˢ K] w.toFun := by
    change (w.mulContDiffHasCompactSupport (parabolicExponent_one_le d)
      (b := b) hb hbCompact).toFun =ᶠ[𝓝ˢ K] w.toFun
    exact hvalue
  have hgtime : g.timeDeriv =ᶠ[𝓝ˢ K] w.timeDeriv := by
    change (w.mulContDiffHasCompactSupport (parabolicExponent_one_le d)
      (b := b) hb hbCompact).timeDeriv =ᶠ[𝓝ˢ K] w.timeDeriv
    exact htime
  have hghess : g.velocityHessian =ᶠ[𝓝ˢ K] w.velocityHessian := by
    change (w.mulContDiffHasCompactSupport (parabolicExponent_one_le d)
      (b := b) hb hbCompact).velocityHessian =ᶠ[𝓝ˢ K]
      w.velocityHessian
    exact hhess
  have hplateau : ∀ᶠ z in 𝓝ˢ K,
      g.toFun z = w.toFun z ∧ g.timeDeriv z = w.timeDeriv z ∧
        g.velocityHessian z = w.velocityHessian z := by
    filter_upwards [hgvalue, hgtime, hghess] with z hzValue hzTime hzHess
    exact ⟨hzValue, hzTime, hzHess⟩
  obtain ⟨O0, hO0, hKO0, hplateau0⟩ := eventually_nhdsSet_iff_exists.mp hplateau
  let O : Set (TimeVelocity d) := O0 ∩ V
  have hO : IsOpen O := hO0.inter hV
  have hKO : K ⊆ O := fun z hz => ⟨hKO0 hz, hKV hz⟩
  have hOV : O ⊆ V := inter_subset_right
  have hOU : O ⊆ U := hOV.trans hVU'
  have hplateauO (z : TimeVelocity d) (hz : z ∈ O) :
      g.toFun z = w.toFun z ∧ g.timeDeriv z = w.timeDeriv z ∧
        g.velocityHessian z = w.velocityHessian z :=
    hplateau0 z hz.1
  have hweqO : ∀ᵐ z ∂timeVelocityVolumeOn O,
      w.timeDeriv z = matrixContraction (coefficientAt A z) (w.velocityHessian z) := by
    have hweqO' := ae_on_subset hweq hOV
    filter_upwards [hweqO'] with z hz
    exact sub_eq_zero.mp (by simpa only [weakParabolicOperator, Pi.zero_apply] using hz)
  have hExtAEO : ∀ᵐ z ∂timeVelocityVolumeOn O,
      coefficientAt Aext z = coefficientAt A z :=
    ae_on_subset hExtAE hOU
  have hEqO : ∀ᵐ z ∂timeVelocityVolumeOn O,
      g.timeDeriv z =
        matrixContraction (coefficientAt Aext z) (g.velocityHessian z) := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    have hweqO' := (ae_restrict_iff' hO.measurableSet).mp hweqO
    have hExtAEO' := (ae_restrict_iff' hO.measurableSet).mp hExtAEO
    filter_upwards [hweqO', hExtAEO'] with z hweqz hAez hzO
    calc
      g.timeDeriv z = w.timeDeriv z := (hplateauO z hzO).2.1
      _ = matrixContraction (coefficientAt A z) (w.velocityHessian z) := hweqz hzO
      _ = matrixContraction (coefficientAt Aext z) (g.velocityHessian z) := by
        rw [hAez hzO, (hplateauO z hzO).2.2]
  have hgvalue : g.toFun =ᵐ[timeVelocityVolumeOn O] u := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    have hwuO := (ae_restrict_iff' hO.measurableSet).mp (ae_on_subset hwu hOV)
    filter_upwards [hwuO] with z hwuz hzO
    exact (hplateauO z hzO).1.trans (hwuz hzO)
  exact ⟨g, O, hO, hKO, hOV, hgvalue, hEqO⟩

private theorem eventually_residual_equation_of_ae_on_plateau
    {d : Nat} {Aext : CoefficientField d}
    {K O : Set (TimeVelocity d)} {p : ENNReal}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (g : ParabolicW12Function d Set.univ p) (hp : 1 ≤ p)
    (heq : g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt Aext z) (g.velocityHessian z)) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue g n) z =
        weakEquationMollificationResidual Aext g n z := by
  have hkernel : ∀ᶠ n in atTop, ∀ z ∈ K,
      {y | parabolicMollifier d n (z - y) ≠ 0} ⊆ O :=
    eventually_translated_parabolicMollifier_support_subset d K O hK hO hKO
  filter_upwards [hkernel] with n hn
  intro z hz
  have hconv := parabolicConvolution_eq_of_ae_eq_on_support hO.measurableSet z (hn z hz) heq
  calc
    parabolicOperator (parabolicMollifyCoefficient Aext n)
        (parabolicMollifiedValue g n) z =
        parabolicConvolution g.timeDeriv (parabolicMollifier d n) z -
          matrixContraction (coefficientAt (parabolicMollifyCoefficient Aext n) z)
            (parabolicMollifiedHessian g n z) := by
        rw [parabolicOperator_apply, timeDerivative_parabolicMollifiedValue g hp n,
          velocityHessian_parabolicMollifiedValue g hp n]
    _ = weakEquationMollificationResidual Aext g n z := by
        rw [hconv]
        rfl

/-- A local weak solution has eventually smooth mollifications on a strict
collar whose forward equation is exactly the explicit residual. -/
theorem exists_eventually_residual_mollification_on_strictCollar
    (d : Nat) (lam Lam : Real)
    (A Aext : CoefficientField d) (u : TimeVelocity d → Real)
    (K V U : Set (TimeVelocity d))
    (hCol : IsStrictMollificationCollar K V U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtSymm : IsSymmetricCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u) :
    ∃ g : ParabolicW12Function d Set.univ (parabolicExponent d),
      (∀ᶠ n in atTop,
        IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
        IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
        HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
        HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) ∧
        ContDiff Real (↑(⊤ : ℕ∞)) (parabolicMollifiedValue g n) ∧
        ∀ z ∈ K,
          parabolicOperator (parabolicMollifyCoefficient Aext n)
              (parabolicMollifiedValue g n) z =
            weakEquationMollificationResidual Aext g n z) := by
  rcases hCol with ⟨hK, hU, hV, hVCompact, hKV, hVU⟩
  rcases exists_cutoff_global_jet_on_plateau hK hV hVCompact hKV hVU hExtAE hWeak with
    ⟨g, O, hO, hKO, _hOV, _hvalue, hEqO⟩
  have hpointwise := eventually_residual_equation_of_ae_on_plateau hK hO hKO g
    (parabolicExponent_one_le d) hEqO
  refine ⟨g, ?_⟩
  filter_upwards [hpointwise] with n hn
  exact ⟨isSmoothCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtBorel
      hExtLower hExtUpper n,
    isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtSymm n,
    hasLowerEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtSymm
      hExtLower hExtUpper n,
    hasUpperEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtSymm
      hExtLower hExtUpper n,
    contDiff_parabolicMollifiedValue g (parabolicExponent_one_le d) n, hn⟩

/-- If the local weak solution is nonnegative almost everywhere, the same
strict-collar mollifications are pointwise nonnegative while retaining their
explicit residual equation. -/
theorem exists_eventually_nonnegative_residual_mollification_on_strictCollar
    (d : Nat) (lam Lam : Real)
    (A Aext : CoefficientField d) (u : TimeVelocity d → Real)
    (K V U : Set (TimeVelocity d))
    (hCol : IsStrictMollificationCollar K V U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtSymm : IsSymmetricCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u)
    (huNonneg : ∀ᵐ z ∂timeVelocityVolumeOn U, 0 ≤ u z) :
    ∃ g : ParabolicW12Function d Set.univ (parabolicExponent d),
      ∀ᶠ n in atTop,
        (∀ z ∈ K, 0 ≤ parabolicMollifiedValue g n z) ∧
        (∀ z ∈ K,
          parabolicOperator (parabolicMollifyCoefficient Aext n)
              (parabolicMollifiedValue g n) z =
            weakEquationMollificationResidual Aext g n z) := by
  rcases hCol with ⟨hK, hU, hV, hVCompact, hKV, hVU⟩
  rcases exists_cutoff_global_jet_on_plateau hK hV hVCompact hKV hVU hExtAE hWeak with
    ⟨g, O, hO, hKO, hOV, hvalue, hEqO⟩
  have hOU : O ⊆ U := hOV.trans (subset_closure.trans hVU)
  have hnonneg : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ g.toFun z := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    have hvalue' := (ae_restrict_iff' hO.measurableSet).mp hvalue
    have huNonneg' := (ae_restrict_iff' hO.measurableSet).mp
      (ae_on_subset huNonneg hOU)
    filter_upwards [hvalue', huNonneg'] with z hgz huz hzO
    rw [hgz hzO]
    exact huz hzO
  have hkernel : ∀ᶠ n in atTop, ∀ z ∈ K,
      {y | parabolicMollifier d n (z - y) ≠ 0} ⊆ O :=
    eventually_translated_parabolicMollifier_support_subset d K O hK hO hKO
  have hpointwise := eventually_residual_equation_of_ae_on_plateau hK hO hKO g
    (parabolicExponent_one_le d) hEqO
  have hcoefficient : ∀ᶠ n in atTop,
      IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
      IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
      HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
      HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) :=
    Filter.Eventually.of_forall fun n =>
      ⟨isSmoothCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtLower
        hExtUpper n,
        isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtSymm n,
        hasLowerEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtSymm
          hExtLower hExtUpper n,
        hasUpperEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtSymm
          hExtLower hExtUpper n⟩
  refine ⟨g, ?_⟩
  filter_upwards [hkernel, hpointwise, hcoefficient] with n hn heqn _hcoefficient
  constructor
  · intro z hz
    exact parabolicConvolution_nonneg_of_ae_nonneg_on_support hO.measurableSet z (hn z hz)
      hnonneg (parabolicMollifier_nonneg d n)
  · exact heqn

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Filter

/-- An a.e. local equation for a global selected jet gives the eventual
pointwise residual equation on a compact carrier. -/
theorem eventually_residual_equation_of_ae_on
    {d : Nat} {Aext : CoefficientField d}
    {K O : Set (TimeVelocity d)} {p : ENNReal}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (g : ParabolicW12Function d Set.univ p) (hp : 1 ≤ p)
    (heq : g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt Aext z) (g.velocityHessian z)) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue g n) z =
        weakEquationMollificationResidual Aext g n z :=
  eventually_residual_equation_of_ae_on_plateau hK hO hKO g hp heq

/-- A global selected jet which is a.e. nonnegative on an open neighborhood
of a compact carrier has eventually pointwise nonnegative mollifications
there. -/
theorem eventually_nonnegative_parabolicMollifiedValue_of_ae_nonnegative_on
    {d : Nat} {K O : Set (TimeVelocity d)} {p : ENNReal}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (g : ParabolicW12Function d Set.univ p)
    (hnonneg : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ g.toFun z) :
    ∀ᶠ n in atTop, ∀ z ∈ K, 0 ≤ parabolicMollifiedValue g n z := by
  have hkernel : ∀ᶠ n in atTop, ∀ z ∈ K,
      {y | parabolicMollifier d n (z - y) ≠ 0} ⊆ O :=
    eventually_translated_parabolicMollifier_support_subset d K O hK hO hKO
  filter_upwards [hkernel] with n hn
  intro z hz
  exact parabolicConvolution_nonneg_of_ae_nonneg_on_support hO.measurableSet z
    (hn z hz) hnonneg (parabolicMollifier_nonneg d n)

end HypoellipticAleksandrov.Parabolic
