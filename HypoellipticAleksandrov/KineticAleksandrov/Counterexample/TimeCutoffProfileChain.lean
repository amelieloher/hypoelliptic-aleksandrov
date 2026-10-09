module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileSobolev
public import PDEFoundation.Sobolev.W1p.Smooth
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeakSecond
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSecondBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The first weak chain rule applied to the literal flattened profile and barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The literal velocity barrier in the measure-preserving spatial chart. -/
def spatialPackedBarrier (d : ℕ) (mu R t : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  barrier mu R ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩

/-- The packed barrier is globally smooth at every finite order. -/
theorem contDiff_spatialPackedBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPackedBarrier d mu R t) := by
  simpa only [spatialPackedBarrier, barrier, Function.comp_apply] using!
    (contDiff_const (c := Real.exp (-mu * t))).mul ((contDiff_const (c := (2 : ℝ))).sub
      ((PDE.contDiff_vecNormSq.comp (spatialCoordinateCLE d).contDiff.snd).div_const (R ^ 2)))

/-- The first weak chain rule for the actual cutoff profile. All regularity of the
flattened profile is discharged by the complete published upstream source theorem. -/
theorem weakGradient_timeCutoffProfile_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x))
      (fun x i => deriv timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x) *
        (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
          PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)) := by
  let u := flatProfileW1p_of_flatProfile_source hflat hd ha ha1 h r hr hD
  let B := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    ((contDiff_spatialPackedBarrier d mu R t).of_le (by simp))
  simpa only [u, B, flatProfileW1p_of_flatProfile_source,
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    PDE.W1pFunction.ofContDiffOnIsSobolevRegularDomain] using!
    weakGradient_timeCutoff_sub hD (by norm_num) (by norm_num) u B

/-- The actual velocity Hessian chain rule for the cutoff profile, proved using the
same first and second upstream weak representatives and the smooth barrier. -/
theorem weakSecond_timeCutoffProfile_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) (i k : Fin d) :
    let u := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x)
    let B := spatialPackedBarrier d mu R t
    let gv := fun x j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
      PDE.classicalGradient B x (Fin.natAdd d j)
    PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => deriv timeCutoffTheta (u x - B x) * gv x k)
      (fun x => deriv timeCutoffTheta (u x - B x) *
        (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
          PDE.classicalGradient
            (fun y => PDE.classicalGradient B y (Fin.natAdd d k)) x (Fin.natAdd d i)) +
        deriv (deriv timeCutoffTheta) (u x - B x) * gv x i * gv x k) := by
  let u := flatProfileW1p_of_flatProfile_source hflat hd ha ha1 h r hr hD
  have hw : PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => u.grad x (Fin.natAdd d k))
      (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
    simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient,
      Fin.addCases_right] using!
      weak_velocityJet_spatialCoordinate_of_flatProfile_source hflat hd ha ha1 h r hr D i k
  have hm := memLp_flatProfileHessian_spatialCoordinate_of_flatProfile_source
    hflat hd ha ha1 h r hr hD i k 2
  obtain ⟨M, hM, hb⟩ := timeCutoffTheta_deriv2_abs_bound
  have he := weakSecond_cutoff_sub_smooth hD u (spatialPackedBarrier d mu R t)
    (contDiff_spatialPackedBarrier d mu R t) (Fin.natAdd d i) (Fin.natAdd d k)
    _ hm hw timeCutoffTheta (contDiff_timeCutoffTheta.of_le (by simp)) M hM.le hb
  simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient,
    Fin.addCases_right] using! he

/-- The proved flattened-profile theorem discharges the complete source interface. -/
theorem weakGradient_timeCutoffProfile_of_profile
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x))
      (fun x i => deriv timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x) *
        (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
          PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)) :=
  weakGradient_timeCutoffProfile_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr hD mu R t

/-- The proved flattened-profile theorem discharges the complete source interface. -/
theorem weakSecond_timeCutoffProfile_of_profile
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) (i k : Fin d) :
    let u := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x)
    let B := spatialPackedBarrier d mu R t
    let gv := fun x j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
      PDE.classicalGradient B x (Fin.natAdd d j)
    PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => deriv timeCutoffTheta (u x - B x) * gv x k)
      (fun x => deriv timeCutoffTheta (u x - B x) *
        (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
          PDE.classicalGradient
            (fun y => PDE.classicalGradient B y (Fin.natAdd d k)) x (Fin.natAdd d i)) +
        deriv (deriv timeCutoffTheta) (u x - B x) * gv x i * gv x k) :=
  weakSecond_timeCutoffProfile_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr hD mu R t i k

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
