module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets

/-! # Hessian and transport signs of the literal full kinetic profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The full-product velocity quadratic second jet. -/
def fullVelocityQuadratic {d : ℕ} (H : XV d → ℝ) (q : XV d) (w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ H z (0, w)) q (0, w)

/-- The profile's full velocity Hessian has the source cutoff prefactor at nonzero position. -/
theorem geometricProfile_quadratic_nonzero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : XV d) (hx : q.1 ≠ 0) (w : PDE.Vec d) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w =
      Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
        cutoffHessian alpha C₀ sigma R (normalizedVelocity q.1 q.2) (positionDirection q.1) w := by
  have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun v => geometricProfile alpha C₀ sigma R (q.1, v)) =
      (fun v => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) q.1 v) := by
    funext v
    simp only [geometricProfile, ite_eq_right hx]
  unfold fullVelocityQuadratic
  rw [show q = (q.1, q.2) from rfl,
    full_velocity_hessian_eq_slice _ q.1 q.2 w w hH, heq]
  exact homogeneousAnsatz_velocity_hessian alpha C₀ sigma R hsigma hR q.1 q.2 w w hx

/-- The full profile transport has the same source prefactor at nonzero position. -/
theorem geometricProfile_transport_nonzero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : XV d) (hx : q.1 ≠ 0) :
    PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q) =
      Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
        ansatzTransport alpha (cutoffProfile alpha C₀ sigma R)
          (normalizedVelocity q.1 q.2) (positionDirection q.1) := by
  have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  rw [transport_eq_direction, ← fderiv_position_slice _ q.1 q.2 q.2
    (hH.differentiableAt (by simp))]
  have heq : (fun x => geometricProfile alpha C₀ sigma R (x, q.2)) =ᶠ[nhds q.1]
      (fun x => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x q.2) := by
    filter_upwards [continuous_id.continuousAt.eventually_ne hx] with x hx'
    change x ≠ 0 at hx'
    simp only [geometricProfile, ite_eq_right hx']
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  apply homogeneousAnsatz_transport alpha _ q.1 q.2 hx
  exact (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).differentiable
    (by simp) (normalizedVelocity q.1 q.2, positionDirection q.1)

/-- The full velocity Hessian at zero position is the exact radial Hessian. -/
theorem geometricProfile_quadratic_zero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (v w : PDE.Vec d) (hv : v ≠ 0) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) (0, v) w =
      radialHessianForm alpha v w w := by
  have hq : ((0, v) : XV d) ≠ 0 := fun h => hv (congrArg Prod.snd h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun a => geometricProfile alpha C₀ sigma R ((0 : PDE.Vec d), a)) =
      radialProfile alpha := by
    funext a
    simp only [geometricProfile, ite_true]
  unfold fullVelocityQuadratic
  rw [full_velocity_hessian_eq_slice _ 0 v w w hH, heq]
  exact radialProfile_hessian alpha v w w hv

/-- All source Hessian and transport sign conditions hold for the actual full profile. -/
theorem exists_geometricProfile_sign_parameters (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
      ∀ q : XV d, q ≠ 0 →
        (∃ w, 0 < fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w) ∧
        ((∃ w, fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w < 0) ∨
          0 < PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q)) := by
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_cutoff_sign_parameters d hd alpha ha ha1
  have hR : 0 < R := lt_trans (by norm_num) hR2
  refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
  intro q hq
  by_cases hx : q.1 = 0
  · have hv : q.2 ≠ 0 := fun hv => hq (Prod.ext hx hv)
    obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha q.2 hv
    refine ⟨⟨w, ?_⟩, Or.inl ⟨q.2, ?_⟩⟩
    · rw [show q = (0, q.2) from Prod.ext hx rfl,
        geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 w hv]
      exact hw
    · rw [show q = (0, q.2) from Prod.ext hx rfl,
        geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 q.2 hv]
      exact radialHessian_radial_neg alpha ha ha1 q.2 hv
  · have hr : 0 < Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) :=
      Real.rpow_pos_of_pos (PDE.vecEuclideanNorm_pos_iff.mpr hx) _
    obtain ⟨⟨w, hw⟩, hneg⟩ := hsign (normalizedVelocity q.1 q.2) (positionDirection q.1)
      (positionDirection_normSq q.1 hx)
    refine ⟨⟨w, ?_⟩, ?_⟩
    · rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
      exact mul_pos hr hw
    · rcases hneg with ⟨u, hu⟩ | hb
      · left
        refine ⟨u, ?_⟩
        rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
        exact mul_neg_of_pos_of_neg hr hu
      · right
        rw [geometricProfile_transport_nonzero_position alpha C₀ sigma R hsigma hR q hx]
        exact mul_pos hr (lt_of_lt_of_le zero_lt_one hb)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
