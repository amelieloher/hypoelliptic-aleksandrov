module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion

/-!
# A terminal window uniform along the finite ellipsoid exhaustion

Compact terminal support, a common curve Lipschitz constant and an explicit lower
truncation radius ensure that the terminal datum vanishes on every actual lateral face
in the window. This is proved before constructing any full-domain solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- Terminal support remains strictly inside the moving ellipsoid throughout a window
whose length depends on the collar distance and the common curve Lipschitz constant. -/
theorem mem_straightenedEllipsoid_of_terminal_support_window
    {n : ℕ} {r R d Z L τ : ℝ} (hr : 0 < r) (hR : 0 < R) (hd : 0 < d)
    (hL : 0 ≤ L) {g : ℝ → PDE.Vec n}
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (hsuppZ : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      PDE.vecEuclideanNorm q.2 ≤ Z)
    (hsize : (r - d) ^ 2 / r ^ 2 + Z ^ 2 / R ^ 2 < 1)
    {p : KineticPoint n} (hτ : p.time ≤ τ) (hwin : τ - d / (1 + L) ≤ p.time)
    (hp : (p.position, p.velocity) ∈ tsupport (F : EvolutionAmbientState n → ℝ)) :
    (straightenedPoint g p).2 ∈ openEllipsoid (straightenedEllipsoidMatrix n r R) := by
  have hg : PDE.vecEuclideanNorm (g τ - g p.time) ≤ d := by
    have ht := hgL τ p.time
    rw [abs_of_nonneg (sub_nonneg.mpr hτ)] at ht
    have hw : τ - p.time ≤ d / (1 + L) := by linarith
    have he : d / (1 + L) * (1 + L) = d := div_mul_cancel₀ _ (by linarith)
    have hdq : 0 ≤ d / (1 + L) := div_nonneg hd.le (by linarith)
    nlinarith
  have hnorm : PDE.vecEuclideanNorm (p.position - g p.time) ≤ r - d := by
    have he : p.position - g p.time = (p.position - g τ) + (g τ - g p.time) := by abel
    rw [he]
    have hsum := PDE.vecEuclideanNorm_add_le (p.position - g τ) (g τ - g p.time)
    have hs := hsupp _ hp
    linarith
  have hY : PDE.vecNormSq (p.position - g p.time) ≤ (r - d) ^ 2 := by
    have he := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hnorm 2
    rwa [PDE.vecEuclideanNorm_sq] at he
  have hZ' : PDE.vecNormSq p.velocity ≤ Z ^ 2 := by
    have he := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) (hsuppZ _ hp) 2
    rwa [PDE.vecEuclideanNorm_sq] at he
  rw [(straightenedEllipsoid_characterization n r R hr hR).2]
  simp only [straightenedPoint, spatialY_spatialPack, spatialZ_spatialPack]
  exact lt_of_le_of_lt
    (add_le_add (div_le_div_of_nonneg_right hY (sq_nonneg r))
      (div_le_div_of_nonneg_right hZ' (sq_nonneg R))) hsize

/-- The original terminal datum is zero on every artificial lateral face near terminal
time, once the transported radius satisfies the explicit support margin condition. -/
theorem terminalDatum_eq_zero_on_straightened_lateral_window
    {n : ℕ} {r R d Z L τ : ℝ} (hr : 0 < r) (hR : 0 < R) (hd : 0 < d)
    (hL : 0 ≤ L) {g : ℝ → PDE.Vec n}
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (hsuppZ : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      PDE.vecEuclideanNorm q.2 ≤ Z)
    (hsize : (r - d) ^ 2 / r ^ 2 + Z ^ 2 / R ^ 2 < 1)
    {p : KineticPoint n} (hτ : p.time ≤ τ) (hwin : τ - d / (1 + L) ≤ p.time)
    (hp : (straightenedPoint g p).2 ∈
      frontier (openEllipsoid (straightenedEllipsoidMatrix n r R))) :
    F (p.position, p.velocity) = 0 := by
  by_contra hn
  have hm := subset_tsupport _ (Function.mem_support.mpr hn)
  have hi := mem_straightenedEllipsoid_of_terminal_support_window
    hr hR hd hL hgL hsupp hsuppZ hsize hτ hwin hm
  rw [(isOpen_straightenedEllipsoid n hr hR).frontier_eq] at hp
  exact hp.2 hi

end HypoellipticAleksandrov.KineticAleksandrov
