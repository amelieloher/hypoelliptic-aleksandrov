module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationMass
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryKernelBorel

/-! # Restricting the actual boundary solution to a shorter time strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic TheoremA

/-- Increasing the lower time endpoint shrinks the open strip. -/
theorem localStrip_lower_subset {d : ℕ} {a b T R : ℝ} (hab : a ≤ b) (v₀ : PDE.Vec d) :
    localStrip b T v₀ R ⊆ localStrip a T v₀ R :=
  fun _ h => ⟨hab.trans_lt h.1, h.2⟩

/-- Increasing the lower time endpoint shrinks the closed strip. -/
theorem localClosedStrip_lower_subset {d : ℕ} {a b T R : ℝ}
    (hab : a ≤ b) (v₀ : PDE.Vec d) :
    localClosedStrip b T v₀ R ⊆ localClosedStrip a T v₀ R :=
  fun _ h => ⟨hab.trans h.1, h.2⟩

/-- The later terminal and lateral traces are contained in the earlier trace. -/
theorem localTrace_lower_subset {d : ℕ} {a b T R : ℝ} (hab : a ≤ b) (v₀ : PDE.Vec d) :
    localTrace b T v₀ R ⊆ localTrace a T v₀ R := by
  intro Q hQ
  rcases hQ with hQ | hQ
  · exact Or.inl hQ
  · exact Or.inr ⟨hab.trans hQ.1, hQ.2⟩

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Boundary solutions with identical terminal time and data agree on their common strip. -/
theorem ballBoundarySolution_lowerTime_eq (a b T : ℝ) (hab : a ≤ b) (hbT : b < T)
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    EqOn (ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ)
      (ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR b T φ)
      (localClosedStrip b T v₀ R) := by
  have haT := hab.trans_lt hbT
  let u := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ
  let v := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR b T φ
  have hu := ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
    a T haT φ hφ hc
  have hv := ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
    b T hbT φ hφ hc
  have hsub := localStrip_lower_subset (T := T) (R := R) hab v₀
  have hcl := localClosedStrip_lower_subset (T := T) (R := R) hab v₀
  obtain ⟨M, hM⟩ := ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR
    a T haT φ hφ hc
  have he := mass_homogeneous_abs_weighted B hB b T hbT v₀ R u v
    (hu.1.mono (image_mono hsub)) hv.1
    (fun Q hQ => hu.2.1 Q (hsub hQ)) hv.2.1
    (hu.2.2.1.mono hcl) hv.2.2.1 ⟨M, fun Q hQ => hM Q (hcl hQ)⟩
    (ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR b T hbT φ hφ hc)
    0 le_rfl (fun Q hQ => by
      dsimp only [u, v]
      rw [hu.2.2.2 (localTrace_lower_subset hab v₀ hQ), hv.2.2.2 hQ]
      simp)
  intro Q hQ
  have h := he Q hQ
  have hz : |u Q - v Q| = 0 := le_antisymm (by simpa only [zero_mul] using h)
    (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- Compact boundary tests can be evaluated on the shorter strip using the genuine solution. -/
theorem ballExit_smooth_short_strip_representation
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1})
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    (∫ Q, φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
      ∫ Q, ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ Q
        ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩ := by
  let u := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ
  have hu := ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 φ hφ hc
  have hs : localStrip P.1.time H.1 v₀ R ⊆ localStrip P.1.time T.1 v₀ R :=
    fun Q hQ => ⟨hQ.1, hQ.2.1.trans H.2.2, hQ.2.2⟩
  have hcl : localClosedStrip P.1.time H.1 v₀ R ⊆
      localClosedStrip P.1.time T.1 v₀ R :=
    fun Q hQ => ⟨hQ.1, hQ.2.1.trans H.2.2.le, hQ.2.2⟩
  obtain ⟨M, hM⟩ := ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 φ hφ hc
  have hr := isKineticC112On_of_contDiffOn (isOpen_localStrip P.1.time H.1 v₀ R)
    (boundary_physical_smooth_to_native (hu.1.mono (image_mono hs)))
  exact ((ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.2 φ hφ hc).trans
    (ballExit_represents hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩ u
      (hu.2.2.1.mono hcl) hr ⟨M, fun Q hQ => hM Q (hcl hQ)⟩
      (fun Q hQ => hu.2.1 Q (hs hQ)))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
