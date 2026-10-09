module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestBoundary

/-! # The literal physical C112 regularity of the clock pullback -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- Scalar-coordinate smoothness of a normalized test gives literal physical C112 smoothness
of its clock pullback throughout the physical active strip. -/
theorem clock_pullback_C112 (c : Clock) (e : Point) (h : Point → ℝ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}) :
    IsKineticC112On (h ∘ c.map e) {p | p.velocity 0 ∈ c.active} := by
  let l : (ℝ × PDE.Vec 1 × PDE.Vec 1) → (Fin 3 → ℝ) := fun q =>
    ![q.1, q.2.1 0, q.2.2 0]
  have hl : ContDiff ℝ (⊤ : ℕ∞) l := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.1)
      exact contDiff_fst
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.2.1 0)
      exact (contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.fst
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.2.2 0)
      exact (contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.snd
  have hm : MapsTo (c.mapCoordinates e ∘ l)
      (KineticPoint.equivProd 1 '' {p : Point | p.velocity 0 ∈ c.active})
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} := by
    rintro q ⟨p, hp, rfl⟩
    change (c.map e (scalarPoint (l (KineticPoint.equivProd 1 p)))).velocity 0 ∈
      normalizedActive
    have heq : scalarPoint (l (KineticPoint.equivProd 1 p)) = p := by
      change scalarPoint (scalarCoordinates p) = p
      exact scalarPoint_coordinates p
    rw [heq]
    exact (c.mem_active_iff (p.velocity 0)).mp hp
  have hs := hh.comp ((c.mapCoordinates_smooth e).comp hl).contDiffOn hm
  have heq : (h ∘ scalarPoint) ∘ (c.mapCoordinates e ∘ l) =
      (h ∘ c.map e) ∘ (KineticPoint.equivProd 1).symm := by
    funext q
    change h (scalarPoint (scalarCoordinates (c.map e (scalarPoint (l q))))) = _
    rw [scalarPoint_coordinates]
    apply congrArg (h ∘ c.map e)
    apply (KineticPoint.equivProd 1).injective
    rw [Equiv.apply_symm_apply]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;>
      have hi : i = 0 := Fin.eq_zero i <;> subst i <;> rfl
  apply nested_raw_isKineticC112On
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))
  rwa [heq] at hs

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
