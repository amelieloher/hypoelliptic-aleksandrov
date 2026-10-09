module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Explicit profile statements for Appendix C

These are named conditional statements.
They state the profile construction's conclusions; definitions do not prove existence.
The classical branch deliberately has no distributional conclusion at the origin.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory
open scoped MatrixOrder

/-- The dimension-at-least-two profile statement. -/
def CounterProfileGeTwoStatement (d : ℕ) (alpha : ℝ) : Prop :=
  ∃ lam Lam c C : ℝ, ∃ A : XV d → PDE.Mat d, ∃ H : XV d → ℝ,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)) ∧
    (∀ q : XV d, q ≠ 0 → matrixContraction (A q) (dvv H q) =
      PDE.vecDot q.2 (dx H q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1))

/-- The literal autonomous scalar coefficient, including its specified axial values. -/
noncomputable def scalarProfileCoefficient (Lam : ℝ) (q : XV 1) : PDE.Mat 1 :=
  (if q.1 0 * q.2 0 < 0 then Lam else 1) • (1 : PDE.Mat 1)

/-- The scalar branch, including its source-proved weak identities away from the origin. -/
def CounterProfileOneStatement (alpha : ℝ) : Prop :=
  ∃ Lam c C : ℝ, ∃ H : XV 1 → ℝ,
    ∃ gx gv : XV 1 → PDE.Vec 1, ∃ hess : XV 1 → PDE.Mat 1,
    1 < Lam ∧ 0 < c ∧ 0 < C ∧ Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (scalarProfileCoefficient Lam q) (hess q) =
      PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV 1, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV 1), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ r : ℝ, 0 < r → ∀ q,
      gx (dilate r q) = Real.rpow r (alpha - 3) • gx q ∧
      gv (dilate r q) = Real.rpow r (alpha - 1) • gv q ∧
      hess (dilate r q) = Real.rpow r (alpha - 2) • hess q) ∧
    (∀ test : XV 1 → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (0 : XV 1) ∉ tsupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    ContDiffOn ℝ 2 H {q : XV 1 | q.1 0 ≠ 0}

/-- The shared profile surface, with actual weak derivatives on the whole native carrier. -/
def CounterProfileStatement (d : ℕ) (alpha : ℝ) : Prop :=
  ∃ lam Lam c C : ℝ, ∃ A : XV d → PDE.Mat d, ∃ H : XV d → ℝ,
    ∃ gx gv : XV d → PDE.Vec d, ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q)

/-- The lam witness selected from the shared conditional profile statement. -/
noncomputable def profileLowerEllipticity {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ :=
  h.choose

/-- The remaining source conclusions for the selected lam witness. -/
theorem profileLowerEllipticity_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    ∃ Lam : ℝ,
    ∃ c : ℝ,
    ∃ C : ℝ,
    ∃ A : XV d → PDE.Mat d,
    ∃ H : XV d → ℝ,
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact h.choose_spec

/-- The Lam witness selected from the shared conditional profile statement. -/
noncomputable def profileUpperEllipticity {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ :=
  (profileLowerEllipticity_spec h).choose

/-- The remaining source conclusions for the selected Lam witness. -/
theorem profileUpperEllipticity_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    ∃ c : ℝ,
    ∃ C : ℝ,
    ∃ A : XV d → PDE.Mat d,
    ∃ H : XV d → ℝ,
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileLowerEllipticity_spec h).choose_spec

/-- The c witness selected from the shared conditional profile statement. -/
noncomputable def profileLowerComparison {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ :=
  (profileUpperEllipticity_spec h).choose

/-- The remaining source conclusions for the selected c witness. -/
theorem profileLowerComparison_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    ∃ C : ℝ,
    ∃ A : XV d → PDE.Mat d,
    ∃ H : XV d → ℝ,
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileUpperEllipticity_spec h).choose_spec

/-- The C witness selected from the shared conditional profile statement. -/
noncomputable def profileUpperComparison {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ :=
  (profileLowerComparison_spec h).choose

/-- The remaining source conclusions for the selected C witness. -/
theorem profileUpperComparison_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    ∃ A : XV d → PDE.Mat d,
    ∃ H : XV d → ℝ,
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileLowerComparison_spec h).choose_spec

/-- The A witness selected from the shared conditional profile statement. -/
noncomputable def profileMatrix {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Mat d :=
  (profileUpperComparison_spec h).choose

/-- The remaining source conclusions for the selected A witness. -/
theorem profileMatrix_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    let A := profileMatrix h
    ∃ H : XV d → ℝ,
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileUpperComparison_spec h).choose_spec

/-- The H witness selected from the shared conditional profile statement. -/
noncomputable def profileFunction {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → ℝ :=
  (profileMatrix_spec h).choose

/-- The remaining source conclusions for the selected H witness. -/
theorem profileFunction_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    let A := profileMatrix h
    let H := profileFunction h
    ∃ gx : XV d → PDE.Vec d,
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileMatrix_spec h).choose_spec

/-- The gx witness selected from the shared conditional profile statement. -/
noncomputable def profilePositionJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Vec d :=
  (profileFunction_spec h).choose

/-- The remaining source conclusions for the selected gx witness. -/
theorem profilePositionJet_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    let A := profileMatrix h
    let H := profileFunction h
    let gx := profilePositionJet h
    ∃ gv : XV d → PDE.Vec d,
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileFunction_spec h).choose_spec

/-- The gv witness selected from the shared conditional profile statement. -/
noncomputable def profileVelocityJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Vec d :=
  (profilePositionJet_spec h).choose

/-- The remaining source conclusions for the selected gv witness. -/
theorem profileVelocityJet_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    let A := profileMatrix h
    let H := profileFunction h
    let gx := profilePositionJet h
    let gv := profileVelocityJet h
    ∃ hess : XV d → PDE.Mat d,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profilePositionJet_spec h).choose_spec

/-- The hess witness selected from the shared conditional profile statement. -/
noncomputable def profileHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Mat d :=
  (profileVelocityJet_spec h).choose

/-- The remaining source conclusions for the selected hess witness. -/
theorem selectedProfile_spec {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) :
    let lam := profileLowerEllipticity h
    let Lam := profileUpperEllipticity h
    let c := profileLowerComparison h
    let C := profileUpperComparison h
    let A := profileMatrix h
    let H := profileFunction h
    let gx := profilePositionJet h
    let gv := profileVelocityJet h
    let hess := profileHessian h
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
    (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
    (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q) := by
  exact (profileVelocityJet_spec h).choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
