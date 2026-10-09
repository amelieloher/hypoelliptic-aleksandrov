module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJetHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SpectralMeasurablePunctured

/-! # Canonical gauge normalization of the profile jets -/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The positive kinetic dilation carrying every nonzero point to the unit gauge shell. -/
def normalizeGauge {d : ℕ} (q : XV d) : XV d := dilate (rho q)⁻¹ q

/-- A nonzero point normalizes to the unit gauge shell. -/
theorem rho_normalizeGauge {d : ℕ} (q : XV d) (hq : q ≠ 0) : rho (normalizeGauge q) = 1 := by
  have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  rw [normalizeGauge, rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

/-- Gauge normalization preserves nonzero points. -/
theorem normalizeGauge_ne_zero {d : ℕ} (q : XV d) (hq : q ≠ 0) : normalizeGauge q ≠ 0 := by
  intro hz
  have hh := rho_normalizeGauge q hq
  simp [hz] at hh

/-- Positive dilation by the gauge recovers the original nonzero point. -/
theorem dilate_normalizeGauge {d : ℕ} (q : XV d) (hq : q ≠ 0) :
    dilate (rho q) (normalizeGauge q) = q := by
  have hr : rho q ≠ 0 := (rho_eq_zero_iff q).not.mpr hq
  rw [normalizeGauge, dilate_mul, mul_inv_cancel₀ hr, dilate_one]

/-- Normalization is continuous throughout the punctured kinetic space. -/
theorem continuousOn_normalizeGauge (d : ℕ) :
    ContinuousOn (normalizeGauge (d := d)) ({0}ᶜ) := by
  have hi := (continuous_rho d).continuousOn.inv₀ (fun q hq => (rho_eq_zero_iff q).not.mpr hq)
  exact (hi.pow 3 |>.smul continuous_fst.continuousOn).prodMk
    (hi.smul continuous_snd.continuousOn)

/-- The normalized velocity Hessian, assigned the identity at the joint origin. -/
def normalizedProfileMatrix {d : ℕ} (H : XV d → ℝ) (q : XV d) : PDE.Mat d :=
  if q = 0 then 1 else dvv H (normalizeGauge q)

/-- The normalized transport scalar, assigned one at the joint origin. -/
def normalizedProfileTransport {d : ℕ} (H : XV d → ℝ) (q : XV d) : ℝ :=
  if q = 0 then 1 else PDE.vecDot (normalizeGauge q).2 (dx H (normalizeGauge q))

/-- The normalized Hessian field is continuous off the origin. -/
theorem continuousOn_normalizedProfileMatrix {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) :
    ContinuousOn (normalizedProfileMatrix H) ({0}ᶜ) := by
  apply ((continuousOn_dvv_off_origin H hH).comp (continuousOn_normalizeGauge d)
    (fun q hq => normalizeGauge_ne_zero q hq)).congr
  intro q hq
  change q ≠ 0 at hq
  simp only [normalizedProfileMatrix, ite_eq_right hq, Function.comp_apply]

/-- The normalized transport is continuous off the origin. -/
theorem continuousOn_normalizedProfileTransport {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) :
    ContinuousOn (normalizedProfileTransport H) ({0}ᶜ) := by
  apply ((continuousOn_transport_off_origin H hH).comp (continuousOn_normalizeGauge d)
    (fun q hq => normalizeGauge_ne_zero q hq)).congr
  intro q hq
  change q ≠ 0 at hq
  simp only [normalizedProfileTransport, ite_eq_right hq, Function.comp_apply]

/-- The normalized Hessian field is Hermitian everywhere, including its assigned origin value. -/
theorem normalizedProfileMatrix_isHermitian {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (q : XV d) :
    (normalizedProfileMatrix H q).IsHermitian := by
  by_cases hq : q = 0
  · simp only [normalizedProfileMatrix, hq, ite_true]
    exact Matrix.isHermitian_one
  · rw [normalizedProfileMatrix, ite_eq_right hq]
    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
    exact dvv_isHermitian H _ (hH.contDiffAt (hopen.mem_nhds (normalizeGauge_ne_zero q hq)))

/-- The source canonical spectral matrix on normalized jets, with identity at the origin. -/
def homogeneousSpectralMatrix {d : ℕ} (H : XV d → ℝ) (cminus : ℝ) (q : XV d) : PDE.Mat d :=
  if q = 0 then 1 else
    spectralTraceMatrix (normalizedProfileMatrix H q) (normalizedProfileTransport H q) cminus

/-- The globally extended canonical matrix has measurable entries. -/
theorem measurable_homogeneousSpectralMatrix {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (cminus : ℝ) (i k : Fin d) :
    Measurable (fun q => homogeneousSpectralMatrix H cminus q i k) := by
  classical
  have hb := measurable_of_continuousOn_compl_singleton 0
    (continuousOn_normalizedProfileTransport H hH)
  have hm := measurable_spectralTraceMatrix_punctured (normalizedProfileMatrix H)
    (continuousOn_normalizedProfileMatrix H hH) (normalizedProfileMatrix_isHermitian H hH)
    (normalizedProfileTransport H) hb cminus i k
  have hh : Measurable (fun q : XV d => if q ∈ ({0} : Set (XV d)) then
      (1 : PDE.Mat d) i k else spectralTraceMatrix (normalizedProfileMatrix H q)
        (normalizedProfileTransport H q) cminus i k) :=
    (measurable_const (a := (1 : PDE.Mat d) i k)).ite (measurableSet_singleton (0 : XV d)) hm
  convert hh using 1
  funext q
  simp only [homogeneousSpectralMatrix, Set.mem_singleton_iff]
  split_ifs <;> rfl

/-- Scalar identity matrices are ordered according to their scalar weights. -/
theorem scalar_identity_le {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hab)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
