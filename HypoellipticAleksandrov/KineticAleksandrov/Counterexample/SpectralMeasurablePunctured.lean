module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Canonical spectral measurability for fields continuous off the origin -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Ramp functional calculus is continuous on a set supporting a Hermitian field. -/
theorem continuousOn_spectralRamp {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (S : Set X) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) (n : ℕ) :
    ContinuousOn (fun x => cfc (positiveSpectralRamp n) (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_spectralRamp (fun x : S => M x) hM (fun x => hherm x x.property) n

/-- Continuous positive-part calculus is continuous on any Hermitian field domain. -/
theorem continuousOn_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (S : Set X) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) :
    ContinuousOn (fun x => positiveSpectralMass (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_positiveSpectralMass (fun x : S => M x) hM (fun x => hherm x x.property)

/-- Positive spectral projections of punctured continuous Hermitian fields are measurable. -/
theorem measurable_positiveSpectralProjection_punctured {d : ℕ}
    (M : PDE.Vec d × PDE.Vec d → PDE.Mat d) (hM : ContinuousOn M ({0}ᶜ))
    (hherm : ∀ q, (M q).IsHermitian) :
    Measurable (fun q => positiveSpectralProjection (M q)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_of_continuousOn_compl_singleton 0
      (continuousOn_spectralRamp M _ hM (fun q _ => hherm q) n))
  apply tendsto_pi_nhds.mpr
  intro q
  have heq : (fun n : ℕ => cfc (positiveSpectralRamp n) (M q)) =ᶠ[atTop]
      (fun _ => positiveSpectralProjection (M q)) := spectralRamp_eventually (M q) (hherm q)
  exact tendsto_const_nhds.congr' heq.symm

/-- Entries of the canonical trace solver are measurable for punctured continuous data. -/
theorem measurable_spectralTraceMatrix_punctured {d : ℕ}
    (M : PDE.Vec d × PDE.Vec d → PDE.Mat d) (hM : ContinuousOn M ({0}ᶜ))
    (hherm : ∀ q, (M q).IsHermitian) (b : PDE.Vec d × PDE.Vec d → ℝ)
    (hb : Measurable b) (cminus : ℝ) (i k : Fin d) :
    Measurable (fun q => spectralTraceMatrix (M q) (b q) cminus i k) := by
  have hp : Measurable (fun q => positiveSpectralMass (M q)) :=
    measurable_of_continuousOn_compl_singleton 0
      (continuousOn_positiveSpectralMass M _ hM (fun q _ => hherm q))
  have hn : Measurable (fun q => negativeSpectralMass (M q)) :=
    measurable_of_continuousOn_compl_singleton 0
      (continuousOn_positiveSpectralMass (fun q => -M q) _ hM.neg
        (fun q _ => (hherm q).neg))
  have hproj := (measurable_positiveSpectralProjection_punctured M hM hherm).eval_matrix
    (i := i) (j := k)
  have hneg := (measurable_positiveSpectralProjection_punctured (fun q => -M q) hM.neg
    (fun q => (hherm q).neg)).eval_matrix (i := i) (j := k)
  have hw : Measurable (fun q =>
      (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)) :=
    (hb.add (measurable_const.mul hn)).div hp
  unfold spectralTraceMatrix zeroSpectralProjection
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((hw.mul hproj).add (measurable_const.mul hneg)).add
    ((measurable_const.sub hproj).sub hneg)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
