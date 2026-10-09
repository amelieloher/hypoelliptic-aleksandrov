module

public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Addition of representative-level `H¹₀` functions

This file equips the representative facade `PDE.H10Function` with addition.
The approximation certificate is obtained by adding the two supplied smooth,
compactly supported approximation sequences term by term.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.H10Function

open Filter MeasureTheory

variable {d : ℕ} {U : Set (PDE.Vec d)}

/-- Add two representative-level `H¹₀` functions, using the pointwise sum
of their supplied smooth compactly supported approximations. -/
noncomputable def add (u v : PDE.H10Function U) : PDE.H10Function U where
  toH1Function := u.toH1Function + v.toH1Function
  approx := fun n => u.approx n + v.approx n
  approx_smooth := fun n => (u.approx_smooth n).add (v.approx_smooth n)
  approx_hasCompactSupport := fun n =>
    (u.approx_hasCompactSupport n).add (v.approx_hasCompactSupport n)
  approx_support_subset := fun n =>
    (tsupport_add (u.approx n) (v.approx n)).trans
      (Set.union_subset (u.approx_support_subset n) (v.approx_support_subset n))
  tendsto_approx := by
    have hbound : Tendsto
        (fun n =>
          eLpNorm (fun x => u.approx n x - u.toH1Function.toFun x)
              (2 : ℝ≥0∞) (volume.restrict U) +
            eLpNorm (fun x => v.approx n x - v.toH1Function.toFun x)
              (2 : ℝ≥0∞) (volume.restrict U))
        atTop (nhds 0) := by
      simpa using u.tendsto_approx.add v.tendsto_approx
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => zero_le) (fun n => ?_)
    have huApprox : AEStronglyMeasurable (u.approx n) (volume.restrict U) :=
      (u.approx_smooth n).continuous.aestronglyMeasurable
    have hvApprox : AEStronglyMeasurable (v.approx n) (volume.restrict U) :=
      (v.approx_smooth n).continuous.aestronglyMeasurable
    have heq :
        (fun x => (u.approx n x + v.approx n x) -
          (u.toH1Function + v.toH1Function).toFun x) =
          (fun x => u.approx n x - u.toH1Function.toFun x) +
            (fun x => v.approx n x - v.toH1Function.toFun x) := by
      funext x
      simp only [PDE.H1Function.add_toFun, Pi.add_apply]
      ring
    change eLpNorm
      (fun x => (u.approx n x + v.approx n x) -
        (u.toH1Function + v.toH1Function).toFun x)
      (2 : ℝ≥0∞) (volume.restrict U) ≤ _
    rw [heq]
    exact eLpNorm_add_le (by norm_num)
  tendsto_approx_grad := by
    intro i
    have hbound : Tendsto
        (fun n =>
          eLpNorm
              (fun x =>
                (fderiv ℝ (u.approx n) x) (basisVec i) -
                  u.toH1Function.grad x i)
              (2 : ℝ≥0∞) (volume.restrict U) +
            eLpNorm
              (fun x =>
                (fderiv ℝ (v.approx n) x) (basisVec i) -
                  v.toH1Function.grad x i)
              (2 : ℝ≥0∞) (volume.restrict U))
        atTop (nhds 0) := by
      simpa using (u.tendsto_approx_grad i).add (v.tendsto_approx_grad i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => zero_le) (fun n => ?_)
    have huDeriv : AEStronglyMeasurable
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i))
        (volume.restrict U) := by
      exact ((((u.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
        contDiff_const).continuous.aestronglyMeasurable)
    have hvDeriv : AEStronglyMeasurable
        (fun x => (fderiv ℝ (v.approx n) x) (basisVec i))
        (volume.restrict U) := by
      exact ((((v.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
        contDiff_const).continuous.aestronglyMeasurable)
    have heq :
        (fun x =>
          (fderiv ℝ (fun y => u.approx n y + v.approx n y) x) (basisVec i) -
            (u.toH1Function + v.toH1Function).grad x i) =
          (fun x =>
            (fderiv ℝ (u.approx n) x) (basisVec i) -
              u.toH1Function.grad x i) +
            (fun x =>
              (fderiv ℝ (v.approx n) x) (basisVec i) -
                v.toH1Function.grad x i) := by
      funext x
      rw [fderiv_fun_add
        ((u.approx_smooth n).differentiable (by simp) x)
        ((v.approx_smooth n).differentiable (by simp) x)]
      simp only [PDE.H1Function.add_grad, Pi.add_apply,
        add_apply]
      ring
    change eLpNorm
      (fun x =>
        (fderiv ℝ (fun y => u.approx n y + v.approx n y) x) (basisVec i) -
          (u.toH1Function + v.toH1Function).grad x i)
      (2 : ℝ≥0∞) (volume.restrict U) ≤ _
    rw [heq]
    exact eLpNorm_add_le (by norm_num)

@[simp]
theorem add_toH1Function (u v : PDE.H10Function U) :
    (add u v).toH1Function = u.toH1Function + v.toH1Function :=
  rfl

noncomputable instance : Add (PDE.H10Function U) where
  add := add

@[simp]
theorem toH1Function_add (u v : PDE.H10Function U) :
    (u + v).toH1Function = u.toH1Function + v.toH1Function :=
  rfl

end PDE.H10Function
