module

public import HypoellipticAleksandrov.Measure.DensityNearOneMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Source bookkeeping for the near-one density argument

This module combines the supplied source and the near-one deficit in the
literal local parabolic norm.  It contains no PDE, ABP, or density argument.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem memLp_restrict_of_continuousOn_unit_collar
    {d : Nat} {U : Set (TimeVelocity d)}
    {f : TimeVelocity d → Real} {s : Set (TimeVelocity d)}
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hf : ContinuousOn f U)
    (hs :
      s ⊆ parabolicClosedBox 1 1 0 (0 : PDE.Vec d)) :
    MemLp f (parabolicExponent d) (volume.restrict s) := by
  let K : Set (TimeVelocity d) :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact : IsCompact K :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hfK : ContinuousOn f K := hf.mono hclosed
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hfK
  have hfKmem :
      MemLp f (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hfK.aestronglyMeasurable hKmeas) M ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hM z hz
  exact hfKmem.mono_measure (Measure.restrict_mono_set volume hs)

/-- The exponentially weighted local norm of the supplied source plus the
near-one deficit forcing is bounded by the literal unit-box source norm and
the strict-low-set error. -/
theorem
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_source_add_one_sub_le
    (d : Nat) (hd : 0 < d) (rho : Real) (hrho : 0 ≤ rho)
    (U : Set (TimeVelocity d)) (Fsrc u : TimeVelocity d → Real)
    (hclosed :
      parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hFsrc : ContinuousOn Fsrc U)
    (hu_nonneg :
      IsNonnegativeOn u (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (hFsrc_nonneg :
      IsNonnegativeOn Fsrc (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (v0 : PDE.Vec d)
    (hv0 :
      v0 ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2 : Real)) :
    Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) *
            (Fsrc z + rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 (0 : PDE.Vec d)) +
        rho * Real.rpow
          (volume
            (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩
              {z | u z < 1})).toReal
          (1 / ((d : Real) + 1)) := by
  let Q : Set (TimeVelocity d) :=
    parabolicBox 1 1 0 (0 : PDE.Vec d)
  let K : Set (TimeVelocity d) :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  let L : Set (TimeVelocity d) := localABPInterior v0
  let E : Set (TimeVelocity d) := Q ∩ {z | u z < 1}
  let W : TimeVelocity d → Real :=
    fun z ↦ Real.exp (rho * (z.1 - 3 / 4))
  let S : TimeVelocity d → Real := fun z ↦ W z * Fsrc z
  let D : TimeVelocity d → Real := fun z ↦ W z * (rho * max (1 - u z) 0)
  let T : TimeVelocity d → Real :=
    fun z ↦ W z * (Fsrc z + rho * max (1 - u z) 0)
  have hQK : Q ⊆ K := by
    rintro ⟨t, v⟩ ⟨⟨ht0, ht1⟩, hv⟩
    exact ⟨⟨ht0.le, ht1.le⟩, fun i ↦ (hv i).le⟩
  have hQU : Q ⊆ U := hQK.trans hclosed
  have hLQ : L ⊆ Q := by
    simpa only [L, Q] using
      (localABPInterior_subset_parabolicBox_one hv0)
  have hLK : L ⊆ K := hLQ.trans hQK
  have hLmeas : MeasurableSet L := by
    simpa only [L] using measurableSet_localABPInterior v0
  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have hScont : ContinuousOn S U := by
    dsimp only [S]
    exact hW.continuousOn.mul hFsrc
  have hdefCont : ContinuousOn (fun z ↦ rho * max (1 - u z) 0) U :=
    continuousOn_const.mul
      ((continuousOn_const.sub hu.continuousOn).sup continuousOn_const)
  have hDcont : ContinuousOn D U := by
    dsimp only [D]
    exact hW.continuousOn.mul hdefCont
  have hFQmem :
      MemLp Fsrc (parabolicExponent d) (volume.restrict Q) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hFsrc hQK
  have hSmem : MemLp S (parabolicExponent d) (volume.restrict L) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hScont hLK
  have hDmem : MemLp D (parabolicExponent d) (volume.restrict L) :=
    memLp_restrict_of_continuousOn_unit_collar hclosed hDcont hLK
  have hFQtop : parabolicELpNormOn d Fsrc Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFQmem.eLpNorm_ne_top
  have hStop : parabolicELpNormOn d S L ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hSmem.eLpNorm_ne_top
  have hDtop : parabolicELpNormOn d D L ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hDmem.eLpNorm_ne_top
  have hdENN : (1 : ENNReal) ≤ (d : ENNReal) := by
    exact_mod_cast hd
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    calc
      (1 : ENNReal) ≤ (d : ENNReal) := hdENN
      _ ≤ (d : ENNReal) + 1 := le_add_of_nonneg_right bot_le
      _ = parabolicExponent d := rfl
  have hT : T = S + D := by
    funext z
    dsimp only [T, S, D, W, Pi.add_apply]
    ring
  have htriENN :
      parabolicELpNormOn d T L ≤
        parabolicELpNormOn d S L + parabolicELpNormOn d D L := by
    unfold parabolicELpNormOn
    rw [hT]
    exact eLpNorm_add_le hp
  have hsumTop :
      parabolicELpNormOn d S L + parabolicELpNormOn d D L ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hStop, hDtop⟩
  have htriRealRaw := ENNReal.toReal_mono hsumTop htriENN
  have htriReal :
      parabolicLpNormOn d T L ≤
        parabolicLpNormOn d S L + parabolicLpNormOn d D L := by
    unfold parabolicLpNormOn
    rw [ENNReal.toReal_add hStop hDtop] at htriRealRaw
    exact htriRealRaw
  have hsourcePointwise :
      ∀ z ∈ L, ‖S z‖ ≤ ‖Real.exp (rho / 4) * Fsrc z‖ := by
    intro z hz
    have hzQ : z ∈ Q := hLQ hz
    have htime : rho * (z.1 - 3 / 4) ≤ rho / 4 := by
      have hbase : z.1 - 3 / 4 ≤ 1 / 4 := by
        linarith [hzQ.1.2]
      have hmul := mul_le_mul_of_nonneg_left hbase hrho
      nlinarith
    have hweight :
        Real.exp (rho * (z.1 - 3 / 4)) ≤ Real.exp (rho / 4) :=
      Real.exp_le_exp.mpr htime
    have hFz : 0 ≤ Fsrc z := hFsrc_nonneg z hzQ
    have hleft : 0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z :=
      mul_nonneg (Real.exp_pos _).le hFz
    have hright : 0 ≤ Real.exp (rho / 4) * Fsrc z :=
      mul_nonneg (Real.exp_pos _).le hFz
    change ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ ≤
      ‖Real.exp (rho / 4) * Fsrc z‖
    calc
      ‖Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z‖ =
          Real.exp (rho * (z.1 - 3 / 4)) * Fsrc z := by
        rw [Real.norm_eq_abs, abs_of_nonneg hleft]
      _ ≤ Real.exp (rho / 4) * Fsrc z :=
        mul_le_mul_of_nonneg_right hweight hFz
      _ = ‖Real.exp (rho / 4) * Fsrc z‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hright]
  have hSmono :
      parabolicELpNormOn d S L ≤
        eLpNorm (fun z ↦ Real.exp (rho / 4) * Fsrc z)
          (parabolicExponent d) (volume.restrict L) := by
    exact eLpNorm_mono_ae hSmem.aestronglyMeasurable
      (ae_restrict_of_forall_mem hLmeas hsourcePointwise)
  have hFLQ :
      parabolicELpNormOn d Fsrc L ≤ parabolicELpNormOn d Fsrc Q := by
    exact eLpNorm_mono_measure Fsrc (Measure.restrict_mono_set volume hLQ)
  have hsourceENN :
      parabolicELpNormOn d S L ≤
        ENNReal.ofReal (Real.exp (rho / 4)) * parabolicELpNormOn d Fsrc Q := by
    calc
      parabolicELpNormOn d S L ≤
          eLpNorm (fun z ↦ Real.exp (rho / 4) * Fsrc z)
            (parabolicExponent d) (volume.restrict L) := hSmono
      _ = ENNReal.ofReal (Real.exp (rho / 4)) *
          parabolicELpNormOn d Fsrc L := by
        change eLpNorm ((Real.exp (rho / 4)) • Fsrc)
          (parabolicExponent d) (volume.restrict L) =
          ENNReal.ofReal (Real.exp (rho / 4)) *
            eLpNorm Fsrc (parabolicExponent d) (volume.restrict L)
        rw [eLpNorm_const_smul,
          Real.enorm_of_nonneg (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (rho / 4)) *
          parabolicELpNormOn d Fsrc Q :=
        mul_le_mul_right hFLQ _
  have hsourceRightTop :
      ENNReal.ofReal (Real.exp (rho / 4)) * parabolicELpNormOn d Fsrc Q ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFQtop
  have hsourceRealRaw := ENNReal.toReal_mono hsourceRightTop hsourceENN
  have hsourceReal :
      parabolicLpNormOn d S L ≤
        Real.exp (rho / 4) * parabolicLpNormOn d Fsrc Q := by
    unfold parabolicLpNormOn at hsourceRealRaw
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      at hsourceRealRaw
    exact hsourceRealRaw
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    calc
      Real.exp (-rho / 4) * Real.exp (rho / 4) =
          Real.exp ((-rho / 4) + rho / 4) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        congr 1
        ring
      _ = 1 := Real.exp_zero
  have hsourceCancelled :
      Real.exp (-rho / 4) * parabolicLpNormOn d S L ≤
        parabolicLpNormOn d Fsrc Q := by
    calc
      Real.exp (-rho / 4) * parabolicLpNormOn d S L ≤
          Real.exp (-rho / 4) *
            (Real.exp (rho / 4) * parabolicLpNormOn d Fsrc Q) :=
        mul_le_mul_of_nonneg_left hsourceReal (Real.exp_pos _).le
      _ = parabolicLpNormOn d Fsrc Q := by
        rw [← mul_assoc, hcancel, one_mul]
  have hdeficit :=
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le
      d rho hrho U u hQU hu hu_nonneg v0 hv0
  have hdeficit' :
      Real.exp (-rho / 4) * parabolicLpNormOn d D L ≤
        rho * Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
    simpa only [D, W, L, E, Q] using hdeficit
  calc
    Real.exp (-rho / 4) * parabolicLpNormOn d T L ≤
        Real.exp (-rho / 4) *
          (parabolicLpNormOn d S L + parabolicLpNormOn d D L) :=
      mul_le_mul_of_nonneg_left htriReal (Real.exp_pos _).le
    _ = Real.exp (-rho / 4) * parabolicLpNormOn d S L +
        Real.exp (-rho / 4) * parabolicLpNormOn d D L := by ring
    _ ≤ parabolicLpNormOn d Fsrc Q +
        rho * Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) :=
      add_le_add hsourceCancelled hdeficit'
    _ = _ := by rfl

end HypoellipticAleksandrov.Parabolic
