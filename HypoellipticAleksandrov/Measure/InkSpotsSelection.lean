module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-!
# Selection geometry for parabolic ink spots

This module proves the purely geometric selected-box step in the
Krylov--Safonov crawling-of-ink-spots argument.  In particular, it contains
the exact shrinking density transfer and extracts a genuine forward-box
crossing from the strict large-outside alternative.  It has no PDE, crossing,
measurability, or countability hypothesis.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem closedSourceBox_subset_closedUnitBox (d : Nat) (q : InkSpotsBox d)
    (hR : 0 < q.radius) (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    parabolicClosedBox 1 q.radius q.baseTime q.center ⊆
      parabolicClosedBox 1 1 0 0 := by
  have hsource : closure (inkSpotsSourceBox q) =
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    simpa only [inkSpotsSourceBox] using
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
        (r := q.radius) (t0 := q.baseTime) (v0 := q.center)
        (by norm_num) hR)
  have hunit : closure (inkSpotsUnitBox d) =
      parabolicClosedBox 1 1 0 0 := by
    simpa only [inkSpotsUnitBox] using
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
        (r := (1 : Real)) (t0 := 0) (v0 := (0 : PDE.Vec d))
        (by norm_num) (by norm_num))
  rw [← hsource, ← hunit]
  exact closure_mono hq

private theorem strictDense_source_bounds {d : Nat} {Gamma : Set (TimeVelocity d)}
    {xi : Real} {q : InkSpotsBox d} (hq : inkSpotsStrictDense Gamma xi q) :
    0 ≤ q.baseTime ∧ q.baseTime + q.radius ^ 2 ≤ 1 ∧
      ∀ i, |q.center i| + q.radius ≤ 1 := by
  have hclosed := closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1
  have hterminal : (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, fun i => ?_⟩
    · nlinarith [sq_nonneg q.radius]
    · norm_num
    · simp [hq.1.le]
  have hterminalUnit := hclosed hterminal
  rw [mem_parabolicClosedBox_iff] at hterminalUnit
  have hplus : (q.baseTime, q.center + q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨le_rfl, ?_, ?_⟩
    · nlinarith [sq_nonneg q.radius]
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      rw [add_sub_cancel_left]
      simp [abs_of_nonneg hq.1.le]
  have hminus : (q.baseTime, q.center - q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨le_rfl, ?_, ?_⟩
    · nlinarith [sq_nonneg q.radius]
    · intro i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      rw [sub_sub_cancel_left]
      simp [abs_of_nonneg hq.1.le]
  have hplusUnit := hclosed hplus
  have hminusUnit := hclosed hminus
  rw [mem_parabolicClosedBox_iff] at hplusUnit hminusUnit
  refine ⟨hplusUnit.1, by norm_num at hterminalUnit ⊢; exact hterminalUnit.2.1, ?_⟩
  intro i
  have hp := hplusUnit.2.2 i
  have hm := hminusUnit.2.2 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, Pi.zero_apply, sub_zero] at hp hm
  have hp' : q.center i + q.radius * 1 ≤ 1 := (le_abs_self _).trans hp
  have hm' : -(q.center i - q.radius * 1) ≤ 1 := (neg_le_abs _).trans hm
  have habs : |q.center i| ≤ 1 - q.radius := by
    rw [abs_le]
    constructor <;> linarith
  linarith

private theorem parabolicBox_subset_closed {d : Nat} {vartheta r t0 : Real}
    {v0 : PDE.Vec d} :
    parabolicBox vartheta r t0 v0 ⊆ parabolicClosedBox vartheta r t0 v0 := by
  intro z hz
  rw [mem_parabolicBox_iff] at hz
  rw [mem_parabolicClosedBox_iff]
  exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩

private theorem sourceBox_measure_ne_top {d : Nat} (q : InkSpotsBox d) :
    volume (inkSpotsSourceBox q) ≠ ∞ := by
  apply measure_ne_top_of_subset
    (parabolicBox_subset_closed (d := d) (vartheta := (1 : Real))
      (r := q.radius) (t0 := q.baseTime) (v0 := q.center))
  exact (isCompact_parabolicClosedBox 1 q.radius q.baseTime q.center).measure_ne_top

private theorem inkSpotsQ3_subset_positive_unit {d : Nat}
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : Real} {q : InkSpotsBox d}
    (heta : 0 < eta) (hzeta : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ3 eta zeta q ⊆ Ioi 0 ×ˢ velocityCube (0 : PDE.Vec d) 1 := by
  rintro z hz
  rcases (mem_inkSpotsQ3_iff.mp hz) with ⟨y, hy, hyz⟩
  rcases (mem_inkSpotsQ2_iff.mp hy) with ⟨hyleft, hyright, hycenter, hyunit⟩
  obtain ⟨hbase, hterminal, hcenter⟩ := strictDense_source_bounds hq
  subst z
  constructor
  · dsimp [inkSpotsContraction]
    have hstart : 0 < q.baseTime + q.radius ^ 2 := by
      nlinarith [sq_pos_of_pos hq.1]
    have hT : 0 < inkSpotsTerminalTime eta q := by
      rw [inkSpotsTerminalTime_eq]
      have hspan : 0 < 4 * q.radius ^ 2 / eta :=
        div_pos (mul_pos (by norm_num) (sq_pos_of_pos hq.1)) heta
      linarith
    have hypos : 0 < y.1 := hstart.trans hyleft
    have hsq : 0 < zeta ^ 2 := sq_pos_of_pos hzeta
    have hsqOne : zeta ^ 2 < 1 := by nlinarith
    have hrewrite :
        inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - y.1) =
          (1 - zeta ^ 2) * inkSpotsTerminalTime eta q + zeta ^ 2 * y.1 := by
      ring
    change 0 < inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - y.1)
    rw [hrewrite]
    exact add_pos (mul_pos (sub_pos.mpr hsqOne) hT) (mul_pos hsq hypos)
  · intro i
    have hyabs : |y.2 i| < 1 := by
      simpa only [Pi.zero_apply, sub_zero] using hyunit i
    have hcabs : |q.center i| < 1 := by
      nlinarith [hcenter i, hq.1]
    have hrewrite : q.center i + zeta * (y.2 i - q.center i) =
        (1 - zeta) * q.center i + zeta * y.2 i := by ring
    change |q.center i + zeta * (y.2 i - q.center i) - 0| < 1
    simp only [sub_zero]
    rw [hrewrite]
    calc
      |(1 - zeta) * q.center i + zeta * y.2 i| ≤
          |(1 - zeta) * q.center i| + |zeta * y.2 i| := abs_add_le _ _
      _ = (1 - zeta) * |q.center i| + zeta * |y.2 i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_pos hzeta]
      _ < (1 - zeta) * 1 + zeta * 1 := by
        have hleft : (1 - zeta) * |q.center i| < (1 - zeta) * 1 :=
          mul_lt_mul_of_pos_left hcabs (sub_pos.mpr hzeta1)
        have hright : zeta * |y.2 i| < zeta * 1 :=
          mul_lt_mul_of_pos_left hyabs hzeta
        linarith
      _ = 1 := by ring

private theorem inkSpotsD3_subset_positive_unit (d : Nat) (Gamma : Set (TimeVelocity d))
    (xi eta zeta : Real) (heta : 0 < eta) (hzeta : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD3 Gamma xi eta zeta ⊆ Ioi 0 ×ˢ velocityCube (0 : PDE.Vec d) 1 := by
  intro z hz
  rw [inkSpotsD3] at hz
  rcases Set.mem_iUnion.mp hz with ⟨q, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hq, hzq⟩
  exact inkSpotsQ3_subset_positive_unit heta hzeta hzeta1 hq hzq

private theorem volume_closed_unit_slab_toReal (d : Nat) (c : Real) (hc : 0 ≤ c) :
    (volume (Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1)).toReal =
      c * (volume (inkSpotsUnitBox d)).toReal := by
  have hunit : (volume (inkSpotsUnitBox d)).toReal = (2 : Real) ^ d := by
    simpa only [inkSpotsUnitBox, one_mul, zero_add, one_pow, mul_one] using
      (volume_parabolicBox_toReal (d := d) (vartheta := (1 : Real))
        (r := (1 : Real)) (t₀ := 0) (v₀ := (0 : PDE.Vec d))
        (by norm_num) (by norm_num))
  calc
    (volume (Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1)).toReal =
        (volume (Icc 1 (1 + c))).toReal *
          (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
      rw [Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul]
    _ = c * (2 : Real) ^ d := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
        volume_velocityCube_toReal (by norm_num : (0 : Real) ≤ 1)]
      ring
    _ = c * (volume (inkSpotsUnitBox d)).toReal := by rw [hunit]

/-- The source box obtained by retaining its base and centre and shrinking its
radius by `alpha`. -/
def inkSpotsShrunkSourceBox {d : Nat} (alpha : Real) (q : InkSpotsBox d) :
    InkSpotsBox d :=
  { radius := alpha * q.radius
    baseTime := q.baseTime
    center := q.center }

/-- A non-expanding positive radius factor gives nested source boxes. -/
theorem inkSpotsSourceBox_shrunk_subset
    (d : Nat) (alpha : Real) (q : InkSpotsBox d)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q) ⊆
      inkSpotsSourceBox q := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsSourceBox_iff] at hz ⊢
  change q.baseTime < t ∧
    t < q.baseTime + (alpha * q.radius) ^ 2 ∧
      v ∈ velocityCube q.center (alpha * q.radius) at hz
  refine ⟨hz.1, ?_, ?_⟩
  · have hfactor : alpha ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ (1 - alpha) * (1 + alpha) :=
        mul_nonneg (sub_nonneg.mpr halpha1) (by linarith)
      nlinarith
    have hsquare : (alpha * q.radius) ^ 2 ≤ q.radius ^ 2 := by
      calc
        (alpha * q.radius) ^ 2 = alpha ^ 2 * q.radius ^ 2 := by ring
        _ ≤ 1 * q.radius ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor (sq_nonneg q.radius)
        _ = q.radius ^ 2 := by ring
    nlinarith [hz.2.1, hsquare]
  · intro i
    have hi := hz.2.2 i
    have hprod : 0 < alpha * q.radius :=
      lt_of_le_of_lt (abs_nonneg (v i - q.center i)) hi
    have hR : 0 < q.radius := by
      rcases (mul_pos_iff.mp hprod) with h | h
      · exact h.2
      · exact False.elim ((not_lt_of_ge halpha0.le) h.1)
    have hle : alpha * q.radius ≤ q.radius :=
      by simpa using mul_le_mul_of_nonneg_right halpha1 hR.le
    exact hi.trans_le hle

/-- The volume of a shrunk source box has the exact parabolic scaling factor. -/
theorem volume_inkSpotsSourceBox_shrunk_toReal
    (d : Nat) (alpha : Real) (q : InkSpotsBox d)
    (halpha : 0 ≤ alpha) (hR : 0 ≤ q.radius) :
    (volume (inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q))).toReal =
      alpha ^ (d + 2) * (volume (inkSpotsSourceBox q)).toReal := by
  change (volume (parabolicBox 1 (alpha * q.radius) q.baseTime q.center)).toReal =
    alpha ^ (d + 2) *
      (volume (parabolicBox 1 q.radius q.baseTime q.center)).toReal
  rw [volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
      (vartheta := (1 : Real)) (r := alpha * q.radius) (t₀ := q.baseTime)
      (v₀ := q.center) (by norm_num) (mul_nonneg halpha hR),
    volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
      (vartheta := (1 : Real)) (r := q.radius) (t₀ := q.baseTime) (v₀ := q.center)
      (by norm_num) hR]
  rw [mul_pow]
  ring

/-- The selected shrinking factor has the reciprocal parabolic volume power. -/
theorem selected_inkSpots_alpha_pow
    (d : Nat) (a alpha : Real) (ha : 0 < a)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : Real) + 2)))) :
    alpha ^ (d + 2) = (1 + a)⁻¹ := by
  have hbase : 0 < 1 + a := by linarith
  have hden : (d : Real) + 2 ≠ 0 := by positivity
  calc
    alpha ^ (d + 2) = (1 + a) ^
        (-(1 / ((d : Real) + 2)) * (d + 2 : Real)) := by
      rw [halpha, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
      congr 1
      norm_num [Nat.cast_add]
    _ = (1 + a) ^ (-1 : Real) := by
      congr 1
      field_simp [hden]
    _ = (1 + a)⁻¹ := Real.rpow_neg_one _

/-- Strict density `a` on a source box transfers to strict density `a^2` on
the selected shrunk source box. -/
theorem inkSpotsStrictDense_shrunkSourceBox
    (d : Nat) (Gamma : Set (TimeVelocity d)) (a alpha : Real)
    (q : InkSpotsBox d)
    (ha0 : 0 < a) (ha1 : a < 1)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : Real) + 2))))
    (hq : inkSpotsStrictDense Gamma a q) :
    inkSpotsStrictDense Gamma (a ^ 2) (inkSpotsShrunkSourceBox alpha q) := by
  have halpha0 : 0 < alpha := by
    rw [halpha]
    exact Real.rpow_pos_of_pos (by linarith) _
  have halpha1 : alpha < 1 := by
    rw [halpha]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · have hden : 0 < (d : Real) + 2 := by positivity
      exact neg_lt_zero.mpr (one_div_pos.mpr hden)
  let Q : Set (TimeVelocity d) := inkSpotsSourceBox q
  let Q' : Set (TimeVelocity d) := inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q)
  have hsub : Q' ⊆ Q := inkSpotsSourceBox_shrunk_subset d alpha q halpha0 halpha1.le
  have hQfinite : volume Q ≠ ∞ := sourceBox_measure_ne_top q
  have hQ'finite : volume Q' ≠ ∞ := measure_ne_top_of_subset hsub hQfinite
  have hQGammafinite : volume (Q ∩ Gamma) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left hQfinite
  have hQdiffFinite : volume (Q \ Q') ≠ ∞ :=
    measure_ne_top_of_subset diff_subset hQfinite
  have hQ'measurable : MeasurableSet Q' := by
    exact measurableSet_parabolicBox 1 (alpha * q.radius) q.baseTime q.center
  have hratio : (volume Q').toReal = alpha ^ (d + 2) * (volume Q).toReal := by
    exact volume_inkSpotsSourceBox_shrunk_toReal d alpha q halpha0.le hq.1.le
  have hpow : alpha ^ (d + 2) = (1 + a)⁻¹ :=
    selected_inkSpots_alpha_pow d a alpha ha0 halpha
  have hnum : a + alpha ^ (d + 2) - 1 = a ^ 2 * alpha ^ (d + 2) := by
    rw [hpow]
    have hden : 1 + a ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hinter : Q ∩ Q' = Q' := inter_eq_right.mpr hsub
  have hGammaInter : (Q ∩ Gamma) ∩ Q' = Q' ∩ Gamma := by
    ext z
    constructor
    · rintro ⟨⟨hzQ, hzGamma⟩, hzQ'⟩
      exact ⟨hzQ', hzGamma⟩
    · rintro ⟨hzQ', hzGamma⟩
      exact ⟨⟨hsub hzQ', hzGamma⟩, hzQ'⟩
  have hresidual : (Q ∩ Gamma) \ Q' ⊆ Q \ Q' := by
    rintro z ⟨hz, hzQ'⟩
    exact ⟨hz.1, hzQ'⟩
  have hQdecomp : (volume Q').toReal + (volume (Q \ Q')).toReal =
      (volume Q).toReal := by
    simpa only [Measure.real, hinter] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hQ'measurable hQfinite)
  have hGammaDecomp : (volume (Q' ∩ Gamma)).toReal +
      (volume ((Q ∩ Gamma) \ Q')).toReal = (volume (Q ∩ Gamma)).toReal := by
    simpa only [Measure.real, hGammaInter] using
      (measureReal_inter_add_diff (μ := volume) (s := Q ∩ Gamma)
        hQ'measurable hQGammafinite)
  have hresidualLe : (volume ((Q ∩ Gamma) \ Q')).toReal ≤
      (volume (Q \ Q')).toReal :=
    ENNReal.toReal_mono hQdiffFinite (measure_mono hresidual)
  have hstrict : a * (volume Q).toReal < (volume (Q ∩ Gamma)).toReal := hq.2.2
  have hQnonneg : 0 ≤ (volume Q).toReal := ENNReal.toReal_nonneg
  have hresult : a ^ 2 * (volume Q').toReal < (volume (Q' ∩ Gamma)).toReal := by
    rw [hratio]
    nlinarith
  have hunit : Q' ⊆ inkSpotsUnitBox d := fun z hz => hq.2.1 (hsub hz)
  refine ⟨mul_pos halpha0 hq.1, hunit, ?_⟩
  exact hresult

/-- A strict large-outside volume alternative contains a strict dense source
box whose forward enlargement contains a point at the time `1 + c`. -/
theorem exists_inkSpotsQ2_crossing_of_volume_outside
    (d : Nat) (Gamma : Set (TimeVelocity d)) (a eta zeta c : Real)
    (hc : 0 < c)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (houtside : c * (volume (inkSpotsUnitBox d)).toReal <
      (volume (inkSpotsD3 Gamma a eta zeta \ inkSpotsUnitBox d)).toReal) :
    ∃ q : InkSpotsBox d, ∃ w : PDE.Vec d,
      inkSpotsStrictDense Gamma a q ∧ (1 + c, w) ∈ inkSpotsQ2 eta q := by
  have heta_le_one : eta ≤ 1 := heta1.le
  have hambient := inkSpotsD3_subset_positive_unit d Gamma a eta zeta heta0 hzeta0 hzeta1
  have hslabFinite : volume (Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1) ≠ ∞ := by
    apply measure_ne_top_of_subset
      (show Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1 ⊆
          parabolicClosedBox c 1 1 (0 : PDE.Vec d) by
        intro z hz
        rw [mem_parabolicClosedBox_iff]
        exact ⟨hz.1.1, by simpa using hz.1.2, fun i => (hz.2 i).le⟩)
    exact (isCompact_parabolicClosedBox c 1 1 (0 : PDE.Vec d)).measure_ne_top
  have hexists : ∃ z ∈ inkSpotsD3 Gamma a eta zeta, 1 + c < z.1 := by
    by_contra hnone
    push_neg at hnone
    have hsubset : inkSpotsD3 Gamma a eta zeta \ inkSpotsUnitBox d ⊆
        Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1 := by
      rintro z ⟨hzD3, hznotunit⟩
      have hzambient := hambient hzD3
      refine ⟨?_, hzambient.2⟩
      constructor
      · by_contra hlt
        have htime : z.1 < 1 := lt_of_not_ge hlt
        apply hznotunit
        rw [inkSpotsUnitBox, mem_parabolicBox_iff]
        exact ⟨hzambient.1, by simpa using htime, hzambient.2⟩
      · exact hnone z hzD3
    have hmeasure := ENNReal.toReal_mono hslabFinite (measure_mono hsubset)
    rw [volume_closed_unit_slab_toReal d c hc.le] at hmeasure
    exact (not_lt_of_ge hmeasure) houtside
  rcases hexists with ⟨z, hzD3, hzlarge⟩
  rw [inkSpotsD3] at hzD3
  rcases Set.mem_iUnion.mp hzD3 with ⟨q, hzD3⟩
  rcases Set.mem_iUnion.mp hzD3 with ⟨hq, hzQ3⟩
  rcases (mem_inkSpotsQ3_iff.mp hzQ3) with ⟨y, hyQ2, hyz⟩
  rcases (mem_inkSpotsQ2_iff.mp hyQ2) with ⟨hyleft, hyright, hycenter, hyunit⟩
  obtain ⟨hbase, hsourceTerminal, hcenter⟩ := strictDense_source_bounds hq
  refine ⟨q, y.2, hq, ?_⟩
  rw [mem_inkSpotsQ2_iff]
  refine ⟨?_, ?_, hycenter, hyunit⟩
  · linarith
  · have hgap : 0 < inkSpotsTerminalTime eta q - y.1 := by
      exact sub_pos.mpr hyright
    have hcontracted' : (inkSpotsContraction eta zeta q y).1 <
        inkSpotsTerminalTime eta q := by
      dsimp [inkSpotsContraction]
      rw [inkSpotsTerminalTime_eq] at hgap
      have hsq : 0 < zeta ^ 2 := sq_pos_of_pos hzeta0
      nlinarith [mul_pos hsq hgap]
    have hcontracted : z.1 < inkSpotsTerminalTime eta q := by
      rw [← hyz]
      exact hcontracted'
    exact hzlarge.trans hcontracted

end

end HypoellipticAleksandrov.Parabolic
