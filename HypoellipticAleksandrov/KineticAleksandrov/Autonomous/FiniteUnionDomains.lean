module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign
import Mathlib.Topology.Connected.Basic

/-! # Finite disjoint velocity interval unions and their unique component poles -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- A finite disjoint union is represented by its actual open interval components. -/
structure FiniteIntervalUnion where
  count : ℕ
  component : Fin count → Interval
  disjoint : Pairwise (fun i j => Disjoint (component i).carrier (component j).carrier)

/-- The physical velocity carrier of the finite union. -/
def FiniteIntervalUnion.carrier (H : FiniteIntervalUnion) : Set ℝ :=
  ⋃ i, (H.component i).carrier

/-- Every component is contained in the velocity union. -/
theorem FiniteIntervalUnion.component_subset (H : FiniteIntervalUnion) (i : Fin H.count) :
    (H.component i).carrier ⊆ H.carrier := subset_iUnion (fun j => (H.component j).carrier) i

/-- The union is open in the physical scalar velocity coordinate. -/
theorem FiniteIntervalUnion.isOpen_carrier (H : FiniteIntervalUnion) : IsOpen H.carrier :=
  isOpen_iUnion (fun _ => isOpen_Ioo)

/-- A velocity in the union belongs to exactly one component. -/
theorem FiniteIntervalUnion.existsUnique_component (H : FiniteIntervalUnion)
    {v : ℝ} (hv : v ∈ H.carrier) : ∃! i, v ∈ (H.component i).carrier := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hv
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (H.disjoint hji) hj hi

/-- The selected component is chosen from proved unique geometric membership. -/
def FiniteIntervalUnion.componentIndex (H : FiniteIntervalUnion)
    (v : ℝ) (hv : v ∈ H.carrier) : Fin H.count :=
  (H.existsUnique_component hv).exists.choose

/-- The selected component contains the given physical velocity. -/
theorem FiniteIntervalUnion.mem_componentIndex (H : FiniteIntervalUnion)
    (v : ℝ) (hv : v ∈ H.carrier) : v ∈ (H.component (H.componentIndex v hv)).carrier :=
  (H.existsUnique_component hv).exists.choose_spec

/-- Any certified component gives the same selected index; there is no choice dependence. -/
theorem FiniteIntervalUnion.componentIndex_eq (H : FiniteIntervalUnion)
    {v : ℝ} (hv : v ∈ H.carrier) (i : Fin H.count) (hi : v ∈ (H.component i).carrier) :
    H.componentIndex v hv = i := by
  obtain ⟨j, hj, hu⟩ := H.existsUnique_component hv
  exact (hu _ (H.mem_componentIndex v hv)).trans (hu i hi).symm

/-- A physical pole for a finite disjoint union retains the same time convention. -/
abbrev FiniteUnionPole (H : FiniteIntervalUnion) (T : WithTop ℝ) :=
  {p : Point // (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier}

/-- The component selected by a physical union pole. -/
def finiteUnionPoleIndex (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : Fin H.count := H.componentIndex (e.1.velocity 0) e.2.2

/-- Regard a union pole as a pole in its unique interval component. -/
def finiteUnionComponentPole (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : StripPole (H.component (finiteUnionPoleIndex H T e)) T :=
  ⟨e.1, e.2.1, H.mem_componentIndex _ e.2.2⟩

/-- Include a certified component pole into the union without changing physical coordinates. -/
def componentPoleInclusion (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) (e : StripPole (H.component i) T) : FiniteUnionPole H T :=
  ⟨e.1, e.2.1, H.component_subset i e.2.2⟩

/-- Component inclusion followed by selection recovers the original component. -/
theorem finiteUnionPoleIndex_inclusion (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) (e : StripPole (H.component i) T) :
    finiteUnionPoleIndex H T (componentPoleInclusion H i T e) = i :=
  H.componentIndex_eq _ i e.2.2

/-- A single interval is a finite union with one component. -/
def Interval.toFiniteUnion (H : Interval) : FiniteIntervalUnion where
  count := 1
  component := fun _ => H
  disjoint := fun _i _j h => False.elim (h (Subsingleton.elim _ _))

/-- The singleton representation has exactly the original scalar carrier. -/
theorem Interval.toFiniteUnion_carrier (H : Interval) : H.toFiniteUnion.carrier = H.carrier := by
  ext v
  simp only [FiniteIntervalUnion.carrier, Interval.toFiniteUnion, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact hi
  · intro hv
    exact ⟨0, hv⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
