module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Mathlib.Topology.Sets.Compacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.HaarExist

variable (r : ℕ)

theorem entryBall_compact_open (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ∧
      IsOpen {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have e : {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} =
      Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : K) 1 := by
    ext A
    exact ⟨fun h i _ j _ => mem_closedBall_zero_iff.2 (h i j),
      fun h i j => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))⟩
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero⟩

theorem norm_one_entry_le (K : Type) [NormedField K] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) K) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem glO_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact (glO r K) ∧ IsOpen (glO r K) ∧ (glO r K).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r K
  have e : glO r K = Units.embedProduct _ ⁻¹' ({A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1})) := by
    ext g
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  refine ⟨?_, ?_, 1, fun i j => ⟨norm_one_entry_le r K i j, by rw [inv_one]; exact norm_one_entry_le r K i j⟩⟩
  · rw [e]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hc.prod (MulOpposite.opHomeomorph.symm.isClosedEmbedding.isCompact_preimage hc))
  · rw [e]
    exact (ho.prod (ho.preimage MulOpposite.continuous_unop)).preimage Units.continuous_embedProduct

theorem continuousStar_of_norm_star (E : Type) [NormedField E] [StarRing E] (h : ∀ y : E, ‖star y‖ = ‖y‖) :
    ContinuousStar E :=
  ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) h).continuous⟩

theorem uO_isCompact_isOpen (E : Type) [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [ContinuousStar E] :
    IsCompact (uO r E) ∧ IsOpen (uO r E) ∧ (uO r E).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r E
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  exact ⟨hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, ho.preimage continuous_subtype_val,
    1, fun i j => norm_one_entry_le r E i j⟩

def positiveCompactsOf {X : Type} [TopologicalSpace X] (s : Set X) (h : IsCompact s ∧ IsOpen s ∧ s.Nonempty) :
    TopologicalSpace.PositiveCompacts X :=
  ⟨⟨s, h.1⟩, by simpa [h.2.1.interior_eq] using h.2.2⟩

theorem unitBall_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] :
    IsCompact (Metric.closedBall (0 : K) 1) ∧ IsOpen (Metric.closedBall (0 : K) 1) ∧
      (Metric.closedBall (0 : K) 1).Nonempty := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ⟨isCompact_closedBall _ _, IsUltrametricDist.isOpen_closedBall _ one_ne_zero, 0, by simp⟩

theorem meas_nonempty : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  intro F E _ _ _ _ h r
  haveI := h.ultraF; haveI := h.ultraE; haveI := h.lcF; haveI := h.lcE
  haveI := continuousStar_of_norm_star E h.norm_star
  letI : MeasurableSpace (GL (Fin r) F) := borel _
  haveI : BorelSpace (GL (Fin r) F) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin r) E) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin r) E) := ⟨rfl⟩
  letI : MeasurableSpace F := borel _
  haveI : BorelSpace F := ⟨rfl⟩
  letI : MeasurableSpace E := borel _
  haveI : BorelSpace E := ⟨rfl⟩
  exact ⟨{ μG := Measure.haarMeasure (positiveCompactsOf _ (glO_isCompact_isOpen r F))
           μU := Measure.haarMeasure (positiveCompactsOf _ (uO_isCompact_isOpen r E))
           μF := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen F))
           μE := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen E))
           haarG := inferInstance, haarU := inferInstance, haarF := inferInstance, haarE := inferInstance
           volG := Measure.haarMeasure_self, volU := Measure.haarMeasure_self
           volF := Measure.addHaarMeasure_self, volE := Measure.addHaarMeasure_self }⟩

end GlobalTheory.JR.HaarExist
