module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegrality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.idempotent_decomposition_of_integrality : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  first | exact @GlobalTheory.JR.Et.Idem.main | exact GlobalTheory.JR.Et.Idem.main | (intros; apply GlobalTheory.JR.Et.Idem.main <;> assumption)
