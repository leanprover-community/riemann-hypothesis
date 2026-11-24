module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBounded
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.adic_completion_regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded | exact GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded <;> assumption)
