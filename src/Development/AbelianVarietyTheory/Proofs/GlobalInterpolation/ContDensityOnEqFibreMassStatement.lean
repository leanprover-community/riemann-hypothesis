module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContDensityOnEqFibreMass
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.contDensity_eq_fibre_measure_of_compact_open : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.contDensityOn_eq_fibre_mass | exact GlobalTheory.contDensityOn_eq_fibre_mass | (intros; apply GlobalTheory.contDensityOn_eq_fibre_mass <;> assumption)
