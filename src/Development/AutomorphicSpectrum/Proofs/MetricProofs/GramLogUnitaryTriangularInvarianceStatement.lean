module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
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

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors : ∀ (N j : ℕ), j ≤ N → IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧ ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k, (gramHead (sigForm N j) k g).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | exact GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors <;> assumption)
