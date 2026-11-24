module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenOfRightInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.section_eigenfunction_maximal_compact : GlobalTheory.CompanionTheory.Jp.SectionEigenfunctionMaximalCompact := by
  first | exact @GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | exact GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant <;> assumption)
