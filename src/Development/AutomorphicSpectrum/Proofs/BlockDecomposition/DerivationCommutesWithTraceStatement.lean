module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTrace
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

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.derivation_commutes_with_trace : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L] (D : Derivation K L L) (D0 : Derivation K F F), (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) → ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) = algebraMap F L (Algebra.trace F L (D y)) := by
  first | exact @GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | exact GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | (intros; apply GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation <;> assumption)
