module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
