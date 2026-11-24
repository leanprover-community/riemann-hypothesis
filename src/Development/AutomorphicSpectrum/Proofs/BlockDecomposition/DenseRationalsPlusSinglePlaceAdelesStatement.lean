module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdeles
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

open scoped Pointwise

theorem _root_.GlobalTheory.T.dense_rationals_plus_single_place_adeles : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  first | exact @GlobalTheory.CompanionTheory.AddSA.dense_add_place | exact GlobalTheory.CompanionTheory.AddSA.dense_add_place | (intros; apply GlobalTheory.CompanionTheory.AddSA.dense_add_place <;> assumption)
