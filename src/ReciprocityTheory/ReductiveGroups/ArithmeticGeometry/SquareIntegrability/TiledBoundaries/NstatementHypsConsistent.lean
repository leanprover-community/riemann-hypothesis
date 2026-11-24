module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex

noncomputable section

abbrev E4 : Type := CyclotomicField 4 ℚ

instance : NumberField E4 := inferInstanceAs (NumberField (CyclotomicField 4 ℚ))

instance : IsCyclotomicExtension {4} ℚ E4 := by
  have h : @IsCyclotomicExtension {4} ℚ E4 _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance : IsCMField E4 := IsCyclotomicExtension.Rat.isCMField E4 (S := {4}) ⟨4, rfl, by norm_num⟩

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
