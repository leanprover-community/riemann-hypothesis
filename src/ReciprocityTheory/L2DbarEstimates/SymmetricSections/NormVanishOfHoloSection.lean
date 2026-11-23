module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.EsymmZero
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.LineFinite
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfParts
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.RemovableFinset
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Section
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmGrowth
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
