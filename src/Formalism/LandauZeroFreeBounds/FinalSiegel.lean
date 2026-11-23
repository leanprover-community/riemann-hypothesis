module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.ZeroFreeDirichlet

theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet
