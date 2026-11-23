module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DiscreteSeriesCoefficientsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.Fc.S0

structure Hypotheses1 : Prop extends toArithmeticGeometryHyps : ArithmeticGeometryHyps where
  hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  localTateDualityK : Formalism.GaloisCohomology.LocalTateDualityK
  localEulerCharK : Formalism.GaloisCohomology.LocalEulerCharK
  localFinitenessK : Formalism.GaloisCohomology.LocalFinitenessK
  bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral
  jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity

end GlobalTheory.Fc.S0
