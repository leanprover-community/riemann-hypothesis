module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetryOf
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.HtCancel
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryTranspositionFactor
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.EmbImmersion
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.ExistsBase
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsMultiHomogRenameBaseInc
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.PolySmulOfSameSing
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SmoothComb
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.StFormB
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

@[expose] public section

namespace SquareStatements

theorem antisymmetry_of_singular_statement (hSing : StSing) : GoodTowerAntisymmetry :=
  good_tower_antisymmetry_of stXB (alg_of stEmb stFormB) HeightCancellation.stHt hSing stBase stCmp
    antisymmetry_transposition_factor

end SquareStatements
