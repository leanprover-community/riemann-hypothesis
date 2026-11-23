module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeilStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidthsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk

theorem rowDiag_of_siegelWeilUnitary
    (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) :
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  have hDeg := GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths
  have hOne := GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil hSW 3
  exact GlobalTheory.Core.Rk.diagonalRow_bound_from_windowWidthThree GlobalTheory.wuDecayOfGap (hDeg.1 3) (hDeg.2 3) hOne.1 hOne.2

end GlobalTheory.Core.Rk
