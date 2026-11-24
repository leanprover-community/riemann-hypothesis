module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianFields
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFormulaOfInvM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDivRp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteBadScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixEqBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingHomMulSubEqZero
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellOf
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

@[expose] public section

namespace PositivityTheory.Rg.Rsw.Cell

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem muCell : HtExist → IdemEx → MuCell := fun hH hI =>
  have hU := GlobalTheory.CompanionTheory.UnitCell.unitCrit hI
  have hA := GlobalTheory.CompanionTheory.CellTop.cellAlg hI
  muCell_of GlobalTheory.CompanionTheory.RswCell.riesz (GlobalTheory.CompanionTheory.RswCell.NullCompl.nullC_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) (GlobalTheory.CompanionTheory.RswCell.cellFormula_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) hA (GlobalTheory.CompanionTheory.CellDecomp.decomp hI)
    (GlobalTheory.CompanionTheory.CellFew.fewC hI hU (GlobalTheory.CompanionTheory.MoveCell.move_of_unitCrit hU) (GlobalTheory.CompanionTheory.SmallRatCell.smallRat hI) hA) (GlobalTheory.CompanionTheory.SetCell.setC hH) GlobalTheory.CompanionTheory.RswTop.topC

end PositivityTheory.Rg.Rsw.Cell
