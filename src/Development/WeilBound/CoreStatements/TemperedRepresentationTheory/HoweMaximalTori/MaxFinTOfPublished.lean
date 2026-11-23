module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
public import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountDef
public import Development.WeilBound.ThetaLifts.Reductions.JoinDef
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolReOf2T
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem PositivityTheory.HoweDualityUnitaryAlt.polRe_of2T : PositivityTheory.ThKR.JoinTri → PositivityTheory.HoweDualityUnitaryAlt.MaxFinT → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.PolCount → PositivityTheory.ThKF.CartanConj → PositivityTheory.ThKF.CartanMove → GlobalTheory.ThK.KCoinv → PositivityTheory.ThKF.ILeft → GlobalTheory.ThK.PolRe := GlobalTheory.CompanionTheory.ThetaK.polRe_of2T
