module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.AbsCount2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ClassChar2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.CoverEx
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.FibreCG
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LogAsym
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SysEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.TwoParts
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.UnitOfPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ZeroExp
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

theorem count_holds : Count := count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)

theorem normCharPow_holds : NormCharPow := normCharPow count_holds

theorem fibreCG_holds : FibreCG := fibreCG classChar2 count_holds normCharPow_holds

theorem fibre_holds : Fibre := fibre fibreCG_holds

theorem twoParts_holds : TwoParts := twoParts classChar2 count_holds normCharPow_holds

theorem partA_holds : PartA := by
  intro E _ _ _ n P ι _ m Ps hn hm hι h
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm
    (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)
  have := Fintype.card_congr s
  simp at this
  omega

end UpperTheory.ConvolutionTheory.R
