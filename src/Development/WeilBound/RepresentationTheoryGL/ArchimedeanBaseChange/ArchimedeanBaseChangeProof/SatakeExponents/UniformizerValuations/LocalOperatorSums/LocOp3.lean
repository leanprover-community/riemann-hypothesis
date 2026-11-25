module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHecke
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexEqCard
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcN.F2.LocOpPf

theorem locOp3 (E : Type) [Field E] [NumberField E] [IsCMField E] : LocOpUniformizer E := by
  intro n a b h w K' hK'o hK'le hK'n X hXK hX
  exact ⟨GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_locally_constant E n a b h w K' hK'o hK'le hK'n X hXK hX, GlobalTheory.CompanionTheory.DiagAvg.ct_eq_diag E n a b h w K' hK'o hK'le hK'n X hXK hX,
    GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution E n a b h w K' hK'o hK'le hK'n X hXK hX, GlobalTheory.CompanionTheory.HeckeAct.hk_ind_apply E n a b h w K' hK'o hK'le hK'n X hXK hX⟩

end PositivityTheory.Rg.BcN.F2.LocOpPf
