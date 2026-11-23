module

public import Formalism.UnipotentAdelicQuotients.EllReg
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.BaseLevel
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.ConvolutionBound
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Decompose
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.ExistsSmoothExt
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.IteratedPartialFourierChar
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Moments
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingFourier
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingLocal
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.SmoothOfLocallySmooth
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.StepCore
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.SymbLower
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeakFourier
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightDiff
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightedNormFinite
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.UnipotentAdelicQuotients.EllRegCut
public import Formalism.UnipotentAdelicQuotients.EllRegStep

@[expose] public section

namespace ZetaZeros.D.EllReg

theorem elliptic_regularity_of_parts : Internal := by
  have hSP : StepOfParts :=
    stepOfParts_of frozenDecompositionOfParts weightedNormFinite weightedNormLimit regularity_inductive_step
  exact internal_of_all smoothOfSobolevAll existsBump cutoffContinuous smoothOfLocallySmooth
    sobolevOfCompactSupport symbolLowerBound sobolevWeightLipschitz convolution_bound frozenKernelSmall
    adjointPairingFourier iteratedPartialFourierChar integralFourierChar adjointPairingLocal weakEquationFourier hSP

end ZetaZeros.D.EllReg
