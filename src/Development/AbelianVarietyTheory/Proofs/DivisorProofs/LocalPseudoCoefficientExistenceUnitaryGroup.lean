module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffIter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFamF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConstOfTendsto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCutFnIteratedDerivScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuPowLambdaProductCoeffMuVariablePencilEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbIntAdSpanEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StOrbCpt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StProfileHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StTrAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq
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

open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc

theorem localPC_holds : LocalPC :=
  GlobalTheory.PsCo.Pc1.localPC_of_steps GlobalTheory.PsCo.Pc1.A.stAlg GlobalTheory.PsCo.Pc1.stProfile_holds
    GlobalTheory.PsCo.Pc1.stFam GlobalTheory.PsCo.Pc1.Homot.stHomot GlobalTheory.PsCo.Pcd.stLim
    GlobalTheory.ShapeSmoothFinite.stShape GlobalTheory.PsCo.Pc1.orbInt_adSpan_eq_zero GlobalTheory.PsCo.Pc1.stOrbCpt
    GlobalTheory.PsCo.NonEll.stNonEll GlobalTheory.PsCo.Pc3.stTr GlobalTheory.PsCo.Pc3.stTrAd GlobalTheory.T.maximalCompact_pseudoCoefficientData

end GlobalTheory.PsCo.Pc
