module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquetStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.DerivSub
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

namespace GlobalTheory.RgGu.Nup2

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.NuPair k := fun k _ _ _ _ =>
  GlobalTheory.T.nu_pair_of_derivatives_jacquet k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.T.derivative_jacquet_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (GlobalTheory.T.jm_theta_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (derivSub_main k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)

end GlobalTheory.RgGu.Nup2
