module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.WhitStd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.RgGu

theorem whitRankIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankIrr k :=
  fun k _ _ _ _ => PositivityTheory.rg.gu.whit.whitRankIrr k

theorem whitRankStd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankStd k :=
  fun k _ _ _ _ => whitRankStd_of_heredity k (GlobalTheory.T.whittaker_heredity k) (whitRankIrr k)

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.NuPair k :=
  fun k _ _ _ _ => GlobalTheory.RgGu.Nup2.nuPair k

end GlobalTheory.RgGu

end
