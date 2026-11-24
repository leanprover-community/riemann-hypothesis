module

public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
public import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.SharpRestriction.GlobalSchurBounds.FrameCodeOfAdditive
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.HN Formalism.LFunctionChainParameters

theorem placesF_min' {eps : ℝ} (Fm : FamP eps) (h26 : LocalQuadraticParts.LevelTFamily Fm) (hNC : Lnk.NuCommensF Fm) (hTu : TuSize Fm)
    (hRank : J.MuRank Fm) (lG : LinkG Fm) (lMu : LinkMu Fm) : Lnk.PlacesF Fm :=
  placesF_of_local_conditions Fm h26 hNC hTu hRank lG lMu

end Formalism.L2.GlobalTheoryTheory.Places

end
