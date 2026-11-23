module

public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField FractionalIdeal

namespace Formalism.IndefR.Fin

theorem diffKPrincipal : Formalism.BasicNotions.DiffKPrincipal := by
  intro R H
  obtain ⟨β, hβ, heq⟩ := Formalism.MainNotions.UnusedSlot33.HK.diffK_holds H
  rw [heq, coeIdeal_span_singleton]
  congr 1

theorem ccNorm : Formalism.BasicNotions.CcNorm := by
  intro R H
  rw [← coeIdeal_mul]
  have h := Formalism.MainNotions.UnusedSlot33.HK.normK_holds H H.ccK H.ccK_ne_bot
  rw [show (H.ccE : Ideal (𝓞 H.E)) = Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK from rfl, h,
    coeIdeal_span_singleton, map_natCast]

theorem factPrincipalDatum : Formalism.BasicNotions.FactPrincipalDatum :=
  Formalism.BasicNotions.factPrincipalDatum_of diffKPrincipal ccNorm

end Formalism.IndefR.Fin

end
