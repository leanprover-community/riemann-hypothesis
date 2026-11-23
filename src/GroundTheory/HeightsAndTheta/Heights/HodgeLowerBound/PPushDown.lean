module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushDown.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hArith : HodgeFlagArith.Statement) : PushDown.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep
  have hY := hArith II Ψ K ι Ω E D Pl H B
  have hX : IsArithVar (imageZ Pl.xV (Pl.flagPrime B)) (D.n + 1) := by
    rw [Pl.imageZ_forget_flagPrime]
    exact D.arith
  refine ⟨fun G J L L' N hJ hL hL' hN => ?_, fun d r L L' N hdr hd hL hL' hN => ?_⟩
  · have h := hPF II hII.1 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) D.flagDim0
      G J L L' N Pl.isBlockMap_xV hY hX hJ hL hL' hN
    rwa [Pl.imageZ_forget_flagPrime] at h
  · exact hII.2.2.2 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) d r L L' N
      Pl.isBlockMap_xV (by rw [hdr]; exact hY) hX hd hL hL' hN

end GroundTheory.Heights₂.Heights.LowerBoundFree
