module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem FlagVandermondeHomogeneous.proof : FlagVandermondeHomogeneous.Statement := by
  intro f N
  have hblock : ∀ τ : Fin f,
      (vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))).IsHomogeneous
        (N * (N - 1) / 2) := fun τ =>
    VandermondeOfHomogeneous.proof _ _ N _ (fun i => isHomogeneous_X ℚ (τ, i))
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)))
    (fun _ => N * (N - 1) / 2) (fun τ _ => hblock τ)
  simpa [blockVandermonde, topDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] using h

end GroundTheory.Heights₂.Heights.RestTerms
