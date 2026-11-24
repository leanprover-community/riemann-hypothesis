module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs
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

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

def DigAbs (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (σ : Type) [Fintype σ] (g rho : σ → ℕ), (∀ v, rho v < p ^ g v) →
    (∀ be : σ →₀ ℕ, (∏ v, gamR (p ^ g v) (rho v) (be v)) ≠ 0 ∧
      padicValRat p (∏ v, gamR (p ^ g v) (rho v) (be v)) = 0) ∧
    ∀ (inv : Bool) (c : ℕ), ∃ lam : (σ →₀ ℕ) →₀ O, (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 4 * c) ∧
      ∀ be : σ →₀ ℕ,
        geQ (vK p ((if inv then (((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O))⁻¹
            else ((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O)) - binomCombF (K := KK O) lam be)) (c : ℝ)

end Formalism.MainNotions.Proposition5Numerics
