module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open Complex Matrix
open scoped Real

noncomputable section

namespace GlobalTheory.RiemannThetaModel

variable {ι : Type*} [Fintype ι]

theorem riemannTheta_eq_thetaChar {g : ℕ} (a b : Fin g → ℝ) (Ω : Matrix (Fin g) (Fin g) ℂ)
    (v : Fin g → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar Ω (fun i => a i) (fun i => b i) v := by
  change ∑' n, riemannThetaTerm a b Ω v n = _
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  refine tsum_congr fun n => ?_
  change cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
    (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) = _
  congr 1
  have e1 : ((fun i => (n i : ℂ)) + fun i => (a i : ℂ)) = fun i => (n i : ℂ) + a i := rfl
  have e2 : (v + fun i => (b i : ℂ)) = fun i => v i + b i := rfl
  rw [e1, e2]
  ring

end GlobalTheory.RiemannThetaModel
