module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PairStep

theorem qWeil_zero_cartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem qNum_zero_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ N : LB X, QNum p N 0 0 := by
  intro X _ _ p _ N
  letI := algebraΓOfHom p
  refine ⟨1, 0, one_pos, CartierDiv.eff_zero, (qWeil_zero_cartier 1).symm, fun C _ => ?_⟩
  rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
  simp

end GlobalTheory.PairStep
