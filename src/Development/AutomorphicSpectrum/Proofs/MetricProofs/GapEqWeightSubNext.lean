module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyTowtBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_toWtS_homogeneous_coeff_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) :=
  @PositivityTheory.Xgp.t_poly_towt_bound

end GlobalTheory.CompanionTheory.Ar.PB
