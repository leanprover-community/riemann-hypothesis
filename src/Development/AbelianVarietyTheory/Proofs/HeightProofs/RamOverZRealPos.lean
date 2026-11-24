module

public import Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem ramOverZ_real_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (0 : ℝ) < (ramOverZ la : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)

theorem numerical_h_one_of_weighted_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (large₂ : SizeData₂ D) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ), Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → NumericalH1Condition T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) (WeightAlgebra.PN D large₂) wL.size ∧ nuOf T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) = nus := by
  intro D T h j hj large₂ wL nus hH
  obtain ⟨h0, h1, h2⟩ := hH
  have he : ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
      (ramOverZ la : ℝ) * (nus la / (ramOverZ la : ℝ)) = nus la := fun la =>
    mul_div_cancel₀ _ (ramOverZ_real_pos la).ne'
  refine ⟨⟨fun la => div_nonneg (h0 la) (Nat.cast_nonneg _), h1.subset ?_, ?_⟩, funext he⟩
  · intro la hla h'
    exact hla (by simp only [show nus la = 0 from h', zero_div])
  · refine le_of_eq_of_le ?_ h2
    have hs : (Function.support fun la : HeightOneSpectrum (𝓞 T.Q.c.F) =>
        nus la * ReciprocityTheory.ChartRestriction.G.T0.logNorm la).Finite :=
      h1.subset fun la hla h' => hla (by simp only [show nus la = 0 from h', zero_mul])
    simp only [he]
    rw [div_eq_mul_inv, finsum_mul' _ _ hs]
    refine finsum_congr fun la => ?_
    rw [abs_of_nonneg (h0 la), mul_assoc, ← div_eq_mul_inv]
    rfl

end GlobalTheory
