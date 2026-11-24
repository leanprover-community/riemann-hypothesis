module

public import Mathlib.RingTheory.PowerSeries.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory

theorem coeff_coeff_pow_eq_of_box :
    ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧),
      (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  intro R _ m i n G H h
  induction m generalizing i n with
  | zero => simp
  | succ k ih =>

    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨s, t⟩ hst
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hst
    dsimp only at hpq hst ⊢
    rw [ih p s (fun i' hi' n' hn' => h i' (by omega) n' (by omega)), h q (by omega) t (by omega)]

end GlobalTheory
