module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem ofW_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t i n c
  funext τ
  have hR : (cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i) τ
      = C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i := by
    simp only [Pi.mul_apply, Pi.pow_apply, cstW, uFam, dFam, xFam]
    have h1 : (X : K⟦X⟧) ^ n = X ^ (n % e) * X ^ (e * (n / e)) := by
      rw [← pow_add, Nat.mod_add_div]
    rw [h1, dpDen, Nat.cast_mul, div_eq_mul_inv, mul_inv]
    simp only [map_mul, map_pow]
    ring
  rw [hR]
  ext i' n'
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow, Pi.single_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hn : n' = n
    · subst hn
      simp [coeff_C_mul, coeff_X_pow]
    · simp [coeff_C_mul, coeff_X_pow, hn]
  · simp [hi]

end GlobalTheory.CrysPrism
