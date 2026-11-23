module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem exists_eq_of_coeff_box_eq_zero {R : Type} [CommRing R] (i n : ℕ) (D : R⟦X⟧⟦X⟧)
    (h : ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' D) = 0) :
    ∃ A B : R⟦X⟧⟦X⟧, D = X ^ (i + 1) * A + C (X ^ (n + 1)) * B := by
  classical
  obtain ⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by
    refine ⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩
    ext m
    rw [coeff_X_pow_mul', coeff_mk]
    split_ifs with hm
    · rw [coeff_mk, Nat.sub_add_cancel hm]
    · exact (h k hk m (by omega)).symm
  have hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_C_mul, hlow k (by omega), sub_self]
  obtain ⟨A, hA⟩ := hdvd
  exact ⟨A, B, by rw [← hA]; ring⟩

theorem coeff_frob2_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  intro l _ K _ φ₂ hC hX i n G H h
  obtain ⟨A, B, hAB⟩ := exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by
    rw [map_sub, map_sub, h i' hi' n' hn', sub_self])
  obtain ⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by
    rw [hX, map_pow]
    have hd := sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l
    rwa [add_sub_cancel_left] at hd
  have hl : 1 ≤ l := (Fact.out : Nat.Prime l).one_lt.le
  have e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A) := by
    rw [map_mul, map_pow, hc]
    ring
  have e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B := by
    rw [map_mul, hC, map_pow, frob_X, ← pow_mul]
  have hz : coeff n (coeff i (φ₂ (G - H))) = 0 := by
    rw [hAB, map_add (f := _), e1, e2, map_add (f := _), map_add (f := _), coeff_X_pow_mul',
      if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul',
      if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]
  rwa [map_sub, map_sub, map_sub, sub_eq_zero] at hz

end GlobalTheory.CrysPrism
