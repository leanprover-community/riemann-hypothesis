module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.Int.Geo
open NumberField

private lemma natDvd_of_eq_mul {F : Type} [Field F] [NumberField F] {n m : ℕ} {x : 𝓞 F}
    (h : (n : 𝓞 F) * x = (m : 𝓞 F)) : n ∣ m := by
  have hd : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  have hn := congrArg (Algebra.norm ℤ) h
  have e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := fun k => by simp
  rw [map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at hn
  have hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F) :=
    ⟨_, hn.symm⟩
  exact Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)

theorem UpperTheory.exists_number_field_point_of_generic :
    GenEx → NumEx := by
  intro hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN
  refine ⟨fun hmem => ?_, fun c a t h => ?_⟩
  · rw [S.lev] at hmem
    obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.1 hmem
    have hNa : (N : 𝓞 D.F) ∈ S.𝔞 := hxe ▸ Ideal.mul_mem_left _ _ hx
    obtain ⟨a, ha⟩ := (hG (𝓞 D.F) S.𝔞 N hN).1 hNa
    obtain ⟨c, hc⟩ := natDvd_of_eq_mul hxe
    exact ⟨c, a, hc, ha⟩
  · exact ⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩
