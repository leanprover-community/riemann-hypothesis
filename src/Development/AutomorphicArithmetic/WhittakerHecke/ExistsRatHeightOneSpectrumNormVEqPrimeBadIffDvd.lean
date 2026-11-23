module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

theorem UpperTheory.exists_rat_heightOneSpectrum_normV_eq_prime_bad_iff_dvd :
    ∀ (p N : ℕ), p.Prime → ∃ v : H.P ℚ, normV v = p ∧ (Bad N v ↔ p ∣ N) := by
  intro p N hp
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpr.ne_zero
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr, hne⟩, ?_, ?_⟩
  · have h : ∀ w : HeightOneSpectrum (𝓞 ℚ), normV w = Ideal.absNorm w.asIdeal := fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [h]
    change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · change (N : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ p ∣ N
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
      Int.natCast_dvd_natCast]
