module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
