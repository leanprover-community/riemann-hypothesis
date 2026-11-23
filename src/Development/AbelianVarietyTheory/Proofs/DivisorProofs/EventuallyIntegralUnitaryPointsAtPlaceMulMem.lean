module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

section General

variable {C : Type} [Ring C] [Algebra ℚ C] {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ C)
  {R : Type} [CommRing R] [Algebra ℚ R] (S : Subring R)

theorem repr_mul_mem (hc : ∀ i j k, algebraMap ℚ R (b.repr (b i * b j) k) ∈ S)
    {y y' : R ⊗[ℚ] C} (hy : ∀ i, (Algebra.TensorProduct.basis R b).repr y i ∈ S)
    (hy' : ∀ i, (Algebra.TensorProduct.basis R b).repr y' i ∈ S) (k : ι) :
    (Algebra.TensorProduct.basis R b).repr (y * y') k ∈ S := by
  set B := Algebra.TensorProduct.basis R b
  have hB : ∀ i j, B.repr (B i * B j) k = algebraMap ℚ R (b.repr (b i * b j) k) := by
    intro i j
    simp [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  rw [← B.sum_repr y, ← B.sum_repr y', Finset.sum_mul_sum]

  simp only [smul_mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
  Finsupp.smul_apply, smul_eq_mul, hB]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.mul_mem (S.mul_mem (hy i) (hy' j)) (hc i j k)

end General

theorem eventually_rat_mem (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (show Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] from
    algebraMap ℚ (AfP p) q).2
  filter_upwards [h] with v hv
  have e : (AfP.eval v) (algebraMap ℚ (AfP p) q) = algebraMap ℚ (Qv v) q := (AfP.eval v).commutes q
  rw [← e]
  exact hv

theorem mul_mem_IntV_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  intro p _ G
  have hall : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k,
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem p _
  filter_upwards [hall] with v hv
  intro a ha a' ha'
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨h1', h2', h3', h4'⟩ := ha'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h1 h1' k
    simpa [IsIntV, basV] using this
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h2' h2 k
    simpa [IsIntV, basV, _root_.mul_inv_rev] using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h3 h3'
    simpa using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h4' h4
    simpa [_root_.mul_inv_rev] using this

end GlobalTheory.OrbFinAf
