module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem coinv_top_or_rat (P Q R S : ℕ) (x : ℂ) :
    coinv P Q R S x = ⊤ ∨ ∃ x' : ℚ, coinv P Q R S x = coinv P Q R S (x' : ℂ) := by
  by_cases hx : ∃ x' : ℚ, x = x'
  · obtain ⟨x', rfl⟩ := hx
    exact Or.inr ⟨x', rfl⟩
  push_neg at hx
  by_cases hI : IsEmpty (Ix P Q)
  · right
    refine ⟨0, ?_⟩
    unfold coinv
    congr 1
    ext g
    simp [Matrix.trace, Finset.univ_eq_empty]
  · left
    rw [not_isEmpty_iff] at hI
    obtain ⟨a⟩ := hI
    let K : Subring ℂ := (Rat.castHom ℂ).range
    have hxK : x ∉ K := by
      rintro ⟨q, hq⟩
      exact hx q hq.symm
    have hsign : ∀ c : Ix R S, lineSign a c ∈ K := by
      intro c
      rcases a with a | a <;> rcases c with c | c <;> simp only [lineSign] <;>
        first | exact K.one_mem | exact K.neg_mem K.one_mem
    have hc : ∀ α : Ln P Q R S →₀ ℕ, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) ∈ K := by
      intro α
      refine K.sum_mem fun c _ => K.mul_mem (hsign c) (K.add_mem (natCast_mem K _) ?_)
      exact RingHom.mem_range.mpr ⟨1 / 2, by simp⟩
    have hmon : ∀ α : Ln P Q R S →₀ ℕ, (MvPolynomial.monomial α (1 : ℂ) : Pol P Q R S) ∈ coinv P Q R S x := by
      intro α
      have hne : (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x ≠ 0 := by
        intro h
        apply hxK
        rw [sub_eq_zero] at h
        rw [← h]
        exact hc α
      have hg : fockAct1 P Q R S (Eab a a) (MvPolynomial.monomial α 1) -
          (x * (Eab a a : Mat P Q).trace) • MvPolynomial.monomial α 1 ∈ coinv P Q R S x :=
        Submodule.subset_span ⟨Eab a a, _, rfl⟩
      have htr : (Eab a a : Mat P Q).trace = 1 := by simp [Eab]
      rw [cartan1, htr, mul_one, ← sub_smul] at hg
      have h2 := (coinv P Q R S x).smul_mem ((∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x)⁻¹ hg
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have he : (MvPolynomial.monomial α (AddMonoidAlgebra.coeff f α) : Pol P Q R S) =
        AddMonoidAlgebra.coeff f α • MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    exact (coinv P Q R S x).smul_mem _ (hmon α)

end GlobalTheory.HoweR
