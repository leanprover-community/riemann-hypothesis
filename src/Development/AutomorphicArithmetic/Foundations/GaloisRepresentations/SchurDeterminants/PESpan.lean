module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem elementary_span_mul (K : Type) [CommRing K] (n k l : ℕ)
    (P Q : MvPolynomial (Fin n) K) (hP : P ∈ eSpan K n k) (hQ : Q ∈ eSpan K n l) :
    P * Q ∈ eSpan K n (k + l) := by
  have hmem : P * Q ∈ eSpan K n k * eSpan K n l := Submodule.mul_mem_mul hP hQ
  have hle : eSpan K n k * eSpan K n l ≤ eSpan K n (k + l) := by
    unfold eSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
    refine ⟨Fin.append m m', ?_⟩
    simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  exact hle hmem

private theorem one_mem_eSpan (K : Type) [CommRing K] (n j : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n j := by
  unfold eSpan
  apply Submodule.subset_span
  refine ⟨fun _ => 0, ?_⟩
  simp [esymm_zero]

theorem eSpanMul : ESpanMul := by
  intro K _ n
  refine ⟨fun k l hkl => ?_, fun k l P Q hP hQ => elementary_span_mul K n k l P Q hP hQ⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  intro P hP
  simpa using elementary_span_mul K n k d P 1 hP (one_mem_eSpan K n d)

end UpperTheory.Gal.Schur
