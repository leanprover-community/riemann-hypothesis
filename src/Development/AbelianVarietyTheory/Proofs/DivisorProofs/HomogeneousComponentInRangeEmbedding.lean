module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

end GlobalTheory.CharPair.GradR
