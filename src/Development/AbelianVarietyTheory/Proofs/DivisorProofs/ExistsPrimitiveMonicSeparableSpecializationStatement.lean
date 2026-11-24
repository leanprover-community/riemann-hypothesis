module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveMonicSeparableSpecialization
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

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_primitive_monic_separable_specialization' : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x → ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ)) (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧ (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧ (P.map (MvPolynomial.eval c)).Separable := by
  first | exact @GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | exact GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | (intros; apply GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization <;> assumption)
