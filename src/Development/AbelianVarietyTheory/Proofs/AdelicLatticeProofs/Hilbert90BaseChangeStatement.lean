module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChange
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_baseChange' : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  first | exact @GlobalTheory.CNorm.hilbert90_baseChange | exact GlobalTheory.CNorm.hilbert90_baseChange | (intros; apply GlobalTheory.CNorm.hilbert90_baseChange <;> assumption)
