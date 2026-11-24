module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinear
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  first | exact @GlobalTheory.CompactHowe.PolyTensor.exists_tensor | exact GlobalTheory.CompactHowe.PolyTensor.exists_tensor | (intros; apply GlobalTheory.CompactHowe.PolyTensor.exists_tensor <;> assumption)
