module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow : ∀ (d N : ℕ), ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) → (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) → MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * AddMonoidAlgebra.coeff P α = 0 := by
  first | exact @GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | exact GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | (intros; apply GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero <;> assumption)
