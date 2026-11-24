module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurface
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
