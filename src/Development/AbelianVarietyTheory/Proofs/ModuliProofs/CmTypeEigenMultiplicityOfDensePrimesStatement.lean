module

public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R] (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) → Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) → ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  first | exact @GlobalTheory.eigenMult_of_dense | exact GlobalTheory.eigenMult_of_dense | (intros; apply GlobalTheory.eigenMult_of_dense <;> assumption)
