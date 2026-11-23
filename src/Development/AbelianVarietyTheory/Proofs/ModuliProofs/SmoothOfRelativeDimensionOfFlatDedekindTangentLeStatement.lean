module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe
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
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), Algebra.FiniteType ℤ o → Flat s → LocallyOfFiniteType s → (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X), x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) → (∀ lam : (Fin r → K) →ₗ[K] K, spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le | exact GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le | (intros; apply GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le <;> assumption)
