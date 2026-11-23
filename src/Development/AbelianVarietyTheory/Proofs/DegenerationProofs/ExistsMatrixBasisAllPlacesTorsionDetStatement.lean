module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMatrixBasisAllPlacesTorsionDet
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_global_matrix_eq_unit_det_mul_local : ∀ (K : Type) [Field K] (r : ℕ) (T : Tab K r) (N n d : ℕ) (κ : K) (P : Set (ValuationSubring K)) (S₀ : ValuationSubring K), 1 ≤ N → 1 ≤ n → 1 ≤ d → S₀ ∈ P → T.Full N n → (∀ S ∈ P, ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ = S ∧ T.Near N n d κ σ O T' B) → (∀ x : K, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1) → ∃ Φ : Matrix (Fin r) (Fin r) K, ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B → ∃ U : Matrix (Fin r) (Fin r) O, IsUnit U.det ∧ Φ.map σ = U.map O.subtype * B := by
  first | exact @GlobalTheory.OneBasis.Places.exists_basis_all_places | exact GlobalTheory.OneBasis.Places.exists_basis_all_places | (intros; apply GlobalTheory.OneBasis.Places.exists_basis_all_places <;> assumption)
