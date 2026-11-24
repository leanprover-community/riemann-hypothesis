module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  first | exact @GlobalTheory.Mum.thetaLevels_galois | exact GlobalTheory.Mum.thetaLevels_galois | (intros; apply GlobalTheory.Mum.thetaLevels_galois <;> assumption)
