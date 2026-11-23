module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwo
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.dedekind_constants_degree_two : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L L' : Lat ξ E) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' w Q → (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) → ∃ (B B' : ChartBundle O (segreVec y) r E) (v v' : Module.Basis (Fin r) Ω E), (∀ c, segreVec y c ≠ 0 → ∀ z, (z ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L q) ∧ (z ∈ B'.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L' q)) ∧ IsModelOver (pointIdeal O y) d ∧ SameGenericFibre ϖ B B' ∧ IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat | exact GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat <;> assumption)
