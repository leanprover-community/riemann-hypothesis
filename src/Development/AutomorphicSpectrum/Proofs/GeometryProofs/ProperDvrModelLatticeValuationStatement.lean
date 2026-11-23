module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDvrModelLatticeValuation
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.proper_dvr_model_lattice_valuation : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X' ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O) (L : Lat ξ Ω) (σ : Ω) (ℓ : ℕ) (u : O), PropZ → Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ξ' ≫ g = ξ → IsCptGen ξ → IsCptGen ξ' → (∀ q' : X', genPt ξ' ⤳ q') → NormalCpt ξ → ConstClosed O Ω → (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) → L.IsVB 1 ⊤ → (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ) → (ℓ : Ω) = algebraMap O Ω (ϖ * u) → (TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∃ p' : Cpt ξ', g p'.1 = p.1) → OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd.order_at_place | exact GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd.order_at_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd.order_at_place <;> assumption)
