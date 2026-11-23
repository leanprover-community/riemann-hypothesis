module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dvr_model_of_number_field_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation
