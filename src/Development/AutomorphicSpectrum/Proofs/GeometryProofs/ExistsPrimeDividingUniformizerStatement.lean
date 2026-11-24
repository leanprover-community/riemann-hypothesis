module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizer
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_prime_dividing_uniformizer : ∀ (F' : Type) [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | exact GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | (intros; apply GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser <;> assumption)
