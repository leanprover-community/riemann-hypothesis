module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianNormSectionValue
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_norm_section_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | exact GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.EvalPt.norm_evC_of_forms <;> assumption)
