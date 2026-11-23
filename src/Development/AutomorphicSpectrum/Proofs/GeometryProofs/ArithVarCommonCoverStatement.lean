module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.FieldTheory.Relrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.arith_var_common_cover : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω :=
  @_root_.PositivityTheory.UnitarySelfGeneration.j_normal
