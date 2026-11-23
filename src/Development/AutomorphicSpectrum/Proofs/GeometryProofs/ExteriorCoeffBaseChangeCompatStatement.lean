module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exterior_coeff_base_change_compat : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | exact GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull <;> assumption)
