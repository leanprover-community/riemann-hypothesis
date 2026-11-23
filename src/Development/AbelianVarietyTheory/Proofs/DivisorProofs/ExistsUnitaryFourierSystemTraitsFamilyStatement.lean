module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamily
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_unitary_fourier_system_traits_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  first | exact @GlobalTheory.USep.exists_system_with_traits_and_family | exact GlobalTheory.USep.exists_system_with_traits_and_family | (intros; apply GlobalTheory.USep.exists_system_with_traits_and_family <;> assumption)
