module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackData
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.torusExtensionPointAction_pullback_data : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  first | exact @GlobalTheory.Mum.Two.ActPull.main | exact GlobalTheory.Mum.Two.ActPull.main | (intros; apply GlobalTheory.Mum.Two.ActPull.main <;> assumption)
