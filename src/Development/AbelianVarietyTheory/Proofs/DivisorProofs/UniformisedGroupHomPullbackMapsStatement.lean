module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMaps
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

theorem _root_.GlobalTheory.T.uniformisedGroupHom_pullback_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  first | exact @GlobalTheory.Mum.Two.PullLin.linPull | exact GlobalTheory.Mum.Two.PullLin.linPull | (intros; apply GlobalTheory.Mum.Two.PullLin.linPull <;> assumption)
