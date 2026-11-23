module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficients
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_translated_expansion_coefficients : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.TrCoef.exists_translated_coef | exact GlobalTheory.MumCmp.TrCoef.exists_translated_coef | (intros; apply GlobalTheory.MumCmp.TrCoef.exists_translated_coef <;> assumption)
