module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPoint
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitaryTrait_finiteExtension_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → ∃ (T' : UTrait Xo cf) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : ratHull S.R →+* FractionRing T'.V) (e : T'.P.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₁ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.be a b = (k : ℤ) * T.be (e a) (e b) := by
  first | exact @GlobalTheory.UTraitExtLab.main | exact GlobalTheory.UTraitExtLab.main | (intros; apply GlobalTheory.UTraitExtLab.main <;> assumption)
