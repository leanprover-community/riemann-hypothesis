module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVR
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArc.exists_input_recovering | exact GlobalTheory.TraitArc.exists_input_recovering | (intros; apply GlobalTheory.TraitArc.exists_input_recovering <;> assumption)
