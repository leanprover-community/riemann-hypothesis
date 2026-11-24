module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  first | exact @GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | exact GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | (intros; apply GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre <;> assumption)
