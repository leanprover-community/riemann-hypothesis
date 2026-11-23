module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeries
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arc_generic_point_extends_powerSeries : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  first | exact @GlobalTheory.LN.ArcExtends.exists_extension | exact GlobalTheory.LN.ArcExtends.exists_extension | (intros; apply GlobalTheory.LN.ArcExtends.exists_extension <;> assumption)
