module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.card_mul_phi_le_valuation_productForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  first | exact @GlobalTheory.EtaVal.card_mul_phiC_le_valuation | exact GlobalTheory.EtaVal.card_mul_phiC_le_valuation | (intros; apply GlobalTheory.EtaVal.card_mul_phiC_le_valuation <;> assumption)
