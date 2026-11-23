module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraic
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.phiC_le_normalized_valuation_product_form_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (z : PointsOfFlagModel.Pt Tw .yy), OverLa la T.V io e → y.IsAlg → LiesOverBaseChange la Tw T io y z → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (A : DatAt (Tw.Y z.1) z.2.2.1) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧ ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f → ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  first | exact @GlobalTheory.EtaVal.phiC_le_nval_of_lies | exact GlobalTheory.EtaVal.phiC_le_nval_of_lies | (intros; apply GlobalTheory.EtaVal.phiC_le_nval_of_lies <;> assumption)
