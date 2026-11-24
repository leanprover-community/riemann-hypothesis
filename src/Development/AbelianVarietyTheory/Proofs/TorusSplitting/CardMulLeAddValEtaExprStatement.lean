module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulLeAddValEtaExpr
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
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.card_mul_le_val_etaExpr_of_le_sum_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (k : ℕ) [Finite (LevGrp Dw k)] (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw k) (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (w : LatMod Dw k → F) (q : ℚ), (∀ (g : LevGrp Dw k) j, (q : WithTop ℚ) ≤ ∑ b, v (w (g (xs j b)))) → (((Nat.card (LevGrp Dw k) : ℚ) * q : ℚ) : WithTop ℚ) ≤ v (etaExpr k cf xs w) := by
  first | exact @GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr | exact GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr | (intros; apply GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr <;> assumption)
