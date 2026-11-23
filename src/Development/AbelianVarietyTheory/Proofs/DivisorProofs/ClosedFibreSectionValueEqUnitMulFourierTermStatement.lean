module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  first | exact @GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | exact GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | (intros; apply GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term <;> assumption)
