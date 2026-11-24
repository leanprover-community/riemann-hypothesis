module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdeal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cocycle_correction_square_zero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  first | exact @GlobalTheory.LBLift.cocycle_of_sqZero | exact GlobalTheory.LBLift.cocycle_of_sqZero | (intros; apply GlobalTheory.LBLift.cocycle_of_sqZero <;> assumption)
