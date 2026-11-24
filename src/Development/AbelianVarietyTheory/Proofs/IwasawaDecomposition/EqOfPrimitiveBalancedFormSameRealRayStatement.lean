module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | exact GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | (intros; apply GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul <;> assumption)
