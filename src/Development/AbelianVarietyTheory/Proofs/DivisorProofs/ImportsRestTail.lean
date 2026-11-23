module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' hc
  have key : (e' ∘ liftSemi f) = (liftSemi g ∘ e.baseChange R') := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => simp [liftSemi_tmul, LinearMap.baseChange_tmul, hc]
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  have hb : Function.Bijective (e.baseChange R') := by
    have h := ((LinearEquiv.ofBijective e he).baseChange R R' M N).bijective
    convert h using 1
    refine congrArg DFunLike.coe ?_
    ext m
    simp
  rw [← Function.Bijective.of_comp_iff' he' (liftSemi f), key, Function.Bijective.of_comp_iff _ hb]

end GlobalTheory.Div.BaseChangeIso
