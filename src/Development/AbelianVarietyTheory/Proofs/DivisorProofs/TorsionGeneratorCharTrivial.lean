module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelianStatement
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := GlobalTheory.T.torsionPoint_locally_constant_complexAbelian A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory
