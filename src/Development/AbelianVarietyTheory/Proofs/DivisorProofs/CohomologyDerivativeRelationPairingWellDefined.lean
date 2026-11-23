module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vf_of_frame {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  apply GlobalTheory.AbCoh.exists_vectorField_of_functional <;> assumption

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem derivClass_eq : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  intro R _ C _ F hF h0 x n n' y w y' w' hd hd' l
  obtain ⟨δ, hnat, hδ⟩ := exists_vf_of_frame F hF h0 l
  obtain ⟨f, g, ω, rfl, hg, hf⟩ := hd
  obtain ⟨f', g', ω', hx, hg', hf'⟩ := hd'
  obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 hx
  obtain rfl : y = fun k ↦ H1.mk F (g k) := funext fun k ↦ (hg k).symm
  obtain rfl : y' = fun k ↦ H1.mk F (g' k) := funext fun k ↦ (hg' k).symm
  have e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k) := by simp [map_sum, map_smul]
  have e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k) := by simp [map_sum, map_smul]
  rw [e1, e2, H1.mk_eq_mk]
  refine ⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩
  funext T T' φ
  have hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ := congrFun (congrFun (congrFun hb T) T') φ
  have key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T)) := by
    rw [← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]
  rw [hf φ, hf' φ] at key
  have e := congrArg (δ T') key

  simp only [map_sub, map_add (f := _), map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e
  simp only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  simp only [mul_comm (algebraMap R _ _)] at e ⊢
  linear_combination e

end GlobalTheory.AbCoh
