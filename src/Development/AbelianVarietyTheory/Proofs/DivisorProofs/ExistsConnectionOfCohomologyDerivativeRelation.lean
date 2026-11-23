module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneFormsStatement
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_obRel_of_dRel : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  intro R _ C _ F hF h0 x n y w hD hy
  obtain ⟨N, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl2⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
  obtain ⟨f, g, ω, hf, hg, hfD⟩ := hD
  have hcl : ∀ i, ∃ b : C0 F, d0 F b = (∑ k, l i (w k) • g k).1 := fun i ↦ by
    refine H1.mk_eq_zero.1 ?_

    simp only [map_sum, map_smul, hg]
    exact hy (l i)
  choose b hb using hcl
  have hb' : ∀ i ⦃T T' : C⦄ (φ : T ⟶ T'),
      b i T' - mp F φ (b i T) = ∑ k, l i (w k) • (g k).1 T T' φ := fun i T T' φ ↦ by
    have := congrFun (congrFun (congrFun (hb i) T) T') φ
    rw [amitsur_d0_apply] at this
    rw [this, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  have hw : ∀ k (T : C), (w k).1 T = ∑ i, l i (w k) • (Φ.w i).1 T := fun k T ↦ by
    have := congrArg (fun v : Glob1 F ↦ v.1 T) (hl2 (w k))
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hsum : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ∑ k, (g k).1 T T' φ • (w k).1 T' =
      ∑ i, (b i T' - mp F φ (b i T)) • (Φ.w i).1 T' := fun T T' φ ↦ by
    simp only [hb', hw, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_comm, smul_assoc]
  let ω' : A0 F := fun T ↦ ω T + ∑ i, b i T • (Φ.w i).1 T
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω' T' = p1 F φ (ω' T) + D R (F.obj T') (f.1 T T' φ) := by
    intro T T' φ
    rw [hfD φ, hsum φ]

    simp only [ω', map_add (f := _), map_sum, oneFormsMapOfFunctorMorphism_smul, ← (Φ.w _).2 φ, sub_smul, Finset.sum_sub_distrib]
    abel
  have hglob : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      dOne R (F.obj T') (ω' T') = pOm F 2 φ (dOne R (F.obj T) (ω' T)) := by
    intro T T' φ
    rw [hconn φ, map_add (f := _), dOne_D, add_zero, pOm_dOne]
  obtain ⟨m, u, v, hζ⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨N, ⟨Φ⟩⟩ h0 (fun T ↦ dOne R (F.obj T) (ω' T)) hglob
  exact ⟨m, u, v, f, ω', hf, hconn, fun T ↦ congrFun hζ T⟩

end GlobalTheory.AbCoh
