module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.FinClsLoc.BaseChangeCent in
theorem GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg :
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ) (L : Type) [Ring L] [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι →
    (∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c) →
    ∀ (K : Type) [Field K] [Algebra ℚ K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) ∧
      ∀ x : K ⊗[ℚ] G.C, x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        Commute x (inC G K (Y : G.C)) ∧
          inC G K (β : G.C) * (starT G.star K x).unop * inC G K ((β⁻¹ : G.Cˣ) : G.C) = x := by
  intro p _ G β Y L _ _ ι hinj hrange K _ _
  have hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro c
    change _ ↔ c ∈ Set.range ι
    rw [phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    rfl
  have hex' := Module.Flat.lTensor_exact K hex
  refine ⟨?_, ?_⟩
  · have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj
    intro a b hab
    apply this
    rw [← hmap, ← hmap, hab]
  · intro x
    have e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        x ∈ Set.range (ι.toLinearMap.lTensor K) := by
      constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩
    rw [e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi,
      Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    exact and_congr Iff.rfl Iff.rfl
