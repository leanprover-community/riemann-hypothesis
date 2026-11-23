module

public import Development.EtaleCohomology.EtaleSheaves.LeafSpecGenClosed
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
