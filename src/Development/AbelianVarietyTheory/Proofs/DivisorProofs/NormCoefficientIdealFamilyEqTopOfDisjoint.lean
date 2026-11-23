module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent


open MvPolynomial in
theorem normIdeal_top (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
    [FiniteDimensional K L] [CommRing B] [Algebra B L] :
    GlobalTheory.NormSheaf.normIdeal A K L B (⊤ : Ideal B) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨1, fun _ => 1, fun _ => Submodule.mem_top, Finsupp.single 0 (Module.finrank K L), ?_⟩
  have hform : GlobalTheory.NormSheaf.normForm K L (fun _ : Fin 1 => algebraMap B L 1) =
      X 0 ^ Module.finrank K L := by
    unfold GlobalTheory.NormSheaf.normForm
    simp [Fin.sum_univ_one, map_one, Matrix.det_smul]
  rw [hform, coeff_X_pow]
  simp

theorem ideal_eq_top_of_forall_not_mem {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by
  have hV : IsAffineOpen V.1 := V.2
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ V.1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxV
    exact h x ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).2 hx) hxV
  rw [← hV.fromSpec_image_zeroLocus] at hempty
  have h0 : PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := Set.image_eq_empty.mp hempty
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top] at h0
  exact h0

theorem famIdeal_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  intro Y Z π _ _ hK hfd I U hU
  unfold famIdeal
  split_ifs with h
  · have hV : I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ = ⊤ :=
      ideal_eq_top_of_forall_not_mem I _ (fun y hy hyV => hU y hy hyV)
    simp only [hV]
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    exact normIdeal_top _ _ _ _
  · rfl

end GlobalTheory.NormSheafDescent
