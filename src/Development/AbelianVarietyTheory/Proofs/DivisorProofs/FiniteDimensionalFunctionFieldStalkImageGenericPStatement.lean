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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    letI := GlobalTheory.NormSheafDescent.algKL π;
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  let := GlobalTheory.NormSheafDescent.fieldK π hK
  let := GlobalTheory.NormSheafDescent.algKL π
  let K := Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)
  have hFinite : FiniteDimensional K Y.functionField := by
    obtain ⟨U, hU, hζU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := Z) (U := ⊤) (x := GlobalTheory.NormSheafDescent.genPt π) trivial
    have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
    have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
    let f : Γ(Z, U) →+* K :=
      (Z.presheaf.germ U (GlobalTheory.NormSheafDescent.genPt π) hζU).hom
    let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField := (Y.germToFunctionField (π ⁻¹ᵁ U)).hom
    let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
    have hsq : ∀ a, algebraMap K Y.functionField (f a) = φ (g a) :=
      fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
    let : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
    have : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := π.finite_app U hU
    have : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ hV
    have hint (b : Γ(Y, π ⁻¹ᵁ U)) : IsIntegral K (φ b) := by
      obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
      refine ⟨p.map f, hp.map f, ?_⟩
      have e : (algebraMap K Y.functionField).comp f = φ.comp g := RingHom.ext hsq
      have hpb' : p.eval₂ g b = 0 := hpb
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
    have : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
    let E := IntermediateField.adjoin K (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))
    have hE : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
    have hmem (b : Γ(Y, π ⁻¹ᵁ U)) : φ b ∈ E := by
      have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) :=
        hs ▸ Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have e : φ (a • x) = algebraMap K Y.functionField (f a) * φ x := by
          rw [hsq, Algebra.smul_def, map_mul]
          rfl
        rw [e]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    have htop : E = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
      exact div_mem (hmem b) (hmem c)
    have : FiniteDimensional K (⊤ : IntermediateField K Y.functionField) := htop ▸ hE
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  exact hFinite
