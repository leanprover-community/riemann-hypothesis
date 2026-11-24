module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
