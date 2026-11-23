module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0LevelStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma petersson_smul_of_mem {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : CuspForm Γ k) {h : SL(2, ℤ)}
    (hh : h ∈ Γ) (τ : ℍ) : petersson k ⇑f ⇑g (h • τ) = petersson k ⇑f ⇑g τ := by
  have hf : (⇑f ∣[k] h) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ ⟨h, hh, rfl⟩
  have hg : (⇑g ∣[k] h) = ⇑g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn g _ ⟨h, hh, rfl⟩
  rw [← petersson_slash_SL, hf, hg]

def cosetShift (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h₁ : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ) (h₂ : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) :
    SL(2, ℤ) ⧸ Γ ≃ SL(2, ℤ) ⧸ Γ where
  toFun := Quotient.map' (· * σ⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₁ _ hab
  invFun := Quotient.map' (· * σ) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₂ _ hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem pet_dia_dia : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) =
        GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  intro N l k d σ _ _ hσ f g
  have h₁ : ∀ γ ∈ lev N l, σ * γ * σ⁻¹ ∈ lev N l := fun γ hγ => GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l d σ γ hσ hγ
  have hσ' : IsDia N l (σ 0 0) σ⁻¹ := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hσ.1]
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h₂ : ∀ γ ∈ lev N l, σ⁻¹ * γ * σ ∈ lev N l := fun γ hγ => by
    simpa using GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level N l _ σ⁻¹ γ hσ' hγ
  set e := cosetShift (lev N l) σ h₁ h₂
  unfold pet
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun γ => ?_
  congr 1
  funext z
  have he : e γ = QuotientGroup.mk (γ.out * σ⁻¹) := by
    conv_lhs => rw [← QuotientGroup.out_eq' γ]
    rfl
  have hx : (QuotientGroup.mk (e γ).out : SL(2, ℤ) ⧸ lev N l) = QuotientGroup.mk (γ.out * σ⁻¹) := by
    rw [QuotientGroup.out_eq', he]
  have hmem := QuotientGroup.eq.mp hx.symm
  have hinv : (e γ).out⁻¹ = ((γ.out * σ⁻¹)⁻¹ * (e γ).out)⁻¹ * (σ * γ.out⁻¹) := by group
  rw [hinv, mul_smul, petersson_smul_of_mem f g (inv_mem hmem), dia, dia, petersson_slash_SL,
    mul_smul]

end GlobalTheory.Hk
