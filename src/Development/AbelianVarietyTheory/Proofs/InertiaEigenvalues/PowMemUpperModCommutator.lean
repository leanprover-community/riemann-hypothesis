module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfCommStatement
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.UpperNumbering
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

private lemma commutator_le_of_forall_commutator_mem {G : Type*} [Group G] (C : Subgroup G)
    (hC : ∀ σ τ : G, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a _ b _ => by
    rw [commutatorElement_def]
    exact hC a b

theorem pow_mem_upper_mod_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p e v C hC hv hpe σ hσ

  let H : Subgroup (L ≃ₐ[F] L) := ⁅(⊤ : Subgroup (L ≃ₐ[F] L)), ⊤⁆
  let Q : IntermediateField F L := IntermediateField.fixedField H
  haveI : IsGalois F Q := IsGalois.of_fixedField_normal_subgroup H
  have hker : (AlgEquiv.restrictNormalHom Q).ker = H := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_fixedField H
  have hab : ∀ s t : Q ≃ₐ[F] Q, s * t = t * s := by
    intro s t
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) s
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) t
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ (AlgEquiv.restrictNormalHom Q).ker := by
      rw [hker]
      have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [commutatorElement_def] at h
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  have hσQ : AlgEquiv.restrictNormalHom Q σ ∈ upperRamificationGroup F Q v := by
    rw [← GroundTheory.LocalField.map_upperRamificationGroup Q v]
    exact Subgroup.mem_map_of_mem _ hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' F Q p e v hab hv hpe _ hσQ
  rw [← map_pow, ← GroundTheory.LocalField.map_upperRamificationGroup Q] at hpow
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hpow
  refine ⟨τ, hτ, commutator_le_of_forall_commutator_mem C hC ?_⟩
  have hk : τ⁻¹ * σ ^ p ∈ (AlgEquiv.restrictNormalHom Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
  rw [hker] at hk
  exact hk

end GlobalTheory.PMon.Ram
