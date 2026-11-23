module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrimeStatement
public import GroundTheory.LocalFields.UpperNumbering
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild_of_exponent :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E →
      lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) →
      (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B hp hE h0 hord hcomm hpow hB
  have hBn : B.Normal := ⟨fun b hb σ => by
    have h := B.mul_mem (hcomm σ b) hb
    simpa [mul_assoc] using h⟩
  set M := IntermediateField.fixedField B
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) M).ker = B := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) L
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hM0 : upperRamificationGroup F M 0 = ⊤ := by
    rw [← map_upperRamificationGroup M 0, upperRamificationGroup_zero, h0, Subgroup.map_top_of_surjective _ hsurj]
  have hMexp : ∀ s : M ≃ₐ[F] M, s ^ p = 1 := by
    intro s
    obtain ⟨σ, rfl⟩ := hsurj s
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hpow σ
  have hM1 := GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime F M p e hp he hordF hM0 hMexp
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ ∉ B := by
    by_contra h
    push_neg at h
    exact hB (eq_top_iff.mpr fun x _ => h x)
  have hmem : AlgEquiv.restrictNormalHom M σ₀ ∈ (upperRamificationGroup F L 1).map (AlgEquiv.restrictNormalHom M) := by
    rw [map_upperRamificationGroup M 1, hM1]; trivial
  obtain ⟨σ, hσ, hσe⟩ := hmem
  have hσB : σ ∉ B := by
    intro hσB
    apply hσ₀
    rw [← hker, MonoidHom.mem_ker, ← hσe, ← MonoidHom.mem_ker, hker]
    exact hσB
  have := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L B 1 h0 σ hσ hσB
  rw [mul_one] at this
  exact_mod_cast this

end GlobalTheory.PMon.Ram
