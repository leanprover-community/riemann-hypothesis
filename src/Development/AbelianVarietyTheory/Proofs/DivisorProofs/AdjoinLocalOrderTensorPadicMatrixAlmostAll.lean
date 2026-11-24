module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Mathlib.Algebra.Central.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderContainingIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionAvoidPrime
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra

@[expose] public section

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
