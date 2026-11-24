module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (y : ι → F) : DM B ρ *ᵥ emb ρ y = emb ρ (B *ᵥ y) := by
  funext p
  obtain ⟨i, w⟩ := p
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]

  simp [map_sum, map_mul]

theorem gM_transpose_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) (z : ι × InfinitePlace F → ℝ) (i : ι)
    (v : InfinitePlace F) :
    ((gM ρ b N)ᵀ *ᵥ z) (i, v) = (N : ℝ) * ∑ w, ρ w (b v : F) * z (i, w) := by
  simp only [mulVec, dotProduct, gM, transpose_apply, Matrix.smul_apply, kroneckerMap_apply, EM,
    Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Finset.sum_ite_eq, mul_assoc]

theorem gM_DM_emb_eq_trace : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  intro F _ _ ι _ _ _ M B ρ P hQ b N y
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  funext p
  obtain ⟨i, v⟩ := p
  rw [DM_mulVec_emb, gM_transpose_mulVec]
  have h := sum_rho_eq_trace hT hρ ((b v : F) * (B *ᵥ y) i)
  simp only [emb, ← map_mul]
  rw [h]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.ThW
