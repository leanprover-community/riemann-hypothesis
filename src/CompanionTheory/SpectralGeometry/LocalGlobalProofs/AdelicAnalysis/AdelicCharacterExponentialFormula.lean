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
import Mathlib.Tactic.Basify
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb_apply {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by
  have h : ρ w ((B *ᵥ y) i) = ∑ j, ρ w (B i j) * ρ w (y j) := by

    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h]
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type_right, blockDiagonal_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp

theorem emb_dotProduct_DM {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by
  have h : ∀ w, ρ w (a ⬝ᵥ (B *ᵥ y)) = ∑ i, ρ w (a i) * ρ w ((B *ᵥ y) i) := by
    intro w

    simp [dotProduct, map_sum, map_mul]
  simp only [h]
  rw [dotProduct, Fintype.sum_prod_type_right]
  simp only [DM_mulVec_emb_apply, emb]

theorem toA_dotProduct_Bf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by

  simp only [dotProduct, mulVec, toA, Bf, map_sum, map_mul, Matrix.map_apply]

theorem chiB_toA_eq_exp (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ)
    (hψ : IsStdChar F ψ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (hQ : QSetup M B ρ P) (a y : ι → F) :
    chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  rw [chiB, toA_dotProduct_Bf, hψ.2, emb_dotProduct_DM, sum_rho_eq_trace hT hρ]
  norm_cast

end GlobalTheory.CompanionTheory.SW.ThW
