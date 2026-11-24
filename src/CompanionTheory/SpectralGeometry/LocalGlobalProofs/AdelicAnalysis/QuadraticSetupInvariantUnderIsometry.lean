module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem qsetup_conj_majorant (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (h : QSetup M B ρ P)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hb : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := ((ρ w).map_det B).symm
    rw [e]
    exact (map_ne_zero _).2 h4
  have hd : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have e := congrArg Matrix.det (hg w)
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
    exact hb w e.symm
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro w
    have hinj : Function.Injective (gi w).mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hd w)))
    have := (h6 w).conjTranspose_mul_mul_same hinj
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro w
    set g := gi w with hgdef
    set b := B.map (ρ w) with hbdef
    have hbu : IsUnit b.det := isUnit_iff_ne_zero.2 (hb w)
    have hgw : gᵀ * b * g = b := hg w
    have e1 : (b⁻¹ * gᵀ * b) * g = 1 := by
      rw [Matrix.mul_assoc b⁻¹ gᵀ b, Matrix.mul_assoc b⁻¹, hgw,
        Matrix.nonsing_inv_mul _ hbu]
    have e2 : g * (b⁻¹ * gᵀ * b) = 1 := mul_eq_one_comm.1 e1
    have e3 : (g * b⁻¹ * gᵀ) * b = 1 := by
      rw [← e2]; simp only [Matrix.mul_assoc]
    have e4 : g * b⁻¹ * gᵀ = b⁻¹ := (Matrix.inv_eq_left_inv e3).symm
    calc gᵀ * P w * g * b⁻¹ * (gᵀ * P w * g)
        = gᵀ * P w * (g * b⁻¹ * gᵀ) * P w * g := by simp only [Matrix.mul_assoc]
      _ = gᵀ * (P w * b⁻¹ * P w) * g := by rw [e4]; simp only [Matrix.mul_assoc]
      _ = b := by rw [h7 w, hgw]

end GlobalTheory.CompanionTheory.SW.ThW
