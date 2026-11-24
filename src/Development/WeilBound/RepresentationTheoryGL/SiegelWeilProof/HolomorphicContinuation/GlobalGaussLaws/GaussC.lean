module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem identG {g : M2 n} (hg : InG g) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) = Xᴴ - Y := by
  obtain ⟨h1, h2, h3⟩ := inG_rel hg
  have h3' : g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = 1 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have key : (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) =
      Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂) -
        (g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁) * Y +
        Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁) * Y +
        (g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [key, h3, h3', h1, h2]
  simp

theorem det_CZD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Z Z
  have h0 : star v ⬝ᵥ ((Zᴴ - Z) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have h0' : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← neg_sub, neg_mulVec, dotProduct_neg, h0, neg_zero]
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h0', smul_zero] at hpos
  exact lt_irrefl _ hpos

end PositivityTheory.Rg.Sw.Glob.GaussH
