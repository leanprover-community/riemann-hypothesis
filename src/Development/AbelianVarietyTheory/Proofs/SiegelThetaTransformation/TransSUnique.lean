module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEqStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitarySiegelThetaTransformationLawStandar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff

@[expose] public section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

theorem transS_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ _ I_mem_siegel
  refine GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e1 := h _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e2 := h' _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e := e1.trans e2.symm
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.vecMul_one] using e

theorem val_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ →
      TransS (Matrix.J ι ℚ) φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ),
        Ph u ∧ ψ y = u * haar (fun x => φ x * chr y' x) := by
  intro κ ι _ _ _ ⟨p, hp⟩ φ ψ ⟨R, hR, h⟩ hψ ht y
  have e := transS_unique (SymplecticGroup.J_mem ι ℚ) hψ
    ⟨R, hR, FourierJ.ft_level hR h _⟩ ht (FourierJ.trans_J hp hR h)
  refine ⟨I ^ (Fintype.card ι * p), y, ⟨4, by norm_num, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; simp [Complex.I_pow_four]
  · rw [e]
    simp only [FourierJ.ft, FourierJ.pr, FourierJ.ech, chr]

end GlobalTheory.Phase
