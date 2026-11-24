module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumFirstBlockBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveFrameDatumBlockSubstitutionStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.SquareFlipCols

theorem squareFlip_blockDiag_cols : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ M₁ hM₁ M₂ hM₂ X
  have h1 : fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) =
      fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) :=
    funext (GlobalTheory.T.partialFourierSum_firstBlock_blockDiagonal ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂)
  have h2 : phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) =
      ((ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ)) • fun Z => phiA μ σ ν ϖ e
        (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
          (Z * fromBlocks M₁.val 0 0 (invT M₂).val) :=
    funext fun Z => by rw [Pi.smul_apply, smul_eq_mul]; exact GlobalTheory.T.primitiveFrameDatum_blockSubstitution μ σ ν ϖ e _ M₁ hM₁ M₂ hM₂ Z
  have hd := GlobalTheory.FrameDepth.hasDepth_phiA (hμ := by assumption) k A A' (D₁ ⊕ D₂) μ σ ν ϖ e
    (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν
    ((FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e _ hϖ hψ).1 Φ hΦ)
  have h3 : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) (phiA μ σ ν ϖ e
      (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    rw [← latA_blockLat]; exact hd
  unfold squareFlip
  rw [h1, h2, map_smul, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks ψ⁻¹ ϖ e hϖ (hasConductor_inv hψ) _ h3 M₁ hM₁ M₂ hM₂ X]

end GlobalTheory.SquareFlipCols
