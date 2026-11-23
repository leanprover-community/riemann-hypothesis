module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwFibre

theorem twisted_fibre_isLocallyConstant_hasCompactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)), IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧ HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := by
  intro k _ _ _ _ i t ψ hψ τ σ f y
  obtain ⟨hl, hc⟩ := GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
      (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
    have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
        (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
      h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
    exact IsLocallyConstant.comp₂ h2 hl (fun a b => a • b)
  · refine hc.mono fun d hd h0 => hd ?_
    have h0' : evX f (dEmb k i t d * y) = 0 := h0
    show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
    rw [h0', smul_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.TwFibre
