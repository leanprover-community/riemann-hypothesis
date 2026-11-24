module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.IsLocOpOfOk
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMVal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

alias chiW_mul := _root_.PositivityTheory.SiegelWeilFormula.SD.chiW_mul_pf

alias chiW_cont := _root_.PositivityTheory.SiegelWeilFormula.SD.chiW_cont_pf

theorem chiW_norm (w : InfinitePlace F) : ∀ z : ℂ, z ≠ 0 → ‖d.chiW w z‖ = 1 := by
  intro z _
  by_cases h : IsUnit (d.uW w z)
  · rw [SD.chiW, dite_eq_left h]
    exact Circle.norm_coe _
  · rw [SD.chiW, dite_eq_right h, norm_one]

alias chiW_pos := _root_.PositivityTheory.SiegelWeilFormula.SD.chiW_pos_pf

theorem chiW_form (w : InfinitePlace F) : ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → d.chiW w z = (z / (‖z‖ : ℂ)) ^ k :=
  _root_.GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow (d.chiW w) (d.chiW_mul w) (d.chiW_cont w) (d.chiW_norm w) (d.chiW_pos w)

end SD

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

alias stepM_val := _root_.PositivityTheory.SiegelWeilFormula.RD.stepM_val_pf

variable {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem locOp_mM_law (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ k : ℤ, ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ d.m * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := d.chiW_form w
  refine ⟨k, fun y a ha hy f hf => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepM_val w hT y a ha hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  rw [R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2), hk _ ha.ne_zero]
  rfl

end RD

end PositivityTheory.SiegelWeilFormula

end
