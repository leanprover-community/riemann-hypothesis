module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_fou : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ μ _ w φ
  obtain ⟨β, hβ, hsym, -, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI : IsTopologicalAddGroup (Matrix α ν E) := (hM α ν).2.grp
  have hh : ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) (x : Matrix α ν E),
      heisFun c ψ Q w φ x = ψ (β x w.toCols₂ + 2⁻¹ * β w.toCols₁ w.toCols₂) * φ (x + w.toCols₁) := by
    intro w φ x
    show ψ (pr c Q _ _ + 2⁻¹ * pr c Q _ _) * _ = _
    rw [← hβ, ← hβ]
  have hJ : w * stdJ ν E = fromCols (-w.toCols₂) w.toCols₁ := by
    ext i (j | j) <;> simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, fromBlocks, toCols₁, toCols₂]
  funext x
  simp only [fou]
  rw [hh, hJ]
  simp only [four, hh, toCols₁_fromCols, toCols₂_fromCols, ← hβ]
  set x₁ := w.toCols₁
  set y₁ := w.toCols₂
  rw [← integral_add_right_eq_self (μ := μ) (fun y => ψ (β x y) * (ψ (β y x₁ + 2⁻¹ * β (-y₁) x₁) * φ (y + -y₁))) y₁,
    ← integral_const_mul]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add (f := _), map_neg, LinearMap.add_apply, LinearMap.neg_apply, hsym y x₁, hsym y₁ x₁]
  ring

end GlobalTheory.KSp
