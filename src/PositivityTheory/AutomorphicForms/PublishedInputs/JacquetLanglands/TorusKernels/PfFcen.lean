module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
