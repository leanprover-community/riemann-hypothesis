module

public import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised

@[expose] public section

noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SelfDualFil

theorem isRegular_of_mul_eq_smul {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) : IsRegular M ∧ IsRegular N := by
  have hd : M.det * N.det ≠ 0 := by
    rw [← Matrix.det_mul, H, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (left_ne_zero_of_mul hd)).1,
    Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (right_ne_zero_of_mul hd)).1⟩

theorem mul_eq_smul_comm {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) :
    N * M = c • (1 : Matrix (Fin h) (Fin h) A) := by
  apply (isRegular_of_mul_eq_smul hc H).1.1
  show M * (N * M) = M * (c • 1)
  rw [← Matrix.mul_assoc, H]
  simp

section

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ]
  [Algebra ℤ_[p] Γ]

theorem G_eq [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply (isRegular_of_mul_eq_smul hμ D.G_mul_F).2.2
  show D.G * D.F = D.G.map (phiInv p O) * D.Ψ' * D.F
  have e1 : D.G.map (phiInv p O) * D.F.map (phiInv p O) = nu ε • 1 := by
    rw [← Matrix.map_mul, D.G_mul_F]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, phiInv_mu]
  have e2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, mul_eq_smul_comm hξ D.Ψ_mul]
    simp
  rw [Matrix.mul_assoc, e2, Matrix.mul_smul, e1, smul_smul, xi_mul_nu, D.G_mul_F]

def dualDatum [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    Datum ε h ℤ_[p] where
  F := D.Gᵀ
  G := D.Fᵀ
  Ψ := D.Ψ'ᵀ
  Ψ' := D.Ψᵀ
  ρT := (etale ε h).ρT
  ρM := (etale ε h).ρM
  G_mul_F := by rw [← Matrix.transpose_mul, D.G_mul_F]; simp
  F_eq := by
    rw [Matrix.transpose_map, ← Matrix.transpose_mul, ← G_eq hμ hξ D]
  Ψ_mul := by rw [← Matrix.transpose_mul, D.Ψ_mul]; simp
  F_act := by
    intro a
    have e : ((etale ε h).ρT a).map (ofPadic p O) = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, hij]
    have e' : (etale ε h).ρM a = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Matrix.algebraMap_matrix_apply, hij]
    rw [e, e']
    simp

variable (C : Type) [Field C] [Algebra O C]

end

end GlobalTheory.SelfDualFil
