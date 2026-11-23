module

public import Formalism.LocalRingCardinality.DataKerI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KFormCore

section Generic

variable {K : Type} [Field K] {σ σ' δ δ' : Type}

def jetL (J : (δ →₀ ℕ) → K) : MvPolynomial (σ ⊕ δ) K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials (σ ⊕ δ) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

theorem jetL_monomial (J : (δ →₀ ℕ) → K) (m : σ ⊕ δ →₀ ℕ) (c : K) :
    jetL J (monomial m c) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial (σ ⊕ δ) K) = c • basisMonomials (σ ⊕ δ) K m := by
    simp [smul_monomial]
  rw [h1, map_smul, jetL, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

end Generic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem applyAt0_eq (l : ℕ) [Fact l.Prime] (a b : ℕ) (Th : MvPowerSeries (ι × Fin a × Fin b) ℂ_[l])
    (Q : MvPolynomial (KM.XZ ι a b) ℤ) :
    KM.applyAt0 a b l Th Q = jetL (fun m => (m.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff m Th)
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) := by

  conv_rhs => rw [Q.as_sum, map_sum, map_sum]
  unfold KM.applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_monomial, jetL_monomial, mul_assoc]
  rfl

end Main

end GlobalTheory.KFormCore
