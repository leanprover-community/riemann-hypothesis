module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementD
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.FischerAdjointnessHolds
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem mem_intPol_addSubgroup {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ (IntPol p σ).toAddSubgroup ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  rw [Submodule.mem_toAddSubgroup, intPol_iff_norm]

theorem intPol_zpClosed (σ : Type) : ZpClosed p (IntPol p σ).toAddSubgroup := by
  intro c hc x hx
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hx m)

theorem intPol_whc {σ M : Type} [AddCommMonoid M] (w : σ → M) (μ : M) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ (IntPol p σ).toAddSubgroup) :
    weightedHomogeneousComponent w μ x ∈ (IntPol p σ).toAddSubgroup := by
  classical
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hx m
  · rw [norm_zero]; exact zero_le_one

theorem polLatData_of (hB : LatBasisPol) {p : ℕ} [Fact p.Prime] {N r n : ℕ} (LL L2 : Letters N) (j : ℕ)
    (e : Fin n ↪o Fin r) :
    LatData p (GAe p LL j e) (Pol p r L2) (IntPol p (Fin N × Fin r)).toAddSubgroup L2.total := by
  let hfd := pol_fd (p := p) (r := r) L2
  refine
    { stable := GAe_pol_stable LL L2 j e
      fd := hfd
      finW := GAe_pol_finW LL L2 j e
      bound := GAe_pol_bound LL L2 j e
      closed := intPol_zpClosed _
      div := ?_
      graded := ?_
      basis := ?_ }
  · intro a b hab k x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    rw [GAe_E, Submodule.mem_toAddSubgroup]
    exact divided_integral_holds p N r LL j (e a) (e b) (fun h => hab (e.injective h)) k x hx
  · intro μ x hx
    rw [GAe_comp]
    exact intPol_whc _ μ x hx
  · intro U hU
    exact hB p _ U (Submodule.finiteDimensional_of_le hU)

end Formalism.InvariantFactorPaths.PW
