module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem coe_aeval_sym_substAlg {n : ℕ} (φ : V n → V n) (v : V n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    ((MvPolynomial.aeval sym (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) p) : Ev n) : Alt n) =
      pull (fderiv ℂ φ v) ((MvPolynomial.aeval sym p : Ev n) : Alt n) := by
  have h : ((Subalgebra.center ℂ (Alt n)).val.comp ((MvPolynomial.aeval sym).comp
      (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)))) =
      (pull (fderiv ℂ φ v)).comp ((Subalgebra.center ℂ (Alt n)).val.comp (MvPolynomial.aeval sym)) := by
    refine MvPolynomial.algHom_ext fun x => ?_

    simp only [AlgHom.comp_apply, GlobalTheory.ChernPull.substAlg, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, Subalgebra.coe_val, sym, (pull_dz _ _).1, (pull_dz _ _).2, Finset.sum_mul_sum,
    smul_mul_smul_comm, GlobalTheory.ChernPull.jac]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact DFunLike.congr_fun h p

theorem chernAt_comp : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  intro n r _ _ H φ v hφ h2 hu j
  rw [chernAt, chernAt, GlobalTheory.ChernPull.chernPoly_comp hφ h2 hu, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul,
    coe_aeval_sym_substAlg]

end GlobalTheory.CxForm
