module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem posDef_conj_toMK {ε : Fin n → Bool} (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

theorem muNext_add_smul (μ D : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    muNext (μ + t • D) i = muNext μ i + t * muNext D i := by
  unfold muNext
  split_ifs <;> simp

theorem phiM_add_smul (μ D : Fin n → ℤ) (t : ℕ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    PhiM (μ + (t : ℤ) • D) y = PhiM μ y * PhiM D y ^ t := by
  unfold PhiM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : lead ((i : ℕ) + 1) y ≠ 0 := hy i
  rw [muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem phiMul : PhiMul := by
  intro n ε μ t x hx k
  have hy := posDef_conj_toMK k hx
  have h1 := phiM_posDef μ hy
  have h2 := phiM_posDef (Dz n) hy
  refine ⟨h1.1, ?_⟩
  unfold phiK
  rw [phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]
  have e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h1.2])
  have e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h2.2])
  rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

end CompanionTheory.RgFd
