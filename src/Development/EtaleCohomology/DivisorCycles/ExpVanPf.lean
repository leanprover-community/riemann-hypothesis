module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Mathlib.RingTheory.PowerSeries.Derivative
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

theorem deriv_E (Y : Mat C N) (p : Fin N × Fin N) :
    PowerSeries.derivative (R := C) (E Y p) = MvPolynomial.aeval (E Y) (DX Y (MvPolynomial.X p)) := by
  rw [DX, MvPolynomial.mkDerivation_X]
  ext n

  rw [PowerSeries.coeff_derivative, map_sum, map_sum]
  simp only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  have hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹ := by
    have : ((n:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ]; push_cast; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]; ring

omit [CharZero C] in
theorem cc_F (Y : Mat C N) (f : MP C N) : PowerSeries.constantCoeff (F Y f) = ev 1 f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F, ev]
  | add p q hp hq => simp only [F, ev, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *
    rw [hp]; congr 1
    simp [E]

theorem deriv_F (Y : Mat C N) (f : MP C N) :
    PowerSeries.derivative (R := C) (F Y f) = F Y (DX Y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F]
  | add p q hp hq => simp only [F, map_add (f := _)] at * <;> rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add (f := _)] at *
    rw [hp, ← deriv_E]

theorem coeff_F (hT : TanField) (S : Submonoid (Mat C N)) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) :
    ∀ k, ∀ f ∈ Van (S : Set (Mat C N)), PowerSeries.coeff k (F Y f) = 0 := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]
    exact hf 1 S.one_mem
  | succ k ih =>
    intro f hf
    have h := ih _ ((hT C N S Y).1 hY f hf)
    rw [← deriv_F, PowerSeries.coeff_derivative] at h
    have : ((k:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp h).resolve_right this

end LateralTheory.DivDb.ExpVanPf

namespace LateralTheory.DivDb
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
