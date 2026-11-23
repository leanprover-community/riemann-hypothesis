module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem span_eq_ker_theta_of_distinguished : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 →
    IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  intro l hl x hx hu
  obtain ⟨ξ, h, -, h1⟩ := GlobalTheory.Prism.exists_generator l
  have h0 : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
  obtain ⟨c, hc⟩ : ξ ∣ x := by
    rw [← Ideal.mem_span_singleton, ← h]; exact hx
  have hφ := (ainfDelta l).φ_eq x
  have hφ' : (ainfDelta l).φ x = WittVector.frobenius x := rfl
  have hfx : WittVector.frobenius x = WittVector.frobenius ξ * WittVector.frobenius c := by
    rw [hc, map_mul]
  rw [hφ', hfx] at hφ
  have h3 := congrArg (Per.θ l) hφ
  rw [map_mul, h1, map_add (f := _), map_pow, map_mul, map_natCast, hx,
    zero_pow hl.out.ne_zero, zero_add] at h3
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h4 : v * WittVector.frobenius c - 1 ∈ Ideal.span {ξ} := by
    rw [← h, RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
    have h5 : Per.θ l (WittVector.frobenius c) = Per.θ l ((ainfDelta l).δ x) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : OC l) ≠ 0) h3
    rw [h5, ← map_mul, hv, map_one]
  have := (GlobalTheory.Per.AinfComplete.main l ξ fun hu =>  (hu.map (Per.θ l)).ne_zero h0).2
  have h5 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h4) 1
  rw [mul_one, sub_add_cancel] at h5
  have h6 : IsUnit c := by
    rw [← (WittVector.frobeniusEquiv l (OCb l)).symm_apply_apply c]
    exact (isUnit_of_mul_isUnit_right h5).map (WittVector.frobeniusEquiv l (OCb l)).symm
  rw [h, hc, Ideal.span_singleton_mul_right_unit h6]

end GlobalTheory.BSP
