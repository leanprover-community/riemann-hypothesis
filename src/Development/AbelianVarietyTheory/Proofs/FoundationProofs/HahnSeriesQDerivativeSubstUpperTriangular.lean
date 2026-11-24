module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dite_eq_left hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
