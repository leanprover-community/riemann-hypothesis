module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UseLoc.Cases

theorem _root_.UpperTheory.KN.exists_cyclic_generator_lam_power_quotient :
    ∀ {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL], Function.Injective (algebraMap O LL) →
      ∀ (lam : O) (a : ℕ), algebraMap O LL lam ≠ 0 → ∃ x₀ : ↥(Xq LL lam a), ∀ x : ↥(Xq LL lam a), ∃ c : O, x = c • x₀ := by
  intro O LL _ _ _ _ lam a hlam
  have hK : algebraMap O LL (lam ^ a) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hlam
  have hmem : ∀ s : LL, Submodule.Quotient.mk (p := intO (O := O) LL) s ∈ Xq LL lam a ↔
      ∃ c : O, algebraMap O LL c = lam ^ a • s := by
    intro s
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  refine ⟨⟨Submodule.Quotient.mk (algebraMap O LL (lam ^ a))⁻¹, (hmem _).2 ⟨1, ?_⟩⟩, ?_⟩
  · rw [Algebra.smul_def, mul_inv_cancel₀ hK, map_one]
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc⟩ := (hmem s).1 hx
    refine ⟨c, Subtype.ext ?_⟩
    have hs : s = c • (algebraMap O LL (lam ^ a))⁻¹ := by
      rw [Algebra.smul_def, hc, Algebra.smul_def, mul_comm (algebraMap O LL (lam ^ a)) s, mul_assoc,
        mul_inv_cancel₀ hK, mul_one]
    change Submodule.Quotient.mk s = c • Submodule.Quotient.mk (p := intO (O := O) LL) (algebraMap O LL (lam ^ a))⁻¹
    rw [← Submodule.Quotient.mk_smul, ← hs]
