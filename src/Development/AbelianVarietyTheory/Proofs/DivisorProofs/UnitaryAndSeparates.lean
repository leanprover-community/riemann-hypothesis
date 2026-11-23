module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
