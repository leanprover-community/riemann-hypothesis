module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

theorem UpperTheory.V.Sd.Wc.exChi :
    UpperTheory.V.Sd.Wc.ExChi := by
  intro G Z _ _ K ζ ω hc hK
  have hcomm : ∀ (z : Z) (g : G), g * ζ z = ζ z * g := fun z g =>
    Subgroup.mem_center_iff.mp (hc z) g
  have hN : ζ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨z, rfl⟩ g
    refine ⟨z, ?_⟩
    rw [hcomm z g, mul_assoc, mul_inv_cancel, mul_one]
  have hrep : ∀ x ∈ K ⊔ ζ.range, ∃ k ∈ K, ∃ z : Z, x = k * ζ z := by
    intro x hx
    obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    exact ⟨k, hk, z, rfl⟩
  have hwd : ∀ k ∈ K, ∀ k' ∈ K, ∀ z z' : Z, k * ζ z = k' * ζ z' → ω z = ω z' := by
    intro k hk k' hk' z z' h
    have h1 : ζ (z' * z⁻¹) = k'⁻¹ * k := by
      rw [map_mul, map_inv]
      calc ζ z' * (ζ z)⁻¹ = k'⁻¹ * (k' * ζ z') * (ζ z)⁻¹ := by group
        _ = k'⁻¹ * (k * ζ z) * (ζ z)⁻¹ := by rw [h]
        _ = k'⁻¹ * k := by group
    have h2 : ω (z' * z⁻¹) = 1 := hK _ (by rw [h1]; exact K.mul_mem (K.inv_mem hk') hk)
    rw [map_mul, map_inv] at h2
    exact (mul_inv_eq_one.mp h2).symm
  choose kf hkf zf hzf using fun h : ↥(K ⊔ ζ.range) => hrep h.1 h.2
  have hval : ∀ (h : ↥(K ⊔ ζ.range)) (k : G), k ∈ K → ∀ z : Z,
      (h : G) = k * ζ z → ω (zf h) = ω z := by
    intro h k hk z hz
    exact hwd _ (hkf h) _ hk _ _ ((hzf h).symm.trans hz)
  refine ⟨{ toFun := fun h => ω (zf h), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (hval 1 1 K.one_mem 1 (by simp)).trans (map_one ω)
  · intro a b
    show ω (zf (a * b)) = ω (zf a) * ω (zf b)
    rw [← map_mul]
    refine hval _ (kf a * kf b) (K.mul_mem (hkf a) (hkf b)) _ ?_
    rw [Subgroup.coe_mul, hzf a, hzf b, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (ζ (zf a)), ← hcomm (zf a) (kf b), mul_assoc]
  · intro h
    exact ⟨⟨kf h, hkf h, zf h, hzf h⟩, fun k hk z hz => hval h k hk z hz⟩
