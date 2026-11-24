module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatDen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem latDen : (∀ (r : ℕ) (X : Data E r), (∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ) ∧ ∃ n : ℕ, 0 < n ∧ ∀ v ∈ X.Λ, ∀ k, IsIntegral ℤ ((n : E) * v k)) := by
  intro r X
  have hsq : ∀ k : ℤ, (((k.natAbs * k.natAbs : ℕ)) : E) = (k : E) * (k : E) := by
    intro k
    have h : ((k.natAbs * k.natAbs : ℕ) : ℤ) = k * k := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' k
    rw [← Int.cast_natCast, h, Int.cast_mul]
  have hpos : ∀ k : ℤ, k ≠ 0 → 0 < k.natAbs * k.natAbs := fun k hk =>
    Nat.mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨k, hk, hm⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
    refine ⟨_, hpos k hk, ?_⟩
    rw [hsq, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact zsmul_mem hm k
  · obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den X.Λ X.Λ_fg
    refine ⟨_, hpos k hk, fun v hv a => ?_⟩
    rw [hsq, mul_assoc]
    have h1 : IsIntegral ℤ (k : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := k))
    exact h1.mul (hi v hv a)

end GlobalTheory.LatDen
