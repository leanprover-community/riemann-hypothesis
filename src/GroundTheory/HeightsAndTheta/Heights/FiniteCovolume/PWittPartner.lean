module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem WittPartner.proof (h : HermitianForm F E W) : WittPartner.Statement h := by
  intro x₀ hx₀ hiso

  have hne : h.toSesq x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply h.nonsingular.1
    rw [h0, map_zero]
  obtain ⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by
    by_contra hc
    exact hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)

  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1 :=
    ⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩
  have hyx : h.toSesq y x₀ = 1 := by
    rw [← h.isSymm.eq x₀ y, hy, map_one]

  obtain ⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a := ⟨_, rfl⟩
  have ha : conjHom F E a = a := by
    rw [← ha_def]
    exact h.isSymm.eq y y
  have ht : conjHom F E (a / 2) = a / 2 := by
    rw [map_div₀, ha, map_ofNat]

  have hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z := by
    intro z
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]
  refine ⟨y - (a / 2) • x₀, ?_, ?_⟩
  · rw [map_sub, map_smul, hy, hiso, smul_zero, sub_zero]
  · rw [hl]
    simp only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]
    ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
