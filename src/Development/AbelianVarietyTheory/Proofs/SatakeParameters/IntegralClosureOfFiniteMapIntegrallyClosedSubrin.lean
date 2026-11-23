module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem integralClosure_of_finite_map : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hfin hB hB' hK hL
  letI : Algebra B B' := φ.toAlgebra
  haveI : IsScalarTower B B' L := IsScalarTower.of_algebraMap_eq fun x => (hφ x).symm
  have fracK : IsFractionRing B K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hK z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have fracL : IsFractionRing B' L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hL z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have hint : (algebraMap B B').IsIntegral := RingHom.Finite.to_isIntegral hfin
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : IsIntegral B (⟨y, hy⟩ : B') := hint _
    have := h1.algebraMap (B := L)
    simpa using this
  · obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff K).mp hB hx
    rw [← hc]; exact c.2
  · have h2 : IsIntegral B' y := hy.tower_top
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff L).mp hB' h2
    rw [← hc]; exact c.2

end GlobalTheory.W1
