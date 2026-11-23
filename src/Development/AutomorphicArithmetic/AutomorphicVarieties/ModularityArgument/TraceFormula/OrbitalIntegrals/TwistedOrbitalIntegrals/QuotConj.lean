module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotConj :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotConj := by
  intro hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH
  have hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H := fun z => by rw [hy]; simp [mul_assoc]
  have hH' : IsClosed (H' : Set G) := by
    have : (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H := Set.ext hy'
    rw [this]
    exact hH.preimage (by fun_prop)
  have hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b := fun a ha b hb => by
    have := (hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq
    have h : y * a * b = y * b * a := by simpa [← mul_assoc] using this
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  obtain ⟨s1, i1, -⟩ := hC G H hH hc μ h1
  obtain ⟨s2, i2, -⟩ := hC G H' hH' hc' μ' h2
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ' := fun f hf => by
    rw [← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm,
      lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g) := ⟨hρ.1.comp (measurable_const_mul y), fun g => by
      rw [← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by
      rw [← hFH _ ((hy' h).1 hh) (y * g)]; simp [mul_assoc]) _ hρ']
    exact integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ := fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by
      rw [← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [quotIntegral, quotIntegral, dite_eq_right hex, dite_eq_right hex']
