module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.AdicCont

theorem norm_le_one_of_monic_root_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    (P : K[X]) (hm : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {y : K} (hy : P.eval y = 0) : ‖y‖ ≤ 1 := by
  apply GlobalTheory.NormEvalSubBound.norm_le_one_of_root <;> assumption

theorem continuous_adic (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf
  have hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hiq

  have h1 : ∀ x : O, ‖f x‖ ≤ 1 := by
    intro x
    obtain ⟨p, hpm, hpx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    let g : ℤ_[l] →+* Qbar l := f.comp (algebraMap ℤ_[l] O)
    refine norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_
    · rw [coeff_map]
      simp only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]
      exact (p.coeff i).2
    · have := congrArg f hpx
      rw [hom_eval₂, map_zero] at this
      rw [eval_map]
      exact this

  have hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hlnorm
    have : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hr : ‖f ϖ‖ < 1 := by
    have he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O) := by
      rw [hlu, ← mul_assoc, Units.inv_mul, one_mul]
    have hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]
      calc ‖f ((u⁻¹ : Oˣ) : O)‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (h1 _) (by positivity)
        _ = _ := one_mul _
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖f ϖ‖ ^ e := one_le_pow₀ hge
    linarith
  have hcont : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    rw [dist_zero_right]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖f a‖ * ‖f ϖ‖ ^ n ≤ 1 * ‖f ϖ‖ ^ n := mul_le_mul_of_nonneg_right (h1 a) (by positivity)
      _ < ε := by rwa [one_mul]
  exact continuous_of_continuousAt_zero f hcont

end GlobalTheory.AdicCont

end
