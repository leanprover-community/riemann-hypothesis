module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

theorem laurentConst_eq_of_tendsto :
    ∀ (h : ℂ → ℂ) (s₀ c c' : ℂ), LaurentConst h s₀ c → Tendsto h (𝓝[≠] s₀) (𝓝 c') → c = c' := by
  rintro h s₀ c c' ⟨p, hp0, hp⟩ hh
  have h1 : Tendsto (fun s : ℂ => p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 (c' - c)) := by
    refine (hh.sub hp).congr fun s => ?_
    ring
  have h2 : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).tendsto s₀
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.2 hs
  have h3 : Tendsto (fun s : ℂ => ‖(s - s₀)⁻¹‖) (𝓝[≠] s₀) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp h2)
  by_cases hd : 0 < p.degree
  · exact absurd (p.tendsto_norm_atTop hd h3) (not_tendsto_atTop_of_tendsto_nhds h1.norm)
  · have hp' : p = 0 := by
      rw [Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd), hp0, map_zero]
    subst hp'
    simp only [Polynomial.eval_zero, sub_zero] at hp
    exact tendsto_nhds_unique hp hh

end GlobalTheory.ThetaInner
