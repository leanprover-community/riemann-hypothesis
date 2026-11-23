module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem integral_weight_holds : IntWt := by
  unfold IntWt ForRep
  intro n ε H _ _ _ ρ hρ ν x hx hwt a
  have hD := isDerivedOn_smE hρ
  have hG := (isWtOn_iff hρ hD x ν).2 hwt
  let θ : Fin n → ℝ := Pi.single a (2 * Real.pi)
  have hdiag : (diagonal fun b => Complex.exp (↑(θ b) * Complex.I)) = 1 := by
    rw [← diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      have : θ b = 2 * Real.pi := by simp [θ]
      rw [this]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · have : θ b = 0 := by simp [θ, hb]
      rw [this]
      simp
  have hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := ⟨one_mem _, by simp⟩
  have h1 := hG θ (by rw [hdiag]; exact hK)
  rw [hdiag, hρ.1.1] at h1
  have hsum : ∑ b, ν b * θ b = ν a * (2 * Real.pi) := by
    rw [Finset.sum_eq_single a]
    · simp [θ]
    · intro b _ hb
      simp [θ, hb]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hsum] at h1
  have hx' : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
  have hexp : Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hx'
    have h3 : (Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) - 1) • (x : H) = 0 := by
      rw [sub_smul, ← h1]
      simp
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨m, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h4 : ((ν a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast h4

end PositivityTheory.RgHe3
