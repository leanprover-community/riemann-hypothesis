module

public import Formalism.LocalRingCardinality.DataHost
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
import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

@[expose] public section

open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.FrobeniusOrbits
open _root_.Formalism.L2.DIV

namespace GlobalTheory.Formalism.L2.Col

namespace HostOk

variable {R : Ranks} {H : _root_.Formalism.BasicNotions.Host R} (T : Frame H)

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply (H.φ₀.comp (σ : H.E →+* H.E)) x
  have h2 := H.conjE_apply H.φ₀ (σ x)
  exact h1.trans h2.symm

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_b (g : R.Psi) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD :=
  (H.galE_mem_Psi_iff _).1 (by rw [galE_sigmaOf]; exact g.2)

theorem d_pos (H : _root_.Formalism.BasicNotions.Host R) : 0 < H.d := H.hyp.2.1.pos

theorem b_sq (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_b (H : _root_.Formalism.BasicNotions.Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem b_ne (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ≠ -H.sqrtMinusD := by
  intro h
  have h0 : H.sqrtMinusD = 0 := by
    have : (2 : H.E) * H.sqrtMinusD = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h1 := b_sq H
  rw [h0] at h1
  have h2 : (H.d : H.E) = 0 := by linear_combination h1
  have h3 : H.d = 0 := by exact_mod_cast h2
  exact (d_pos H).ne' h3

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

end HostOk

end GlobalTheory.Formalism.L2.Col
