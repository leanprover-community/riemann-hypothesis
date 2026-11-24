module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Filtration

@[expose] public section

namespace GlobalTheory.EqZeroOfMemMaximalPow

theorem eq_zero_of_mem_pow_maximal {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  by_contra hy
  have hJ : LinearMap.ker (LinearMap.toSpanSingleton R R y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hmem : y ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · have hi := h (⟨m, hm⟩, i)
      simpa [smul_eq_mul, Ideal.mul_top] using hi
  obtain ⟨⟨r, hr⟩, hry⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m y).mp hmem
  have hJr : (1 - r) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, one_smul]
    exact sub_eq_zero.mpr hry.symm
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hle hJr) hr
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory.EqZeroOfMemMaximalPow
