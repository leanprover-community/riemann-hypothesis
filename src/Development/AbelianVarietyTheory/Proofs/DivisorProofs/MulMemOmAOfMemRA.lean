module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section DualMono

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem rA_le_of_subset {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem div_mem_rA_of_mem {J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ J) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x J :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem mem_omA_iff_mul {I : Finset (Fin (d + 1))} {y : F} :
    y ∈ omA k x I ↔ ∀ i ∈ I, (∏ j, x i / x j) * y ∈ rA k x I := by
  simp [omA, Submodule.mem_iInf]

theorem mul_mem_omA_of_mem_rA {J : Finset (Fin (d + 1))} {r y : F} (hr : r ∈ rA k x J) (hy : y ∈ omA k x J) :
    r * y ∈ omA k x J := by
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  rw [mul_left_comm]
  exact (rA k x J).mul_mem hr (hy i hi)

theorem omA_le_of_subset (hx : ∀ i, x i ≠ 0) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (h : I ⊆ J) :
    omA k x I ≤ omA k x J := by
  obtain ⟨i₀, hi₀⟩ := hI
  intro y hy
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  have e : (∏ j, x i / x j) = (x i / x i₀) ^ (d + 1) * ∏ j, x i₀ / x j := by
    have hc : (x i / x i₀) ^ (d + 1) = ∏ _j : Fin (d + 1), (x i / x i₀) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hx i₀, hx j]
  rw [e, mul_assoc]
  exact (rA k x J).mul_mem ((rA k x J).pow_mem (div_mem_rA_of_mem (h hi₀) i) _) (rA_le_of_subset h (hy i₀ hi₀))

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

end DualMono

end GlobalTheory.PD
