module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix Polynomial

theorem keyInert (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - 1 - (x - 1) * (x ^ (2 * n + 1) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - (-1) ^ n * x ^ (-(n : ℤ))) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, he.add_one.neg_one_pow]
    field_simp
    ring
  · rw [ho.neg_one_pow, ho.add_one.neg_one_pow]
    field_simp
    ring

theorem fixed_mem_range {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (h2 : Module.finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) (t : K) (ht : σ t = t) :
    ∃ c : k, t = algebraMap k K c := by
  classical
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[k] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ τ : K ≃ₐ[k] K, τ = AlgEquiv.refl ∨ τ = σ := by
    intro τ
    by_contra h
    push_neg at h
    have h3 : ({AlgEquiv.refl, σ, τ} : Finset (K ≃ₐ[k] K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)] at h3
    omega
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr (fun τ => by
    rcases hall τ with rfl | rfl
    · rfl
    · exact ht)
  exact ⟨c, hc.symm⟩

end PI.OmVe
