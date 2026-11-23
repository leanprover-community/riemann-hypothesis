module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem exists_pow_mem_congUnits : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  intro F _ _ 𝔣 h𝔣
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hpos : 0 < Nat.card (𝓞 F ⧸ 𝔣)ˣ := Nat.card_pos
  refine ⟨2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ, by omega, fun u => ⟨?_, fun σ => ?_⟩⟩
  · have h1 : (Units.map (Ideal.Quotient.mk 𝔣 : 𝓞 F →* 𝓞 F ⧸ 𝔣) u) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) = 1 := by
      rw [mul_comm, pow_mul, pow_card_eq_one', one_pow]
    have h2 : Ideal.Quotient.mk 𝔣 ((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) = Ideal.Quotient.mk 𝔣 1 := by
      have h3 := congrArg (fun z : (𝓞 F ⧸ 𝔣)ˣ => (z : 𝓞 F ⧸ 𝔣)) h1
      simpa using h3
    exact Ideal.Quotient.eq.mp h2
  · have hne : σ (((u : 𝓞 F)) : F) ≠ 0 := by
      rw [Ne, map_eq_zero]
      simp
    have h : (((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) : F) = (((u : 𝓞 F)) : F) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) := by
      simp
    rw [h, map_pow, pow_mul]
    exact pow_pos (by positivity) _

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
