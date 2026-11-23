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

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem IsFinCover.dlog_basis_and_vanish : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  intro k _ _ F K _ _ _ _ _ _ d x h
  obtain ⟨b, hb⟩ := h.exists_basis
  have hu : ∀ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹ ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  refine ⟨⟨b.unitsSMul (fun j => Units.mk0 _ (hu j)), fun j => ?_⟩, fun q hq y hy => ?_⟩
  · rw [Module.Basis.unitsSMul_apply, hb]
    rfl
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      apply AlternatingMap.map_linearDependent
      intro hli
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis b] at h1
      simp at h1
      omega
    | zero => rfl
    | add a c _ _ ha hc => rw [ha, hc, add_zero]
    | smul r a _ ha => rw [ha, smul_zero]

end GlobalTheory.PD
