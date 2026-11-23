module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorsUnit2
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorsUnit3

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem unit_point (L : PeriodPair) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (h5 : 5 ≤ l) (μ : ℂ_[l])
    (hμ : μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1) (hg2 : ‖μ ^ 4 * ι L.g₂‖ ≤ 1)
    (hg3 : ‖μ ^ 6 * ι L.g₃‖ ≤ 1) (e N : ℕ)
    (he : e = 3 ∧ ‖μ ^ 4 * ι L.g₂‖ < 1 ∨ e = 2 ∧ ‖μ ^ 6 * ι L.g₃‖ < 1) (hlN : ¬ l ∣ N) (heN : ¬ e ∣ N)
    (z : ℂ) (hz : z ∉ L.lattice) (hNz : (N : ℂ) * z ∈ L.lattice) :
    ‖μ ^ 2 * ι (L.weierstrassP z)‖ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := red_norm_natCast l (n := 2) (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by
    have := red_norm_natCast l (n := 3) (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hN : ‖(N : ℂ_[l])‖ = 1 := red_norm_natCast l hlN
  have hΔ : ‖(μ ^ 4 * ι L.g₂) ^ 3 - 27 * (μ ^ 6 * ι L.g₃) ^ 2‖ = 1 := by
    have : (μ ^ 4 * ι L.g₂) ^ 3 - 27 * (μ ^ 6 * ι L.g₃) ^ 2 = μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [this, hμ, norm_one]
  obtain ⟨h, hP⟩ := Formalism.L2.Th1.E.scaled_torsion_point_of_add Formalism.L2.Th1.E.PtOfAdd_of l L ι μ hμ0 z N hNz hz
  rcases he with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
  · exact torsUnit3 ℂ_[l] _ _ h2 h3 hlt hg3 hΔ N hN heN _ _ h hP
  · exact torsUnit2 ℂ_[l] _ _ h2 h3 hg2 hlt hΔ N hN heN _ _ h hP

theorem unit_prod (L : PeriodPair) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (h5 : 5 ≤ l) (μ : ℂ_[l])
    (hμ : μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1) (hg2 : ‖μ ^ 4 * ι L.g₂‖ ≤ 1)
    (hg3 : ‖μ ^ 6 * ι L.g₃‖ ≤ 1) (e N : ℕ)
    (he : e = 3 ∧ ‖μ ^ 4 * ι L.g₂‖ < 1 ∨ e = 2 ∧ ‖μ ^ 6 * ι L.g₃‖ < 1) (hlN : ¬ l ∣ N) (heN : ¬ e ∣ N)
    (T : Finset ℂ) (hT : ∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) :
    ‖μ‖ ^ (2 * T.card) * ‖ι (∏ z ∈ T, L.weierstrassP z)‖ = 1 := by
  have key : ∏ z ∈ T, ‖μ ^ 2 * ι (L.weierstrassP z)‖ = 1 :=
    Finset.prod_eq_one fun z hz =>
      unit_point L l ι h5 μ hμ hg2 hg3 e N he hlN heN z (hT z hz).1 (hT z hz).2
  rw [← key, map_prod, norm_prod]
  simp only [norm_mul, norm_pow, Finset.prod_mul_distrib, Finset.prod_const, pow_mul]

end ReciprocityTheory.ChartRestriction.L1
