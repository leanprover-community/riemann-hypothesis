module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPsi

open Formalism.QuantumDeterminants

theorem hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem inv_fix {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) {v : Fin n → ℂ}
    (h : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]

theorem uw_inv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  obtain ⟨hu, hi⟩ := (uHGroup _ _ (hpk_unit k r)).2.2 g hg.1
  exact ⟨hi, fun a => ⟨inv_fix hu (hg.2.1 a).1, inv_fix hu (hg.2.1 a).2⟩, inv_fix hu hg.2.2⟩

theorem uw_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) (hg' : g' ∈ UWset k r z) : g * g' ∈ UWset k r z := by
  refine ⟨(uHGroup _ _ (hpk_unit k r)).2.1 g hg.1 g' hg'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).1, (hg.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).2, (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hg'.2.2, hg.2.2]

theorem psi_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  intro k r z c hz
  refine ⟨fun g => ?_, fun m hm m' hm' => ⟨(nSubgroup k r).2.1 m hm m' hm', (psiChar k r z c hz m hm).1 m' hm'⟩,
    fun m hm => ⟨(nSubgroup k r).2.2 m hm, ?_⟩, fun g hg m hm => ?_,
    fun g hg g' hg' => ⟨uw_mul hg hg', uw_inv hg, hg.1⟩, fun m hm => hm.1⟩
  · unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [← BesselUnipotentEquiv.star_psi_inv z c hz m hm, star_star]
  · have hu := ((uHGroup _ _ (hpk_unit k r)).2.2 g hg.1).1
    have h1 := uWNormal k r z hz g hg m hm
    have h2 := uWNormal k r z hz g⁻¹ (uw_inv hg) m hm
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at h2
    refine ⟨h1.1, h2.1, ?_, ?_⟩
    · unfold psi; rw [h1.2]
    · unfold psi; rw [h2.2]

end GlobalTheory.BesselPsi
