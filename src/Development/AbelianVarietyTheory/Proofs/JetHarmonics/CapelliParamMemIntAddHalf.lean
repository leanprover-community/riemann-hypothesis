module

public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsBesselMapSmBesselCharIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
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

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace GlobalTheory

theorem capelliParam_mem_int_add_half : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → Q.IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, u i = (m : ℝ) + ((k : ℝ) - 1) / 2 := by
  intro k r Wp _ _ _ z π u hz hT hπ i hi
  obtain ⟨u₀, h₀⟩ := GlobalTheory.besType_hcParam k r Wp z π u hz hT hπ
  have ha := (GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW h₀).2
  rw [Finset.mem_Icc] at hi
  have h1 := GlobalTheory.SupNonzero.prod_eq hπ h₀ (-(u i : ℂ))
  have h2 : ∏ s : Fin k, (-(u i : ℂ) + (u (s.val + 1) : ℂ)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨i - 1, by omega⟩) ?_
    have : i - 1 + 1 = i := by omega
    simp [this]
  rw [h2] at h1
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h1
  have e : u i = u₀ t := by exact_mod_cast neg_add_eq_zero.1 ht
  obtain ⟨m, hm⟩ := ha t
  exact ⟨m, by rw [e]; linarith⟩

end GlobalTheory
