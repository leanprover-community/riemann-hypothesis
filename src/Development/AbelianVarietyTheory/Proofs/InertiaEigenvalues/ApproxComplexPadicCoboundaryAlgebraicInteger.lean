module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.Interface

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem approx_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  intro l _ r S x a h
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r := by positivity
  obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ
  have hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l]) := by
    intro σ
    exact Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))
  refine ⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩
  · intro σ hσ
    have hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← dist_eq_norm, dist_comm]; exact hy.le
    have hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
      obtain ⟨c, hc⟩ := hdiff σ
      rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r := hδ.le
      calc ((l : ℝ)⁻¹) ^ r * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    have key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) =
        (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) +
        (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) +
        (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])) := by
      have h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l]) := (GlobalTheory.RingBasics.σC_coe σ y).symm
      generalize algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A
      rw [map_sub]
      push_cast
      rw [h1]
      ring
    have hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      simpa only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast] using hAB
    rw [← PadicComplex.norm_extends, key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC]; exact hY
    · rw [norm_neg]; exact hY
  · intro σ _
    have : (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l]) := by ring
    rw [this]
    refine dvd_add (hdiff σ) ?_
    have := map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))
    simpa using this

end GlobalTheory.PMon.Ram
