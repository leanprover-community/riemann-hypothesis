module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
