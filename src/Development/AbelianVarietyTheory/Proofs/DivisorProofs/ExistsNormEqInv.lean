module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.NormFvFacts

theorem absNorm_gt_one (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast (omega : 1 < Ideal.absNorm v.asIdeal)

theorem norm_eq_zpow (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨(Valued.v x).log, ?_⟩
  simp only [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow,
    NNReal.coe_natCast]

theorem exists_norm_eq_inv (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  refine ⟨((π : F) : v.adicCompletion F), ?_⟩
  simp only [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    WithZero.log_exp, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

end GlobalTheory.NormFvFacts
