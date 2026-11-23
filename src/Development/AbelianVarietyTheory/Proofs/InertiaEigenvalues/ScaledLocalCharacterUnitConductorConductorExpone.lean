module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.RamShift

theorem condOne_condExp : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  intro E _ _ ϖ w hϖ
  obtain ⟨ψ, hψ, hlc, hne⟩ := GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w
  have hcont : Continuous ψ := hlc.continuous
  have hnorm : ∀ t, ‖ψ t‖ = 1 := fun t => by
    rw [hψ]; exact Circle.norm_coe _
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'
  have hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    rw [← WithZero.exp, ← WithZero.exp_zsmul]
    simp
  have key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
    intro x
    have h1 := hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)
    simp only [hψ] at h1
    rw [map_mul, hval] at h1
    have h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1 := by
      conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]
      exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
    rw [h2] at h1
    exact h1
  unfold condExp
  split_ifs with h1 h2
  · simpa using h1
  · exact h2.choose_spec
  · exact absurd ⟨-n, key⟩ h2

end GlobalTheory.RamShift
