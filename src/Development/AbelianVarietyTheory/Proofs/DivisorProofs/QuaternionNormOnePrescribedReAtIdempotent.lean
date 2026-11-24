module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem quat_norm_one_re_at_idem : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b →
    IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  intro R _ a b ε p q hε ha hb h2 hE t
  obtain ⟨c, hc⟩ := ((h2.mul ha).mul hb)
  have hu : 2 * a * b * ((c⁻¹ : Rˣ) : R) = 1 := by
    rw [← hc]; simp
  set u : R := ((c⁻¹ : Rˣ) : R) with hu_def
  set l : R := (t ^ 2 - a - 1) * u with hl
  refine ⟨⟨ε * t + (1 - ε), ε * (l * b + 1), ε * (l * a * q), ε * (l * p)⟩, ?_, ?_⟩
  · simp only [nrm]
    linear_combination ((t - 1) ^ 2 + (-a * (l * b + 1) ^ 2 - b * (l * a * q) ^ 2 + a * b * (l * p) ^ 2)) * hε
      - ε * (t ^ 2 - a - 1) * hu - l ^ 2 * a * b * hE
  · show ε * (ε * t + (1 - ε)) = ε * t
    linear_combination (t - 1) * hε

end GlobalTheory
