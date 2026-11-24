module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.UnitarySelfGeneration.Mend

theorem specInt_norm_le_one_iff_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

open Polynomial in
theorem specInt_isIntegral_iff_coeff {K L : Type*} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)
    [Algebra O L] [IsScalarTower O K L] (y : L) (hy : IsIntegral K y) :
    IsIntegral O y ↔ ∀ n, (minpoly K y).coeff n ∈ O := by
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]
    exact Subtype.property _
  · intro h
    have hl : minpoly K y ∈ lifts (algebraMap O K) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap K, hq, minpoly.aeval]

end PositivityTheory.UnitarySelfGeneration.Mend
