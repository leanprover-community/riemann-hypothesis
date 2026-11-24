module

public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.MassSt
public import Formalism.HermitianLattices.StatementMass
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

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  simp only [conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  apply le_antisymm
  · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
    rintro r ⟨s, hs, h⟩
    show conjO K r ∈ P
    have hrs : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      exact (congrArg star h).trans (star_star _)
    rw [hrs]
    exact hs
  · intro r hr
    rw [Formalism.HermitianLatticesTheory.conjIdeal]
    apply Ideal.subset_span
    refine ⟨conjO K r, hr, ?_⟩
    show (r : K) = star ((conjO K r : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨-, -, h3⟩ := hK
  obtain ⟨θ, t, ht, hθ⟩ := h3 P hP
  refine ⟨θ, ?_⟩
  have htθ : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rw [htθ]
  exact hθ

end NoF


variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]


end ReciprocityTheory.ChartRestriction.L3
