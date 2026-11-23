module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
