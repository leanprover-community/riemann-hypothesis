module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
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

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
