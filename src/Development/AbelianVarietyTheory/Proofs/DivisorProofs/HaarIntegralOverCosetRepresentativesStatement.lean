module

public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentatives
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply

@[expose] public section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.haar_integral_over_coset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  first | exact @GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | exact GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | (intros; apply GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets <;> assumption)
