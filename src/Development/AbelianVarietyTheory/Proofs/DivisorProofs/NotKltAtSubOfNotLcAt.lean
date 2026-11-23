module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x →
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D x hD hk hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, hd⟩ := hk
  obtain ⟨m', f, hm', hf, hDf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x
  obtain ⟨m₁, g₁, hm₁, hg₁, hd₁⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hDf
  rw [one_smul] at hg₁
  have hnl := (GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ hg₁).not.1 hlc
  push_neg at hnl
  obtain ⟨E, hE, hlt⟩ := hnl
  rw [hd₁, one_mul] at hlt
  set a := discrep E η m g with ha
  set t : ℚ := (E.ord f : ℚ) / m' with ht
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)) hm'q.le
  have ha1 := hd E hE
  refine ⟨(-1 - a + t) / (t + 1), div_pos (by linarith) (by linarith), fun δ hδ0 hδ hk' => ?_⟩
  obtain ⟨m₂, g₂, hm₂, hg₂, hd₂⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hDf
  have := ((hg₂.kltAt_iff hn hη hm₂).1 hk') E hE
  rw [hd₂] at this
  have h1 : δ * (t + 1) ≤ -1 - a + t := (le_div_iff₀ (by linarith)).1 hδ
  nlinarith
end GlobalTheory.PairStep
