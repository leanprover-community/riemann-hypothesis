module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.IdGenRat

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    ∃ r, Presents (l • A) (lbPow (toLB A) l) r := by
  have h := GlobalTheory.CombChern.presents_zpow (presents_toLB A) (l : ℤ)
  rw [natCast_zsmul] at h
  exact ⟨_, h⟩

theorem exists_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  intro X _ _ p hp A z hA
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1
    (GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed X p hp (toLB A) (Closeds.closure {z}) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  obtain ⟨r, κ, -, hz, hy⟩ := hl₁ l hl
  obtain ⟨ρ, hρ⟩ := presents_lbPow_toLB A l
  refine ⟨r, fun i => hρ.rat (κ i), fun i => hρ.rat_mem _, fun i => ?_, fun y hy' => ?_⟩
  · exact (hρ.vanishesAt_rat_iff _).2 (hz i z (subset_closure rfl))
  · have hyZ : y ∉ Closeds.closure ({z} : Set X) := fun h => hy' (specializes_iff_mem_closure.2 h)
    obtain ⟨i, hi⟩ := hy y hyZ
    exact ⟨i, (hρ.generatesAt_rat_iff _).2 hi⟩

end GlobalTheory.IdGenRat
