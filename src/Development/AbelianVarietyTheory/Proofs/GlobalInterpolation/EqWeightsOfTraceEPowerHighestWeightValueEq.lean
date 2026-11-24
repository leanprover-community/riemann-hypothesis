module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinkedStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEqStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeriesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))
  have gν := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_
  refine GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
