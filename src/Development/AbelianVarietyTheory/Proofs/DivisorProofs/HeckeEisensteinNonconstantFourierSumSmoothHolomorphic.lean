module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOnStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBoundStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem bOne_isGood : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  intro F _ _ _ 𝔞 𝔟
  refine GlobalTheory.T.heckeWeightTwo_isGood_of_tsum F _ (fun p σ z => fTerm σ z (p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ×
      NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1.out.1 p.2.1) _
    (fun p σ hσ => GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm F _ _ p.1.out.2.2 σ hσ) (fun p w z hz => GlobalTheory.T.heckeFourierTerm_wirtingerWord_differentiableOn F _ _ p.1.out.2.2 w z hz)
    (GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟) ?_
  intro σ hσ z hz
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟 {σ} isCompact_singleton (by simpa using hσ) {z} isCompact_singleton
    (by simpa using hz) 0
  have hs : Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
      fTerm σ z p.1.out.1 p.2.1) := by
    refine Summable.of_norm_bounded hu fun p => ?_
    have := hb p σ rfl z rfl
    rwa [norm_iteratedFDeriv_zero] at this
  unfold bOne
  exact (hs.tsum_prod' fun c => hs.prod_factor c).symm

end GlobalTheory.HeckeTwo
