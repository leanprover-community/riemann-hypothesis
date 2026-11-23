module

public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.DworkPowerSeriesWeights
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LetterLogIntegrality
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.OneLetterJetKernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel

open Formalism.MainNotions Formalism.DworkPowerSeriesWeights Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality

theorem tieB_of (hB4 : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]),
      product_zeroth_first_parts.B3 l d be → product_zeroth_first_parts.B4 l d be →
      (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) ∧
        MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de1 be))) = 1) ∧
      (Integral (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) ∧
        MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp (de2 be))) = 1)) :
    TieB := by
  intro l _ d _ h5 h2 he be h1 hb2 h3 h4
  obtain ⟨K0, hK0, hU⟩ := wfrac_unram (l := l) (by omega)
  obtain ⟨ζ, hζ⟩ := exists_prim l (l ^ d - 1) (by
    have : 1 < l ^ d := Nat.one_lt_pow (by omega) (by omega)
    omega)
  refine ⟨K0, ζ, hU, hζ, ?_⟩
  unfold BHyp
  exact ⟨fun n => hK0 _ (h1 n), torus_invariant_of_teichmuller l d be ζ hζ hb2, no_low_bidegree_of_vanishing l d be h3, hB4 l d be h3 h4⟩

theorem tieB : TieB := tieB_of integrality_of_letter_log

end Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel

namespace Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

open Formalism.MainNotions Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel

end Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights
