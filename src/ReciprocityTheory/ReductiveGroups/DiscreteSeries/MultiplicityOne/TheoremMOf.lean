module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.CoefficientIntegralPointwise
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.DerivSmulConstAll
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HalfRatioLeSegmentBaseOfStd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HpkMulVecMulVec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HsInnerSmulSmul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.IsTestGTranslate
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MinorsOnOfDD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SepMinors
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut4
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntIntegrableOf

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 TopH

theorem theoremM_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists)
    (hH : StBeHerm) (hP : StBePos) (hW : StSchurW) (hS : StSInt)
    (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) (hD1 : StBeEquiv) (h2 : StRepro) (h3 : StSmooth)
    (hF : StFrame) (h4a : StInvGroup) (h4b : StInvChar) (h4c : StInvCC) (h5 : StReps) (h6 : StTransM)
    (h7 : StSym) (h7' : StSymBeta) (h8 : StBetaInf) (h9g : StDichoG) (h9w : StDichoW) (h10 : StMixed)
    (hR : RankOneMinors) : ThmM := by
  intro k r Wp _ _ _ D X hD hX ha
  have hGN : GNIntSharp := hIn.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha0 : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) ha
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  have hInt := beInt_integrable_of D X hD hX ha h0 h1 h1'
  have hHV : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ :=
    fun u hu u' hu' η ξ => hH k r Wp D X hD hX u hu u' hu' η ξ
  have hb0 : 0 ≤ X.a - AG k r - 1 := le_trans (by unfold AB; positivity) (half_ratio_le_segment_base_of_std D.k_pos ha)
  have hab : AB k r ≤ X.a - (X.a - AG k r - 1) := by
    have := AG_ge (r := r) D.k_pos; linarith
  have hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r,
      ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ (X.a - AG k r - 1) := by
    intro v hv
    obtain ⟨Cp, hCp⟩ := h1 k r Wp D X hD hX d hd X.a X.a X.w (w_mem X) v hv
    rw [min_self] at hCp
    exact be_bound D X hb0 hCp (hS k r Wp D hD _ (half_ratio_le_segment_base_of_std D.k_pos ha))
  have hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG :=
    fun u hu v hv => (h2 k r Wp D X hD hX ha d hd u hu v hv).1
  have hM : MinorsOn D X := minorsOn_of_DD D X hGN ha0 hd.1 hb0 hab hbe hRep hHV
    (minors_DD hIn hXi h3 (stCut0 hIn) (stCut1p hIn) (stCut2 hIn) (stCut3 hIn) (stCut4 hIn) h8 h7' h4c h4a
      hD1 h0 h1 h1' hW hF h9g h9w h10 D X hD hX ha)
  exact multOne_of_minors D X hHV (fun u hu ξ => hP k r Wp D X hD hX ha u hu ξ) hInt
    (fun u hu u' hu' h hh m hm => (hD1 k r Wp D X hD hX u u' (hInt u hu u' hu') h hh m hm).1) hM

end ReciprocityTheory.ChartRestriction.DS.Mult1
