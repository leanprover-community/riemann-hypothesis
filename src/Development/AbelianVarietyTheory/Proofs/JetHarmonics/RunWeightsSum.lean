module

public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EntriesOfGaps
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ThetaMemLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.RunDepth

theorem run_weights_sum : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (fR Tp hK j).n ∧ (kaR Tp hK j).n = (fR Tp hK j).n + Tp.TO * (lR Tp hK j).n ∧ WeightFamilies.dimY D j ≤ Tp.TO ∧ D.R.r ≤ (fR Tp hK j).n := by
  intro D L Pm Tp hK j hj
  have hP : (fR Tp hK j).n = Tp.nP := rfl
  have hW : (lR Tp hK j).n = Tp.nWn := rfl
  refine ⟨GlobalTheory.RunWeightTest.isF'_fWt _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [hP, hW, ← Tp.split]; exact kaWt_n D hK _ j
  · rw [GlobalTheory.DepthBoundTest.dimY_eq_flag hj, ← Tp.Dp_eq]
    have := Tp.TO_40
    omega
  · rw [hP, Tp.nP_eq]
    have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
    nlinarith

end GlobalTheory.RunDepth
