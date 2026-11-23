module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.TheoremIIOfEdgeBoundConstants
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ColSpanMap
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GoodRankOfPrim
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.NumericProductInequality
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.InitialLevelMonoWeights
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Pf14

theorem theorem_II_of_edge_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR : RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound_constants D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 manyEdges s7 asm num hA h14a h14b hR

theorem prvE_degree_five_of_adm_sources_realisable (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restEdge_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hR3 hRC)

theorem theorem_II_of_cloud_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  prvE_degree_five_of_adm_sources_realisable D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b (sources_realisable_holds D CLa Ck Crk Cdeg CLa' CD Csz) hRC

theorem theorem_II_of_cloud_bound_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloud_of_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_cloud_bound_Y (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudY D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudX_of_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_split_cloud_bounds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (h6a : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg) (h6b : RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudY_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 h6a h6b)

end Formalism.MainNotions.Pf14
