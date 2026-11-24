module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdFromSelfEqOne
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypOfTypical
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WindowSmall
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

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

theorem lemT_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : LemT :=
  lemT_of (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) path_count_finite (atypical_path_small_weight D hAdm.2.2.1) typical_path_orders_small

theorem good_path_weight_of_top_count (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (h41 : TopCountLowerBounds 1088) : GoodPathWeight 1088 :=
  good_path_weight_of_parts 1088 (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) (lemT_of_adm D hAdm) (TE.letter_dictionary_bounds h41)

end Formalism.MainNotions.SelectionLemmas.Pf
