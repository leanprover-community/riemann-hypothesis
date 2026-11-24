module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsWellDefined
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists

theorem ThmIExists.proof (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩

end GroundTheory.Heights₂.Heights.Inter
