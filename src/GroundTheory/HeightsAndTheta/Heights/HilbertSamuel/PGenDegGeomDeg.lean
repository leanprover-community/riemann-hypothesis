module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GenDegGeomDeg.proof (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    GenDegGeomDeg.Statement := by
  intro K _ ι _ Ω _ y D A hV hA
  classical
  have h := hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)
  have hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GroundTheory.Heights₂.Heights.HilbertSamuel
