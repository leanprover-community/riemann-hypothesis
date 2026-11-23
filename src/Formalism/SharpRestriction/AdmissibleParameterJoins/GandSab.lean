module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
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

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem four_orbit_conditions_of_proof {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Formalism.MainNotions.OrbitPlaces.Ent D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp C : ℝ} (h : Formalism.MainNotions.OrbitPlaces.Conclusion₂ D L X K Dx T E lev Xe ce sp C) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.OrbitsWithoutOperator D L X K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp ∧
      Formalism.MainNotions.WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.IsotypicPartsInternalDirectSum D Dx T sp := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.MainNotions.J
