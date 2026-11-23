module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.PeriodIntegrals.UJClassMassAlt
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassItems
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian
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

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem genus_class_mass : PI.UJClassMass2.UJClassMass := _root_.unitary_class_mass_hermitian

theorem classMass_of_D7 (D : D7) : ClassMass D := class_mass_of_genus_classes genus_class_mass D

theorem volume_mass_of_genus_rank (D : D7) (n : ℕ) (hT : VolTie D) (hG : GenusMassAt D n) : volumeAtLevelZero D n :=
  volume_mass_of_class_data D n hT hG (class_number_finite_rank D n) (classMassAt_of D (classMass_of_D7 D) n)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
