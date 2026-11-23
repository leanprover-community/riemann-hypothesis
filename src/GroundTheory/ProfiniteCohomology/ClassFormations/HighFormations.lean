module

public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLimitDefs
public import Mathlib.NumberTheory.LocalField.Basic
public import GroundTheory.ProfiniteCohomology.ClassFormations.SubsingletonCohomologyTopOfThreeLeInt
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem subsingleton_cohomology_galUnits_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (galUnits.{0} K Ksep) r) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_top_of_three_le hr

end Local

section Global

open GroundTheory.Global

theorem subsingleton_cohomology_classLimitRep_of_three_le (K : FiniteSubfield) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (classLimitRep K) r) :=
  (globalClassFormation K).subsingleton_cohomology_top_of_three_le_int hr

end Global

end GroundTheory.ProfCoh
