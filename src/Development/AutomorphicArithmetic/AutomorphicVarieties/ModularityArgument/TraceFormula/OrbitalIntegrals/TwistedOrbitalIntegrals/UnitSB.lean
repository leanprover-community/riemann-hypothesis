module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.LocalFields.Uniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.unitSB :
    UpperTheory.V.Z.Tf.Orb.UnitSB := by
  intro E _ _ _ _ n
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have ho : IsOpen (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isOpen_integralGL E n
  have hc : IsCompact (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isCompact_integralGL E n
  refine ⟨ho, hc, ?_, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    by_cases hx : x ∈ (unitGL (n := Fin n) E : Set (GL (Fin n) E))
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_mem hx, Set.indicator_of_mem hy, Pi.one_apply]
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
