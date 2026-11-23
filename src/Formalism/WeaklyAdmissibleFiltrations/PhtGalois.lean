module

public import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExLattice
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExistsPeriodRingDataHolds
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.TrivCrys
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.WachCol
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem pht_galois : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe ∧ TrivCrys ∧ ExLattice ∧ ExPD ∧ WachCol :=
  ⟨finiteCocycles_properties.1, finiteCocycles_properties.2.1, finiteCocycles_properties.2.2.1, finiteCocycles_properties.2.2.2, trivialIsCrystalline_holds,
    existsStableLattice_holds, existsPeriodRingData_holds, cokernelLengthEqWach_holds⟩

end Formalism.WeaklyAdmissibleFiltrations
