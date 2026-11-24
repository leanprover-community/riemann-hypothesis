module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ImportsAlt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CompactPowers.ExistsPowSmulMemOfIsCompact
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.IdempotentFibres.TraceNeZeroOfIdem
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.NabsPow
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.StepModPf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.SupportedComposition.ProjectionOfOrbitClosure
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

namespace PositivityTheory.RgUd.T.Nil.Orb.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbP [CharZero k] : OrbP (k := k) :=
  Oasm.orbP_of k (Ozn.zNClosed (k := k)) (Ofib.fibZN (k := k)) (BReps.reps k) (BStep.stepMod_pf k) (BModbound.modBound k)

end PositivityTheory.RgUd.T.Nil.Orb.Final
