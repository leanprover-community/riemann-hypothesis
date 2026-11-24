module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementP
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.TwoTorsionIntegral
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

universe u v

namespace Formalism.L2.Th1.A

theorem twoTorsionZ : TwoTorsionZ.{u} := two_torsion_integral
theorem plusZ : PlusZ.{u} := addition_integral
theorem wpInU : WpInU.{u} := wpInU_of wpShape
theorem tInZ : TInZ.{u} := tInZ_of wpShape

theorem bridgeWp : BridgeWp := bridgeWp_of wpCleared
theorem bridgeLaw : BridgeLaw := bridgeLaw_of coeffMem fglLog halfSpec halfLog
theorem bridgeCurve : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR

end Formalism.L2.Th1.A
