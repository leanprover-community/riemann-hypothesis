module

public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NabDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.L2.DIV

theorem fockSTen : FockSTen := fockSymTensor_holds
theorem pairRat : PairRat := pairingRational_holds
theorem actRat : ActRat := actionRational_holds
theorem pairNondeg : PairNondeg := pairingNondegenerate_holds
theorem pairPos : PairPos := pairingPositive_holds
theorem basisAtEx : BasisAtEx := latticeBasisExists_holds
theorem nabDelLoc : NabDelLoc := nablaDeltaLocal_holds
theorem nabDelLattice : NabDelLattice := nablaDeltaLattice_holds
theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds
theorem dualFrLattice : DualFrLattice := dualFrameLattice_holds
theorem dualFrHdual : DualFrHdual := dualFrameHdual_holds
theorem tauLatDual : TauLatDual := tauLatticeDual_holds
theorem roundLat : RoundLat := roundLattice_holds
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla := weyl_eq_dual_nabla_holds
theorem pairBDualStd : PairBDualStd := pairBDualStd_of weyl_eq_dual_nabla_holds
theorem pairBDualK : PairBDualK := pairBDualK_of pairBDualStd
theorem pairBDual : PairBDual := pairBDual_of pairBDualStd
theorem nabDelDual : NabDelDual := nabDelDual_of nablaDeltaDescent_holds pairBDualK

end Formalism.L2.DIV
