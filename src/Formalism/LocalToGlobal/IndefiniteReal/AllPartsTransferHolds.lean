module

public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferOfFacts
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing
public import Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
public import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
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

namespace Formalism.IndefR.LatticeTransfer

theorem dimSq : DimSq := dimSq_of schur

theorem idemP : IdemP := idemP_of charFacts

theorem core : Core := core_of charFacts keyZero schur idemP

theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
