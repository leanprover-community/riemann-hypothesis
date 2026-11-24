module

public import Formalism.SharpRestriction.GrowthBounds.AevalValuation.MemSupportedOf
public import Formalism.SharpRestriction.GrowthBounds.AevalValuation.ValGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.PhMonomialMul
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients
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

namespace Formalism.MainNotions.TraceSpectra

theorem restChain : Formalism.MainNotions.PairMembershipBlocks.RestChain :=
  restChain_of valAeval valFilt Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.phMon Formalism.MainNotions.LetterSubstitution.compPh Formalism.MainNotions.LetterSubstitution.fdigPh
    Formalism.MainNotions.LetterSubstitution.fdigSum

theorem stmtE (D : Formalism.BasicNotions.D7) : tableLineDegreeFive.ClosedFormOfAdmitted D := Formalism.MainNotions.PairMembershipBlocks.stmtE_of_chain D restChain

end Formalism.MainNotions.TraceSpectra
