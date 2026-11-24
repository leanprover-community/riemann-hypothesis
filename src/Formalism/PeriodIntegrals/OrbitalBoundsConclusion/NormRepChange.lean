module

public import Formalism.PeriodIntegrals.NormRepChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.GlobEntry
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NormRepMoveOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.StepGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.TraceIntOfMulDd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_representative_move (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (hS : Formalism.L2.SG.TermDef.TermStable D u u') (hE : Formalism.L2.SG.TermDef.TermEqIff D u u') (hF : Formalism.L2.SG.TermDef.TermFun D u u') (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hsig : (Formalism.MainNotions.S.VS D).SigOK) : PI.NormRepChange.NormRepMove D u u' :=
  PI.NRCW.normRepMove_of_steps D u u' hE (PI.NRCW.stepExp D) (PI.NRCW.stepGram D) (PI.NRCW.stepGlob D)
    (PI.NRCW.stepLoc D) (PI.NRCW.stepTr D)
