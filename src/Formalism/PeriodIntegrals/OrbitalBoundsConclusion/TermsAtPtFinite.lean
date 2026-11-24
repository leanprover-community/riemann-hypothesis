module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DShort
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.TermsAtFiniteOfFrameOpShortFin
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

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem terms_at_point_finite (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermsAtFinite D u u' :=
  PI.TermsAtPtFiniteW.termsAtFinite_of_frameOp_shortFin PI.TermsAtPtFiniteW.frameOp_holds PI.TermsAtPtFiniteW.shortFin_holds D u u'
