module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpOrbQuot
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootHaar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootJac
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.AmpOrbQ
public import Formalism.PeriodIntegrals.AmpRoot
public import Formalism.PeriodIntegrals.AmpRootH

@[expose] public section

namespace Formalism.MainNotions.S.Pv.LemmaJ

theorem relAtPt_holds : RelAtPt := (show PI.AmpRoot.RelAtPt ↔ RelAtPt from Iff.rfl).mp _root_.amplifier_relation_at_point

theorem rootJac_holds : RootJac := (show PI.AmpRoot.RootJac ↔ RootJac from Iff.rfl).mp _root_.amplifier_root_jacobian

theorem rootHaar_holds : RootHaar := (show PI.AmpRootH.RootHaar ↔ RootHaar from Iff.rfl).mp _root_.amplifier_root_haar

theorem exists_orbQuot₂ : OrbQuotEx := (show PI.AmpOrbQ.OrbQuotEx ↔ OrbQuotEx from Iff.rfl).mp (_root_.orbQuotEx_of_haarLieN (show PI.AmpOrbQ.HaarLieN from Formalism.MainNotions.BridgeCSB.haarLieN))

end Formalism.MainNotions.S.Pv.LemmaJ
