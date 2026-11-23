module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace GlobalTheory.RowNGClosed

theorem ooVanish_all : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) := by
  intro D X Y u u' t ht
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht

theorem hermitian_tuple_nondegenerate_gram_step : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    have := X.n_eq; have := D.R.rS_two; have := D.R.r_eq; have := D.R.k_ge; omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => congrFun (congrFun X.B.I.J_herm i) j
  obtain ⟨X0, h0⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  convert h0 using 2
  ext a b
  rfl

theorem closedSteps : CorankOneEquivalence ∧ StepNormals ∧ StepPoints ∧ StepNormOne ∧ NondegenerateGramTuple := by
  have h1 : StepNormOne := VanishingOrbitalPoints.stepNormOne_of_ooVanish ooVanish_all
  exact ⟨CorankRelation.corankOne_equivalence_holds,
    NormalInvariants.stepNormals_of NormalVectorPairings.NmlInv_holds NormalCount.NormCount_holds h1,
    VanishingOrbitalPoints.stepPoints_of_ooVanish ooVanish_all, h1, hermitian_tuple_nondegenerate_gram_step⟩

end GlobalTheory.RowNGClosed
