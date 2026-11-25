module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LogNormEstimates
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
public import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.AdmissibleVectors
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.BoundedOperators
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CommutatorAdjointHolds
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GrowthOfBasic
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.KSpanFinB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CasScalar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LocalPointData
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CasimirRealScalar
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

theorem GlobalTheory.HcPort.kfinDense_UJC {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} :=
  _root_.GlobalTheory.CompactRep.dense_isKFin n ε H σ hσ

section

open Matrix Topology Filter
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_kfin_near_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (_hw : w ∈ smD ε σ) {δ : ℝ} (hδ : 0 < δ) : ∃ a : H, Formalism.MainNotions.S.IsKFin ε σ a ∧ ‖a - w‖ < δ := by
  obtain ⟨a, ha, hK⟩ := Metric.dense_iff.1 (kfinDense_UJC hσ) w δ hδ
  exact ⟨a, hK, by rwa [Metric.mem_ball, dist_eq_norm] at ha⟩

end GlobalTheory.HcPort

end
