module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.GKGlobalise

theorem kFin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) = GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  apply le_antisymm
  · refine sSup_le fun W hW v hv => ?_
    exact ⟨W, hW.1, hv, hW.2⟩
  · rintro v ⟨A, hA, hv, hs⟩
    exact le_sSup (show A ∈ {W : Submodule ℂ (M.H τ) | FiniteDimensional ℂ W ∧
      Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W} from ⟨hA, hs⟩) hv

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun v hv =>
  (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ v).2 ((GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)).2.2.1 v hv)

end GlobalTheory.GKGlobalise
