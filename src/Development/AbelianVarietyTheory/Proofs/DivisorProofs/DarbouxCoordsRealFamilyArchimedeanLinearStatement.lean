module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.darbouxCoords_real_family_archimedean_linear : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  first | exact @GlobalTheory.RealDirCoord.darboux_real_coords | exact GlobalTheory.RealDirCoord.darboux_real_coords | (intros; apply GlobalTheory.RealDirCoord.darboux_real_coords <;> assumption)
