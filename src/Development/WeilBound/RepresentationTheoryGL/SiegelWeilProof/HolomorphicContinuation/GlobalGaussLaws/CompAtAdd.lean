module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilBH

variable {D : D7} {n : ℕ}

theorem compAt_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem pointAt {m : ℕ} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (hfr : IsUnit fr.det) (x₀ : Mx D m n) (u : Fin m → Fin n → ℂ) :
    ∃ x : Mx D m n, fr⁻¹ * compAt θ τ x = Matrix.of u ∧ (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x₀) ∧
      x.map (finPart D) = x₀.map (finPart D) := by
  obtain ⟨L, _, hLf, hLz⟩ :=
    Formalism.IndefR.Eqv.lineAtExists_holds D θ hθ m n τ (fr * Matrix.of u - compAt θ τ x₀)
  refine ⟨x₀ + L 1, ?_, ?_, ?_⟩
  · rw [compAt_add, hLz 1 τ, if_pos rfl, Complex.ofReal_one, one_smul]
    have hs : compAt θ τ x₀ + (fr * Matrix.of u - compAt θ τ x₀) = fr * Matrix.of u := by abel
    rw [hs]
    exact Matrix.nonsing_inv_mul_cancel_left _ _ hfr
  · intro τ' h
    rw [compAt_add, hLz 1 τ', if_neg h, add_zero]
  · ext i j
    have h1 := congrFun (congrFun (hLf 1) i) j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), Matrix.zero_apply] at h1 ⊢
    rw [h1, add_zero]

end PositivityTheory.Rg.Sw.Glob.DilBH
