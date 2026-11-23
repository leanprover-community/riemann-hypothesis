module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.siegelTorusElement_real_components_of_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  exact @GlobalTheory.TorusDict.torus_dict
