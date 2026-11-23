module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.fockTargetGlAction_compact_preserves_jointHarmonics : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  first | exact @GlobalTheory.CompactHarm.fockT_compact_harm | exact GlobalTheory.CompactHarm.fockT_compact_harm | (intros; apply GlobalTheory.CompactHarm.fockT_compact_harm <;> assumption)
