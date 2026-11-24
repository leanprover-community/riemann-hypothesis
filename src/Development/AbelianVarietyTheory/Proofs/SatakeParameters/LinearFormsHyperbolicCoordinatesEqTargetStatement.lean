module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.linearForms_hyperbolicCoordinates_eq_target : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  first | exact @GlobalTheory.KerStd.HypCoord.linForm_hypZ | exact GlobalTheory.KerStd.HypCoord.linForm_hypZ | (intros; apply GlobalTheory.KerStd.HypCoord.linForm_hypZ <;> assumption)
