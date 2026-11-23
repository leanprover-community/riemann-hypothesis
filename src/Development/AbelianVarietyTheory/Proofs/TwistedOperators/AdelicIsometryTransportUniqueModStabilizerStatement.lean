module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer
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

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S hS n be be' hL hbe x hx x'
  first
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL hbe x hx x'
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL.toIsLattice hbe x hx x' 
