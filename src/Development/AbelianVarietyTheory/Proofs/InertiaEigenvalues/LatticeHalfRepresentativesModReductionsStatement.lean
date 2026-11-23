module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHalfRepresentativesModReductions
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.lattice_half_representatives_mod_reductions : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  first | exact @GlobalTheory.ZRepBlock.zrep_block | exact GlobalTheory.ZRepBlock.zrep_block | (intros; apply GlobalTheory.ZRepBlock.zrep_block <;> assumption)
