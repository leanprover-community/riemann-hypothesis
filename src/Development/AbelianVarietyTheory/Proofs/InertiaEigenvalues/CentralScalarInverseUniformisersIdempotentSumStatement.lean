module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSum
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.centralScalar_inverse_uniformisers_idempotent_sum : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  first | exact @GlobalTheory.CentralScalar.centralScalar | exact GlobalTheory.CentralScalar.centralScalar | (intros; apply GlobalTheory.CentralScalar.centralScalar <;> assumption)
